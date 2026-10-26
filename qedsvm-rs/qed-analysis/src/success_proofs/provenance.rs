//! Rust producer corresponding to AbsInterp.absMap/absStep. This is not a verifier:
//! SuccessInputs still computes its own Lean map and checks every emitted operand pin.
use std::collections::VecDeque;
use std::fmt;

use solana_sbpf::ebpf;

use crate::{
    cfg::{Cfg, Flow},
    image::ProgramImage,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum AVal {
    Top,
    Const(u64),
    InPtr(u64),
    Fp,
    InLoad(&'static str, u64),
}

impl fmt::Display for AVal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Top => f.write_str(".top"),
            Self::Const(n) => write!(f, "(.const {n})"),
            Self::InPtr(o) => write!(f, "(.inPtr {o})"),
            Self::Fp => f.write_str(".fp"),
            Self::InLoad(w, o) => write!(f, "(.inLoad .{w} {o})"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct AState {
    pub regs: [AVal; 11],
    written: Option<Vec<(u64, u64)>>,
}

impl AState {
    fn initial() -> Self {
        let mut regs = std::array::from_fn(|_| AVal::Top);
        regs[1] = AVal::InPtr(0);
        regs[10] = AVal::Fp;
        Self {
            regs,
            written: Some(vec![]),
        }
    }

    fn set(&mut self, dst: u8, value: AVal) {
        if dst != 10 {
            self.regs[dst as usize] = value;
        }
    }

    fn join(&self, other: &Self) -> Self {
        let regs = std::array::from_fn(|r| {
            if self.regs[r] == other.regs[r] {
                self.regs[r].clone()
            } else {
                AVal::Top
            }
        });
        let written = match (&self.written, &other.written) {
            (Some(a), Some(b)) => {
                let mut combined = a.clone();
                combined.extend(b.iter().copied().filter(|range| !a.contains(range)));
                Some(combined)
            }
            _ => None,
        };
        Self { regs, written }
    }

    /// Same implication check as Lean's AState.le.
    fn le(&self, other: &Self) -> bool {
        self.regs
            .iter()
            .zip(&other.regs)
            .all(|(a, b)| *b == AVal::Top || a == b)
            && match (&self.written, &other.written) {
                (_, None) => true,
                (Some(a), Some(b)) => a.iter().all(|r| b.contains(r)),
                (None, Some(_)) => false,
            }
    }

    fn step(&self, i: &ebpf::Insn, flow: &Flow) -> Self {
        let mut out = self.clone();
        match flow {
            Flow::Call(_) | Flow::Syscall { .. } => {
                let keep = if matches!(flow, Flow::Call(_)) { 6 } else { 10 };
                for value in &mut out.regs[..keep] {
                    *value = AVal::Top;
                }
                out.written = None;
                return out;
            }
            _ => {}
        }
        match i.opc {
            ebpf::LD_DW_IMM | ebpf::MOV64_IMM => out.set(i.dst, AVal::Const(i.imm as u64)),
            ebpf::MOV64_REG => out.set(i.dst, self.regs[i.src as usize].clone()),
            ebpf::LD_B_REG | ebpf::LD_H_REG | ebpf::LD_W_REG | ebpf::LD_DW_REG => {
                let value = match (&self.regs[i.src as usize], &self.written) {
                    (AVal::InPtr(base), Some(written)) => {
                        let offset = i128::from(*base) + i128::from(i.off);
                        if offset >= 0 && offset <= i128::from(u64::MAX - 8) {
                            let offset = offset as u64;
                            if written
                                .iter()
                                .all(|&(start, len)| offset + 8 <= start || start + len <= offset)
                            {
                                let width = match i.opc {
                                    ebpf::LD_B_REG => "byte",
                                    ebpf::LD_H_REG => "half",
                                    ebpf::LD_W_REG => "word",
                                    _ => "dword",
                                };
                                AVal::InLoad(width, offset)
                            } else {
                                AVal::Top
                            }
                        } else {
                            AVal::Top
                        }
                    }
                    _ => AVal::Top,
                };
                out.set(i.dst, value);
            }
            opc if matches!(opc & ebpf::BPF_CLS_MASK, ebpf::BPF_ST | ebpf::BPF_STX) => {
                match self.regs[i.dst as usize] {
                    AVal::Fp if i.off <= 0x1000 => {}
                    AVal::InPtr(base) => {
                        let offset = i128::from(base) + i128::from(i.off);
                        if offset >= 0 && offset <= i128::from(u64::MAX - 8) {
                            if let Some(written) = &mut out.written {
                                written.insert(0, (offset as u64, 8));
                            }
                        } else {
                            out.written = None;
                        }
                    }
                    _ => out.written = None,
                }
            }
            opc if matches!(
                opc & ebpf::BPF_CLS_MASK,
                ebpf::BPF_ALU32_LOAD | ebpf::BPF_ALU64_STORE
            ) =>
            {
                out.set(i.dst, AVal::Top)
            }
            _ => {}
        }
        out
    }
}

pub(super) fn abstract_map(
    image: &ProgramImage,
    cfg: &Cfg,
    succ: &[Vec<usize>],
    entry: usize,
) -> Result<Vec<Option<AState>>, String> {
    let mut map = vec![None; image.insns.len()];
    map[entry] = Some(AState::initial());
    let mut work = VecDeque::from([entry]);
    // Match the original producer's fuel and successor/worklist ordering exactly.
    let mut fuel = image.insns.len() * 40;
    while let Some(pc) = work.pop_front() {
        if fuel == 0 {
            return Err("abstract-map worklist exhausted its fuel".into());
        }
        fuel -= 1;
        let out = map[pc]
            .as_ref()
            .unwrap()
            .step(&image.insns[pc], &cfg.flow[pc]);
        let mut next = Vec::new();
        for &q in &succ[pc] {
            let joined = map[q]
                .as_ref()
                .map_or_else(|| out.clone(), |old| old.join(&out));
            if map[q].as_ref() != Some(&joined) {
                map[q] = Some(joined);
                next.push(q);
            }
        }
        for q in next {
            work.push_front(q);
        }
    }
    if !AState::initial().le(map[entry].as_ref().unwrap()) {
        return Err("abstract entry check failed".into());
    }
    for (pc, state) in map.iter().enumerate() {
        if let Some(state) = state {
            let out = state.step(&image.insns[pc], &cfg.flow[pc]);
            if succ[pc]
                .iter()
                .any(|&q| !map[q].as_ref().is_some_and(|other| out.le(other)))
            {
                return Err(format!("abstract post-fixpoint check failed at {pc}"));
            }
        }
    }
    Ok(map)
}
