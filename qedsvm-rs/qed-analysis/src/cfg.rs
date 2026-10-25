//! Function-partitioned control-flow recovery and program-outcome partition.
//!
//! A compiled Solana program has a single program `exit` (LLVM emits one return block per
//! function), so every terminating run ends at that exit with some `r0`, in `sol_panic_`/`abort`,
//! or in a VM fault. This module recovers the function partition (entry + every internal `call`
//! target), infers which functions never return, and classifies each edge into the entry
//! function's exit by what reaches `r0` there. That is the structure the fail-closed half of a
//! whole-program theorem composes over: success edges (`r0 = 0`) versus error-conversion calls.
//!
//! All PCs are logical (decoded-array index; `lddw` = 1), matching Lean and `.pcs` traces.

use std::collections::{BTreeMap, BTreeSet};

use solana_sbpf::{ebpf, program::SBPFVersion};

use crate::image::ProgramImage;

/// Syscalls that never return control to the program.
const NORETURN_SYSCALLS: &[&[u8]] = &[b"abort", b"sol_panic_"];

/// Syscall names recognised for labelling. Unlisted hashes stay `Syscall { name: None }`.
const KNOWN_SYSCALLS: &[&[u8]] = &[
    b"abort",
    b"sol_panic_",
    b"sol_log_",
    b"sol_log_64_",
    b"sol_log_pubkey",
    b"sol_log_compute_units_",
    b"sol_log_data",
    b"sol_memcpy_",
    b"sol_memmove_",
    b"sol_memset_",
    b"sol_memcmp_",
    b"sol_set_return_data",
    b"sol_get_return_data",
    b"sol_get_sysvar",
    b"sol_get_clock_sysvar",
    b"sol_get_rent_sysvar",
    b"sol_invoke_signed_c",
    b"sol_invoke_signed_rust",
    b"sol_create_program_address",
    b"sol_try_find_program_address",
    b"sol_sha256",
    b"sol_keccak256",
    b"sol_secp256k1_recover",
    b"sol_alloc_free_",
];

/// How control leaves one instruction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Flow {
    /// Falls through to `pc + 1`.
    Seq,
    /// Unconditional jump.
    Jump(usize),
    /// Conditional jump: taken target, else `pc + 1`.
    Branch(usize),
    /// Internal call to the function at this logical PC; resumes at `pc + 1` if it returns.
    Call(usize),
    /// Syscall; `name` when the hash matches a known syscall.
    Syscall {
        hash: u32,
        name: Option<&'static str>,
    },
    /// Indirect call (`callx`); its target is not statically recovered.
    CallReg,
    /// `exit`: returns from the current function (the program, for the entry function).
    Exit,
    /// A call whose target could not be resolved (fail loudly downstream).
    Unresolved,
}

/// What reaches `r0` at a point, as seen by a backward walk to the nearest write.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum R0Def {
    /// `mov r0, 0` (or `lddw r0, 0`).
    Zero,
    /// A nonzero constant.
    NonZero(u64),
    /// The return value of the internal function at this PC.
    CallResult(usize),
    /// The return value of a syscall.
    SyscallResult(u32),
    /// Any other write (load, arithmetic, register move).
    Computed,
}

/// One edge into the entry function's program exit, classified by its reaching `r0`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExitEdge {
    /// The predecessor instruction (the edge is `from -> exit`).
    pub from: usize,
    pub r0: BTreeSet<R0Def>,
}

impl ExitEdge {
    /// Every reaching definition is `r0 = 0`: this edge ends the program successfully.
    pub fn is_success(&self) -> bool {
        !self.r0.is_empty() && self.r0.iter().all(|d| *d == R0Def::Zero)
    }
}

/// The entry function's terminal structure.
#[derive(Clone, Debug)]
pub struct Outcomes {
    pub exits: Vec<usize>,
    pub edges: Vec<ExitEdge>,
    /// Call/syscall sites in the entry function that never return (panic paths).
    pub panic_sites: Vec<usize>,
    /// `callx` sites in any function reachable from the entry.
    pub reachable_callx: Vec<usize>,
}

impl Outcomes {
    pub fn success_edges(&self) -> Vec<usize> {
        self.edges
            .iter()
            .filter(|e| e.is_success())
            .map(|e| e.from)
            .collect()
    }
}

pub struct Cfg {
    pub flow: Vec<Flow>,
    pub entry: usize,
    /// Function entry PC -> instructions reachable without leaving the function.
    pub functions: BTreeMap<usize, BTreeSet<usize>>,
    pub noreturn: BTreeSet<usize>,
}

impl Cfg {
    pub fn build(image: &ProgramImage) -> Result<Cfg, String> {
        let flow = decode_flow(image);
        let entry_slot = image.executable.get_entrypoint_instruction_offset();
        let entry = image
            .pc_map
            .slot_to_logical(entry_slot)
            .ok_or_else(|| format!("entrypoint slot {entry_slot} is out of range"))?;
        let mut entries: BTreeSet<usize> = flow
            .iter()
            .filter_map(|f| match f {
                Flow::Call(t) => Some(*t),
                _ => None,
            })
            .collect();
        entries.insert(entry);
        let mut cfg = Cfg {
            flow,
            entry,
            functions: BTreeMap::new(),
            noreturn: BTreeSet::new(),
        };
        // A function is noreturn when no `exit` is reachable once calls into noreturn functions
        // are treated as terminal. Start from "everything returns" and grow to the fixpoint.
        loop {
            cfg.functions = entries.iter().map(|&e| (e, cfg.body(e))).collect();
            let noreturn: BTreeSet<usize> = cfg
                .functions
                .iter()
                .filter(|(_, body)| !body.iter().any(|&p| cfg.flow[p] == Flow::Exit))
                .map(|(&e, _)| e)
                .collect();
            if noreturn == cfg.noreturn {
                return Ok(cfg);
            }
            cfg.noreturn = noreturn;
        }
    }

    /// Whether control stops at `pc` (a call that never returns).
    pub fn is_terminal(&self, pc: usize) -> bool {
        match &self.flow[pc] {
            Flow::Call(t) => self.noreturn.contains(t),
            Flow::Syscall {
                name: Some(name), ..
            } => NORETURN_SYSCALLS.contains(&name.as_bytes()),
            _ => false,
        }
    }

    /// Intra-procedural successors (calls that return resume at `pc + 1`).
    pub fn successors(&self, pc: usize) -> Vec<usize> {
        if self.is_terminal(pc) {
            return Vec::new();
        }
        match self.flow[pc] {
            Flow::Exit | Flow::Unresolved => Vec::new(),
            Flow::Jump(t) => vec![t],
            Flow::Branch(t) => vec![t, pc + 1],
            _ => vec![pc + 1],
        }
    }

    fn body(&self, entry: usize) -> BTreeSet<usize> {
        let mut seen = BTreeSet::new();
        let mut stack = vec![entry];
        while let Some(pc) = stack.pop() {
            if pc < self.flow.len() && seen.insert(pc) {
                stack.extend(self.successors(pc));
            }
        }
        seen
    }

    /// Functions reachable from the entry through internal calls.
    pub fn reachable_functions(&self) -> BTreeSet<usize> {
        let mut seen = BTreeSet::new();
        let mut stack = vec![self.entry];
        while let Some(f) = stack.pop() {
            if !seen.insert(f) {
                continue;
            }
            for &pc in &self.functions[&f] {
                if let Flow::Call(t) = self.flow[pc] {
                    stack.push(t);
                }
            }
        }
        seen
    }

    pub fn outcomes(&self, image: &ProgramImage) -> Outcomes {
        let body = &self.functions[&self.entry];
        let exits: Vec<usize> = body
            .iter()
            .copied()
            .filter(|&p| self.flow[p] == Flow::Exit)
            .collect();
        let mut preds: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
        for &pc in body {
            for s in self.successors(pc) {
                preds.entry(s).or_default().push(pc);
            }
        }
        let mut edges = Vec::new();
        for &x in &exits {
            for &from in preds.get(&x).into_iter().flatten() {
                let r0 = match self.r0_write(image, from) {
                    Some(d) => BTreeSet::from([d]),
                    None => self.r0_defs(image, &preds, from),
                };
                edges.push(ExitEdge { from, r0 });
            }
        }
        let panic_sites = body
            .iter()
            .copied()
            .filter(|&p| self.is_terminal(p))
            .collect();
        let reachable_callx = self
            .reachable_functions()
            .iter()
            .flat_map(|f| self.functions[f].iter().copied())
            .filter(|&p| self.flow[p] == Flow::CallReg)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        Outcomes {
            exits,
            edges,
            panic_sites,
            reachable_callx,
        }
    }

    /// The `r0` definitions reaching the entry of `pc`, walking predecessors to the nearest write.
    fn r0_defs(
        &self,
        image: &ProgramImage,
        preds: &BTreeMap<usize, Vec<usize>>,
        pc: usize,
    ) -> BTreeSet<R0Def> {
        let mut out = BTreeSet::new();
        let mut seen = BTreeSet::new();
        let mut stack = vec![pc];
        while let Some(at) = stack.pop() {
            for &p in preds.get(&at).into_iter().flatten() {
                if !seen.insert(p) {
                    continue;
                }
                match self.r0_write(image, p) {
                    Some(d) => {
                        out.insert(d);
                    }
                    None => stack.push(p),
                }
            }
        }
        out
    }

    /// The `r0` definition made by `pc`, if it writes `r0`.
    fn r0_write(&self, image: &ProgramImage, pc: usize) -> Option<R0Def> {
        match self.flow[pc] {
            Flow::Call(t) => return Some(R0Def::CallResult(t)),
            Flow::Syscall { hash, .. } => return Some(R0Def::SyscallResult(hash)),
            Flow::CallReg | Flow::Unresolved => return Some(R0Def::Computed),
            _ => {}
        }
        let insn = &image.insns[pc];
        // V0 and V3 (the versions `ProgramImage` accepts) keep the classic memory classes, so a
        // `dst` write is exactly an LD (`lddw`), LDX, ALU32, or ALU64 instruction.
        let writes_dst = matches!(
            insn.opc & ebpf::BPF_CLS_MASK,
            ebpf::BPF_LD | ebpf::BPF_LDX | ebpf::BPF_ALU32_LOAD | ebpf::BPF_ALU64_STORE
        );
        if !writes_dst || insn.dst != 0 {
            return None;
        }
        let imm = insn.imm as u64;
        Some(match insn.opc {
            ebpf::MOV64_IMM | ebpf::MOV32_IMM | ebpf::LD_DW_IMM if imm == 0 => R0Def::Zero,
            ebpf::MOV64_IMM | ebpf::LD_DW_IMM => R0Def::NonZero(imm),
            ebpf::MOV32_IMM => R0Def::NonZero(imm & 0xffff_ffff),
            _ => R0Def::Computed,
        })
    }
}

fn syscall_name(hash: u32) -> Option<&'static str> {
    KNOWN_SYSCALLS
        .iter()
        .find(|n| ebpf::hash_symbol_name(n) == hash)
        .map(|n| std::str::from_utf8(n).expect("ascii syscall name"))
}

fn decode_flow(image: &ProgramImage) -> Vec<Flow> {
    let registry = image.executable.get_function_registry();
    let n = image.insns.len();
    let target = |pc: usize, off: i64| -> Option<usize> {
        usize::try_from(image.pc_map.resolve_jump_target(pc, off))
            .ok()
            .filter(|t| *t < n)
    };
    image
        .insns
        .iter()
        .enumerate()
        .map(|(pc, insn)| match insn.opc {
            ebpf::EXIT => Flow::Exit,
            ebpf::JA => target(pc, insn.off as i64).map_or(Flow::Unresolved, Flow::Jump),
            ebpf::CALL_REG => Flow::CallReg,
            ebpf::CALL_IMM => {
                let hash = insn.imm as u32;
                let internal = if image.version == SBPFVersion::V3 {
                    (insn.src == 1).then(|| target(pc, insn.imm)).flatten()
                } else {
                    registry
                        .lookup_by_key(hash)
                        .and_then(|(_, slot)| image.pc_map.slot_to_logical(slot))
                };
                match internal {
                    Some(t) => Flow::Call(t),
                    None if image.version == SBPFVersion::V3 && insn.src == 1 => Flow::Unresolved,
                    None => Flow::Syscall {
                        hash,
                        name: syscall_name(hash),
                    },
                }
            }
            opc if is_cond_jump(opc, image.version) => {
                target(pc, insn.off as i64).map_or(Flow::Unresolved, Flow::Branch)
            }
            _ => Flow::Seq,
        })
        .collect()
}

/// A conditional jump: JMP64 other than `ja`/`call`/`callx`/`exit`, or V3 JMP32 (class 6, which
/// V0 never emits and only V2 would read as PQR).
fn is_cond_jump(opc: u8, version: SBPFVersion) -> bool {
    match opc & ebpf::BPF_CLS_MASK {
        ebpf::BPF_JMP64 => !matches!(opc, ebpf::JA | ebpf::CALL_IMM | ebpf::CALL_REG | ebpf::EXIT),
        ebpf::BPF_JMP32 => version.enable_jmp32(),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;

    fn load(name: &str) -> (ProgramImage, Cfg) {
        let image = ProgramImage::load(Path::new(&format!("../tests/fixtures/{name}")))
            .expect("load fixture");
        let cfg = Cfg::build(&image).expect("build cfg");
        (image, cfg)
    }

    #[test]
    fn p_token_has_one_exit_and_a_clean_outcome_partition() {
        let (image, cfg) = load("p_token.so");
        assert_eq!(cfg.entry, 198);
        let out = cfg.outcomes(&image);
        assert_eq!(out.exits, vec![3542]);
        assert_eq!(
            out.success_edges(),
            vec![
                3575, 3584, 4065, 4141, 4177, 4226, 4237, 4310, 4346, 4391, 4401, 4527, 4556, 4672,
                4679, 4759, 4793, 4825, 4832, 5063, 5070, 5159, 5250, 5426, 5473
            ]
        );
        // The only non-success edge is the error tail's ProgramError -> u64 conversion call.
        let rest: Vec<_> = out.edges.iter().filter(|e| !e.is_success()).collect();
        assert_eq!(rest.len(), 1);
        assert_eq!(rest[0].from, 3541);
        assert_eq!(rest[0].r0, BTreeSet::from([R0Def::CallResult(116)]));
        assert_eq!(out.panic_sites.len(), 12);
        assert!(out.reachable_callx.is_empty());
    }

    #[test]
    fn p_token_panics_bottom_out_in_sol_panic() {
        let (_, cfg) = load("p_token.so");
        assert_eq!(
            cfg.noreturn.iter().copied().collect::<Vec<_>>(),
            vec![10823, 10858, 10862, 10868, 10881, 11177, 11618]
        );
        let sink = &cfg.functions[&10823];
        assert!(sink.iter().any(|&p| matches!(
            cfg.flow[p],
            Flow::Syscall {
                name: Some("sol_panic_"),
                ..
            }
        )));
    }

    #[test]
    fn syscall_sites_are_not_mistaken_for_internal_calls() {
        let (_, cfg) = load("p_token.so");
        // PC 6988 is a relocated `sol_log_` call, not a self-call.
        assert_eq!(
            cfg.flow[6988],
            Flow::Syscall {
                hash: ebpf::hash_symbol_name(b"sol_log_"),
                name: Some("sol_log_"),
            }
        );
    }

    #[test]
    fn pinocchio_escrow_and_spl_token_have_a_single_program_exit() {
        for name in ["libupstream_pinocchio_escrow.so", "token.so"] {
            let (image, cfg) = load(name);
            assert_eq!(cfg.outcomes(&image).exits.len(), 1, "{name}");
        }
        // solana-program builds reach `callx` (formatting vtables); pinocchio builds do not.
        let (image, cfg) = load("token.so");
        assert!(!cfg.outcomes(&image).reachable_callx.is_empty());
        let (image, cfg) = load("libupstream_pinocchio_escrow.so");
        assert!(cfg.outcomes(&image).reachable_callx.is_empty());
    }

    #[test]
    fn every_loadable_fixture_partitions_without_panicking() {
        let mut built = 0;
        for entry in std::fs::read_dir("../tests/fixtures").expect("fixtures dir") {
            let path = entry.expect("dir entry").path();
            if path.extension().is_none_or(|e| e != "so") {
                continue;
            }
            // Some fixtures are deliberately malformed ELFs; only loadable ones are in scope.
            let Ok(image) = ProgramImage::load(&path) else {
                continue;
            };
            let cfg = Cfg::build(&image).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
            let out = cfg.outcomes(&image);
            assert!(
                !out.exits.is_empty() || !cfg.noreturn.is_empty(),
                "{}",
                path.display()
            );
            built += 1;
        }
        assert!(built > 40, "only {built} fixtures loaded");
    }
}
