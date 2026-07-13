//! Idiom recogniser — asm-side domain vocabulary (lever 4, issue #11).
//!
//! Tags canonical instruction shapes inside recovered blocks without dataflow analysis
//! (consecutive-instruction patterns + one call-window pattern):
//! - `u64_field_increment`/`u64_field_decrement`: ldx/alu/stx triple on the same `[base+off]`
//!   cell — the balance-mutation shape every token lift proves (`lamports_add`/`lamports_sub`).
//! - `error_propagation_check`: `call f` + conditional r0 test within a short fall-through window
//!   — the `Err(e) => return e` seam; marks where error-exit reasoning must cross a call boundary.
//! - `read_discriminator`: emitted from the already-recovered dispatch site (r1 = input pointer
//!   by Solana ABI), not from a blind scan — that's what makes the tag sound.
//!
//! Constant error exits are tagged separately in main.rs (`constExitBlocks`) as they carry a payload.

use solana_sbpf::{
    ebpf,
    static_analysis::{Analysis, CfgNode},
};

/// One recognised idiom: `pc` = logical PC of the pattern's first instruction.
pub struct Idiom {
    pub pc: usize,
    pub name: &'static str,
    pub detail: String,
}

/// Max instructions past a `call` to search for the r0 test. p_token inserts a spill-restore
/// + `lsh64/rsh64 r0,32` pinocchio `ProgramError` unpack before the test, so window = 4.
const CALL_TEST_WINDOW: usize = 4;

fn is_cond_jump_on_r0(insn: &ebpf::Insn) -> bool {
    // JMP/JMP32 class, conditional (excludes ja/call/exit), dst=r0.
    let class = insn.opc & 0x07;
    if class != 0x05 && class != 0x06 {
        return false;
    }
    if matches!(
        insn.opc,
        ebpf::JA | ebpf::CALL_IMM | ebpf::CALL_REG | ebpf::EXIT
    ) {
        return false;
    }
    insn.dst == 0
}

fn scan_block(analysis: &Analysis, b: &CfgNode, out: &mut Vec<Idiom>) {
    let insns = &analysis.instructions;
    let r = &b.instructions;
    let mut i = r.start;
    while i < r.end {
        if i + 2 < r.end {
            let (ld, alu, st) = (&insns[i], &insns[i + 1], &insns[i + 2]);
            if ld.opc == ebpf::LD_DW_REG
                && st.opc == ebpf::ST_DW_REG
                && (alu.opc == ebpf::ADD64_REG || alu.opc == ebpf::SUB64_REG)
                && alu.dst == ld.dst
                && st.src == ld.dst
                && st.dst == ld.src
                && st.off == ld.off
            {
                let name = if alu.opc == ebpf::ADD64_REG {
                    "u64_field_increment"
                } else {
                    "u64_field_decrement"
                };
                out.push(Idiom {
                    pc: i,
                    name,
                    detail: format!("base=r{} off={} amount=r{}", ld.src, ld.off, alu.src),
                });
                i += 3;
                continue;
            }
        }
        // A call always splits the CFG, so the r0 test lives in the fall-through successor.
        if insns[i].opc == ebpf::CALL_IMM && b.destinations.len() == 1 {
            if let Some(next) = analysis.cfg_nodes.get(&b.destinations[0]) {
                let nr = &next.instructions;
                let window_end = (nr.start + CALL_TEST_WINDOW).min(nr.end);
                if let Some(j) = (nr.start..window_end).find(|&j| is_cond_jump_on_r0(&insns[j])) {
                    out.push(Idiom {
                        pc: i,
                        name: "error_propagation_check",
                        detail: format!("call_pc={} test_pc={}", i, j),
                    });
                }
            }
        }
        i += 1;
    }
}

/// Scan the recovered arm slice. `dispatch = (load_pc, disc_width_bytes)` emits a `read_discriminator` idiom.
pub fn scan_arm(
    analysis: &Analysis,
    arm_blocks: &[&CfgNode],
    dispatch: Option<(usize, usize)>,
) -> Vec<Idiom> {
    let mut out = Vec::new();
    if let Some((load_pc, width)) = dispatch {
        out.push(Idiom {
            pc: load_pc,
            name: "read_discriminator",
            detail: format!("width={}", width),
        });
    }
    for b in arm_blocks {
        scan_block(analysis, b, &mut out);
    }
    out.sort_by_key(|i| i.pc);
    out
}
