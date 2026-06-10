//! Idiom recogniser — the asm-side dual of the Layer-0 domain
//! vocabulary (lever 4 from issue #11).
//!
//! Recovery (main.rs) emits CFG metadata; this module recognises
//! canonical instruction shapes inside the recovered blocks and tags
//! them with domain-level names, so the surface reads
//! `u64_field_decrement base=r5 off=72 amount=r8` instead of
//! `ldxdw r1, [r5+72]; sub64 r1, r8; stxdw [r5+72], r1`.
//!
//! Starter vocabulary, chosen from shapes that are honestly
//! recognisable WITHOUT dataflow analysis (consecutive instructions
//! inside one basic block, plus one call-window pattern):
//!
//! - `u64_field_increment` / `u64_field_decrement` — the
//!   load/add-or-sub/store-back triple on the same `[base+off]` u64
//!   cell. This is the balance-mutation shape every token lift proves
//!   (`amount ±= x`), and the asm form of `lamports_add`/`lamports_sub`.
//! - `error_propagation_check` — `call f` followed within a short
//!   window by a conditional jump testing r0: the compiled
//!   `Err(e) => return e` propagation seam. p_token's transfer arm
//!   returns ALL its nonzero errors through this shape (the constant
//!   error landings live in the entrypoint prelude; see
//!   `constExitBlocks`), so these tags mark exactly where error-exit
//!   reasoning must cross a call boundary.
//! - `read_discriminator` — the dispatcher's `ldx rD, [r1+0]` load.
//!   Emitted from the already-recovered dispatch site (where r1 is
//!   known to be the input pointer), not from a blind scan.
//!
//! Constant error exits are tagged separately (`constExitBlocks`,
//! main.rs) since they carry a payload (the exit code), not just a
//! shape name.

use solana_sbpf::{ebpf, static_analysis::{Analysis, CfgNode}};

/// One recognised idiom occurrence: the logical PC of the shape's
/// first instruction, the canonical pattern name, and the rendered
/// bindings (registers/offsets the pattern matched).
pub struct Idiom {
    pub pc:     usize,
    pub name:   &'static str,
    pub detail: String,
}

/// How far past a `call` the r0 test may sit. p_token interleaves a
/// spill restore plus the `lsh64/rsh64 r0, 32` unpack of pinocchio's
/// `ProgramError` encoding before testing, so the window is 4.
const CALL_TEST_WINDOW: usize = 4;

fn is_cond_jump_on_r0(insn: &ebpf::Insn) -> bool {
    // JMP/JMP32 class, conditional (not ja/call/exit), reading r0.
    let class = insn.opc & 0x07;
    if class != 0x05 && class != 0x06 { return false; }
    if matches!(insn.opc, ebpf::JA | ebpf::CALL_IMM | ebpf::CALL_REG | ebpf::EXIT) {
        return false;
    }
    insn.dst == 0
}

/// Scan one block for in-block idioms.
fn scan_block(analysis: &Analysis, b: &CfgNode, out: &mut Vec<Idiom>) {
    let insns = &analysis.instructions;
    let r = &b.instructions;
    let mut i = r.start;
    while i < r.end {
        // u64_field_{increment,decrement}: ldxdw v,[base+off];
        // {add64,sub64} v, a; stxdw [base+off], v — consecutive, same
        // base register, same offset, value register threaded through.
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
                    detail: format!("base=r{} off={} amount=r{}",
                                    ld.src, ld.off, alu.src),
                });
                i += 3;
                continue;
            }
        }
        // error_propagation_check: call f; …; cond-jump on r0 within
        // the window. A call always terminates its basic block (the
        // CFG splits at `insn.ptr + 1`), so the r0 test lives in the
        // fall-through successor — follow the single destination edge
        // and scan its head.
        if insns[i].opc == ebpf::CALL_IMM && b.destinations.len() == 1 {
            if let Some(next) = analysis.cfg_nodes.get(&b.destinations[0]) {
                let nr = &next.instructions;
                let window_end = (nr.start + CALL_TEST_WINDOW).min(nr.end);
                if let Some(j) = (nr.start..window_end)
                    .find(|&j| is_cond_jump_on_r0(&insns[j]))
                {
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

/// Scan the recovered arm slice. `dispatch` is the already-recovered
/// dispatcher site `(load_pc, disc_width_bytes)`, emitted as the
/// `read_discriminator` idiom (r1 is the input pointer there by the
/// Solana ABI, which is what makes the tag sound).
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
