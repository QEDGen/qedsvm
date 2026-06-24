use solana_sbpf::{ebpf, static_analysis::Analysis};

use super::core::{lean_off, Expr};
use super::input::BinaryCtx;

/// Convert an sBPF `Insn` to Lean constructor syntax. `call_target` provides the resolved callee PC (raw imm is a Murmur3 hash); `jump_target` is the caller-resolved logical target for conditional jumps.
pub(super) fn insn_to_lean_full(
    insn: &ebpf::Insn,
    pc: usize,
    call_target: Option<usize>,
    jump_target: Option<i64>,
) -> Result<String, String> {
    use ebpf::*;
    let (dst, src, off, imm) = (insn.dst, insn.src, insn.off as i64, insn.imm);
    // Caller-resolved logical target; falls back to raw slot-relative sum.
    let jt = || jump_target.unwrap_or((pc as i64) + 1 + off);
    let reg = |n: u8| match n {
        0 => ".r0",
        1 => ".r1",
        2 => ".r2",
        3 => ".r3",
        4 => ".r4",
        5 => ".r5",
        6 => ".r6",
        7 => ".r7",
        8 => ".r8",
        9 => ".r9",
        10 => ".r10",
        _ => "?reg",
    };
    // Negative offsets need parens in Lean syntax (`.r10 -2072` parses as subtraction).
    let offl = lean_off(off);
    Ok(match insn.opc {
        LD_B_REG => format!(".ldx .byte {} {} {}", reg(dst), reg(src), offl),
        LD_H_REG => format!(".ldx .half {} {} {}", reg(dst), reg(src), offl),
        LD_W_REG => format!(".ldx .word {} {} {}", reg(dst), reg(src), offl),
        LD_DW_REG => format!(".ldx .dword {} {} {}", reg(dst), reg(src), offl),
        ST_B_REG => format!(".stx .byte {} {} {}", reg(dst), offl, reg(src)),
        ST_H_REG => format!(".stx .half {} {} {}", reg(dst), offl, reg(src)),
        ST_W_REG => format!(".stx .word {} {} {}", reg(dst), offl, reg(src)),
        ST_DW_REG => format!(".stx .dword {} {} {}", reg(dst), offl, reg(src)),
        ADD64_IMM => format!(".add64 {} (.imm ({}))", reg(dst), imm),
        SUB64_IMM => format!(".sub64 {} (.imm ({}))", reg(dst), imm),
        MOV64_IMM => format!(".mov64 {} (.imm ({}))", reg(dst), imm),
        AND64_IMM => format!(".and64 {} (.imm ({}))", reg(dst), imm),
        LSH64_IMM => format!(".lsh64 {} (.imm ({}))", reg(dst), imm),
        LD_DW_IMM => format!(".lddw {} ({})", reg(dst), imm),
        ST_B_IMM => format!(".st .byte {} {} ({})", reg(dst), offl, imm),
        ST_H_IMM => format!(".st .half {} {} ({})", reg(dst), offl, imm),
        ST_W_IMM => format!(".st .word {} {} ({})", reg(dst), offl, imm),
        ST_DW_IMM => format!(".st .dword {} {} ({})", reg(dst), offl, imm),
        ADD64_REG => format!(".add64 {} (.reg {})", reg(dst), reg(src)),
        SUB64_REG => format!(".sub64 {} (.reg {})", reg(dst), reg(src)),
        MUL64_REG => format!(".mul64 {} (.reg {})", reg(dst), reg(src)),
        OR64_REG => format!(".or64 {} (.reg {})", reg(dst), reg(src)),
        AND64_REG => format!(".and64 {} (.reg {})", reg(dst), reg(src)),
        XOR64_REG => format!(".xor64 {} (.reg {})", reg(dst), reg(src)),
        LSH64_REG => format!(".lsh64 {} (.reg {})", reg(dst), reg(src)),
        RSH64_REG => format!(".rsh64 {} (.reg {})", reg(dst), reg(src)),
        MOV64_REG => format!(".mov64 {} (.reg {})", reg(dst), reg(src)),
        EXIT => ".exit".to_string(),
        JEQ64_IMM | JEQ32_IMM => {
            let t = jt();
            format!(".jeq {} (.imm ({})) {}", reg(dst), imm, t)
        }
        JNE64_IMM | JNE32_IMM => {
            let t = jt();
            format!(".jne {} (.imm ({})) {}", reg(dst), imm, t)
        }
        JGT64_IMM | JGT32_IMM => {
            let t = jt();
            format!(".jgt {} (.imm ({})) {}", reg(dst), imm, t)
        }
        JGE64_IMM | JGE32_IMM => {
            let t = jt();
            format!(".jge {} (.imm ({})) {}", reg(dst), imm, t)
        }
        JLT64_IMM | JLT32_IMM => {
            let t = jt();
            format!(".jlt {} (.imm ({})) {}", reg(dst), imm, t)
        }
        JLE64_IMM | JLE32_IMM => {
            let t = jt();
            format!(".jle {} (.imm ({})) {}", reg(dst), imm, t)
        }
        RSH64_IMM => format!(".rsh64 {} (.imm ({}))", reg(dst), imm),
        OR64_IMM => format!(".or64 {} (.imm ({}))", reg(dst), imm),
        XOR64_IMM => format!(".xor64 {} (.imm ({}))", reg(dst), imm),
        MUL64_IMM => format!(".mul64 {} (.imm ({}))", reg(dst), imm),
        DIV64_IMM => format!(".div64 {} (.imm ({}))", reg(dst), imm),
        MOD64_IMM => format!(".mod64 {} (.imm ({}))", reg(dst), imm),
        NEG64 => format!(".neg64 {}", reg(dst)),
        ADD32_IMM => format!(".add32 {} (.imm ({}))", reg(dst), imm),
        SUB32_IMM => format!(".sub32 {} (.imm ({}))", reg(dst), imm),
        MUL32_IMM => format!(".mul32 {} (.imm ({}))", reg(dst), imm),
        DIV32_IMM => format!(".div32 {} (.imm ({}))", reg(dst), imm),
        MOD32_IMM => format!(".mod32 {} (.imm ({}))", reg(dst), imm),
        OR32_IMM => format!(".or32 {} (.imm ({}))", reg(dst), imm),
        AND32_IMM => format!(".and32 {} (.imm ({}))", reg(dst), imm),
        XOR32_IMM => format!(".xor32 {} (.imm ({}))", reg(dst), imm),
        LSH32_IMM => format!(".lsh32 {} (.imm ({}))", reg(dst), imm),
        RSH32_IMM => format!(".rsh32 {} (.imm ({}))", reg(dst), imm),
        MOV32_IMM => format!(".mov32 {} (.imm ({}))", reg(dst), imm),
        NEG32 => format!(".neg32 {}", reg(dst)),
        ADD32_REG => format!(".add32 {} (.reg {})", reg(dst), reg(src)),
        SUB32_REG => format!(".sub32 {} (.reg {})", reg(dst), reg(src)),
        MUL32_REG => format!(".mul32 {} (.reg {})", reg(dst), reg(src)),
        OR32_REG => format!(".or32 {} (.reg {})", reg(dst), reg(src)),
        AND32_REG => format!(".and32 {} (.reg {})", reg(dst), reg(src)),
        XOR32_REG => format!(".xor32 {} (.reg {})", reg(dst), reg(src)),
        LSH32_REG => format!(".lsh32 {} (.reg {})", reg(dst), reg(src)),
        RSH32_REG => format!(".rsh32 {} (.reg {})", reg(dst), reg(src)),
        MOV32_REG => format!(".mov32 {} (.reg {})", reg(dst), reg(src)),
        ARSH64_IMM => format!(".arsh64 {} (.imm ({}))", reg(dst), imm),
        ARSH64_REG => format!(".arsh64 {} (.reg {})", reg(dst), reg(src)),
        ARSH32_IMM => format!(".arsh32 {} (.imm ({}))", reg(dst), imm),
        ARSH32_REG => format!(".arsh32 {} (.reg {})", reg(dst), reg(src)),
        JA => {
            let t = jt();
            format!(".ja {}", t)
        }
        JSGT64_IMM | JSGT32_IMM => {
            let t = jt();
            format!(".jsgt {} (.imm ({})) {}", reg(dst), imm, t)
        }
        JSLE64_IMM | JSLE32_IMM => {
            let t = jt();
            format!(".jsle {} (.imm ({})) {}", reg(dst), imm, t)
        }
        JSLT64_IMM | JSLT32_IMM => {
            let t = jt();
            format!(".jslt {} (.imm ({})) {}", reg(dst), imm, t)
        }
        JEQ64_REG | JEQ32_REG => {
            let t = jt();
            format!(".jeq {} (.reg {}) {}", reg(dst), reg(src), t)
        }
        JNE64_REG | JNE32_REG => {
            let t = jt();
            format!(".jne {} (.reg {}) {}", reg(dst), reg(src), t)
        }
        JLT64_REG | JLT32_REG => {
            let t = jt();
            format!(".jlt {} (.reg {}) {}", reg(dst), reg(src), t)
        }
        JSLE64_REG | JSLE32_REG => {
            let t = jt();
            format!(".jsle {} (.reg {}) {}", reg(dst), reg(src), t)
        }
        JGT64_REG | JGT32_REG => {
            let t = jt();
            format!(".jgt {} (.reg {}) {}", reg(dst), reg(src), t)
        }
        JLE64_REG | JLE32_REG => {
            let t = jt();
            format!(".jle {} (.reg {}) {}", reg(dst), reg(src), t)
        }
        JSGE64_REG | JSGE32_REG => {
            let t = jt();
            format!(".jsge {} (.reg {}) {}", reg(dst), reg(src), t)
        }
        JGE64_REG | JGE32_REG => {
            let t = jt();
            format!(".jge {} (.reg {}) {}", reg(dst), reg(src), t)
        }
        JSGT64_REG | JSGT32_REG => {
            let t = jt();
            format!(".jsgt {} (.reg {}) {}", reg(dst), reg(src), t)
        }
        JSLT64_REG | JSLT32_REG => {
            let t = jt();
            format!(".jslt {} (.reg {}) {}", reg(dst), reg(src), t)
        }
        JSET64_REG | JSET32_REG => {
            let t = jt();
            format!(".jset {} (.reg {}) {}", reg(dst), reg(src), t)
        }
        JSGE64_IMM | JSGE32_IMM => {
            let t = jt();
            format!(".jsge {} (.imm ({})) {}", reg(dst), imm, t)
        }
        JSET64_IMM | JSET32_IMM => {
            let t = jt();
            format!(".jset {} (.imm ({})) {}", reg(dst), imm, t)
        }
        // call_local imm is a Murmur3 hash, not an offset; caller must pre-resolve via Analysis::cfg_nodes.
        // Mirror Decode.lean (0x85): `SyscallHash.fromHash` is consulted FIRST,
        // then the function registry. The fault-terminal syscalls
        // (abort / sol_panic_) are the only host syscalls a small-decode lift
        // carries (Phase 7 sub-item 3 emitter), so render them as `.call <ctor>`
        // to match `decodeProgram`; everything else is an internal `.call_local`.
        CALL_IMM => {
            let himm = imm as u32;
            if himm == hash_symbol_name(b"abort") {
                ".call .abort".to_string()
            } else if himm == hash_symbol_name(b"sol_panic_") {
                ".call .sol_panic_".to_string()
            } else if himm == hash_symbol_name(b"sol_secp256k1_recover") {
                ".call .sol_secp256k1_recover".to_string()
            } else if himm == hash_symbol_name(b"sol_get_clock_sysvar") {
                ".call .sol_get_clock_sysvar".to_string()
            } else {
                match call_target {
                    Some(t) => format!(".call_local {}", t),
                    None => ".call_local TARGET_PC_NOT_RESOLVED".to_string(),
                }
            }
        }
        opc => return Err(format!("opcode 0x{:02x} not yet lifted to Lean", opc)),
    })
}

/// Wrapper for callers without a resolved call target; renders call_local with a placeholder.
pub(super) fn insn_to_lean(insn: &ebpf::Insn, pc: usize) -> Result<String, String> {
    insn_to_lean_full(insn, pc, None, None)
}

/// Resolve CALL_IMM to its callee slot PC by reversing the Murmur3-hash immediate via `analysis.functions`.
fn resolve_call_target(analysis: &Analysis, insn: &ebpf::Insn) -> Option<usize> {
    if insn.opc != ebpf::CALL_IMM {
        return None;
    }
    let target_hash = insn.imm as u32;
    analysis
        .functions
        .iter()
        .find_map(|(&pc, (h, _name))| if *h == target_hash { Some(pc) } else { None })
}

/// Like `resolve_call_target` but converts the slot-based result to a logical index. `lddw` counts as two slots but one logical insn, so a callee past any `lddw` would be off by the lddw count without this (e.g. p_token: logical 10836, slot 11537).
pub(super) fn resolve_call_target_logical(
    ctx: &BinaryCtx,
    analysis: &Analysis,
    insn: &ebpf::Insn,
) -> Option<usize> {
    let slot = resolve_call_target(analysis, insn)?;
    // out of range / mid-lddw: fall back to slot so downstream fails loudly.
    Some(ctx.pc_map.slot_to_logical(slot).unwrap_or(slot))
}

/// Render call stack as a Lean `List CallFrame` literal, newest-frame first (`frame :: cs` per `call_local_spec`). Each frame: `⟨callpc+1, r6..r10⟩`.
pub(super) fn render_callstack(frames: &[(usize, [Expr; 5])]) -> String {
    if frames.is_empty() {
        return "[]".to_string();
    }
    let items: Vec<String> = frames
        .iter()
        .rev()
        .map(|(cp, regs)| {
            format!(
                "⟨{} + 1, {}, {}, {}, {}, {}⟩",
                cp,
                regs[0].atom_lean(),
                regs[1].atom_lean(),
                regs[2].atom_lean(),
                regs[3].atom_lean(),
                regs[4].atom_lean()
            )
        })
        .collect();
    format!("[{}]", items.join(", "))
}

/// Resolve a slot-relative jump to its logical target PC, mirroring `Decode.decodeProgram` so the
/// rendered `.jXX target` matches what `native_decide` proves. Falls back to `logical_pc+1+off`
/// for synthetic fixtures (no lddw => slot == logical).
pub(super) fn resolve_jump_target(ctx: &BinaryCtx, logical_pc: usize, off: i64) -> i64 {
    ctx.pc_map.resolve_jump_target(logical_pc, off)
}

/// The V0 function registry (murmur3 key -> target SLOT) built at load — ground truth that Lean's
/// `Elf.buildFnRegistry` mirrors (audit H2). Sorted by key for deterministic output; slot units
/// match `Decode.decodeInsn`; `entrypoint` (slot 0) included as the Lean side carries it.
pub(super) fn function_registry(ctx: &BinaryCtx) -> Vec<(u32, usize)> {
    let mut v: Vec<(u32, usize)> = ctx
        .executable
        .get_function_registry()
        .iter()
        .map(|(key, (_name, slot))| (key, slot))
        .collect();
    v.sort_by_key(|(k, _)| *k);
    v
}

pub(super) fn function_registry_lean(reg: &[(u32, usize)]) -> String {
    let mut s = String::from("[");
    for (i, (k, slot)) in reg.iter().enumerate() {
        if i > 0 {
            s.push_str(", ");
        }
        if i > 0 && i % 4 == 0 {
            s.push_str("\n  ");
        }
        s.push_str(&format!("({}, {})", k, slot));
    }
    s.push(']');
    s
}
