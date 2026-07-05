//! Symbolic execution: the per-opcode `step` interpreter, the modeled-syscall
//! table and the CFG walk (`walk_and_exec`) with its retry loop and typed
//! fault terminals.

use super::*;

/// Step one instruction's effect through `state`. Returns Ok(true) if
/// the instruction was a recognised non-terminator; Ok(false) if it
/// was `exit` (slice terminates); Err for opcodes the executor
/// doesn't model yet. `pc` is the analysis-PC of `insn` (only used
/// to resolve relative jump targets). `branch_taken` (when `Some`)
/// records the walker's branch decision so the path hypothesis is
/// the right shape (taken vs fall-through).
pub(super) fn step(state: &mut SymState, insn: &ebpf::Insn, pc: Option<usize>,
        branch_taken: Option<bool>) -> Result<bool, String> {
    use ebpf::*;
    let (dst, src, off, imm) = (insn.dst, insn.src, insn.off as i64, insn.imm);
    match insn.opc {
        LD_B_REG => {
            let raw = state.read_mem(src, off, Width::Byte);
            state.write_reg(dst, Expr::Mod(Box::new(raw), 256));
        }
        LD_H_REG => {
            // `ldxh_spec` post is raw ↦U16 value (like ldxdw, not ldxb); reloaded compound → `hReloadLt_<pc>` side hyp.
            let raw = state.read_mem(src, off, Width::Halfword);
            if !matches!(raw, Expr::InitMem(_)) {
                let pcn = pc.unwrap_or(0);
                state.side_hyps.push((
                    format!("hReloadLt_{}", pcn),
                    format!("{} < 2 ^ 16", raw.to_lean()),
                ));
            }
            state.write_reg(dst, raw);
        }
        LD_W_REG => {
            let raw = state.read_mem(src, off, Width::Word);
            if !matches!(raw, Expr::InitMem(_)) {
                let pcn = pc.unwrap_or(0);
                state.side_hyps.push((
                    format!("hReloadLt_{}", pcn),
                    format!("{} < 2 ^ 32", raw.to_lean()),
                ));
            }
            state.write_reg(dst, raw);
        }
        LD_DW_REG => {
            let raw = state.read_mem(src, off, Width::Dword);
            // Reloaded compound (not fresh `oldMemD_N`): register `hReloadLt_<pc>` as the spec's `hv`.
            if !matches!(raw, Expr::InitMem(_) | Expr::ByteCombo(_)) {
                let pcn = pc.unwrap_or(0);
                state.side_hyps.push((
                    format!("hReloadLt_{}", pcn),
                    format!("{} < 2 ^ 64", raw.to_lean()),
                ));
            }
            state.write_reg(dst, raw);
        }
        ST_B_REG => {
            let cur = state.read_reg(src);
            state.write_mem(dst, off, Width::Byte, Expr::Mod(Box::new(cur), 256));
        }
        ST_H_REG => {
            let cur = state.read_reg(src);
            state.write_mem(dst, off, Width::Halfword, cur);
        }
        ST_W_REG => {
            let cur = state.read_reg(src);
            state.write_mem(dst, off, Width::Word, cur);
        }
        ST_DW_REG => {
            let cur = state.read_reg(src);
            state.write_mem(dst, off, Width::Dword, cur);
        }
        ADD64_IMM => {
            let cur = state.read_reg(dst);
            state.write_reg(dst, Expr::WrapAdd(
                Box::new(cur),
                Box::new(Expr::ToU64(Box::new(Expr::Const(imm)))),
            ));
        }
        AND64_IMM => {
            let cur = state.read_reg(dst);
            state.write_reg(dst, Expr::AndU64Imm(Box::new(cur), imm));
        }
        LSH64_IMM => {
            let cur = state.read_reg(dst);
            state.write_reg(dst, Expr::LshU64Imm(Box::new(cur), imm));
        }
        RSH64_IMM => {
            let cur = state.read_reg(dst);
            state.write_reg(dst, Expr::RshU64Imm(Box::new(cur), imm));
        }
        ST_B_IMM => {
            state.write_mem(dst, off, Width::Byte,
                Expr::Mod(Box::new(Expr::ToU64(Box::new(Expr::Const(imm)))), 256));
        }
        ST_H_IMM => {
            state.write_mem(dst, off, Width::Halfword, Expr::StHalfImm(imm));
        }
        ST_W_IMM => {
            state.write_mem(dst, off, Width::Word, Expr::StWordImm(imm));
        }
        ST_DW_IMM => {
            state.write_mem(dst, off, Width::Dword, Expr::StDwordImm(imm));
        }
        SUB64_IMM => {
            let cur = state.read_reg(dst);
            state.write_reg(dst, Expr::WrapSub(
                Box::new(cur),
                Box::new(Expr::ToU64(Box::new(Expr::Const(imm)))),
            ));
        }
        MOV64_IMM => {
            state.write_reg(dst, Expr::ToU64(Box::new(Expr::Const(imm))));
        }
        LD_DW_IMM => {
            // lddw = mov64-from-immediate (merged 64-bit value already in `imm`).
            state.write_reg(dst, Expr::ToU64(Box::new(Expr::Const(imm))));
        }
        MOV64_REG => {
            let v = state.read_reg(src);
            state.write_reg(dst, v);
        }
        ADD64_REG => {
            let a = state.read_reg(dst);
            let b = state.read_reg(src);
            state.write_reg(dst, Expr::WrapAdd(Box::new(a), Box::new(b)));
        }
        SUB64_REG => {
            let a = state.read_reg(dst);
            let b = state.read_reg(src);
            state.write_reg(dst, Expr::WrapSub(Box::new(a), Box::new(b)));
        }
        MUL64_REG => {
            let a = state.read_reg(dst);
            let b = state.read_reg(src);
            state.write_reg(dst, Expr::WrapMul(Box::new(a), Box::new(b)));
        }
        OR64_REG | AND64_REG | XOR64_REG | LSH64_REG | RSH64_REG => {
            let av = state.read_reg(dst);
            let bv = state.read_reg(src);
            let a = av.atom_lean();
            let b = bv.atom_lean();
            // Closed operands: carry the semantic value (RawConst renders
            // identically) so the H8 witness can evaluate derived roots.
            let empty = std::collections::BTreeMap::new();
            let cv = eval_expr(&av, &empty).zip(eval_expr(&bv, &empty));
            let (r, v) = match insn.opc {
                OR64_REG  => (format!("({} ||| {}) % U64_MODULUS", a, b),
                              cv.map(|(x, y)| x | y)),
                AND64_REG => (format!("({} &&& {}) % U64_MODULUS", a, b),
                              cv.map(|(x, y)| x & y)),
                XOR64_REG => (format!("({} ^^^ {}) % U64_MODULUS", a, b),
                              cv.map(|(x, y)| x ^ y)),
                LSH64_REG => (format!("({} <<< ({} % 64)) % U64_MODULUS", a, b),
                              cv.map(|(x, y)| x.wrapping_shl((y % 64) as u32))),
                RSH64_REG => (format!("{} >>> ({} % 64)", a, b),
                              cv.map(|(x, y)| x >> (y % 64))),
                _ => unreachable!(),
            };
            state.write_reg(dst, match v {
                Some(v) => Expr::RawConst(r, v),
                None => Expr::Raw(r),
            });
        }
        OR64_IMM | XOR64_IMM | MUL64_IMM | DIV64_IMM | MOD64_IMM | NEG64 => {
            let av = state.read_reg(dst);
            let a = av.atom_lean();
            let i = lean_off(imm);
            let empty = std::collections::BTreeMap::new();
            let ca = eval_expr(&av, &empty);
            let iv = imm as u64; // toU64 (sign-extend)
            let (r, v) = match insn.opc {
                OR64_IMM  => (format!("({} ||| toU64 {}) % U64_MODULUS", a, i),
                              ca.map(|x| x | iv)),
                XOR64_IMM => (format!("({} ^^^ toU64 {}) % U64_MODULUS", a, i),
                              ca.map(|x| x ^ iv)),
                MUL64_IMM => (format!("wrapMul {} (toU64 {})", a, i),
                              ca.map(|x| x.wrapping_mul(iv))),
                // Nat semantics: `x / 0 = 0`, `x % 0 = x`.
                DIV64_IMM => (format!("({} / toU64 {}) % U64_MODULUS", a, i),
                              ca.map(|x| x.checked_div(iv).unwrap_or(0))),
                MOD64_IMM => (format!("{} % toU64 {}", a, i),
                              ca.map(|x| if iv == 0 { x } else { x % iv })),
                NEG64     => (format!("wrapNeg {}", a),
                              ca.map(|x| x.wrapping_neg())),
                _ => unreachable!(),
            };
            state.write_reg(dst, match v {
                Some(v) => Expr::RawConst(r, v),
                None => Expr::Raw(r),
            });
        }
        ADD32_IMM | SUB32_IMM | MUL32_IMM | OR32_IMM | AND32_IMM | XOR32_IMM
        | LSH32_IMM | RSH32_IMM | MOV32_IMM | DIV32_IMM | MOD32_IMM | NEG32 => {
            let a = state.read_reg(dst).atom_lean();
            let i = lean_off(imm);
            let r = match insn.opc {
                ADD32_IMM => format!("wrapAdd32 {} (toU64 {})", a, i),
                SUB32_IMM => format!("wrapSub32 {} (toU64 {})", a, i),
                MUL32_IMM => format!("wrapMul32 {} (toU64 {})", a, i),
                OR32_IMM  => format!("({} ||| toU64 {}) % U32_MODULUS", a, i),
                AND32_IMM => format!("({} &&& toU64 {}) % U32_MODULUS", a, i),
                XOR32_IMM => format!("({} ^^^ toU64 {}) % U32_MODULUS", a, i),
                LSH32_IMM => format!("({} <<< (toU64 {} % 32)) % U32_MODULUS", a, i),
                RSH32_IMM => format!("({} % U32_MODULUS) >>> (toU64 {} % 32)", a, i),
                MOV32_IMM => format!("toU64 {} % U32_MODULUS", i),
                DIV32_IMM => format!("({} % U32_MODULUS / (toU64 {} % U32_MODULUS)) % U32_MODULUS", a, i),
                MOD32_IMM => format!("{} % U32_MODULUS % (toU64 {} % U32_MODULUS)", a, i),
                NEG32     => format!("wrapNeg32 {}", a),
                _ => unreachable!(),
            };
            state.write_reg(dst, Expr::Raw(r));
        }
        // arsh (arithmetic shift right) — let/if/else post via arsh_render.
        // Closed operands fold to RawConst (identical render) for the witness.
        ARSH64_IMM | ARSH32_IMM => {
            let av = state.read_reg(dst);
            let a = av.atom_lean();
            let bits = if insn.opc == ARSH64_IMM { 64 } else { 32 };
            let empty = std::collections::BTreeMap::new();
            let v = eval_expr(&av, &empty).map(|x| arsh_value(x, imm as u64, bits));
            let r = arsh_render(&a, &format!("toU64 {}", lean_off(imm)), bits);
            state.write_reg(dst, match v {
                Some(v) => Expr::RawConst(r, v),
                None => Expr::Raw(r),
            });
        }
        ARSH64_REG | ARSH32_REG => {
            let av = state.read_reg(dst);
            let bv = state.read_reg(src);
            let a = av.atom_lean();
            let b = bv.atom_lean();
            let bits = if insn.opc == ARSH64_REG { 64 } else { 32 };
            let empty = std::collections::BTreeMap::new();
            let v = eval_expr(&av, &empty).zip(eval_expr(&bv, &empty))
                .map(|(x, sv)| arsh_value(x, sv, bits));
            let r = arsh_render(&a, &b, bits);
            state.write_reg(dst, match v {
                Some(v) => Expr::RawConst(r, v),
                None => Expr::Raw(r),
            });
        }
        ADD32_REG | SUB32_REG | MUL32_REG | OR32_REG | AND32_REG | XOR32_REG
        | LSH32_REG | RSH32_REG | MOV32_REG => {
            let a = state.read_reg(dst).atom_lean();
            let b = state.read_reg(src).atom_lean();
            let r = match insn.opc {
                ADD32_REG => format!("wrapAdd32 {} {}", a, b),
                SUB32_REG => format!("wrapSub32 {} {}", a, b),
                MUL32_REG => format!("wrapMul32 {} {}", a, b),
                OR32_REG  => format!("({} ||| {}) % U32_MODULUS", a, b),
                AND32_REG => format!("({} &&& {}) % U32_MODULUS", a, b),
                XOR32_REG => format!("({} ^^^ {}) % U32_MODULUS", a, b),
                LSH32_REG => format!("({} <<< ({} % 32)) % U32_MODULUS", a, b),
                RSH32_REG => format!("({} % U32_MODULUS) >>> ({} % 32)", a, b),
                MOV32_REG => format!("{} % U32_MODULUS", b),
                _ => unreachable!(),
            };
            state.write_reg(dst, Expr::Raw(r));
        }
        // div/mod reg-form: surface divisor non-zeroness as `hnz_<pc>` hyp; read src before dst write so rendering matches spec arg.
        DIV64_REG | MOD64_REG | DIV32_REG | MOD32_REG => {
            let a = state.read_reg(dst).atom_lean();
            let b = state.read_reg(src).atom_lean();
            let pcn = pc.unwrap_or(0);
            let prop = match insn.opc {
                DIV64_REG | MOD64_REG => format!("{} ≠ 0", b),
                _ /* 32-bit */        => format!("{} % U32_MODULUS ≠ 0", b),
            };
            state.side_hyps.push((format!("hnz_{}", pcn), prop));
            let r = match insn.opc {
                DIV64_REG => format!("({} / {}) % U64_MODULUS", a, b),
                MOD64_REG => format!("{} % {}", a, b),
                DIV32_REG => format!("({} % U32_MODULUS / ({} % U32_MODULUS)) % U32_MODULUS", a, b),
                MOD32_REG => format!("{} % U32_MODULUS % ({} % U32_MODULUS)", a, b),
                _ => unreachable!(),
            };
            state.write_reg(dst, Expr::Raw(r));
        }
        // Conditional jumps: record path hyp (taken or fall-through); no reg/mem change. Default = fall-through (common guard shape).
        JEQ64_IMM | JEQ32_IMM => {
            let r = state.read_reg(dst);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JeqImm, dst_value: r, src_value: None, imm,
                taken: branch_taken.unwrap_or(false),            });
        }
        JNE64_IMM | JNE32_IMM => {
            let r = state.read_reg(dst);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JneImm, dst_value: r, src_value: None, imm,
                taken: branch_taken.unwrap_or(false),            });
        }
        JGT64_IMM | JGT32_IMM => {
            let r = state.read_reg(dst);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JgtImm, dst_value: r, src_value: None, imm,
                taken: branch_taken.unwrap_or(false),            });
        }
        JSGT64_IMM | JSGT32_IMM => {
            let r = state.read_reg(dst);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JsgtImm, dst_value: r, src_value: None, imm,
                taken: branch_taken.unwrap_or(false),            });
        }
        JSLE64_IMM | JSLE32_IMM => {
            let r = state.read_reg(dst);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JsleImm, dst_value: r, src_value: None, imm,
                taken: branch_taken.unwrap_or(false),            });
        }
        JLT64_IMM | JLT32_IMM => {
            let r = state.read_reg(dst);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JltImm, dst_value: r, src_value: None, imm,
                taken: branch_taken.unwrap_or(false),            });
        }
        JLE64_IMM | JLE32_IMM => {
            let r = state.read_reg(dst);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JleImm, dst_value: r, src_value: None, imm,
                taken: branch_taken.unwrap_or(false),            });
        }
        JSLT64_IMM | JSLT32_IMM => {
            let r = state.read_reg(dst);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JsltImm, dst_value: r, src_value: None, imm,
                taken: branch_taken.unwrap_or(false),            });
        }
        JGE64_IMM | JGE32_IMM | JSGE64_IMM | JSGE32_IMM | JSET64_IMM | JSET32_IMM => {
            let r = state.read_reg(dst);
            let kind = match insn.opc {
                JGE64_IMM | JGE32_IMM => BranchKind::JgeImm,
                JSGE64_IMM | JSGE32_IMM => BranchKind::JsgeImm,
                JSET64_IMM | JSET32_IMM => BranchKind::JsetImm,
                _ => unreachable!(),
            };
            state.branch_hyps.push(BranchHyp {
                kind, dst_value: r, src_value: None, imm,
                taken: branch_taken.unwrap_or(false),            });
        }
        JEQ64_REG | JEQ32_REG => {
            let rd = state.read_reg(dst);
            let rs = state.read_reg(src);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JeqReg, dst_value: rd, src_value: Some(rs), imm: 0,
                taken: branch_taken.unwrap_or(false),            });
        }
        JNE64_REG | JNE32_REG => {
            let rd = state.read_reg(dst);
            let rs = state.read_reg(src);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JneReg, dst_value: rd, src_value: Some(rs), imm: 0,
                taken: branch_taken.unwrap_or(false),            });
        }
        JLT64_REG | JLT32_REG => {
            let rd = state.read_reg(dst);
            let rs = state.read_reg(src);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JltReg, dst_value: rd, src_value: Some(rs), imm: 0,
                taken: branch_taken.unwrap_or(false),            });
        }
        JSLE64_REG | JSLE32_REG => {
            let rd = state.read_reg(dst);
            let rs = state.read_reg(src);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JsleReg, dst_value: rd, src_value: Some(rs), imm: 0,
                taken: branch_taken.unwrap_or(false),            });
        }
        JGT64_REG | JGT32_REG | JLE64_REG | JLE32_REG | JSGE64_REG | JSGE32_REG
        | JGE64_REG | JGE32_REG | JSGT64_REG | JSGT32_REG | JSLT64_REG | JSLT32_REG
        | JSET64_REG | JSET32_REG => {
            let rd = state.read_reg(dst);
            let rs = state.read_reg(src);
            let kind = match insn.opc {
                JGT64_REG | JGT32_REG => BranchKind::JgtReg,
                JLE64_REG | JLE32_REG => BranchKind::JleReg,
                JSGE64_REG | JSGE32_REG => BranchKind::JsgeReg,
                JGE64_REG | JGE32_REG => BranchKind::JgeReg,
                JSGT64_REG | JSGT32_REG => BranchKind::JsgtReg,
                JSLT64_REG | JSLT32_REG => BranchKind::JsltReg,
                JSET64_REG | JSET32_REG => BranchKind::JsetReg,
                _ => unreachable!(),
            };
            state.branch_hyps.push(BranchHyp {
                kind, dst_value: rd, src_value: Some(rs), imm: 0,
                taken: branch_taken.unwrap_or(false),            });
        }
        JA => { /* unconditional fall-through reset is handled by the caller's PC walk */ }
        // call_local: bumps r10 by 0x1000 and pushes frame; PC redirect handled by walker.
        CALL_IMM => {
            state.saw_call = true;
            // Snapshot call-time r6..r10 — the frame call_local pushes and exit_pops must restore.
            let r6 = state.read_reg(6); let r7 = state.read_reg(7);
            let r8 = state.read_reg(8); let r9 = state.read_reg(9);
            // Nat.add (not wrapAdd) to match call_local_spec's `r10V + 0x1000` so chains compose.
            let r10_old = state.read_reg(10);
            state.write_reg(10, Expr::NatAdd(
                Box::new(r10_old.clone()),
                Box::new(Expr::Const(0x1000)),
            ));
            // Frame retPc renders as `<callpc> + 1` (Lean keeps unreduced); resume PC is callpc + 1.
            let call_pc = pc.unwrap_or(0);
            state.call_stack.push((call_pc, [r6, r7, r8, r9, r10_old]));
        }
        EXIT => {
            if state.call_stack.is_empty() {
                return Ok(false);
            } else {
                // Nested exit: pop frame + undo r10's +0x1000 bump. Callee must not touch r6..r9 (Solana ABI);
                // ABI violation → chain won't compose → sl_block_iter residual.
                let _ = state.call_stack.pop();
                let r10_cur = state.read_reg(10);
                state.write_reg(10, Expr::WrapSub(
                    Box::new(r10_cur),
                    Box::new(Expr::Const(0x1000)),
                ));
            }
        }
        opc => return Err(format!("symbolic executor: opcode 0x{:02x} not yet modelled", opc)),
    }
    Ok(true)
}

/// True if `imm` is the hash of a syscall the lift emits an effect spec for.
/// Such a call must take the decode-pins path (so `syscall_pcs` resolves it to
/// `.call <ctor>`) and the `sl_block_iter` proof body (so the `call_<name>_spec`
/// preamble is threaded); the small `decodeProgram` bridge and bare `sl_block_auto`
/// can't handle a syscall. Mirrors the trace dispatch in `lift_one_with_layouts`.
pub(super) fn imm_is_modeled_syscall(imm: u32) -> bool {
    syscall_model(imm).is_some_and(|m| m.modeled)
}

/// A typed-fault terminal syscall a happy-path walk can end on (Phase 7
/// sub-item 3). Both halt with `exitCode := ERR_ABORT` and `vmError := .abort`
/// (audit L1's typed channel); they differ only in the `Syscall` constructor
/// and the library terminal-fault spec the `*_fault_correct` corollary composes.
#[derive(Clone, Copy)]
pub(super) enum AbortKind {
    /// `.call .abort` — unconditional abort (`Abort.execAbort`).
    Abort,
    /// `.call .sol_panic_` — panic (logs a message, same `.abort` fault).
    SolPanic,
    /// `.call .sol_invoke_signed` — CPI. The PROOF-facing semantics is the
    /// fail-closed `Cpi.exec` stub (audit C4/C5): it faults with
    /// `.unsupportedInstruction` rather than fabricate an effect-free
    /// invoke, so an invoke ends the walk like a terminal even though the
    /// RUNNER's trace continues past it (the real CPI is executed by
    /// `executeFnCpiWithFuel`). The lifted prefix ends AT the invoke — the
    /// envelope the caller hands the syscall is a claim about that
    /// prefix's post (`SVM.Solana.cpiEnvelope`).
    Invoke,
    /// `.call .sol_invoke_signed_c` — the C-ABI CPI, same fail-closed stub
    /// (envelope predicate: `SVM.Solana.cpiEnvelopeC`).
    InvokeC,
}

impl AbortKind {
    /// Resolve a relocated `call_imm` immediate (a Murmur3 syscall hash) to a
    /// fault terminal, or `None` if it is not abort/sol_panic_.
    fn from_hash(imm: u32) -> Option<AbortKind> {
        syscall_model(imm).and_then(|m| m.abort)
    }
    /// The Lean `Syscall` constructor (CodeReq singleton + `step`/`hCu` term).
    pub(super) fn ctor(self) -> &'static str {
        match self {
            AbortKind::Abort => ".abort",
            AbortKind::SolPanic => ".sol_panic_",
            AbortKind::Invoke => ".sol_invoke_signed",
            AbortKind::InvokeC => ".sol_invoke_signed_c",
        }
    }
    /// The typed `VmError` the terminal faults with.
    pub(super) fn vm_error(self) -> &'static str {
        match self {
            AbortKind::Abort | AbortKind::SolPanic => ".abort",
            AbortKind::Invoke | AbortKind::InvokeC => ".unsupportedInstruction",
        }
    }
    /// The library terminal-fault spec the corollary composes with (both
    /// pre-parametric over the prefix post, faulting as `.abort`).
    pub(super) fn faults_spec(self) -> &'static str {
        match self {
            AbortKind::Abort => "call_abort_faults_spec",
            AbortKind::SolPanic => "call_sol_panic_faults_spec",
            AbortKind::Invoke => "call_sol_invoke_signed_faults_spec",
            AbortKind::InvokeC => "call_sol_invoke_signed_c_faults_spec",
        }
    }
}

/// An out-of-bounds (H6) syscall fault terminal (Phase 7 sub-item 3, the
/// `.accessViolation` family). Unlike abort/panic, the fault is CONDITIONAL on
/// the syscall's input region being out of bounds, so the corollary carries a
/// region requirement `rr` over the region register (`region_reg`, e.g. r1) and
/// `region_size`. Detected only on a trace where the syscall does NOT return
/// (the OOB execution is stuck), and composed via the Mem-Mem
/// `cuTripleWithinMem_seq_fault` (combined `rr = prefixRR ∧ OOB`).
#[derive(Clone, Copy)]
pub(super) struct OobSyscall {
    /// Lean `Syscall` constructor (CodeReq singleton).
    pub(super) ctor: &'static str,
    /// The library OOB fault triple (`cuTripleFaultsWithinMem … .accessViolation`).
    pub(super) faults_spec: &'static str,
    /// The register whose value addresses the guarded region (1 = r1).
    pub(super) region_reg: u8,
    /// The guarded region length in bytes (e.g. 32 for the secp hash input).
    /// Ignored when `region_len_reg` is set.
    pub(super) region_size: i64,
    /// When the region length is REGISTER-sized (e.g. `sol_set_return_data`'s
    /// `[r1, r1+r2)`), the length register. The faults spec then takes both
    /// values plus its literal side conditions (discharged `by decide`), and
    /// the post must carry the length register as the SECOND atom.
    pub(super) region_len_reg: Option<u8>,
    /// `true` if the guard is a WRITE check (`containsWritable`, e.g. a sysvar
    /// output); `false` for a READ check (`containsRange`, e.g. the secp input).
    /// Must match the `rr` of the syscall's `faults_oob` triple.
    pub(super) region_writable: bool,
}

impl OobSyscall {
    /// Resolve a syscall hash to its OOB fault descriptor, or `None`.
    fn from_hash(imm: u32) -> Option<OobSyscall> {
        syscall_model(imm).and_then(|m| m.oob)
    }
}

/// A trace-mode running-effect emitter (`dispatch_traced_syscall` row): shapes
/// the syscall's pre/post atoms + spec-call preamble at the walked PC.
type EffectFn = fn(&mut SymState, &mut Vec<SpecCall>, &mut Vec<usize>, usize, &BinaryCtx)
    -> Result<(), Box<dyn std::error::Error>>;

/// One row of the modeled-syscall table: everything qedlift knows about a
/// syscall hash. The four consumers (`imm_is_modeled_syscall`,
/// `dispatch_traced_syscall`, `AbortKind::from_hash`, `OobSyscall::from_hash`)
/// all derive from `SYSCALLS`, so adding a syscall is a one-row change.
struct SyscallModel {
    /// Symbol name (murmur3-hashed into the relocated `call_imm` imm).
    name: &'static [u8],
    /// In `imm_is_modeled_syscall`'s set: the lift emits an effect spec for
    /// it, forcing the decode-pins path + `sl_block_iter` proof body.
    modeled: bool,
    /// Running-effect emitter for a traced syscall returning to pc+1.
    effect: Option<EffectFn>,
    /// Typed unconditional fault terminal (abort/panic/CPI stub).
    abort: Option<AbortKind>,
    /// Conditional out-of-bounds fault descriptor (H6 `.accessViolation`).
    oob: Option<OobSyscall>,
}

impl SyscallModel {
    /// Row template: fill only the lookups the syscall participates in.
    const DEFAULT: SyscallModel = SyscallModel {
        name: b"", modeled: false, effect: None, abort: None, oob: None,
    };
}

/// The single source of truth for the modeled-syscall set.
static SYSCALLS: &[SyscallModel] = &[
    SyscallModel { name: b"sol_memset_", modeled: true,
        effect: Some(|s, sc, bp, pc, _| { emit_sol_memset(s, sc, bp, pc); Ok(()) }),
        ..SyscallModel::DEFAULT },
    // H8 Phase C-2: faithful buffer-write (rent/offset 0/length 17; else fail-closed).
    SyscallModel { name: b"sol_get_sysvar", modeled: true,
        effect: Some(emit_sol_get_sysvar),
        ..SyscallModel::DEFAULT },
    SyscallModel { name: b"sol_log_", modeled: true,
        effect: Some(|s, sc, bp, pc, _| { emit_sol_log(s, sc, bp, pc); Ok(()) }),
        ..SyscallModel::DEFAULT },
    SyscallModel { name: b"sol_memcpy_", modeled: true,
        effect: Some(|s, sc, bp, pc, _| { emit_sol_memcpy(s, sc, bp, pc, false); Ok(()) }),
        ..SyscallModel::DEFAULT },
    SyscallModel { name: b"sol_memmove_", modeled: true,
        effect: Some(|s, sc, bp, pc, _| { emit_sol_memcpy(s, sc, bp, pc, true); Ok(()) }),
        ..SyscallModel::DEFAULT },
    SyscallModel { name: b"sol_memcmp_", modeled: true,
        effect: Some(|s, sc, bp, pc, _| { emit_sol_memcmp(s, sc, bp, pc); Ok(()) }),
        ..SyscallModel::DEFAULT },
    SyscallModel { name: b"sol_set_return_data", modeled: true,
        effect: Some(|s, sc, bp, pc, _| { emit_sol_set_return_data(s, sc, bp, pc); Ok(()) }),
        oob: Some(OobSyscall {
            ctor: ".sol_set_return_data",
            faults_spec: "call_sol_set_return_data_faults_oob_spec",
            region_reg: 1,
            region_size: 0,
            region_len_reg: Some(2),
            region_writable: false,
        }),
        ..SyscallModel::DEFAULT },
    // H6: single-slice hash — descriptor cells consumed
    // from the program's stores, input/output introduced.
    SyscallModel { name: b"sol_sha256", modeled: true,
        effect: Some(|s, sc, bp, pc, _| emit_sol_sha256(s, sc, bp, pc)),
        oob: Some(OobSyscall {
            ctor: ".sol_sha256",
            faults_spec: "call_sol_sha256_faults_oob_spec",
            region_reg: 3,
            region_size: 32,
            region_len_reg: None,
            region_writable: true,
        }),
        ..SyscallModel::DEFAULT },
    // H6: single-seed PDA — descriptor from stores, seed +
    // program_id + output introduced; off-curve surfaced.
    SyscallModel { name: b"sol_create_program_address", modeled: true,
        effect: Some(|s, sc, bp, pc, _| emit_sol_create_program_address(s, sc, bp, pc)),
        oob: Some(OobSyscall {
            ctor: ".sol_create_program_address",
            faults_spec: "call_sol_create_program_address_faults_oob_spec",
            region_reg: 3,
            region_size: 32,
            region_len_reg: None,
            region_writable: false,
        }),
        ..SyscallModel::DEFAULT },
    SyscallModel { name: b"sol_invoke_signed_rust", modeled: true,
        abort: Some(AbortKind::Invoke),
        ..SyscallModel::DEFAULT },
    SyscallModel { name: b"sol_invoke_signed_c", modeled: true,
        abort: Some(AbortKind::InvokeC),
        ..SyscallModel::DEFAULT },
    SyscallModel { name: b"abort",
        abort: Some(AbortKind::Abort),
        ..SyscallModel::DEFAULT },
    SyscallModel { name: b"sol_panic_",
        abort: Some(AbortKind::SolPanic),
        ..SyscallModel::DEFAULT },
    SyscallModel { name: b"sol_secp256k1_recover",
        oob: Some(OobSyscall {
            ctor: ".sol_secp256k1_recover",
            faults_spec: "call_sol_secp256k1_recover_faults_oob_spec",
            region_reg: 1,
            region_size: 32,
            region_len_reg: None,
            region_writable: false,
        }),
        ..SyscallModel::DEFAULT },
    SyscallModel { name: b"sol_get_clock_sysvar",
        oob: Some(OobSyscall {
            ctor: ".sol_get_clock_sysvar",
            faults_spec: "call_sol_get_clock_sysvar_faults_oob_spec",
            region_reg: 1,
            region_size: 40,
            region_len_reg: None,
            region_writable: true,
        }),
        ..SyscallModel::DEFAULT },
    SyscallModel { name: b"sol_get_rent_sysvar",
        oob: Some(OobSyscall {
            ctor: ".sol_get_rent_sysvar",
            faults_spec: "call_sol_get_rent_sysvar_faults_oob_spec",
            region_reg: 1,
            region_size: 17,
            region_len_reg: None,
            region_writable: true,
        }),
        ..SyscallModel::DEFAULT },
];

/// Look up a relocated `call_imm` immediate (murmur3 syscall hash) in the
/// modeled-syscall table.
fn syscall_model(imm: u32) -> Option<&'static SyscallModel> {
    SYSCALLS.iter().find(|m| imm == ebpf::hash_symbol_name(m.name))
}

/// Arithmetic-shift-right value semantics mirroring `arsh_render`'s Lean
/// let/if form: sign bit replicates into the top `shift` bits.
fn arsh_value(x: u64, shift: u64, bits: u32) -> u64 {
    if bits == 64 {
        let s = (shift % 64) as u32;
        ((x as i64) >> s) as u64
    } else {
        let s = (shift % 32) as u32;
        ((((x as u32) as i32) >> s) as u32) as u64
    }
}

/// What terminated the walked happy path with a typed fault (Phase 7 sub-item
/// 3). `Abort` = unconditional `.abort`/`.sol_panic_`; `Oob` = a conditional
/// out-of-bounds syscall (`.accessViolation`).
#[derive(Clone, Copy)]
pub(super) enum FaultTerminal {
    Abort(AbortKind),
    Oob(OobSyscall),
}

/// What the CFG walk + symbolic execution produced for one arm: the final
/// symbolic state, the per-insn spec calls, the walked PCs, the terminator PC
/// and (when the path ends in an abort-style terminal) the typed fault.
pub(super) struct WalkResult {
    pub(super) state: SymState,
    pub(super) spec_calls: Vec<SpecCall>,
    pub(super) block_pcs: Vec<usize>,
    pub(super) exit_pc: usize,
    pub(super) fault_terminal: Option<FaultTerminal>,
}

/// CFG walk + symbolic execution + the hot-region/blob-split retry loop +
/// syscall dispatch. Straight-line→pc+1, ja→target, cond-jump→fall-through,
/// call_local→push+jump, exit/empty-stack→done, exit/non-empty→pop+resume.
/// Starts at ELF entrypoint (NOT analysis PC 0: linker may place helpers
/// before it).
pub(super) fn walk_and_exec(
    ctx: &BinaryCtx,
    analysis: &Analysis<'_>,
    trace: Option<&[usize]>,
    target_disc: Option<i64>,
    arm_entry: Option<usize>,
    entry_pc: usize,
) -> Result<WalkResult, Box<dyn std::error::Error>> {
    let insns = &ctx.insns;

    // Hot regions: grow monotonically across walk retries (H8 Phase B); attempt cap is a safety net.
    let mut hot_regions: std::collections::BTreeMap<String, Vec<(i64, i64)>> =
        Default::default();
    let mut blob_splits: std::collections::BTreeMap<(String, i64), i64> =
        Default::default();
    let mut walk_attempts = 0usize;
    loop {
    walk_attempts += 1;
    if walk_attempts > 8 {
        return Err("qedlift: hot-region demotion did not converge after 8 \
                    walk retries".into());
    }
    let mut spec_calls: Vec<SpecCall> = Vec::new();

    let mut block_pcs: Vec<usize> = Vec::new();
    let exit_pc: usize;
    // Phase 7 sub-item 3: when the walked happy-path terminates in a typed
    // fault (`.call .abort`/`.sol_panic_` ⇒ `.abort`, or an out-of-bounds
    // syscall ⇒ `.accessViolation`), record it here so the emitter renders a
    // `*_fault_correct` corollary (`cuTripleFaultsWithinMem`) instead of only a
    // success triple. `None` = ordinary `exit` terminator (the success case).
    let mut fault_terminal: Option<FaultTerminal> = None;
    let mut state = SymState::default();
    state.hot_regions = hot_regions.clone();
    state.blob_splits = blob_splits.clone();
    {
        let mut ti: usize = 0; // trace cursor; pc_iter mirrors trace[ti] in trace mode
        let mut pc_iter: usize = match trace {
            Some(t) => {
                // #41 Phase 4: cross-check sidecar arm_entry_pc is on the trace (mismatch → fail-closed).
                if let Some(arm) = arm_entry {
                    if !t.contains(&arm) {
                        return Err(format!(
                            "qedmeta/trace mismatch: recovered arm_entry_pc {} \
                             is not on the execution trace (the sidecar describes \
                             a different arm than the trace executes)", arm).into());
                    }
                }
                t[0] // load_trace guarantees non-empty
            }
            // #41 Phase 4: seed from recovered arm_entry (no disc-cascade nav); fallback = entry_pc.
            None => arm_entry.unwrap_or(entry_pc),
        };
        // Walk cap: prevents runaway on unmodelled back-branches; generous for deep dispatcher cascades.
        let walk_cap: usize = match trace { Some(t) => t.len() + 8, None => 1024 };
        let mut walk_steps: usize = 0;
        loop {
            walk_steps += 1;
            if walk_steps > walk_cap {
                return Err(format!(
                    "walker exceeded {} steps at pc={} (likely back-branch \
                     defaulted to fall-through)", walk_cap, pc_iter).into());
            }
            if let Some(t) = trace {
                if ti >= t.len() { exit_pc = pc_iter; break; }
                pc_iter = t[ti];
            }
            if pc_iter >= insns.len() { exit_pc = pc_iter; break; }
            let ins = &insns[pc_iter];

            // EXIT: nested return (pop call stack + restore r6..r10) or top-level terminator.
            if ins.opc == ebpf::EXIT {
                if state.call_stack.is_empty() {
                    exit_pc = pc_iter;
                    break;
                } else {
                    block_pcs.push(pc_iter);
                    // Emit spec call BEFORE popping (r6..r10 still at callee-frame values).
                    if let Some(sc) = spec_call_for(&state, ins, pc_iter, None, None, None, None) {
                        spec_calls.push(sc);
                    }
                    let (call_pc, saved) = state.call_stack.pop().unwrap();
                    // Mirror exit_pops_spec: restore saved r6..r10 so post-state matches (callee may have clobbered them).
                    for (i, r) in (6u8..=10).enumerate() {
                        state.write_reg(r, saved[i].clone());
                    }
                    // Trace: next PC from trace; static: jump to callpc+1.
                    if trace.is_some() { ti += 1; } else { pc_iter = call_pc + 1; }
                    continue;
                }
            }

            // Typed-fault terminal (Phase 7 sub-item 3): `.call .abort` /
            // `.call .sol_panic_` never return, so they end the walk like
            // `exit` — but with the typed `vmError` channel (audit L1).
            // `sol_invoke_signed` ALSO terminates the walk (proof-side CPI is
            // the fail-closed `Cpi.exec` stub → `.unsupportedInstruction`),
            // even though the runner's trace continues past it. The terminal
            // is NOT pushed to `block_pcs` (it is the fault tail, composed by
            // the emitter via `call_<kind>_faults_spec`, not the prefix).
            if ins.opc == ebpf::CALL_IMM {
                let imm = ins.imm as u32;
                if let Some(kind) = AbortKind::from_hash(imm) {
                    fault_terminal = Some(FaultTerminal::Abort(kind));
                    exit_pc = pc_iter;
                    break;
                }
                // OOB (H6) syscall fault: a known guard-checked syscall that, on
                // this trace, does NOT return to pc+1 (the OOB access is stuck).
                // Trace-only: in static mode the same syscall might succeed.
                if let Some(oob) = OobSyscall::from_hash(imm) {
                    if let Some(t) = trace {
                        if t.get(ti + 1).copied() != Some(pc_iter + 1) {
                            fault_terminal = Some(FaultTerminal::Oob(oob));
                            exit_pc = pc_iter;
                            break;
                        }
                    }
                }
            }

            // Syscall (trace): call_imm returning to pc+1 (no BPF frame push) → dispatch on hash.
            if ins.opc == ebpf::CALL_IMM {
                if let Some(t) = trace {
                    if t.get(ti + 1).copied() == Some(pc_iter + 1) {
                        let imm = ins.imm as u32;
                        dispatch_traced_syscall(&mut state, &mut spec_calls,
                            &mut block_pcs, pc_iter, imm, ctx)?;
                        ti += 1;
                        continue;
                    }
                }
            }

            block_pcs.push(pc_iter);
            let call_target = resolve_call_target_logical(ctx, &analysis, ins);
            // Branch hyp name indexed by number of branches seen so far.
            let branch_idx = state.branch_hyps.len();
            let branch_hyp = format!("h_branch{}", branch_idx);
            let is_cond_jump = is_cond_jump_opc(ins.opc);
            let branch_hyp_for_call = if is_cond_jump {
                Some(branch_hyp.as_str())
            } else { None };
            // Slot-relative offset → logical PC (handles lddw 2-slot encoding); shared by spec + walk.
            let jtgt = resolve_jump_target(ctx, pc_iter, ins.off as i64);
            // Trace: taken iff next PC ≠ pc+1; target mismatch vs decoded offset = fail-closed.
            // Static: discriminator-driven where possible, else fall-through.
            let branch_taken = resolve_branch_taken(
                trace, ti, pc_iter, ins, jtgt, is_cond_jump, target_disc)?;

            if let Some(sc) = spec_call_for(&state, ins, pc_iter, call_target,
                                            branch_hyp_for_call, branch_taken, Some(jtgt)) {
                spec_calls.push(sc);
            }
            step(&mut state, ins, Some(pc_iter), branch_taken)?;
            // Phase A aliasing: surface address equation for same-cell different-rendering (consumed by rw [h_alias_<pc>]).
            if let Some((lhs, rhs)) = state.pending_alias.take() {
                state.side_hyps.push((
                    format!("h_alias_{}", pc_iter),
                    format!("{} = {}", lhs, rhs),
                ));
            }
            for (i, (lhs, rhs)) in state.pending_slot_aliases.drain(..).enumerate() {
                state.side_hyps.push((
                    format!("h_alias_{}_{}", pc_iter, i),
                    format!("{} = {}", lhs, rhs),
                ));
            }

            if trace.is_some() {
                ti += 1;
                continue;
            }
            match ins.opc {
                ebpf::JA => {
                    pc_iter = jtgt as usize;
                }
                ebpf::JEQ64_IMM | ebpf::JEQ32_IMM |
                ebpf::JNE64_IMM | ebpf::JNE32_IMM |
                ebpf::JGT64_IMM | ebpf::JGT32_IMM |
                ebpf::JSGT64_IMM | ebpf::JSGT32_IMM |
                ebpf::JSLE64_IMM | ebpf::JSLE32_IMM |
                ebpf::JLT64_IMM | ebpf::JLT32_IMM |
                ebpf::JLE64_IMM | ebpf::JLE32_IMM |
                ebpf::JEQ64_REG | ebpf::JEQ32_REG |
                ebpf::JNE64_REG | ebpf::JNE32_REG |
                ebpf::JLT64_REG | ebpf::JLT32_REG |
                ebpf::JSLE64_REG | ebpf::JSLE32_REG
                    if branch_taken == Some(true) => {
                    pc_iter = jtgt as usize;
                }
                ebpf::CALL_IMM => {
                    // CALL_IMM: imm is a Murmur3 hash; registry maps it to a logical PC.
                    pc_iter = resolve_call_target_logical(ctx, &analysis, ins).ok_or_else(|| {
                        format!(
                            "qedlift: call_local at pc {} has imm 0x{:x} \
                             but no matching function in the symbol table. \
                             Recompile with symbols, or extend the resolver.",
                            pc_iter, ins.imm as u32)
                    })?;
                }
                _ => { pc_iter += 1; }
            }
        }
    }

    // Blob tail-splits requested: record and re-walk.
    if !state.new_blob_splits.is_empty() {
        for (root, lo, n) in state.new_blob_splits.drain(..) {
            blob_splits.insert((root, lo), n);
        }
        continue;
    }
    // Demotion requested: merge new spans into hot set and re-walk (this pass discarded).
    if !state.new_hot.is_empty() {
        for (root, lo, hi) in state.new_hot.drain(..) {
            let v = hot_regions.entry(root).or_default();
            let (mut nlo, mut nhi) = (lo, hi);
            v.retain(|(l, h)| {
                if *l <= nhi && nlo <= *h {
                    nlo = nlo.min(*l); nhi = nhi.max(*h); false
                } else { true }
            });
            v.push((nlo, nhi));
        }
        continue;
    }
    // H8 FAIL CLOSED: overlapping atom footprints make precondition's sepConj unsatisfiable (vacuous).
    if !state.overlap_errors.is_empty() {
        return Err(format!(
            "qedlift: refusing to emit a vacuous lift — overlapping atom \
             footprints would make the precondition's sepConj \
             unsatisfiable. The walker does not yet alias these at byte \
             granularity (soundness-audit H8, \
             docs/QEDLIFT_ALIASING_DESIGN.md):\n  - {}",
            state.overlap_errors.join("\n  - ")).into());
    }
    return Ok(WalkResult { state, spec_calls, block_pcs, exit_pc, fault_terminal });
    }
}

/// Handle a traced syscall (a `call_imm` whose trace returns to pc+1 without a
/// BPF frame push): dispatch on the murmur3 hash to the effect emitter.
/// Errors on an unmodelled syscall hash.
fn dispatch_traced_syscall(
    state: &mut SymState,
    spec_calls: &mut Vec<SpecCall>,
    block_pcs: &mut Vec<usize>,
    pc_iter: usize,
    imm: u32,
    ctx: &BinaryCtx,
) -> Result<(), Box<dyn std::error::Error>> {
    if let Some(effect) = syscall_model(imm).and_then(|m| m.effect) {
        return effect(state, spec_calls, block_pcs, pc_iter, ctx);
    }
    // NOTE: sol_invoke_signed_rust never reaches here — it is an
    // AbortKind::Invoke walk TERMINAL (the proof-facing CPI is the
    // fail-closed `Cpi.exec` stub, so no running spec can cross it).
    Err(format!(
        "call_imm at pc {} is a syscall (trace returns to {} \
         without a frame push) with imm hash 0x{:08x}, but only \
         sol_memset_ / sol_memcpy_ / sol_memmove_ / sol_memcmp_ / \
         sol_get_sysvar / sol_log_ / sol_set_return_data are \
         modelled so far (sol_invoke_signed terminates the walk). \
         This arm needs a syscall-effect spec for that hash.",
        pc_iter, pc_iter + 1, imm).into())
}

/// True if `opc` is a conditional jump the walker models (imm + reg forms).
fn is_cond_jump_opc(opc: u8) -> bool {
    matches!(opc,
        ebpf::JEQ64_IMM | ebpf::JEQ32_IMM |
        ebpf::JNE64_IMM | ebpf::JNE32_IMM |
        ebpf::JGT64_IMM | ebpf::JGT32_IMM |
        ebpf::JSGT64_IMM | ebpf::JSGT32_IMM |
        ebpf::JSLE64_IMM | ebpf::JSLE32_IMM |
        ebpf::JLT64_IMM | ebpf::JLT32_IMM |
        ebpf::JLE64_IMM | ebpf::JLE32_IMM |
        ebpf::JSLT64_IMM | ebpf::JSLT32_IMM |
        ebpf::JGE64_IMM | ebpf::JGE32_IMM |
        ebpf::JSGE64_IMM | ebpf::JSGE32_IMM |
        ebpf::JSET64_IMM | ebpf::JSET32_IMM |
        ebpf::JEQ64_REG | ebpf::JEQ32_REG |
        ebpf::JNE64_REG | ebpf::JNE32_REG |
        ebpf::JLT64_REG | ebpf::JLT32_REG |
        ebpf::JSLE64_REG | ebpf::JSLE32_REG |
        ebpf::JGT64_REG | ebpf::JGT32_REG |
        ebpf::JLE64_REG | ebpf::JLE32_REG |
        ebpf::JSGE64_REG | ebpf::JSGE32_REG |
        ebpf::JGE64_REG | ebpf::JGE32_REG |
        ebpf::JSGT64_REG | ebpf::JSGT32_REG |
        ebpf::JSLT64_REG | ebpf::JSLT32_REG |
        ebpf::JSET64_REG | ebpf::JSET32_REG)
}

/// Whether the conditional jump at `pc_iter` is taken.
/// Trace: taken iff next PC ≠ pc+1; target mismatch vs decoded offset = fail-closed.
/// Static: discriminator-driven where possible, else fall-through.
#[allow(clippy::too_many_arguments)]
fn resolve_branch_taken(
    trace: Option<&[usize]>,
    ti: usize,
    pc_iter: usize,
    ins: &ebpf::Insn,
    jtgt: i64,
    is_cond_jump: bool,
    target_disc: Option<i64>,
) -> Result<Option<bool>, Box<dyn std::error::Error>> {

    let branch_taken: Option<bool> = if let Some(t) = trace {
        if is_cond_jump {
            let next = t.get(ti + 1).copied();
            let taken = next != Some(pc_iter + 1);
            if taken {
                if let Some(n) = next {
                    if n as i64 != jtgt {
                        return Err(format!(
                            "trace/decoder mismatch at pc {}: trace goes to {} \
                             but the decoded jump target is {} (off={})",
                            pc_iter, n, jtgt, ins.off).into());
                    }
                }
            }
            Some(taken)
        } else { None }
    } else {
        match (ins.opc, target_disc) {
            (ebpf::JEQ64_IMM, Some(td)) | (ebpf::JEQ32_IMM, Some(td)) => {
                Some(ins.imm == td)
            }
            (ebpf::JNE64_IMM, Some(td)) | (ebpf::JNE32_IMM, Some(td)) => {
                Some(ins.imm != td)
            }
            // JGT: take branch when td > imm (disc > N → upper_half pattern).
            (ebpf::JGT64_IMM, Some(td)) | (ebpf::JGT32_IMM, Some(td)) => {
                Some(td > ins.imm)
            }
            _ if is_cond_jump => Some(false), // default: not-taken
            _ => None,
        }
    };
    Ok(branch_taken)
}
