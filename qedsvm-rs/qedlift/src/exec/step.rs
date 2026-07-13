use solana_sbpf::ebpf;

use crate::branch::{BranchHyp, BranchKind};
use crate::core::{arsh_render, eval_expr, lean_off, Expr, Width};
use crate::diagnostic::{DiagnosticKind, LiftError};
use crate::state::SymState;

use super::syscall_registry::arsh_value;

/// was `exit` (slice terminates); Err for opcodes the executor
/// doesn't model yet. `pc` is the analysis-PC of `insn` (only used
/// to resolve relative jump targets). `branch_taken` (when `Some`)
/// records the walker's branch decision so the path hypothesis is
/// the right shape (taken vs fall-through).
pub(super) fn step(
    state: &mut SymState,
    insn: &ebpf::Insn,
    pc: Option<usize>,
    branch_taken: Option<bool>,
) -> Result<bool, LiftError> {
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
            state.write_reg(
                dst,
                Expr::WrapAdd(
                    Box::new(cur),
                    Box::new(Expr::ToU64(Box::new(Expr::Const(imm)))),
                ),
            );
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
            state.write_mem(
                dst,
                off,
                Width::Byte,
                Expr::Mod(Box::new(Expr::ToU64(Box::new(Expr::Const(imm)))), 256),
            );
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
            state.write_reg(
                dst,
                Expr::WrapSub(
                    Box::new(cur),
                    Box::new(Expr::ToU64(Box::new(Expr::Const(imm)))),
                ),
            );
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
                OR64_REG => (
                    format!("({} ||| {}) % U64_MODULUS", a, b),
                    cv.map(|(x, y)| x | y),
                ),
                AND64_REG => (
                    format!("({} &&& {}) % U64_MODULUS", a, b),
                    cv.map(|(x, y)| x & y),
                ),
                XOR64_REG => (
                    format!("({} ^^^ {}) % U64_MODULUS", a, b),
                    cv.map(|(x, y)| x ^ y),
                ),
                LSH64_REG => (
                    format!("({} <<< ({} % 64)) % U64_MODULUS", a, b),
                    cv.map(|(x, y)| x.wrapping_shl((y % 64) as u32)),
                ),
                RSH64_REG => (
                    format!("{} >>> ({} % 64)", a, b),
                    cv.map(|(x, y)| x >> (y % 64)),
                ),
                _ => unreachable!(),
            };
            state.write_reg(
                dst,
                match v {
                    Some(v) => Expr::RawConst(r, v),
                    None => Expr::Raw(r),
                },
            );
        }
        OR64_IMM | XOR64_IMM | MUL64_IMM | DIV64_IMM | MOD64_IMM | NEG64 => {
            let av = state.read_reg(dst);
            let a = av.atom_lean();
            let i = lean_off(imm);
            let empty = std::collections::BTreeMap::new();
            let ca = eval_expr(&av, &empty);
            let iv = imm as u64; // toU64 (sign-extend)
            let (r, v) = match insn.opc {
                OR64_IMM => (
                    format!("({} ||| toU64 {}) % U64_MODULUS", a, i),
                    ca.map(|x| x | iv),
                ),
                XOR64_IMM => (
                    format!("({} ^^^ toU64 {}) % U64_MODULUS", a, i),
                    ca.map(|x| x ^ iv),
                ),
                MUL64_IMM => (
                    format!("wrapMul {} (toU64 {})", a, i),
                    ca.map(|x| x.wrapping_mul(iv)),
                ),
                // Nat semantics: `x / 0 = 0`, `x % 0 = x`.
                DIV64_IMM => (
                    format!("({} / toU64 {}) % U64_MODULUS", a, i),
                    ca.map(|x| x.checked_div(iv).unwrap_or(0)),
                ),
                MOD64_IMM => (
                    format!("{} % toU64 {}", a, i),
                    ca.map(|x| if iv == 0 { x } else { x % iv }),
                ),
                NEG64 => (format!("wrapNeg {}", a), ca.map(|x| x.wrapping_neg())),
                _ => unreachable!(),
            };
            state.write_reg(
                dst,
                match v {
                    Some(v) => Expr::RawConst(r, v),
                    None => Expr::Raw(r),
                },
            );
        }
        ADD32_IMM | SUB32_IMM | MUL32_IMM | OR32_IMM | AND32_IMM | XOR32_IMM | LSH32_IMM
        | RSH32_IMM | MOV32_IMM | DIV32_IMM | MOD32_IMM | NEG32 => {
            let a = state.read_reg(dst).atom_lean();
            let i = lean_off(imm);
            let r = match insn.opc {
                ADD32_IMM => format!("wrapAdd32 {} (toU64 {})", a, i),
                SUB32_IMM => format!("wrapSub32 {} (toU64 {})", a, i),
                MUL32_IMM => format!("wrapMul32 {} (toU64 {})", a, i),
                OR32_IMM => format!("({} ||| toU64 {}) % U32_MODULUS", a, i),
                AND32_IMM => format!("({} &&& toU64 {}) % U32_MODULUS", a, i),
                XOR32_IMM => format!("({} ^^^ toU64 {}) % U32_MODULUS", a, i),
                LSH32_IMM => format!("({} <<< (toU64 {} % 32)) % U32_MODULUS", a, i),
                RSH32_IMM => format!("({} % U32_MODULUS) >>> (toU64 {} % 32)", a, i),
                MOV32_IMM => format!("toU64 {} % U32_MODULUS", i),
                DIV32_IMM => format!(
                    "({} % U32_MODULUS / (toU64 {} % U32_MODULUS)) % U32_MODULUS",
                    a, i
                ),
                MOD32_IMM => format!("{} % U32_MODULUS % (toU64 {} % U32_MODULUS)", a, i),
                NEG32 => format!("wrapNeg32 {}", a),
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
            state.write_reg(
                dst,
                match v {
                    Some(v) => Expr::RawConst(r, v),
                    None => Expr::Raw(r),
                },
            );
        }
        ARSH64_REG | ARSH32_REG => {
            let av = state.read_reg(dst);
            let bv = state.read_reg(src);
            let a = av.atom_lean();
            let b = bv.atom_lean();
            let bits = if insn.opc == ARSH64_REG { 64 } else { 32 };
            let empty = std::collections::BTreeMap::new();
            let v = eval_expr(&av, &empty)
                .zip(eval_expr(&bv, &empty))
                .map(|(x, sv)| arsh_value(x, sv, bits));
            let r = arsh_render(&a, &b, bits);
            state.write_reg(
                dst,
                match v {
                    Some(v) => Expr::RawConst(r, v),
                    None => Expr::Raw(r),
                },
            );
        }
        ADD32_REG | SUB32_REG | MUL32_REG | OR32_REG | AND32_REG | XOR32_REG | LSH32_REG
        | RSH32_REG | MOV32_REG => {
            let a = state.read_reg(dst).atom_lean();
            let b = state.read_reg(src).atom_lean();
            let r = match insn.opc {
                ADD32_REG => format!("wrapAdd32 {} {}", a, b),
                SUB32_REG => format!("wrapSub32 {} {}", a, b),
                MUL32_REG => format!("wrapMul32 {} {}", a, b),
                OR32_REG => format!("({} ||| {}) % U32_MODULUS", a, b),
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
                DIV32_REG => format!(
                    "({} % U32_MODULUS / ({} % U32_MODULUS)) % U32_MODULUS",
                    a, b
                ),
                MOD32_REG => format!("{} % U32_MODULUS % ({} % U32_MODULUS)", a, b),
                _ => unreachable!(),
            };
            state.write_reg(dst, Expr::Raw(r));
        }
        // Conditional jumps: record path hyp (taken or fall-through); no reg/mem change. Default = fall-through (common guard shape).
        JEQ64_IMM | JEQ32_IMM => {
            let r = state.read_reg(dst);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JeqImm,
                dst_value: r,
                src_value: None,
                imm,
                taken: branch_taken.unwrap_or(false),
            });
        }
        JNE64_IMM | JNE32_IMM => {
            let r = state.read_reg(dst);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JneImm,
                dst_value: r,
                src_value: None,
                imm,
                taken: branch_taken.unwrap_or(false),
            });
        }
        JGT64_IMM | JGT32_IMM => {
            let r = state.read_reg(dst);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JgtImm,
                dst_value: r,
                src_value: None,
                imm,
                taken: branch_taken.unwrap_or(false),
            });
        }
        JSGT64_IMM | JSGT32_IMM => {
            let r = state.read_reg(dst);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JsgtImm,
                dst_value: r,
                src_value: None,
                imm,
                taken: branch_taken.unwrap_or(false),
            });
        }
        JSLE64_IMM | JSLE32_IMM => {
            let r = state.read_reg(dst);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JsleImm,
                dst_value: r,
                src_value: None,
                imm,
                taken: branch_taken.unwrap_or(false),
            });
        }
        JLT64_IMM | JLT32_IMM => {
            let r = state.read_reg(dst);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JltImm,
                dst_value: r,
                src_value: None,
                imm,
                taken: branch_taken.unwrap_or(false),
            });
        }
        JLE64_IMM | JLE32_IMM => {
            let r = state.read_reg(dst);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JleImm,
                dst_value: r,
                src_value: None,
                imm,
                taken: branch_taken.unwrap_or(false),
            });
        }
        JSLT64_IMM | JSLT32_IMM => {
            let r = state.read_reg(dst);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JsltImm,
                dst_value: r,
                src_value: None,
                imm,
                taken: branch_taken.unwrap_or(false),
            });
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
                kind,
                dst_value: r,
                src_value: None,
                imm,
                taken: branch_taken.unwrap_or(false),
            });
        }
        JEQ64_REG | JEQ32_REG => {
            let rd = state.read_reg(dst);
            let rs = state.read_reg(src);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JeqReg,
                dst_value: rd,
                src_value: Some(rs),
                imm: 0,
                taken: branch_taken.unwrap_or(false),
            });
        }
        JNE64_REG | JNE32_REG => {
            let rd = state.read_reg(dst);
            let rs = state.read_reg(src);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JneReg,
                dst_value: rd,
                src_value: Some(rs),
                imm: 0,
                taken: branch_taken.unwrap_or(false),
            });
        }
        JLT64_REG | JLT32_REG => {
            let rd = state.read_reg(dst);
            let rs = state.read_reg(src);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JltReg,
                dst_value: rd,
                src_value: Some(rs),
                imm: 0,
                taken: branch_taken.unwrap_or(false),
            });
        }
        JSLE64_REG | JSLE32_REG => {
            let rd = state.read_reg(dst);
            let rs = state.read_reg(src);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JsleReg,
                dst_value: rd,
                src_value: Some(rs),
                imm: 0,
                taken: branch_taken.unwrap_or(false),
            });
        }
        JGT64_REG | JGT32_REG | JLE64_REG | JLE32_REG | JSGE64_REG | JSGE32_REG | JGE64_REG
        | JGE32_REG | JSGT64_REG | JSGT32_REG | JSLT64_REG | JSLT32_REG | JSET64_REG
        | JSET32_REG => {
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
                kind,
                dst_value: rd,
                src_value: Some(rs),
                imm: 0,
                taken: branch_taken.unwrap_or(false),
            });
        }
        JA => { /* unconditional fall-through reset is handled by the caller's PC walk */ }
        // call_local: bumps r10 by 0x1000 and pushes frame; PC redirect handled by walker.
        CALL_IMM => {
            state.saw_call = true;
            // Snapshot call-time r6..r10 — the frame call_local pushes and exit_pops must restore.
            let r6 = state.read_reg(6);
            let r7 = state.read_reg(7);
            let r8 = state.read_reg(8);
            let r9 = state.read_reg(9);
            // Nat.add (not wrapAdd) to match call_local_spec's `r10V + 0x1000` so chains compose.
            let r10_old = state.read_reg(10);
            state.write_reg(
                10,
                Expr::NatAdd(Box::new(r10_old.clone()), Box::new(Expr::Const(0x1000))),
            );
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
                state.write_reg(
                    10,
                    Expr::WrapSub(Box::new(r10_cur), Box::new(Expr::Const(0x1000))),
                );
            }
        }
        opc => {
            return Err(LiftError::new(
                DiagnosticKind::OpcodeUnmodeled,
                format!("symbolic executor: opcode 0x{:02x} not yet modelled", opc),
            ))
        }
    }
    Ok(true)
}
