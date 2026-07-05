//! Per-instruction spec-call emission: the `have h_<pc> := <spec> <args>`
//! preamble lines `sl_block_iter` proof bodies consume.

use super::*;

/// One emitted `have h_<pc> := <spec_name> <args>` line; used by `sl_block_iter` proof bodies when `sl_block_auto` diverges (call_local programs).
#[derive(Clone, Debug)]
pub(super) struct SpecCall {
    pub(super) hyp_name: String,
    pub(super) have_line: String,
}

/// Build the `have h_<pc> := <spec_name> <args>` line for one insn,
/// using `state` as the pre-state (the symbolic values BEFORE the
/// insn applies). Side conditions like `(by decide)` and value-bound
/// hypotheses (`< 2^64`) are filled in based on the spec's signature.
/// Returns `None` for opcodes not in the table (caller can fall back).
/// `branch_taken` (when `Some`) tells the emitter which variant of
/// the conditional-jump spec to use for the current insn:
///   - `Some(true)`  → use `jXX_imm_taken_spec`     (post-PC = target)
///   - `Some(false)` → use `jXX_imm_not_taken_spec` (post-PC = pc+1)
///   - `None`        → not applicable (non-branch instruction)
pub(super) fn spec_call_for(
    state: &SymState,
    insn: &ebpf::Insn,
    pc: usize,
    call_target: Option<usize>,
    branch_hyp_name: Option<&str>,
    branch_taken: Option<bool>,
    jump_target: Option<i64>,
) -> Option<SpecCall> {
    use ebpf::*;
    let dst = insn.dst;
    let src = insn.src;
    let off = insn.off as i64;
    // Parenthesise negatives: `ldxb_same_spec .r10 -8` would parse as `.r10 - 8`.
    let offl = lean_off(off);
    // slot→logical resolved by caller.
    let jt = jump_target.unwrap_or((pc as i64) + 1 + off);
    // Parenthesise negative imm: `and64_imm_spec .r1 -8` would parse as `(and64_imm_spec .r1) - 8`.
    let imm = lean_off(insn.imm);
    let hyp_name = format!("h_{}", pc);
    // `.rN` register literal (dotted Lean ctor form of `core::reg_lit`).
    let reg = |r: u8| -> String { format!(".{}", reg_lit(r)) };
    // Lean string for register r; falls back to initial-name convention (`baseAddr` for r1, `vR<N>Old` otherwise).
    let reg_val_lean = |r: u8| -> String {
        match state.regs.get(&r) {
            Some(e) => e.to_lean(),
            None    => reg_initial_name(r),
        }
    };
    // Expr form of register r, for canon-aware cell lookups.
    let reg_val_expr = |r: u8| -> Expr {
        state.regs.get(&r).cloned()
            .unwrap_or_else(|| Expr::InitReg(reg_initial_name(r)))
    };
    // Phase A aliasing (QEDLIFT_ALIASING_DESIGN.md): same cell under different rendering
    // → append a `rw [h_alias_<pc>]` so the chain composes on ONE atom (not two overlapping unsatisfiable ones).
    let alias_suffix = |lookup: &Option<(usize, bool)>| -> String {
        match lookup {
            Some((_, true)) => format!("\n  rw [h_alias_{}] at {}", pc, hyp_name),
            _ => String::new(),
        }
    };
    let have_line = match insn.opc {
        LD_B_REG => {
            // ldxb_spec dst src off vOldDst baseAddr v pc hne (no < 2^64 bound — bytes always fit).
            // Re-read reuses existing cell value; first access allocates oldMemB_<fresh>.
            let base_addr = reg_val_lean(src);
            let lookup = state.lookup_cell_aliased(&reg_val_expr(src), off, Width::Byte);
            let v_name = lookup
                .map(|(i, _)| state.mem[i].value.atom_lean())
                .unwrap_or_else(|| format!("oldMemB_{}", state.fresh));
            let alias = alias_suffix(&lookup);
            if dst == src {
                // dst == src: generic ldxb_spec would emit two `r ↦ᵣ` atoms (unsatisfiable); use ldxb_same_spec.
                format!(
                    "have {} := ldxb_same_spec {} {} ({}) {} {} (by decide){}",
                    hyp_name, reg(dst), offl, base_addr, v_name, pc, alias,
                )
            } else {
                let v_old_dst = state.regs.get(&dst)
                    .map(|e| e.to_lean())
                    .unwrap_or_else(|| reg_initial_name(dst));
                format!(
                    "have {} := ldxb_spec {} {} {} ({}) ({}) {} {} (by decide){}",
                    hyp_name, reg(dst), reg(src), offl,
                    v_old_dst, base_addr, v_name, pc, alias,
                )
            }
        }
        LD_DW_REG => {
            // ldxdw_spec dst src off vOldDst baseAddr v pc hne hv.
            // Runs BEFORE step()'s read_mem; predicts fresh name `oldMemD_{state.fresh}`, bound `h<var>_lt`.
            let base_addr = reg_val_lean(src);
            // Hot (byte-demoted) region: use `ldxdw_bytes_spec` (H8 Phase B); predictions mirror `read_hot_wide`.
            {
                let bexpr = reg_val_expr(src);
                let (root, lo) = canon_addr(&bexpr, off);
                if dst != src && state.hot_covers(&root, lo, lo + 8) {
                    let mut args = String::new();
                    let mut addrs = String::new();
                    let mut bounds = String::new();
                    let mut haddrs = String::new();
                    let mut n_alias = 0usize;
                    let mut fresh = state.fresh;
                    for k in 0..8i64 {
                        let found = state.mem.iter().find(|c| {
                            matches!(c.width, Width::Byte) && {
                                let (cr, cd) = canon_addr(&c.addr_base, c.addr_off);
                                cr == root && cd + c.delta == lo + k
                            }
                        });
                        match found {
                            Some(c) => {
                                let render_ok = c.addr_base.to_lean() == bexpr.to_lean()
                                    && c.addr_off == off
                                    && ((k == 0 && c.delta == 0) || c.delta == k);
                                if render_ok {
                                    addrs.push_str(&format!(" ({})",
                                        SymState::slot_expected_render(&bexpr, off, k)));
                                    haddrs.push_str(" rfl");
                                } else {
                                    addrs.push_str(&format!(" ({})",
                                        SymState::cell_render(c)));
                                    haddrs.push_str(&format!(
                                        " h_alias_{}_{}", pc, n_alias));
                                    n_alias += 1;
                                }
                                args.push_str(&format!(" {}", c.value.atom_lean()));
                                match &c.value {
                                    Expr::InitMem(n) =>
                                        bounds.push_str(&format!(" h{}_lt", n)),
                                    _ => bounds.push_str(" (by omega)"),
                                }
                            }
                            None => {
                                let n = format!("oldMemB_{}", fresh);
                                fresh += 1;
                                addrs.push_str(&format!(" ({})",
                                    SymState::slot_expected_render(&bexpr, off, k)));
                                haddrs.push_str(" rfl");
                                args.push_str(&format!(" {}", n));
                                bounds.push_str(&format!(" h{}_lt", n));
                            }
                        }
                    }
                    let v_old_dst = state.regs.get(&dst)
                        .map(|e| e.to_lean())
                        .unwrap_or_else(|| reg_initial_name(dst));
                    return Some(SpecCall {
                        hyp_name: hyp_name.clone(),
                        have_line: format!(
                            "have {} := ldxdw_bytes_spec {} {} {} ({}) ({}){}{} {} (by decide){}{}",
                            hyp_name, reg(dst), reg(src), offl,
                            v_old_dst, base_addr, args, addrs, pc, bounds, haddrs,
                        ),
                    });
                }
            }
            // Re-read: reuse existing cell value. First access allocates oldMemD_<fresh> with h<var>_lt.
            // Reloaded compound (spilled reg) surfaces `hReloadLt_<pc>` as the hv bound.
            let lookup = state.lookup_cell_aliased(&reg_val_expr(src), off, Width::Dword);
            let cell_val = lookup.map(|(i, _)| state.mem[i].value.clone());
            let alias = alias_suffix(&lookup);
            let (v_arg, hv) = match &cell_val {
                Some(Expr::InitMem(name)) => (name.clone(), format!("h{}_lt", name)),
                Some(v) => (v.atom_lean(), format!("hReloadLt_{}", pc)),
                None => { let n = format!("oldMemD_{}", state.fresh); (n.clone(), format!("h{}_lt", n)) }
            };
            if dst == src {
                // dst == src: use ldxdw_same_spec.
                format!(
                    "have {} := ldxdw_same_spec {} {} ({}) {} {} (by decide) {}{}",
                    hyp_name, reg(dst), offl, base_addr, v_arg, pc, hv, alias,
                )
            } else {
                let v_old_dst = state.regs.get(&dst)
                    .map(|e| e.to_lean())
                    .unwrap_or_else(|| reg_initial_name(dst));
                format!(
                    "have {} := ldxdw_spec {} {} {} ({}) ({}) {} {} (by decide) {}{}",
                    hyp_name, reg(dst), reg(src), offl,
                    v_old_dst, base_addr, v_arg, pc, hv, alias,
                )
            }
        }
        // Word / halfword loads (dst ≠ src): `ldx{w,h}_spec dst src off
        // vOldDst baseAddr v pc hne hv`, hv = `v < 2^{32,16}` surfaced as
        // `h<var>_lt`. Post is `dst ↦ᵣ v` (the ↦U32/↦U16 cell value, raw).
        LD_W_REG | LD_H_REG => {
            let (spec, w, pfx) = if insn.opc == LD_W_REG {
                ("ldxw_spec", Width::Word, "oldMemW")
            } else { ("ldxh_spec", Width::Halfword, "oldMemH") };
            let base_addr = reg_val_lean(src);
            let lookup = state.lookup_cell_aliased(&reg_val_expr(src), off, w);
            let cell_val = lookup.map(|(i, _)| state.mem[i].value.clone());
            let alias = alias_suffix(&lookup);
            let (v_arg, hv) = match &cell_val {
                Some(Expr::InitMem(name)) => (name.clone(), format!("h{}_lt", name)),
                Some(v) => (v.atom_lean(), format!("hReloadLt_{}", pc)),
                None => { let n = format!("{}_{}", pfx, state.fresh); (n.clone(), format!("h{}_lt", n)) }
            };
            let v_old_dst = state.regs.get(&dst)
                .map(|e| e.to_lean())
                .unwrap_or_else(|| reg_initial_name(dst));
            format!(
                "have {} := {} {} {} {} ({}) ({}) {} {} (by decide) {}{}",
                hyp_name, spec, reg(dst), reg(src), offl,
                v_old_dst, base_addr, v_arg, pc, hv, alias,
            )
        }
        ST_B_REG | ST_H_REG | ST_W_REG | ST_DW_REG => {
            // stx{b,h,w,dw}_spec baseReg valReg off baseAddr vSrc oldV pc — all four share this shape.
            let (spec, w, pfx) = match insn.opc {
                ST_B_REG  => ("stxb_spec",  Width::Byte,     "oldMemB"),
                ST_H_REG  => ("stxh_spec",  Width::Halfword, "oldMemH"),
                ST_W_REG  => ("stxw_spec",  Width::Word,     "oldMemW"),
                ST_DW_REG => ("stxdw_spec", Width::Dword,    "oldMemD"),
                _ => unreachable!(),
            };
            let base_addr = reg_val_lean(dst);
            let v_src = reg_val_lean(src);
            // atom_lean() parenthesises compound prior values, leaving bare `oldMem*_N` unparenthesised.
            let lookup = state.lookup_cell_aliased(&reg_val_expr(dst), off, w);
            let old_v = lookup
                .map(|(i, _)| state.mem[i].value.atom_lean())
                // First access: step()'s write_mem allocates `oldMem*_{fresh}`; predict that name.
                .unwrap_or_else(|| format!("{}_{}", pfx, state.fresh));
            let alias = alias_suffix(&lookup);
            format!(
                "have {} := {} {} {} {} ({}) ({}) {} {}{}",
                hyp_name, spec, reg(dst), reg(src), offl,
                base_addr, v_src, old_v, pc, alias,
            )
        }
        ADD64_IMM => {
            let v_old = reg_val_lean(dst);
            format!(
                "have {} := add64_imm_spec {} {} ({}) {} (by decide)",
                hyp_name, reg(dst), imm, v_old, pc,
            )
        }
        AND64_IMM => {
            let v_old = reg_val_lean(dst);
            format!(
                "have {} := and64_imm_spec {} {} ({}) {} (by decide)",
                hyp_name, reg(dst), imm, v_old, pc,
            )
        }
        LSH64_IMM => {
            let v_old = reg_val_lean(dst);
            format!(
                "have {} := lsh64_imm_spec {} {} ({}) {} (by decide)",
                hyp_name, reg(dst), imm, v_old, pc,
            )
        }
        RSH64_IMM => {
            let v_old = reg_val_lean(dst);
            format!(
                "have {} := rsh64_imm_spec {} {} ({}) {} (by decide)",
                hyp_name, reg(dst), imm, v_old, pc,
            )
        }
        // Bitwise/mul imm-form ALU: `<op>_imm_spec dst imm vOld pc hne`.
        OR64_IMM | XOR64_IMM | MUL64_IMM => {
            let v_old = reg_val_lean(dst);
            let spec = match insn.opc {
                OR64_IMM => "or64_imm_spec", XOR64_IMM => "xor64_imm_spec",
                MUL64_IMM => "mul64_imm_spec", _ => unreachable!(),
            };
            format!(
                "have {} := {} {} {} ({}) {} (by decide)",
                hyp_name, spec, reg(dst), imm, v_old, pc,
            )
        }
        // Div/mod imm-form: extra `hnz : toU64 imm ≠ 0` discharged by `(by decide)` (fails on literal div-by-zero).
        DIV64_IMM | MOD64_IMM => {
            let v_old = reg_val_lean(dst);
            let spec = if insn.opc == DIV64_IMM { "div64_imm_spec" } else { "mod64_imm_spec" };
            format!(
                "have {} := {} {} {} ({}) {} (by decide) (by decide)",
                hyp_name, spec, reg(dst), imm, v_old, pc,
            )
        }
        NEG64 => {
            let v_old = reg_val_lean(dst);
            format!(
                "have {} := neg64_spec {} ({}) {} (by decide)",
                hyp_name, reg(dst), v_old, pc,
            )
        }
        // div/mod reg-form: symbolic divisor → spec's `hnz` surfaced as theorem hyp `hnz_<pc>` (registered by step).
        DIV64_REG | MOD64_REG | DIV32_REG | MOD32_REG => {
            let v_old = reg_val_lean(dst);
            let v_src = reg_val_lean(src);
            let spec = match insn.opc {
                DIV64_REG => "div64_reg_spec", MOD64_REG => "mod64_reg_spec",
                DIV32_REG => "div32_reg_spec", MOD32_REG => "mod32_reg_spec",
                _ => unreachable!(),
            };
            format!(
                "have {} := {} {} {} ({}) ({}) {} (by decide) hnz_{}",
                hyp_name, spec, reg(dst), reg(src), v_old, v_src, pc, pc,
            )
        }
        // 32-bit imm ALU: `<op>32_imm_spec dst imm vOld pc hne`.
        ADD32_IMM | SUB32_IMM | MUL32_IMM | OR32_IMM | AND32_IMM | XOR32_IMM
        | LSH32_IMM | RSH32_IMM | MOV32_IMM => {
            let v_old = reg_val_lean(dst);
            let spec = match insn.opc {
                ADD32_IMM => "add32_imm_spec", SUB32_IMM => "sub32_imm_spec",
                MUL32_IMM => "mul32_imm_spec", OR32_IMM => "or32_imm_spec",
                AND32_IMM => "and32_imm_spec", XOR32_IMM => "xor32_imm_spec",
                LSH32_IMM => "lsh32_imm_spec", RSH32_IMM => "rsh32_imm_spec",
                MOV32_IMM => "mov32_imm_spec", _ => unreachable!(),
            };
            format!(
                "have {} := {} {} {} ({}) {} (by decide)",
                hyp_name, spec, reg(dst), imm, v_old, pc,
            )
        }
        // 32-bit div/mod imm: extra `toU64 imm % U32_MODULUS ≠ 0` (literal → decide).
        DIV32_IMM | MOD32_IMM => {
            let v_old = reg_val_lean(dst);
            let spec = if insn.opc == DIV32_IMM { "div32_imm_spec" } else { "mod32_imm_spec" };
            format!(
                "have {} := {} {} {} ({}) {} (by decide) (by decide)",
                hyp_name, spec, reg(dst), imm, v_old, pc,
            )
        }
        NEG32 => {
            let v_old = reg_val_lean(dst);
            format!(
                "have {} := neg32_spec {} ({}) {} (by decide)",
                hyp_name, reg(dst), v_old, pc,
            )
        }
        // 32-bit reg ALU: `<op>32_reg_spec dst src vOld v pc hne`.
        ADD32_REG | SUB32_REG | MUL32_REG | OR32_REG | AND32_REG | XOR32_REG
        | LSH32_REG | RSH32_REG | MOV32_REG => {
            let v_old = reg_val_lean(dst);
            let v_src = reg_val_lean(src);
            let spec = match insn.opc {
                ADD32_REG => "add32_reg_spec", SUB32_REG => "sub32_reg_spec",
                MUL32_REG => "mul32_reg_spec", OR32_REG => "or32_reg_spec",
                AND32_REG => "and32_reg_spec", XOR32_REG => "xor32_reg_spec",
                LSH32_REG => "lsh32_reg_spec", RSH32_REG => "rsh32_reg_spec",
                MOV32_REG => "mov32_reg_spec", _ => unreachable!(),
            };
            format!(
                "have {} := {} {} {} ({}) ({}) {} (by decide)",
                hyp_name, spec, reg(dst), reg(src), v_old, v_src, pc,
            )
        }
        // arsh (arithmetic shift right), imm + reg, 32 + 64-bit.
        ARSH64_IMM | ARSH32_IMM => {
            let v_old = reg_val_lean(dst);
            let spec = if insn.opc == ARSH64_IMM { "arsh64_imm_spec" } else { "arsh32_imm_spec" };
            format!(
                "have {} := {} {} {} ({}) {} (by decide)",
                hyp_name, spec, reg(dst), imm, v_old, pc,
            )
        }
        ARSH64_REG | ARSH32_REG => {
            let v_old = reg_val_lean(dst);
            let v_src = reg_val_lean(src);
            let spec = if insn.opc == ARSH64_REG { "arsh64_reg_spec" } else { "arsh32_reg_spec" };
            format!(
                "have {} := {} {} {} ({}) ({}) {} (by decide)",
                hyp_name, spec, reg(dst), reg(src), v_old, v_src, pc,
            )
        }
        ST_B_IMM => {
            // stb_spec baseReg off imm baseAddr oldByteVal pc
            let base_addr = reg_val_lean(dst);
            let lookup = state.lookup_cell_aliased(&reg_val_expr(dst), off, Width::Byte);
            let old_v = lookup
                .map(|(i, _)| state.mem[i].value.atom_lean())
                .unwrap_or_else(|| format!("oldMemB_{}", state.fresh));
            let alias = alias_suffix(&lookup);
            format!(
                "have {} := stb_spec {} {} {} ({}) ({}) {}{}",
                hyp_name, reg(dst), offl, imm, base_addr, old_v, pc, alias,
            )
        }
        ST_H_IMM => {
            // sth_spec baseReg off imm baseAddr oldHalfVal pc
            let base_addr = reg_val_lean(dst);
            let lookup = state.lookup_cell_aliased(&reg_val_expr(dst), off, Width::Halfword);
            let old_v = lookup
                .map(|(i, _)| state.mem[i].value.atom_lean())
                .unwrap_or_else(|| format!("oldMemH_{}", state.fresh));
            let alias = alias_suffix(&lookup);
            format!(
                "have {} := sth_spec {} {} {} ({}) ({}) {}{}",
                hyp_name, reg(dst), offl, imm, base_addr, old_v, pc, alias,
            )
        }
        ST_W_IMM => {
            // stw_spec baseReg off imm baseAddr oldWordVal pc
            let base_addr = reg_val_lean(dst);
            // Hot region: `stw_bytes_spec` over 4 byte atoms, LE post bytes by decide; mirrors `write_hot_word_imm`.
            {
                let bexpr = reg_val_expr(dst);
                let (root, lo) = canon_addr(&bexpr, off);
                if state.hot_covers(&root, lo, lo + 4) {
                    let mut bargs = String::new();
                    let mut addrs = String::new();
                    let mut bounds = String::new();
                    let mut haddrs = String::new();
                    let mut n_alias = 0usize;
                    let mut fresh = state.fresh;
                    for k in 0..4i64 {
                        let found = state.mem.iter().find(|c| {
                            matches!(c.width, Width::Byte) && {
                                let (cr, cd) = canon_addr(&c.addr_base, c.addr_off);
                                cr == root && cd + c.delta == lo + k
                            }
                        });
                        match found {
                            Some(c) => {
                                let render_ok = c.addr_base.to_lean() == bexpr.to_lean()
                                    && c.addr_off == off
                                    && ((k == 0 && c.delta == 0) || c.delta == k);
                                if render_ok {
                                    addrs.push_str(&format!(" ({})",
                                        SymState::slot_expected_render(&bexpr, off, k)));
                                    haddrs.push_str(" rfl");
                                } else {
                                    addrs.push_str(&format!(" ({})",
                                        SymState::cell_render(c)));
                                    haddrs.push_str(&format!(
                                        " h_alias_{}_{}", pc, n_alias));
                                    n_alias += 1;
                                }
                                bargs.push_str(&format!(" {}", c.value.atom_lean()));
                                match &c.value {
                                    Expr::InitMem(n) =>
                                        bounds.push_str(&format!(" h{}_lt", n)),
                                    _ => bounds.push_str(" (by omega)"),
                                }
                            }
                            None => {
                                let n = format!("oldMemB_{}", fresh);
                                fresh += 1;
                                addrs.push_str(&format!(" ({})",
                                    SymState::slot_expected_render(&bexpr, off, k)));
                                haddrs.push_str(" rfl");
                                bargs.push_str(&format!(" {}", n));
                                bounds.push_str(&format!(" h{}_lt", n));
                            }
                        }
                    }
                    let w = insn.imm as u32; // toU64 imm % 2^32
                    let cb = w.to_le_bytes();
                    return Some(SpecCall {
                        hyp_name: hyp_name.clone(),
                        have_line: format!(
                            "have {} := stw_bytes_spec {} {} {} ({}){} {} {} {} {}{} {}{} \
(by decide) (by decide) (by decide) (by decide){}",
                            hyp_name, reg(dst), offl, imm, base_addr, bargs,
                            cb[0], cb[1], cb[2], cb[3], addrs, pc, bounds, haddrs,
                        ),
                    });
                }
            }
            let lookup = state.lookup_cell_aliased(&reg_val_expr(dst), off, Width::Word);
            let old_v = lookup
                .map(|(i, _)| state.mem[i].value.atom_lean())
                .unwrap_or_else(|| format!("oldMemW_{}", state.fresh));
            let alias = alias_suffix(&lookup);
            format!(
                "have {} := stw_spec {} {} {} ({}) ({}) {}{}",
                hyp_name, reg(dst), offl, imm, base_addr, old_v, pc, alias,
            )
        }
        ST_DW_IMM => {
            // stdw_spec baseReg off imm baseAddr oldDwordVal pc
            let base_addr = reg_val_lean(dst);
            let lookup = state.lookup_cell_aliased(&reg_val_expr(dst), off, Width::Dword);
            let old_v = lookup
                .map(|(i, _)| state.mem[i].value.atom_lean())
                .unwrap_or_else(|| format!("oldMemD_{}", state.fresh));
            let alias = alias_suffix(&lookup);
            format!(
                "have {} := stdw_spec {} {} {} ({}) ({}) {}{}",
                hyp_name, reg(dst), offl, imm, base_addr, old_v, pc, alias,
            )
        }
        ADD64_REG => {
            let v_old = reg_val_lean(dst);
            let v_src = reg_val_lean(src);
            format!(
                "have {} := add64_reg_spec {} {} ({}) ({}) {} (by decide)",
                hyp_name, reg(dst), reg(src), v_old, v_src, pc,
            )
        }
        SUB64_REG => {
            let v_old = reg_val_lean(dst);
            let v_src = reg_val_lean(src);
            format!(
                "have {} := sub64_reg_spec {} {} ({}) ({}) {} (by decide)",
                hyp_name, reg(dst), reg(src), v_old, v_src, pc,
            )
        }
        // Wrapping/bitwise reg-form ALU: `<op>_reg_spec dst src vOld v pc hne` (hne : dst ≠ .r10).
        MUL64_REG | OR64_REG | AND64_REG | XOR64_REG | LSH64_REG | RSH64_REG => {
            let v_old = reg_val_lean(dst);
            let v_src = reg_val_lean(src);
            let spec = match insn.opc {
                MUL64_REG => "mul64_reg_spec", OR64_REG  => "or64_reg_spec",
                AND64_REG => "and64_reg_spec", XOR64_REG => "xor64_reg_spec",
                LSH64_REG => "lsh64_reg_spec", RSH64_REG => "rsh64_reg_spec",
                _ => unreachable!(),
            };
            format!(
                "have {} := {} {} {} ({}) ({}) {} (by decide)",
                hyp_name, spec, reg(dst), reg(src), v_old, v_src, pc,
            )
        }
        MOV64_REG => {
            let v_old = reg_val_lean(dst);
            let v_src = reg_val_lean(src);
            format!(
                "have {} := mov64_reg_spec {} {} ({}) ({}) {} (by decide)",
                hyp_name, reg(dst), reg(src), v_old, v_src, pc,
            )
        }
        MOV64_IMM => {
            let v_old = reg_val_lean(dst);
            format!(
                "have {} := mov64_imm_spec {} {} ({}) {} (by decide)",
                hyp_name, reg(dst), imm, v_old, pc,
            )
        }
        LD_DW_IMM => {
            // lddw_spec dst imm vOld pc hne — same shape as mov64_imm.
            let v_old = reg_val_lean(dst);
            format!(
                "have {} := lddw_spec {} {} ({}) {} (by decide)",
                hyp_name, reg(dst), imm, v_old, pc,
            )
        }
        CALL_IMM => {
            // call_local_spec target cs r6V r7V r8V r9V r10V pc.
            // `cs` = pre-call stack (push happens in step(), not here); empty at top-level.
            let target = call_target.unwrap_or(0);
            let r6 = reg_val_lean(6); let r7 = reg_val_lean(7);
            let r8 = reg_val_lean(8); let r9 = reg_val_lean(9);
            let r10 = reg_val_lean(10);
            let cs = render_callstack(&state.call_stack);
            format!(
                "have {} := call_local_spec {} {} ({}) ({}) ({}) ({}) ({}) {}",
                hyp_name, target, cs, r6, r7, r8, r9, r10, pc,
            )
        }
        EXIT => {
            // exit_pops_spec frame cs r6Old r7Old r8Old r9Old r10Old pc.
            // r6Old..r10Old are the CURRENT (exit-time) register values in the exit_pops PRE.
            let r6 = reg_val_lean(6); let r7 = reg_val_lean(7);
            let r8 = reg_val_lean(8); let r9 = reg_val_lean(9);
            let r10 = reg_val_lean(10);
            // `frame`: retPc = `<callpc> + 1`, savedR6..savedR10 = CALL-TIME snapshot (NOT current — callee may clobber).
            // `cs` = stack below frame (empty at top-level).
            let n = state.call_stack.len();
            let (call_pc, saved) = state.call_stack.last()
                .map(|(p, s)| (*p, s.clone()))
                .unwrap_or((0, std::array::from_fn(|_| Expr::InitReg("?".into()))));
            let (sv6, sv7, sv8, sv9, sv10) = (
                saved[0].atom_lean(), saved[1].atom_lean(), saved[2].atom_lean(),
                saved[3].atom_lean(), saved[4].atom_lean());
            let cs = render_callstack(&state.call_stack[..n.saturating_sub(1)]);
            // `dsimp` forces iota reduction on `frame.savedR6..savedR10` fields (sl_block_iter doesn't run it).
            format!(
                "have {0} := exit_pops_spec ⟨{1} + 1, ({2}), ({3}), ({4}), ({5}), ({6})⟩ {7} ({8}) ({9}) ({10}) ({11}) ({12}) {13}\n  \
                 dsimp only at {0}",
                hyp_name,
                call_pc, sv6, sv7, sv8, sv9, sv10, cs,
                r6, r7, r8, r9, r10, pc,
            )
        }
        JEQ64_IMM | JEQ32_IMM => {
            let v_dst = reg_val_lean(dst);
            let target = jt;
            let h = branch_hyp_name.unwrap_or("h_branch?");
            let spec = if branch_taken == Some(true) {
                "jeq_imm_taken_spec"
            } else {
                "jeq_imm_not_taken_spec"
            };
            format!(
                "have {} := {} {} {} ({}) {} {} {}",
                hyp_name, spec, reg(dst), imm, v_dst, pc, target, h,
            )
        }
        JNE64_IMM | JNE32_IMM => {
            let v_dst = reg_val_lean(dst);
            let target = jt;
            let h = branch_hyp_name.unwrap_or("h_branch?");
            let spec = if branch_taken == Some(true) {
                "jne_imm_taken_spec"
            } else {
                "jne_imm_not_taken_spec"
            };
            format!(
                "have {} := {} {} {} ({}) {} {} {}",
                hyp_name, spec, reg(dst), imm, v_dst, pc, target, h,
            )
        }
        JGT64_IMM | JGT32_IMM => {
            let v_dst = reg_val_lean(dst);
            let target = jt;
            let h = branch_hyp_name.unwrap_or("h_branch?");
            let spec = if branch_taken == Some(true) {
                "jgt_imm_taken_spec"
            } else {
                "jgt_imm_not_taken_spec"
            };
            format!(
                "have {} := {} {} {} ({}) {} {} {}",
                hyp_name, spec, reg(dst), imm, v_dst, pc, target, h,
            )
        }
        JSGT64_IMM | JSGT32_IMM => {
            let v_dst = reg_val_lean(dst);
            let target = jt;
            let h = branch_hyp_name.unwrap_or("h_branch?");
            let spec = if branch_taken == Some(true) {
                "jsgt_imm_taken_spec"
            } else {
                "jsgt_imm_not_taken_spec"
            };
            format!(
                "have {} := {} {} {} ({}) {} {} {}",
                hyp_name, spec, reg(dst), imm, v_dst, pc, target, h,
            )
        }
        JSLE64_IMM | JSLE32_IMM => {
            let v_dst = reg_val_lean(dst);
            let target = jt;
            let h = branch_hyp_name.unwrap_or("h_branch?");
            let spec = if branch_taken == Some(true) {
                "jsle_imm_taken_spec"
            } else {
                "jsle_imm_not_taken_spec"
            };
            format!(
                "have {} := {} {} {} ({}) {} {} {}",
                hyp_name, spec, reg(dst), imm, v_dst, pc, target, h,
            )
        }
        JLT64_IMM | JLT32_IMM => {
            let v_dst = reg_val_lean(dst);
            let target = jt;
            let h = branch_hyp_name.unwrap_or("h_branch?");
            let spec = if branch_taken == Some(true) {
                "jlt_imm_taken_spec"
            } else {
                "jlt_imm_not_taken_spec"
            };
            format!(
                "have {} := {} {} {} ({}) {} {} {}",
                hyp_name, spec, reg(dst), imm, v_dst, pc, target, h,
            )
        }
        JLE64_IMM | JLE32_IMM => {
            let v_dst = reg_val_lean(dst);
            let target = jt;
            let h = branch_hyp_name.unwrap_or("h_branch?");
            let spec = if branch_taken == Some(true) {
                "jle_imm_taken_spec"
            } else {
                "jle_imm_not_taken_spec"
            };
            format!(
                "have {} := {} {} {} ({}) {} {} {}",
                hyp_name, spec, reg(dst), imm, v_dst, pc, target, h,
            )
        }
        JSLT64_IMM | JSLT32_IMM => {
            let v_dst = reg_val_lean(dst);
            let target = jt;
            let h = branch_hyp_name.unwrap_or("h_branch?");
            let spec = if branch_taken == Some(true) {
                "jslt_imm_taken_spec"
            } else {
                "jslt_imm_not_taken_spec"
            };
            format!(
                "have {} := {} {} {} ({}) {} {} {}",
                hyp_name, spec, reg(dst), imm, v_dst, pc, target, h,
            )
        }
        JEQ64_REG | JEQ32_REG => {
            let v_dst = reg_val_lean(dst);
            let v_src = reg_val_lean(src);
            let target = jt;
            let h = branch_hyp_name.unwrap_or("h_branch?");
            let spec = if branch_taken == Some(true) {
                "jeq_reg_taken_spec"
            } else {
                "jeq_reg_not_taken_spec"
            };
            format!(
                "have {} := {} {} {} ({}) ({}) {} {} {}",
                hyp_name, spec, reg(dst), reg(src), v_dst, v_src, pc, target, h,
            )
        }
        JNE64_REG | JNE32_REG => {
            let v_dst = reg_val_lean(dst);
            let v_src = reg_val_lean(src);
            let target = jt;
            let h = branch_hyp_name.unwrap_or("h_branch?");
            let spec = if branch_taken == Some(true) {
                "jne_reg_taken_spec"
            } else {
                "jne_reg_not_taken_spec"
            };
            format!(
                "have {} := {} {} {} ({}) ({}) {} {} {}",
                hyp_name, spec, reg(dst), reg(src), v_dst, v_src, pc, target, h,
            )
        }
        JLT64_REG | JLT32_REG => {
            let v_dst = reg_val_lean(dst);
            let v_src = reg_val_lean(src);
            let target = jt;
            let h = branch_hyp_name.unwrap_or("h_branch?");
            let spec = if branch_taken == Some(true) {
                "jlt_reg_taken_spec"
            } else {
                "jlt_reg_not_taken_spec"
            };
            format!(
                "have {} := {} {} {} ({}) ({}) {} {} {}",
                hyp_name, spec, reg(dst), reg(src), v_dst, v_src, pc, target, h,
            )
        }
        JSLE64_REG | JSLE32_REG => {
            let v_dst = reg_val_lean(dst);
            let v_src = reg_val_lean(src);
            let target = jt;
            let h = branch_hyp_name.unwrap_or("h_branch?");
            let spec = if branch_taken == Some(true) {
                "jsle_reg_taken_spec"
            } else {
                "jsle_reg_not_taken_spec"
            };
            format!(
                "have {} := {} {} {} ({}) ({}) {} {} {}",
                hyp_name, spec, reg(dst), reg(src), v_dst, v_src, pc, target, h,
            )
        }
        JGT64_REG | JGT32_REG | JLE64_REG | JLE32_REG | JSGE64_REG | JSGE32_REG
        | JGE64_REG | JGE32_REG | JSGT64_REG | JSGT32_REG | JSLT64_REG | JSLT32_REG
        | JSET64_REG | JSET32_REG => {
            let v_dst = reg_val_lean(dst);
            let v_src = reg_val_lean(src);
            let target = jt;
            let h = branch_hyp_name.unwrap_or("h_branch?");
            let stem = match insn.opc {
                JGT64_REG | JGT32_REG => "jgt_reg",
                JLE64_REG | JLE32_REG => "jle_reg",
                JSGE64_REG | JSGE32_REG => "jsge_reg",
                JGE64_REG | JGE32_REG => "jge_reg",
                JSGT64_REG | JSGT32_REG => "jsgt_reg",
                JSLT64_REG | JSLT32_REG => "jslt_reg",
                JSET64_REG | JSET32_REG => "jset_reg",
                _ => unreachable!(),
            };
            let suffix = if branch_taken == Some(true) { "taken_spec" } else { "not_taken_spec" };
            format!(
                "have {} := {}_{} {} {} ({}) ({}) {} {} {}",
                hyp_name, stem, suffix, reg(dst), reg(src), v_dst, v_src, pc, target, h,
            )
        }
        JGE64_IMM | JGE32_IMM | JSGE64_IMM | JSGE32_IMM | JSET64_IMM | JSET32_IMM => {
            let v_dst = reg_val_lean(dst);
            let target = jt;
            let h = branch_hyp_name.unwrap_or("h_branch?");
            let stem = match insn.opc {
                JGE64_IMM | JGE32_IMM => "jge_imm",
                JSGE64_IMM | JSGE32_IMM => "jsge_imm",
                JSET64_IMM | JSET32_IMM => "jset_imm",
                _ => unreachable!(),
            };
            let suffix = if branch_taken == Some(true) { "taken_spec" } else { "not_taken_spec" };
            format!(
                "have {} := {}_{} {} {} ({}) {} {} {}",
                hyp_name, stem, suffix, reg(dst), imm, v_dst, pc, target, h,
            )
        }
        JA => {
            let target = jt;
            format!("have {} := ja_spec {} {}", hyp_name, target, pc)
        }
        _ => return None,
    };
    Some(SpecCall { hyp_name, have_line })
}
