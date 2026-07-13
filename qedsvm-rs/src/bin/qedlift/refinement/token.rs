use super::super::core::{Atom, Expr, Width};
use super::super::emit::{atoms_to_lean, fold_abstractions};
use super::super::input::resolve_layout;
use super::shared::{cell_val, cell_val_dword, strip_refinement};
use super::{CodecKind, RefineSpec, RefinementCtx};

/// A balance/supply cell mutated in the post (`a ± b`, both loaded).
struct MutCell {
    base: Expr,
    base_raw: String,
    off: i64,
    a: Expr,
    b: Expr,
    is_sub: bool,
}

/// A synthesized SPL account field for the N-account walker: pubkey scalar,
/// the mutated `u64`, or an opaque region (split against lift ownership).
enum SynthKind {
    Pubkey,
    U64Updated,
    Blob(i64),
}

/// One account's contribution to the N-account `AsmRefinesFieldUpdates`
/// obligation: `(base, preFields, postFields)` triple plus the frame atoms,
/// consumed lift cells and binders its reshape needs.
struct AcctFields {
    role: &'static str,       // registry role — names the `ensures_<role>` corollary
    base_arg: String,         // "(addr5 + 88)" — account base argument
    pre_fields: Vec<String>,  // rendered `(off, FieldVal)` entries, pre values
    post_fields: Vec<String>, // same with the mutated field shifted
    frame: Vec<String>,       // frame atoms (unowned scalars + blob gaps)
    owned: Vec<(String, i64, bool)>, // lift cells consumed (excluded from setup)
    params: Vec<String>,      // fresh Nat params (framed pubkey limbs)
    ba_params: Vec<String>,   // fresh ByteArray params (blob gaps)
    byte_hyps: Vec<String>,   // `< 256` hyps for owned blob bytes (codecValid)
    // Gap-size hyps `(name, "g.size = len")`: pin offsets so fine atoms land at lift's addresses.
    gap_size_hyps: Vec<(String, String)>,
    has_owned_segs: bool, // any `.byte`/`.u64` seg inside a blob (needs FieldSeg.size)
    field_off: i64,       // mutated `u64`'s offset within the account
    is_sub: bool,         // debit (`-`) vs credit (`+`)
}

/// Emit the N-account token/mint refinement (#25): one `(base, preFields,
/// postFields)` triple per registry account, targeting the layout-general
/// `AsmRefinesFieldUpdates`. Same mechanism as `emit_vault_refinement` —
/// reshape coarse→fine via `codecCoarse_eq_fine`, frame the untouched cells —
/// generalized to N accounts and to `.u64` segs inside opaque regions.
pub(super) fn emit_token_refinement(
    spec: &RefineSpec,
    ctx: RefinementCtx<'_>,
) -> Option<(String, String)> {
    let RefinementCtx {
        lift_module,
        pre,
        post: post_clean,
        abs_subst,
        idl,
        sidecar_layouts,
        ..
    } = ctx;
    let fold = |e: &Expr| fold_abstractions(e.to_lean(), abs_subst);

    // ── Detect mutated account cells (a ± b, both InitMem) ──────────
    let is_initmem = |e: &Expr| matches!(e, Expr::InitMem(_));
    let mut muts: Vec<MutCell> = Vec::new();
    for atom in post_clean {
        if let Atom::Mem {
            addr_base,
            addr_off,
            value,
            ..
        } = atom
        {
            let (a, b, is_sub) = match value {
                Expr::CleanSub(a, b) => ((**a).clone(), (**b).clone(), true),
                Expr::NatAdd(a, b) => ((**a).clone(), (**b).clone(), false),
                _ => continue,
            };
            if is_initmem(&a) && is_initmem(&b) {
                muts.push(MutCell {
                    base: addr_base.clone(),
                    base_raw: addr_base.to_lean(),
                    off: *addr_off,
                    a,
                    b,
                    is_sub,
                });
            }
        }
    }
    if muts.is_empty() {
        return None;
    }
    // The transferred amount `b` is shared across all mutated cells.
    let amount = fold(&muts[0].b);

    // SPL offsets from the IDL where available (fallback: amount@64 in a
    // 165-byte token account, supply@36 in an 82-byte mint).
    let (tok_amount_off, tok_size) = resolve_layout(sidecar_layouts, idl, "token")
        .and_then(|l| {
            let a = l.fields.iter().find(|f| f.name == "amount")?;
            Some((a.offset as i64, l.size as i64))
        })
        .unwrap_or((64, 165));
    let (mint_supply_off, mint_size) = resolve_layout(sidecar_layouts, idl, "mint")
        .and_then(|l| {
            let s = l.fields.iter().find(|f| f.name == "supply")?;
            Some((s.offset as i64, l.size as i64))
        })
        .unwrap_or((36, 82));

    // ── Assign each registry account to a mutated cell; walk its layout ────────────────────────
    // Token amount cells have a mint dword at off-64; mint supply cells have is_initialized at off+9.
    let is_mint_mut = |m: &MutCell| cell_val(pre, &m.base_raw, m.off + 9, true).is_some();
    let is_tok_mut = |m: &MutCell| cell_val(pre, &m.base_raw, m.off - 64, false).is_some();
    let mut used = vec![false; muts.len()];
    let mut accts: Vec<AcctFields> = Vec::new();
    let mut fresh = 0u32;
    for (role, codec) in spec.accounts {
        // Pick unused mutated cell for this codec; for two token accounts (Transfer), src=sub, dst=add.
        let want_sub = *role == "src" || *role == "account";
        let idx = (0..muts.len()).find(|&i| {
            !used[i]
                && match codec {
                    CodecKind::Token => {
                        is_tok_mut(&muts[i])
                            && (spec
                                .accounts
                                .iter()
                                .filter(|(_, c)| *c == CodecKind::Token)
                                .count()
                                < 2
                                || muts[i].is_sub == want_sub)
                    }
                    CodecKind::Mint => is_mint_mut(&muts[i]),
                    // All-counter / all-vault specs take their early
                    // `emit_*_refinement` paths; this loop only runs for
                    // token/mint codecs.
                    CodecKind::Counter | CodecKind::Vault => {
                        unreachable!("counter/vault codec handled by its own emitter")
                    }
                }
        })?;
        used[idx] = true;
        let m = &muts[idx];
        // Synthesized SPL layout: scalar fields + opaque regions covering the
        // remainder (split against lift ownership by `build_account_fields`).
        let (field_off, synth): (i64, Vec<(i64, SynthKind)>) = match codec {
            CodecKind::Token => (
                tok_amount_off,
                vec![
                    (0, SynthKind::Pubkey),
                    (32, SynthKind::Pubkey),
                    (tok_amount_off, SynthKind::U64Updated),
                    (
                        tok_amount_off + 8,
                        SynthKind::Blob(tok_size - tok_amount_off - 8),
                    ),
                ],
            ),
            CodecKind::Mint => (
                mint_supply_off,
                vec![
                    (0, SynthKind::Blob(mint_supply_off)),
                    (mint_supply_off, SynthKind::U64Updated),
                    (
                        mint_supply_off + 8,
                        SynthKind::Blob(mint_size - mint_supply_off - 8),
                    ),
                ],
            ),
            CodecKind::Counter | CodecKind::Vault => {
                unreachable!("counter/vault codec handled by its own emitter")
            }
        };
        accts.push(build_account_fields(
            ctx, m, &amount, field_off, &synth, &mut fresh, role,
        )?);
    }

    // ── Assemble setup atoms (lift cells not owned by any account) ──
    let owned: std::collections::HashSet<(String, i64, bool)> =
        accts.iter().flat_map(|b| b.owned.iter().cloned()).collect();
    let is_owned = |a: &Atom| match a {
        Atom::Mem {
            addr_base,
            addr_off,
            width,
            ..
        } => owned.contains(&(addr_base.to_lean(), *addr_off, matches!(width, Width::Byte))),
        _ => false,
    };
    let setup_pre: Vec<Atom> = pre.iter().filter(|a| !is_owned(a)).cloned().collect();
    let setup_post: Vec<Atom> = post_clean
        .iter()
        .filter(|a| !is_owned(a))
        .cloned()
        .collect();

    let module = format!("{}Refinement", lift_module);
    let lean =
        render_token_refinement(spec, &module, &accts, ctx, &setup_pre, &setup_post, &amount);
    Some((module, lean))
}

/// Walk one account's synthesized layout against the lift's owned cells.
/// Owned scalars flow through the fine codec (their values appear in the
/// field list); unowned scalars become framed params; opaque regions split
/// into owned `.u64`/`.byte` segs and framed `.gap`s, with gap-size
/// hypotheses pinning the running offsets (`segsSL`) to the lift's addresses.
fn build_account_fields(
    ctx: RefinementCtx<'_>,
    m: &MutCell,
    amount: &str,
    field_off: i64,
    synth: &[(i64, SynthKind)],
    fresh: &mut u32,
    role: &'static str,
) -> Option<AcctFields> {
    let RefinementCtx { pre, abs_subst, .. } = ctx;
    let fold = |e: &Expr| fold_abstractions(e.to_lean(), abs_subst);
    let base_off = m.off - field_off;
    let base_expr = fold(&m.base);
    let base_arg = if base_off == 0 {
        base_expr.clone()
    } else {
        format!("({} + {})", base_expr, base_off)
    };
    let mut a = AcctFields {
        role,
        base_arg,
        pre_fields: Vec::new(),
        post_fields: Vec::new(),
        frame: Vec::new(),
        owned: Vec::new(),
        params: Vec::new(),
        ba_params: Vec::new(),
        byte_hyps: Vec::new(),
        gap_size_hyps: Vec::new(),
        has_owned_segs: false,
        field_off,
        is_sub: m.is_sub,
    };
    for (off, kind) in synth {
        let abs = base_off + *off;
        match kind {
            SynthKind::U64Updated => {
                // The account's mutated cell must be this field.
                if abs != m.off {
                    return None;
                }
                let pre_v = fold(&m.a);
                let post_v = if m.is_sub {
                    format!("({} - {})", pre_v, amount)
                } else {
                    format!("({} + {})", pre_v, amount)
                };
                a.pre_fields.push(format!("({}, .u64 {})", off, pre_v));
                a.post_fields.push(format!("({}, .u64 {})", off, post_v));
                a.owned.push((m.base_raw.clone(), abs, false));
            }
            SynthKind::Pubkey => {
                if (0..4).all(|i| cell_val(pre, &m.base_raw, abs + 8 * i, false).is_some()) {
                    // Owned pubkey: its limbs flow through the fine codec.
                    let limbs: Vec<String> = (0..4)
                        .map(|i| {
                            a.owned.push((m.base_raw.clone(), abs + 8 * i, false));
                            fold(cell_val(pre, &m.base_raw, abs + 8 * i, false).unwrap())
                        })
                        .collect();
                    let rec = format!("⟨{}⟩", limbs.join(", "));
                    a.pre_fields.push(format!("({}, .pubkey {})", off, rec));
                    a.post_fields.push(format!("({}, .pubkey {})", off, rec));
                } else {
                    // Unread pubkey: fresh limb params, framed.
                    let limbs: Vec<String> = (0..4)
                        .map(|_| {
                            let p = format!("o{}", *fresh);
                            *fresh += 1;
                            a.params.push(p.clone());
                            p
                        })
                        .collect();
                    let rec = format!("⟨{}⟩", limbs.join(", "));
                    a.pre_fields.push(format!("({}, .pubkey {})", off, rec));
                    a.post_fields.push(format!("({}, .pubkey {})", off, rec));
                    for (i, limb) in limbs.iter().enumerate() {
                        a.frame.push(format!(
                            "(effectiveAddr {} {} ↦U64 {})",
                            base_expr,
                            abs + 8 * i as i64,
                            limb
                        ));
                    }
                }
            }
            SynthKind::Blob(len) => {
                let mut segs: Vec<String> = Vec::new();
                let mut cursor = 0i64; // end of the last owned seg (field-relative)
                let mut rel = 0i64;
                while rel < *len {
                    // Owned dword seg (only if fully inside the region), else owned byte seg.
                    let dw = if rel + 8 <= *len {
                        cell_val_dword(pre, &m.base_raw, abs + rel)
                    } else {
                        None
                    };
                    let by = if dw.is_none() {
                        cell_val(pre, &m.base_raw, abs + rel, true)
                    } else {
                        None
                    };
                    if dw.is_none() && by.is_none() {
                        rel += 1;
                        continue;
                    }
                    if rel > cursor {
                        // Gap before an owned seg: pin its size so `segsSL`
                        // places the following segs at the lift's addresses.
                        let g = format!("fg{}", *fresh);
                        *fresh += 1;
                        a.ba_params.push(g.clone());
                        a.gap_size_hyps.push((
                            format!("h{}_sz", g),
                            format!("{}.size = {}", g, rel - cursor),
                        ));
                        segs.push(format!(".gap {}", g));
                        a.frame.push(format!(
                            "(effectiveAddr {} {} ↦Bytes {})",
                            base_expr,
                            abs + cursor,
                            g
                        ));
                    }
                    if let Some(v) = dw {
                        segs.push(format!(".u64 ({})", fold(v)));
                        a.owned.push((m.base_raw.clone(), abs + rel, false));
                        rel += 8;
                    } else {
                        let val = fold(by.unwrap());
                        segs.push(format!(".byte ({})", val));
                        a.byte_hyps.push(format!("(h_b{} : {} < 256)", *fresh, val));
                        *fresh += 1;
                        a.owned.push((m.base_raw.clone(), abs + rel, true));
                        rel += 1;
                    }
                    a.has_owned_segs = true;
                    cursor = rel;
                }
                if cursor < *len {
                    // Trailing gap (last seg): no size hyp needed — free ByteArray.
                    let g = format!("fg{}", *fresh);
                    *fresh += 1;
                    a.ba_params.push(g.clone());
                    segs.push(format!(".gap {}", g));
                    a.frame.push(format!(
                        "(effectiveAddr {} {} ↦Bytes {})",
                        base_expr,
                        abs + cursor,
                        g
                    ));
                }
                let seglist = format!("[{}]", segs.join(", "));
                a.pre_fields.push(format!("({}, .blob {})", off, seglist));
                a.post_fields.push(format!("({}, .blob {})", off, seglist));
            }
        }
    }
    Some(a)
}

/// True iff `n` occurs in `hay` as a standalone identifier.
fn contains_ident(hay: &str, n: &str) -> bool {
    let ident = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
    hay.match_indices(n).any(|(i, _)| {
        let bytes = hay.as_bytes();
        let before_ok = i == 0 || !ident(bytes[i - 1]);
        let after = i + n.len();
        let after_ok = after >= bytes.len() || !ident(bytes[after]);
        before_ok && after_ok
    })
}

/// Render the N-account token/mint refinement: `refines_asm` targeting
/// `AsmRefinesFieldUpdates` (proof: unfold the account fold, reshape each
/// coarse codec via `codecCoarse_eq_fine`, frame, `sl_exact`) plus one
/// `ensures_<role>` accessor corollary per account.
fn render_token_refinement(
    spec: &RefineSpec,
    module: &str,
    accts: &[AcctFields],
    ctx: RefinementCtx<'_>,
    setup_pre: &[Atom],
    setup_post: &[Atom],
    amount: &str,
) -> String {
    let RefinementCtx {
        pre,
        post: post_clean,
        abs_subst,
        vars,
        n_cu,
        start_pc,
        exit_pc,
        ..
    } = ctx;
    let mut nat_params = vars.join(" ");
    for b in accts {
        for p in &b.params {
            nat_params.push(' ');
            nat_params.push_str(p);
        }
    }
    let ba_params: Vec<String> = accts
        .iter()
        .flat_map(|b| b.ba_params.iter().cloned())
        .collect();
    let mut binders = format!("({nat_params} : Nat)");
    if !ba_params.is_empty() {
        binders.push_str(&format!("\n    ({} : ByteArray)", ba_params.join(" ")));
    }
    for b in accts {
        for h in &b.byte_hyps {
            binders.push_str(&format!("\n    {}", h));
        }
    }
    for b in accts {
        for (name, prop) in &b.gap_size_hyps {
            binders.push_str(&format!("\n    ({} : {})", name, prop));
        }
    }

    // Account `(base, preFields, postFields)` triples, in registry order.
    let triples = accts
        .iter()
        .map(|b| {
            format!(
                "({},\n        [{}],\n        [{}])",
                b.base_arg,
                b.pre_fields.join(", "),
                b.post_fields.join(", ")
            )
        })
        .collect::<Vec<_>>()
        .join(",\n       ");

    let has_bytes = accts.iter().any(|b| !b.byte_hyps.is_empty());
    // Owned blob bytes leave `< 256` residuals after the codecValid simp → `omega`.
    let valid_tac = if has_bytes {
        "by simp [codecValid, FieldVal.fineValid, segsValid, FieldSeg.valid] <;> omega"
    } else {
        "by simp [codecValid, FieldVal.fineValid, segsValid, FieldSeg.valid]"
    };
    let mut rw: Vec<String> = Vec::new();
    for b in accts {
        rw.push(format!(
            "codecCoarse_eq_fine {}\n        [{}]\n        ({})",
            b.base_arg,
            b.pre_fields.join(", "),
            valid_tac
        ));
    }
    for b in accts {
        rw.push(format!(
            "codecCoarse_eq_fine {}\n        [{}]\n        ({})",
            b.base_arg,
            b.post_fields.join(", "),
            valid_tac
        ));
    }

    // Fine simp set: unfold the fine codec to scattered atoms and normalize
    // running blob offsets (`FieldSeg.size` + gap-size hyps) and account-base
    // additions (`Nat.add_assoc`/`Nat.reduceAdd`) to the lift's flat addresses.
    let mut fine: Vec<String> = vec![
        "codecFine".into(),
        "FieldVal.fine".into(),
        "pubkeyIs".into(),
        "segsSL".into(),
        "FieldSeg.sl".into(),
    ];
    if accts.iter().any(|b| b.has_owned_segs) {
        fine.push("FieldSeg.size".into());
    }
    for b in accts {
        for (name, _) in &b.gap_size_hyps {
            fine.push(name.clone());
        }
    }
    fine.push("sepConj_emp_right_eq".into());
    fine.push("Nat.add_zero".into());
    fine.push("Nat.add_assoc".into());
    fine.push("Nat.reduceAdd".into());
    let fine_simp = fine.join(", ");

    let frame_atoms: Vec<String> = accts.iter().flat_map(|b| b.frame.iter().cloned()).collect();
    let frame = frame_atoms.join(" **\n      ");
    let proof_tail = if frame_atoms.is_empty() {
        "  sl_exact lift".to_string()
    } else {
        format!(
            "  have framed := cuTripleWithinMem_frame_right
    ( {frame} )
    (by sl_pcfree) lift
  sl_exact framed"
        )
    };

    let lift_pre = atoms_to_lean(pre, abs_subst);
    let lift_post = atoms_to_lean(post_clean, abs_subst);
    let setup_pre_s = atoms_to_lean(setup_pre, abs_subst);
    let setup_post_s = atoms_to_lean(setup_post, abs_subst);

    // One accessor corollary per account: the mutated `u64` shifts by `amount`.
    // Binders are filtered to the identifiers its field lists mention.
    let nat_pool: Vec<String> = {
        let mut p: Vec<String> = vars.to_vec();
        for b in accts {
            p.extend(b.params.iter().cloned());
        }
        p
    };
    let ensures = accts
        .iter()
        .map(|b| {
            let hay: Vec<&String> = b.pre_fields.iter().chain(b.post_fields.iter()).collect();
            let uses = |n: &String| hay.iter().any(|h| contains_ident(h, n));
            let ens_nat: Vec<String> = nat_pool.iter().filter(|n| uses(n)).cloned().collect();
            let ens_ba: Vec<String> = b.ba_params.iter().filter(|n| uses(n)).cloned().collect();
            let mut ens_binders = format!("({} : Nat)", ens_nat.join(" "));
            if !ens_ba.is_empty() {
                ens_binders.push_str(&format!("\n    ({} : ByteArray)", ens_ba.join(" ")));
            }
            let op = if b.is_sub { "-" } else { "+" };
            format!(
                "/-- qedgen `ensures`-shape for the `{role}` account, mechanically
    discharged: its `u64` field (offset {off}) shifts by `{amount}`. -/
theorem ensures_{role}
    {ens_binders} :
    u64FieldAt {off} [{post_list}]
      = u64FieldAt {off} [{pre_list}] {op} {amount} := by
  qedsvm_discharge",
                role = b.role,
                off = b.field_off,
                amount = amount,
                ens_binders = ens_binders,
                op = op,
                pre_list = b.pre_fields.join(", "),
                post_list = b.post_fields.join(", ")
            )
        })
        .collect::<Vec<_>>()
        .join("\n\n");

    format!(
        "/-
  {pred} asm-refines theorem for the SPL token/mint arms. MECHANICALLY
  EMITTED by qedlift's refinement codegen from the lift's atoms + the IDL
  arm name. One `(base, preFields, postFields)` triple per account on the
  layout-general vault route: each coarse codec is reshaped to fine via
  `codecCoarse_eq_fine` (`account_agg`) and the untouched cells are framed —
  no bespoke record predicate, no aggregation module (#25).
-/

import SVM.SBPF.Tactic.SL
import SVM.SBPF.Tactic.Discharge
import SVM.Solana.Abstract.Refinement
import Generated.{lift}TracedLifted

namespace Examples.{module}
open SVM SVM.SBPF SVM.SBPF.Memory

set_option maxHeartbeats 1600000 in
theorem refines_asm
    (cr : CodeReq) (rr : Memory.RegionTable → Prop)
    {binders}
    (lift : cuTripleWithinMem {n} 0 {entry} {exit} cr
      ({lift_pre})
      ({lift_post}) rr) :
    SVM.Solana.Abstract.{pred} cr {n} 0 {entry} {exit} rr
      [{triples}]
      ({setup_pre})
      ({setup_post}) := by
  unfold SVM.Solana.Abstract.{pred}
  simp only [SVM.Solana.Abstract.codecsPre, SVM.Solana.Abstract.codecsPost]
  rw [{rw}]
  simp only [{fine_simp}]
{proof_tail}

{ensures}

end Examples.{module}
",
        pred = spec.asm_pred,
        lift = strip_refinement(module),
        module = module,
        binders = binders,
        n = n_cu,
        entry = start_pc,
        exit = exit_pc,
        lift_pre = lift_pre,
        lift_post = lift_post,
        triples = triples,
        setup_pre = setup_pre_s,
        setup_post = setup_post_s,
        rw = rw.join(",\n      "),
        fine_simp = fine_simp,
        proof_tail = proof_tail,
        ensures = ensures,
    )
}
