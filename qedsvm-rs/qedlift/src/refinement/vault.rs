use qed_analysis::layout::FieldKind;

use super::super::core::{Atom, Expr, Width};
use super::super::emit::{atoms_to_lean, fold_abstractions};
use super::super::input::resolve_layout;
use super::shared::{cell_val, strip_refinement};
use super::{RefineSpec, RefinementCtx};

/// Emit a vault (`AsmRefinesFieldUpdate`) refinement: owns the updated `u64`, frames the rest,
/// reshapes via `codecCoarse_eq_fine`. IDL-driven — new programs cost only a qedspec.
pub(super) fn emit_vault_refinement(
    spec: &RefineSpec,
    ctx: RefinementCtx<'_>,
) -> Option<(String, String)> {
    let RefinementCtx {
        lift_module,
        pre,
        post: post_clean,
        abs_subst,
        vars,
        n_cu,
        start_pc,
        exit_pc,
        idl,
        sidecar_layouts,
    } = ctx;
    let fold = |e: &Expr| fold_abstractions(e.to_lean(), abs_subst);
    let layout = resolve_layout(sidecar_layouts, idl, "vault")?;

    let mut updated: Option<(Expr, i64, Expr, i64)> = None; // base, off, pre_val, delta (NatAdd(InitMem, Const))
    for atom in post_clean {
        if let Atom::Mem {
            addr_base,
            addr_off,
            width,
            value,
            ..
        } = atom
        {
            if matches!(width, Width::Dword) {
                if let Expr::NatAdd(a, b) = value {
                    if let (Expr::InitMem(_), Expr::Const(k)) = (a.as_ref(), b.as_ref()) {
                        updated = Some(((*addr_base).clone(), *addr_off, (**a).clone(), *k));
                        break;
                    }
                }
            }
        }
    }
    let (base, upd_off, upd_pre, delta) = updated?;
    let base_l = fold(&base);
    let upd_pre_l = fold(&upd_pre);

    // Walk IDL layout: own the updated `u64`, frame every other field.
    let mut fresh = 0u32;
    let mut params: Vec<String> = Vec::new();
    let mut ba_params: Vec<String> = Vec::new();
    let mut pre_fields: Vec<String> = Vec::new();
    let mut post_fields: Vec<String> = Vec::new();
    let mut frame: Vec<String> = Vec::new();
    // Owned blob bytes (SPLIT blob): excluded from `setup`, need `< 256` hyps for codecValid.
    let mut owned_blob_offs: Vec<i64> = Vec::new();
    // `< 256` hyps for split blob's owned bytes; `omega` discharges after codecValid simp.
    let mut byte_hyps: Vec<String> = Vec::new();
    // Gap-size hyps `(name, "g.size = len")`: pin offsets so fine atoms land at lift's addresses.
    let mut gap_size_hyps: Vec<(String, String)> = Vec::new();
    let base_raw_blob = base.to_lean();
    let mut updated_seen = false;
    for f in &layout.fields {
        let off = f.offset as i64;
        match &f.kind {
            FieldKind::U64 if off == upd_off => {
                updated_seen = true;
                pre_fields.push(format!("({}, .u64 {})", off, upd_pre_l));
                post_fields.push(format!("({}, .u64 ({} + {}))", off, upd_pre_l, delta));
            }
            FieldKind::Pubkey => {
                let limbs: Vec<String> = (0..4)
                    .map(|_| {
                        let p = format!("o{}", fresh);
                        fresh += 1;
                        params.push(p.clone());
                        p
                    })
                    .collect();
                let rec = format!("⟨{}⟩", limbs.join(", "));
                pre_fields.push(format!("({}, .pubkey {})", off, rec));
                post_fields.push(format!("({}, .pubkey {})", off, rec));
                for (i, limb) in limbs.iter().enumerate() {
                    frame.push(format!(
                        "(effectiveAddr {} {} ↦U64 {})",
                        base_l,
                        off + 8 * i as i64,
                        limb
                    ));
                }
            }
            FieldKind::U64 => {
                let p = format!("fu{}", fresh);
                fresh += 1;
                params.push(p.clone());
                pre_fields.push(format!("({}, .u64 {})", off, p));
                post_fields.push(format!("({}, .u64 {})", off, p));
                frame.push(format!("(effectiveAddr {} {} ↦U64 {})", base_l, off, p));
            }
            FieldKind::Byte => {
                let p = format!("fb{}", fresh);
                fresh += 1;
                params.push(p.clone());
                pre_fields.push(format!("({}, .byte {})", off, p));
                post_fields.push(format!("({}, .byte {})", off, p));
                frame.push(format!("(effectiveAddr {} {} ↦ₘ {})", base_l, off, p));
            }
            // Blob field: frame as opaque `↦Bytes` gap unless the lift owns bytes inside it (SPLIT path below).
            FieldKind::Bytes(len) => {
                let len = *len as i64;
                // SPLIT if the lift owns bytes inside [off, off+len); else whole field is one opaque gap.
                let owned: Vec<(i64, String)> = (0..len)
                    .filter_map(|rel| {
                        cell_val(pre, &base_raw_blob, off + rel, true).map(|v| (rel, fold(v)))
                    })
                    .collect();
                if owned.is_empty() {
                    let g = format!("fg{}", fresh);
                    fresh += 1;
                    ba_params.push(g.clone());
                    pre_fields.push(format!("({}, .blob [.gap {}])", off, g));
                    post_fields.push(format!("({}, .blob [.gap {}])", off, g));
                    frame.push(format!("(effectiveAddr {} {} ↦Bytes {})", base_l, off, g));
                } else {
                    let mut segs: Vec<String> = Vec::new();
                    let mut cursor = 0i64;
                    for (rel, val) in &owned {
                        if *rel > cursor {
                            // Gap before owned byte: pin size (`fg.size = len`) so segsSL places the byte at `base + rel`.
                            let g = format!("fg{}", fresh);
                            fresh += 1;
                            ba_params.push(g.clone());
                            gap_size_hyps.push((
                                format!("h{}_sz", g),
                                format!("{}.size = {}", g, rel - cursor),
                            ));
                            segs.push(format!(".gap {}", g));
                            frame.push(format!(
                                "(effectiveAddr {} {} ↦Bytes {})",
                                base_l,
                                off + cursor,
                                g
                            ));
                        }
                        // Owned byte: NOT framed; fine `.byte` atom matches directly. Needs `< 256` hyp.
                        segs.push(format!(".byte ({})", val));
                        owned_blob_offs.push(off + rel);
                        byte_hyps.push(format!("(h_blob{} : {} < 256)", off + rel, val));
                        cursor = rel + 1;
                    }
                    if cursor < len {
                        // Trailing gap (last seg): no size hyp needed — free ByteArray.
                        let g = format!("fg{}", fresh);
                        fresh += 1;
                        ba_params.push(g.clone());
                        segs.push(format!(".gap {}", g));
                        frame.push(format!(
                            "(effectiveAddr {} {} ↦Bytes {})",
                            base_l,
                            off + cursor,
                            g
                        ));
                    }
                    let seglist = format!("[{}]", segs.join(", "));
                    pre_fields.push(format!("({}, .blob {})", off, seglist));
                    post_fields.push(format!("({}, .blob {})", off, seglist));
                }
            }
        }
    }
    if !updated_seen {
        return None;
    }

    // setup: lift atoms that don't own codec cells (updated u64 + split blob bytes flow through fine form).
    let owned_base = base.to_lean();
    let is_owned = |a: &Atom| match a {
        Atom::Mem {
            addr_base,
            addr_off,
            width,
            ..
        } => {
            addr_base.to_lean() == owned_base
                && ((*addr_off == upd_off && matches!(width, Width::Dword))
                    || (matches!(width, Width::Byte) && owned_blob_offs.contains(addr_off)))
        }
        _ => false,
    };
    let setup_pre: Vec<Atom> = pre.iter().filter(|a| !is_owned(a)).cloned().collect();
    let setup_post: Vec<Atom> = post_clean
        .iter()
        .filter(|a| !is_owned(a))
        .cloned()
        .collect();

    let module = format!("{}Refinement", lift_module);
    let lean = render_vault_refinement(VaultRender {
        spec,
        module: &module,
        base_l: &base_l,
        pre_fields: &pre_fields,
        post_fields: &post_fields,
        frame: &frame,
        params: &params,
        ba_params: &ba_params,
        pre,
        post_clean,
        setup_pre: &setup_pre,
        setup_post: &setup_post,
        abs_subst,
        vars,
        n_cu,
        start_pc,
        exit_pc,
        upd_off,
        delta,
        upd_pre_l: &upd_pre_l,
        byte_hyps: &byte_hyps,
        gap_size_hyps: &gap_size_hyps,
    });
    Some((module, lean))
}

struct VaultRender<'a> {
    spec: &'a RefineSpec,
    module: &'a str,
    base_l: &'a str,
    pre_fields: &'a [String],
    post_fields: &'a [String],
    frame: &'a [String],
    params: &'a [String],
    ba_params: &'a [String],
    pre: &'a [Atom],
    post_clean: &'a [Atom],
    setup_pre: &'a [Atom],
    setup_post: &'a [Atom],
    abs_subst: &'a std::collections::BTreeMap<String, String>,
    vars: &'a [String],
    n_cu: usize,
    start_pc: usize,
    exit_pc: usize,
    upd_off: i64,
    delta: i64,
    upd_pre_l: &'a str,
    byte_hyps: &'a [String],
    gap_size_hyps: &'a [(String, String)],
}

/// Render the vault refinement. Proof: `codecCoarse_eq_fine` reshape → simp fine atoms → `sl_exact`.
fn render_vault_refinement(r: VaultRender<'_>) -> String {
    let VaultRender {
        spec,
        module,
        base_l,
        pre_fields,
        post_fields,
        frame,
        params,
        ba_params,
        pre,
        post_clean,
        setup_pre,
        setup_post,
        abs_subst,
        vars,
        n_cu,
        start_pc,
        exit_pc,
        upd_off,
        delta,
        upd_pre_l,
        byte_hyps,
        gap_size_hyps,
    } = r;
    let mut nat_params = vars.join(" ");
    for p in params {
        nat_params.push(' ');
        nat_params.push_str(p);
    }
    // `ensures` corollary binders: only params that appear in the field lists (no unused binders).
    let mut ens_nat = upd_pre_l.to_string();
    for p in params {
        ens_nat.push(' ');
        ens_nat.push_str(p);
    }
    let mut ensures_binders = format!("({ens_nat} : Nat)");
    if !ba_params.is_empty() {
        ensures_binders.push_str(&format!("\n    ({} : ByteArray)", ba_params.join(" ")));
    }
    // ByteArray group only when a blob field is present; keeps non-blob output byte-identical.
    let mut binders = format!("({nat_params} : Nat)");
    if !ba_params.is_empty() {
        binders.push_str(&format!("\n    ({} : ByteArray)", ba_params.join(" ")));
    }
    for h in byte_hyps {
        binders.push_str(&format!("\n    {}", h));
    }
    for (name, prop) in gap_size_hyps {
        binders.push_str(&format!("\n    ({} : {})", name, prop));
    }
    // Simp sets: conditioned on field kinds present to avoid `unusedSimpArgs` and keep non-blob output stable.
    let has_pubkey = pre_fields.iter().any(|f| f.contains(".pubkey"));
    let has_blob = !ba_params.is_empty();
    let mut fine: Vec<String> = vec!["codecFine".into(), "FieldVal.fine".into()];
    if has_pubkey {
        fine.push("pubkeyIs".into());
    }
    if has_blob {
        fine.push("segsSL".into());
        fine.push("FieldSeg.sl".into());
    }
    // SPLIT blob: add `FieldSeg.size` + gap-size hyps so running offsets reduce to concrete addresses.
    if !gap_size_hyps.is_empty() {
        fine.push("FieldSeg.size".into());
        for (name, _) in gap_size_hyps {
            fine.push(name.clone());
        }
    }
    fine.push("sepConj_emp_right_eq".into());
    fine.push("Nat.add_zero".into());
    let fine_simp = fine.join(", ");
    let mut valid = vec!["codecValid", "FieldVal.fineValid"];
    if has_blob {
        valid.push("segsValid");
        valid.push("FieldSeg.valid");
    }
    let valid_simp = valid.join(", ");
    // SPLIT blob: `(v % 256) < 256` residual after codecValid simp → `omega`; whole-gap closes in simp alone.
    let valid_tac = if byte_hyps.is_empty() {
        format!("by simp [{valid_simp}]")
    } else {
        format!("by simp [{valid_simp}] <;> omega")
    };
    let pre_list = pre_fields.join(", ");
    let post_list = post_fields.join(", ");
    let frame_s = frame.join(" **\n      ");
    let lift_pre = atoms_to_lean(pre, abs_subst);
    let lift_post = atoms_to_lean(post_clean, abs_subst);
    let setup_pre_s = atoms_to_lean(setup_pre, abs_subst);
    let setup_post_s = atoms_to_lean(setup_post, abs_subst);

    format!(
        "/-
  {pred} asm-refines theorem for a multi-field NON-token account.
  MECHANICALLY EMITTED by qedlift from the Codama IDL account layout +
  the lift's atoms. The lift owns the updated `u64` field; the account
  codec is reshaped coarse→fine via the layout-general `account_agg`
  (`codecCoarse_eq_fine`) and the untouched fields are framed.
-/

import SVM.SBPF.Tactic.SL
import SVM.SBPF.Tactic.Discharge
import SVM.Solana.Abstract.Refinement
import Generated.{lift}TracedLifted

namespace Examples.{module}
open SVM SVM.SBPF SVM.SBPF.Memory

set_option maxHeartbeats 800000 in
theorem refines_asm
    (cr : CodeReq) (rr : Memory.RegionTable → Prop)
    {binders}
    (lift : cuTripleWithinMem {n} 0 {entry} {exit} cr
      ({lift_pre})
      ({lift_post}) rr) :
    SVM.Solana.Abstract.{pred} cr {n} 0 {entry} {exit} rr {base}
      [{pre_list}]
      [{post_list}]
      ({setup_pre})
      ({setup_post}) := by
  unfold SVM.Solana.Abstract.{pred}
  rw [codecCoarse_eq_fine {base}
        [{pre_list}]
        ({valid_tac}),
      codecCoarse_eq_fine {base}
        [{post_list}]
        ({valid_tac})]
  simp only [{fine_simp}]
  have framed := cuTripleWithinMem_frame_right
    ( {frame} )
    (by sl_pcfree) lift
  sl_exact framed

/-- qedgen `ensures`-shape, mechanically discharged: the mutated `u64`
    field (offset {upd_off}) shifts by {delta}. Pairs with `refines_asm`
    (which says the bytecode realises this field-list transition); together
    they discharge qedgen's `accessor post = accessor pre ± k` over the
    decoded field list via the layout-general accessor projection. -/
theorem ensures
    {ensures_binders} :
    u64FieldAt {upd_off} [{post_list}]
      = u64FieldAt {upd_off} [{pre_list}] + {delta} := by
  qedsvm_discharge

end Examples.{module}
",
        pred = spec.asm_pred,
        lift = strip_refinement(module),
        module = module,
        binders = binders,
        ensures_binders = ensures_binders,
        upd_off = upd_off,
        delta = delta,
        valid_tac = valid_tac,
        fine_simp = fine_simp,
        n = n_cu,
        entry = start_pc,
        exit = exit_pc,
        lift_pre = lift_pre,
        lift_post = lift_post,
        base = base_l,
        pre_list = pre_list,
        post_list = post_list,
        setup_pre = setup_pre_s,
        setup_post = setup_post_s,
        frame = frame_s,
    )
}

// ════════════════════════════════════════════════════════════════
// Spec-driven descriptor path (prototype) — the seam to qedspec.
//
