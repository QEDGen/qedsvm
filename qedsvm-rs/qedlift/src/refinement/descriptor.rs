use qed_analysis::layout::FieldKind;

use super::super::core::{canon_addr, Atom, Expr, Width};
use super::super::emit::{atoms_to_lean, fold_abstractions};
use super::super::input::{resolve_layout, DescriptorOp, RefinementDescriptor};
use super::parameter::resolve_parameter;
use super::shared::strip_refinement;
use super::RefinementCtx;
use super::{RefinementOutcome as Outcome, RefinementReason as Reason};

// Same machinery as `emit_vault_refinement` (layout-general `AsmRefinesFieldUpdate`,
// reshape via `account_agg`/`codecCoarse_eq_fine`, frame the untouched fields), but
// the layout + mutated field + delta come from a qedgen-shaped `RefinementDescriptor`
// instead of the hardcoded `refine_registry` arm match and the role-keyed
// `resolve_layout(..., "vault")`. This is what closes the "describe properties →
// prove the bytes" loop: a new program costs a descriptor, not a Rust edit.
//
// Differences from `emit_vault_refinement`, all additive (no change to the registry
// path, so existing pins stay byte-identical):
//   - predicate is always `AsmRefinesFieldUpdate` (no registry lookup);
//   - the layout is the descriptor's, validated against the lift (the bytes must
//     mutate the field the descriptor names — a real soundness check);
//   - the single-field case (empty frame, e.g. the counter) is handled: no
//     `cuTripleWithinMem_frame_right`, just `sl_exact lift`.
//   - split-blob (owned bytes inside a `bytes` field) is not handled here; a `bytes`
//     field is framed whole as one opaque gap (covers counter + vault).
// ════════════════════════════════════════════════════════════════

pub(super) fn emit_descriptor_refinement(
    desc: &RefinementDescriptor,
    ctx: RefinementCtx<'_>,
) -> Result<(String, String), Outcome> {
    // Shape substrate: when the descriptor has no inline layout, its account's
    // layout is resolved from `ctx.idl`/`ctx.sidecar_layouts` — the SAME
    // `qed-analysis` path the registry lift uses, so the seam stays name-level
    // (offsets are the IDL's job, not the descriptor's).
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

    // Shape: inline layout (no-IDL fallback) or resolved from the IDL by account name.
    let mut layout = match desc.explicit_layout() {
        Some(l) => l,
        None => match resolve_layout(sidecar_layouts, idl, &desc.account) {
            Some(l) => l,
            None => {
                return Err(Outcome::unsupported(
                    Reason::MissingLayout,
                    format!(
                        "could not resolve account {:?} from the IDL or inline layout",
                        desc.account
                    ),
                ));
            }
        },
    };
    let binding = if matches!(desc.op, DescriptorOp::AddParam { .. }) {
        Some(resolve_parameter(desc, ctx)?)
    } else {
        if desc.input_layout.is_some() {
            return Err(Outcome::unsupported(
                Reason::UnsupportedShape,
                "input_layout currently requires add_param",
            ));
        }
        None
    };
    if let Some(binding) = &binding {
        let input = desc
            .input_layout
            .as_ref()
            .expect("resolved binding has input layout");
        if layout.size > input.account_data_lengths[input.account_index] {
            return Err(Outcome::rejected(
                Reason::InvalidLayout,
                "account layout exceeds declared data length",
            ));
        }
        // The codec is based at entry r1; express its fields in serialized-input
        // coordinates, preserving the exact addresses in the lifted triple.
        for field in &mut layout.fields {
            field.offset = field
                .offset
                .checked_add(binding.account_offset as usize)
                .ok_or_else(|| Outcome::rejected(Reason::InvalidLayout, "field offset overflow"))?;
        }
    }
    // Mutated field's offset comes from the resolved layout (name-level seam).
    let mutated_off = match layout.fields.iter().find(|f| f.name == desc.mutated) {
        Some(f) if matches!(f.kind, FieldKind::U64) => i64::try_from(f.offset)
            .map_err(|_| Outcome::rejected(Reason::InvalidLayout, "field offset overflow"))?,
        Some(_) => {
            return Err(Outcome::unsupported(
                Reason::UnsupportedShape,
                "mutated field must be u64",
            ))
        }
        None => {
            return Err(Outcome::rejected(
                Reason::MissingField,
                format!(
                    "field {:?} is not in account {:?}",
                    desc.mutated, desc.account
                ),
            ));
        }
    };

    // Determine the mutated cell and the delta expression, by op kind. `delta_expr` is what
    // the field is credited by, rendered as Lean: a literal `k` (add_const) or the
    // parameter's binder name (add_param). `param_binder` is Some only for a parameter
    // delta — it is a lift binder that must also appear in the standalone `ensures` theorem.
    let is_initmem = |e: &Expr| matches!(e, Expr::InitMem(_));
    // Folded Lean value of the Dword cell at (base, off) in the pre — used to tell the
    // mutated field's own pre-value apart from the parameter operand in `field += param`.
    let pre_dword_val = |b: &str, off: i64| -> Option<String> {
        pre.iter().find_map(|a| match a {
            Atom::Mem {
                addr_base,
                addr_off,
                width,
                value,
                ..
            } if addr_base.to_lean() == b && *addr_off == off && matches!(width, Width::Dword) => {
                Some(fold(value))
            }
            _ => None,
        })
    };

    let base: Expr;
    let upd_off: i64;
    let upd_pre: Expr;
    let delta_expr: String;
    let param_binder: Option<String>;

    match &desc.op {
        DescriptorOp::AddConst { add_const } => {
            // Positive constant deltas: `+1` cleans via `wrapAdd_one_of_lt`, any other
            // positive literal via `wrapAdd_const_of_lt`. Zero / negative are out of scope.
            if *add_const < 1 {
                return Err(Outcome::unsupported(
                    Reason::UnsupportedOperation,
                    "add_const must be positive",
                ));
            }
            // The updated `u64` cell: `NatAdd(InitMem, Const)`.
            let mut found: Option<(Expr, i64, Expr, i64)> = None;
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
                                found = Some(((*addr_base).clone(), *addr_off, (**a).clone(), *k));
                                break;
                            }
                        }
                    }
                }
            }
            let (b, off, pre_e, k) = found.ok_or_else(|| {
                Outcome::unsupported(
                    Reason::MutationNotFound,
                    "no constant field increment found",
                )
            })?;
            // Soundness: the bytes' delta must match the descriptor's claimed constant.
            if k != *add_const {
                return Err(Outcome::rejected(
                    Reason::MutationMismatch,
                    format!("descriptor claims +{add_const}, bytes increment by {k}"),
                ));
            }
            base = b;
            upd_off = off;
            upd_pre = pre_e;
            delta_expr = k.to_string();
            param_binder = None;
        }
        DescriptorOp::AddParam { add_param } => {
            // The updated cell is `field += param`: `NatAdd(InitMem_field, InitMem_param)`,
            // where one operand is the cell's own pre-value and the other is a distinct
            // runtime read, whose address must match the IDL argument in the
            // declared serialized input layout.
            let mut found: Option<(Expr, i64, Expr, String)> = None;
            for atom in post_clean {
                if let Atom::Mem {
                    addr_base,
                    addr_off,
                    width,
                    value,
                    ..
                } = atom
                {
                    if !matches!(width, Width::Dword) {
                        continue;
                    }
                    if let Expr::NatAdd(a, b) = value {
                        if !(is_initmem(a) && is_initmem(b)) {
                            continue;
                        }
                        let bl = addr_base.to_lean();
                        let pre_val = match pre_dword_val(&bl, *addr_off) {
                            Some(v) => v,
                            None => continue,
                        };
                        let (a_l, b_l) = (fold(a), fold(b));
                        let (field_e, param_l) = if a_l == pre_val {
                            ((**a).clone(), b_l)
                        } else if b_l == pre_val {
                            ((**b).clone(), a_l)
                        } else {
                            continue;
                        };
                        found = Some(((*addr_base).clone(), *addr_off, field_e, param_l));
                        break;
                    }
                }
            }
            let (b, off, pre_e, param_l) = match found {
                Some(t) => t,
                None => {
                    return Err(Outcome::unsupported(
                        Reason::MutationNotFound,
                        format!("no field increment by runtime argument {add_param:?} found"),
                    ));
                }
            };
            let binding = binding.as_ref().expect("add_param resolved above");
            if !binding.matches_value(&param_l, ctx) {
                return Err(Outcome::rejected(
                    Reason::ParameterMismatch,
                    format!(
                        "increment operand is not argument {add_param:?} at input offset {}",
                        binding.argument_offset
                    ),
                ));
            }
            if canon_addr(&b, off) != canon_addr(&binding.input_base, mutated_off) {
                return Err(Outcome::rejected(
                    Reason::MutationMismatch,
                    "updated cell is not the named field in the declared serialized account",
                ));
            }
            base = b;
            upd_off = off;
            upd_pre = pre_e;
            delta_expr = param_l.clone();
            param_binder = Some(param_l);
        }
    }

    // Soundness: the bytes must mutate the field the descriptor names.
    if upd_off != mutated_off {
        return Err(Outcome::rejected(
            Reason::MutationMismatch,
            format!(
                "field {:?} is at offset {mutated_off}, bytes mutate {upd_off}",
                desc.mutated
            ),
        ));
    }

    let base_l = fold(&base);
    let upd_pre_l = fold(&upd_pre);

    // Walk the descriptor layout: own the updated `u64`, frame every other field.
    let mut fresh = 0u32;
    let mut params: Vec<String> = Vec::new();
    let mut ba_params: Vec<String> = Vec::new();
    let mut pre_fields: Vec<String> = Vec::new();
    let mut post_fields: Vec<String> = Vec::new();
    let mut frame: Vec<String> = Vec::new();
    let mut updated_seen = false;
    for f in &layout.fields {
        let off = f.offset as i64;
        match &f.kind {
            FieldKind::U64 if off == upd_off => {
                updated_seen = true;
                pre_fields.push(format!("({}, .u64 {})", off, upd_pre_l));
                post_fields.push(format!("({}, .u64 ({} + {}))", off, upd_pre_l, delta_expr));
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
            // Opaque region: framed whole as one gap (no split-blob in the prototype).
            FieldKind::Bytes(_) => {
                let g = format!("fg{}", fresh);
                fresh += 1;
                ba_params.push(g.clone());
                pre_fields.push(format!("({}, .blob [.gap {}])", off, g));
                post_fields.push(format!("({}, .blob [.gap {}])", off, g));
                frame.push(format!("(effectiveAddr {} {} ↦Bytes {})", base_l, off, g));
            }
        }
    }
    if !updated_seen {
        return Err(Outcome::unsupported(
            Reason::UnsupportedShape,
            "updated u64 field is unavailable",
        ));
    }

    // setup: lift atoms that don't own the updated `u64` (it flows through the fine codec).
    let owned_base = base.to_lean();
    let is_owned = |a: &Atom| match a {
        Atom::Mem {
            addr_base,
            addr_off,
            width,
            ..
        } => {
            addr_base.to_lean() == owned_base
                && *addr_off == upd_off
                && matches!(width, Width::Dword)
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
    let lean = render_descriptor_refinement(
        desc,
        &module,
        ctx,
        &DescriptorRender {
            base_l: &base_l,
            pre_fields: &pre_fields,
            post_fields: &post_fields,
            frame: &frame,
            params: &params,
            ba_params: &ba_params,
            setup_pre: &setup_pre,
            setup_post: &setup_post,
            upd_off,
            delta_expr: &delta_expr,
            param_binder: param_binder.as_deref(),
            upd_pre_l: &upd_pre_l,
        },
    );
    Ok((module, lean))
}

/// The field-walk products `emit_descriptor_refinement` hands its renderer.
struct DescriptorRender<'a> {
    base_l: &'a str,
    pre_fields: &'a [String],
    post_fields: &'a [String],
    frame: &'a [String],
    params: &'a [String],
    ba_params: &'a [String],
    setup_pre: &'a [Atom],
    setup_post: &'a [Atom],
    upd_off: i64,
    delta_expr: &'a str,
    param_binder: Option<&'a str>,
    upd_pre_l: &'a str,
}

fn render_descriptor_refinement(
    desc: &RefinementDescriptor,
    module: &str,
    ctx: RefinementCtx<'_>,
    r: &DescriptorRender<'_>,
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
    let &DescriptorRender {
        base_l,
        pre_fields,
        post_fields,
        frame,
        params,
        ba_params,
        setup_pre,
        setup_post,
        upd_off,
        delta_expr,
        param_binder,
        upd_pre_l,
    } = r;
    let mut nat_params = vars.join(" ");
    for p in params {
        nat_params.push(' ');
        nat_params.push_str(p);
    }
    // `ensures` corollary binders: the field-list params, plus the runtime parameter binder
    // for a parameter delta (the const case adds none).
    let mut ens_nat = upd_pre_l.to_string();
    for p in params {
        ens_nat.push(' ');
        ens_nat.push_str(p);
    }
    if let Some(pb) = param_binder {
        ens_nat.push(' ');
        ens_nat.push_str(pb);
    }
    let mut ensures_binders = format!("({ens_nat} : Nat)");
    if !ba_params.is_empty() {
        ensures_binders.push_str(&format!("\n    ({} : ByteArray)", ba_params.join(" ")));
    }
    let mut binders = format!("({nat_params} : Nat)");
    if !ba_params.is_empty() {
        binders.push_str(&format!("\n    ({} : ByteArray)", ba_params.join(" ")));
    }

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
    fine.push("sepConj_emp_right_eq".into());
    fine.push("Nat.add_zero".into());
    let fine_simp = fine.join(", ");
    let mut valid = vec!["codecValid", "FieldVal.fineValid"];
    if has_blob {
        valid.push("segsValid");
        valid.push("FieldSeg.valid");
    }
    let valid_tac = format!("by simp [{}]", valid.join(", "));

    let pre_list = pre_fields.join(", ");
    let post_list = post_fields.join(", ");
    let frame_s = frame.join(" **\n      ");
    let lift_pre = atoms_to_lean(pre, abs_subst);
    let lift_post = atoms_to_lean(post_clean, abs_subst);
    let setup_pre_s = atoms_to_lean(setup_pre, abs_subst);
    let setup_post_s = atoms_to_lean(setup_post, abs_subst);
    let handler_clause = desc
        .handler
        .as_ref()
        .map(|h| format!(", handler {}", h))
        .unwrap_or_default();
    let input_clause = desc.input_layout.as_ref().map(|input| format!(
        "\n  Input-layout assumption: aligned non-duplicate accounts with data lengths {:?},\n  tracked account index {}. Codec offsets below are relative to entry r1.\n  The add_param operand was matched to the named IDL argument's input address.",
        input.account_data_lengths, input.account_index
    )).unwrap_or_default();

    // Single-field account (empty frame, e.g. the counter): no `frame_right`,
    // the reshaped fine codec IS the lift's owned cell, so `sl_exact lift`.
    let proof_tail = if frame.is_empty() {
        "  sl_exact lift".to_string()
    } else {
        format!(
            "  have framed := cuTripleWithinMem_frame_right
    ( {frame} )
    (by sl_pcfree) lift
  sl_exact framed",
            frame = frame_s
        )
    };

    format!(
        "/-
  AsmRefinesFieldUpdate asm-refines theorem, SPEC-DRIVEN. Emitted by qedlift
  from a qedspec-shaped refinement descriptor (account {account}{handler},
  mutated field {mutated}), NOT from the hardcoded `refine_registry`. The
  field offsets come from the IDL (the shape substrate), not the descriptor.{input_clause}
  The lift owns the updated `u64` field; the account codec is reshaped
  coarse→fine via the layout-general `account_agg` (`codecCoarse_eq_fine`)
  and the untouched fields (if any) are framed. See docs/DEVEX_QEDSPEC_GAP.md.
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
    SVM.Solana.Abstract.AsmRefinesFieldUpdate cr {n} 0 {entry} {exit} rr {base}
      [{pre_list}]
      [{post_list}]
      ({setup_pre})
      ({setup_post}) := by
  unfold SVM.Solana.Abstract.AsmRefinesFieldUpdate
  rw [codecCoarse_eq_fine {base}
        [{pre_list}]
        ({valid_tac}),
      codecCoarse_eq_fine {base}
        [{post_list}]
        ({valid_tac})]
  simp only [{fine_simp}]
{proof_tail}

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
        account = desc.account,
        handler = handler_clause,
        mutated = desc.mutated,
        lift = strip_refinement(module),
        module = module,
        binders = binders,
        ensures_binders = ensures_binders,
        upd_off = upd_off,
        delta = delta_expr,
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
        proof_tail = proof_tail,
    )
}
