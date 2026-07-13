use super::super::core::{Atom, Expr, Width};
use super::super::emit::{atoms_to_lean, fold_abstractions};
use super::shared::strip_refinement;
use super::{RefineSpec, RefinementCtx};

/// Emit a counter-codec refinement: single owned `u64` cell, constant +1 delta.
/// No aggregation (coarse = fine for `u64`), no frame, no `amount` arg.
pub(super) fn emit_counter_refinement(
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
        ..
    } = ctx;
    let fold = |e: &Expr| fold_abstractions(e.to_lean(), abs_subst);

    // Find the post-state incremented `u64` cell (NatAdd(InitMem, Const) form).
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
    let (base, off, pre_val, delta) = found?;
    let base_l = fold(&base);
    let addr_arg = if off == 0 {
        base_l.clone()
    } else {
        format!("({} + {})", base_l, off)
    };
    let counter_pre = fold(&pre_val);
    let record = format!("{{ counter := {} }}", counter_pre);

    // Owned `u64` cell flows through the codec's fine form; everything else stays in setup.
    let owned_base = base.to_lean();
    let is_owned = |a: &Atom| match a {
        Atom::Mem {
            addr_base,
            addr_off,
            width,
            ..
        } => addr_base.to_lean() == owned_base && *addr_off == off && matches!(width, Width::Dword),
        _ => false,
    };
    let setup_pre: Vec<Atom> = pre.iter().filter(|a| !is_owned(a)).cloned().collect();
    let setup_post: Vec<Atom> = post_clean
        .iter()
        .filter(|a| !is_owned(a))
        .cloned()
        .collect();

    let module = format!("{}Refinement", lift_module);
    let lean = render_counter_refinement(CounterRender {
        spec,
        module: &module,
        addr_arg: &addr_arg,
        record: &record,
        pre,
        post_clean,
        setup_pre: &setup_pre,
        setup_post: &setup_post,
        abs_subst,
        vars,
        n_cu,
        start_pc,
        exit_pc,
        counter_pre: &counter_pre,
        delta,
    });
    Some((module, lean))
}

struct CounterRender<'a> {
    spec: &'a RefineSpec,
    module: &'a str,
    addr_arg: &'a str,
    record: &'a str,
    pre: &'a [Atom],
    post_clean: &'a [Atom],
    setup_pre: &'a [Atom],
    setup_post: &'a [Atom],
    abs_subst: &'a std::collections::BTreeMap<String, String>,
    vars: &'a [String],
    n_cu: usize,
    start_pc: usize,
    exit_pc: usize,
    counter_pre: &'a str,
    delta: i64,
}

/// Render the counter refinement theorem. Proof: `unfold` + `simp [counterValOf]` + `sl_exact`.
fn render_counter_refinement(r: CounterRender<'_>) -> String {
    let CounterRender {
        spec,
        module,
        addr_arg,
        record,
        pre,
        post_clean,
        setup_pre,
        setup_post,
        abs_subst,
        vars,
        n_cu,
        start_pc,
        exit_pc,
        counter_pre,
        delta,
    } = r;
    let nat_params = vars.join(" ");
    let lift_pre = atoms_to_lean(pre, abs_subst);
    let lift_post = atoms_to_lean(post_clean, abs_subst);
    let setup_pre_s = atoms_to_lean(setup_pre, abs_subst);
    let setup_post_s = atoms_to_lean(setup_post, abs_subst);

    format!(
        "/-
  {pred} asm-refines-intrinsic theorem. MECHANICALLY EMITTED by qedlift's
  refinement codegen — the first NON-token refinement. The counter
  account is a single `u64` field (coarse = fine, no codec aggregation),
  so the proof is `unfold` + `simp [counterValOf]` + `sl_exact` with no
  aggregation rewrite and no frame.
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
    ({nat_params} : Nat)
    (lift : cuTripleWithinMem {n} 0 {entry} {exit} cr
      ({lift_pre})
      ({lift_post}) rr) :
    SVM.Solana.Abstract.{pred} cr {n} 0 {entry} {exit} rr {addr}
      {record}
      ({setup_pre})
      ({setup_post}) := by
  unfold SVM.Solana.Abstract.{pred}
  simp only [SVM.Solana.counterValOf_eq]
  sl_exact lift

/-- qedgen `ensures`-shape, mechanically discharged: the counter field
    shifts by {delta}. Pairs with `refines_asm`; the counter account is a
    single-`u64` field list, so the accessor projection is `u64FieldAt 0`. -/
theorem ensures ({counter_pre} : Nat) :
    u64FieldAt 0 [(0, .u64 ({counter_pre} + {delta}))]
      = u64FieldAt 0 [(0, .u64 {counter_pre})] + {delta} := by
  qedsvm_discharge

end Examples.{module}
",
        pred = spec.asm_pred,
        lift = strip_refinement(module),
        module = module,
        nat_params = nat_params,
        counter_pre = counter_pre,
        delta = delta,
        n = n_cu,
        entry = start_pc,
        exit = exit_pc,
        lift_pre = lift_pre,
        lift_post = lift_post,
        addr = addr_arg,
        record = record,
        setup_pre = setup_pre_s,
        setup_post = setup_post_s,
    )
}
