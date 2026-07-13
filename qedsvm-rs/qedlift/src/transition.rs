//! Whole-transition codegen boundary.
//!
//! Callers depend on this facade rather than the codec-refinement module's
//! implementation layout. This keeps the subsequent move of the large
//! transition walkers mechanically reviewable and byte-for-byte testable.

use super::input::{resolve_layout, DescriptorOp};
use super::refinement::{cell_val, cell_val_dword};
use super::*;
use qed_analysis::layout::FieldKind;

/// Structured binder metadata for one path corollary's signature, in
/// signature order. Drives the bundle's canonical renaming.
#[derive(Clone)]
pub(super) enum BItem {
    Val(String),
    Hyp { name: String, prop: String },
    Guard { prop: String },
}

/// The lifted triple a transition corollary composes with.
pub(super) struct RefineTarget<'a> {
    pub(super) name: &'a str,
    pub(super) args: &'a str,
    pub(super) binders: &'a str,
    pub(super) bitems: Vec<BItem>,
}

/// The typed-fault tail of a transition fault corollary.
pub(super) struct FaultTail<'a> {
    pub(super) ctor: &'a str,
    pub(super) spec: &'a str,
    pub(super) oob: Option<(u8, i64, bool)>,
    pub(super) target_post: &'a str,
}

/// One path's contribution to the transition bundle.
pub(super) struct TransitionPathInfo {
    pub(super) namespace: String,
    pub(super) pred: &'static str,
    pub(super) corollary: String,
    pub(super) stmt: String,
    pub(super) bitems: Vec<BItem>,
    pub(super) renames: Vec<(String, String)>,
    pub(super) param_cell: Option<(i64, String)>,
}

pub(super) fn emit_transition_path(
    desc: &RefinementDescriptor,
    ctx: RefinementCtx<'_>,
    target: RefineTarget<'_>,
    m_bound: &str,
    cr: &str,
    rr: &str,
) -> Option<(String, TransitionPathInfo)> {
    emit_transition_path_impl(desc, ctx, target, m_bound, cr, rr)
}

pub(super) fn emit_transition_fault(
    desc: &RefinementDescriptor,
    ctx: RefinementCtx<'_>,
    target: RefineTarget<'_>,
    m_bound: &str,
    cr: &str,
    rr: &str,
    tail: FaultTail<'_>,
) -> Option<(String, TransitionPathInfo)> {
    emit_transition_fault_impl(desc, ctx, target, m_bound, cr, rr, tail)
}

pub(super) fn emit_transition_bundle(
    stem_pascal: &str,
    stem_snake: &str,
    path_modules: &[String],
    paths: &[TransitionPathInfo],
) -> Option<(String, String)> {
    emit_transition_bundle_impl(stem_pascal, stem_snake, path_modules, paths)
}
fn replace_ident(hay: &str, from: &str, to: &str) -> String {
    let ident = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
    let bytes = hay.as_bytes();
    let mut out = String::with_capacity(hay.len());
    let mut i = 0;
    while i < hay.len() {
        if hay[i..].starts_with(from) {
            let before_ok = i == 0 || !ident(bytes[i - 1]);
            let after = i + from.len();
            let after_ok = after >= bytes.len() || !ident(bytes[after]);
            if before_ok && after_ok {
                out.push_str(to);
                i = after;
                continue;
            }
        }
        // Advance one full UTF-8 char.
        let ch = hay[i..].chars().next().unwrap();
        out.push(ch);
        i += ch.len_utf8();
    }
    out
}

pub(super) fn emit_transition_bundle_impl(
    stem_pascal: &str,
    stem_snake: &str,
    path_modules: &[String],
    paths: &[TransitionPathInfo],
) -> Option<(String, String)> {
    // The param-cell naming discovered by the mutating path applies to all.
    let param_rename: Option<(String, String)> = paths.iter().find_map(|p| {
        p.param_cell
            .as_ref()
            .map(|(off, name)| (format!("m{}", off), name.clone()))
    });

    let rename_all = |p: &TransitionPathInfo, s: &str| -> String {
        let mut out = s.to_string();
        for (from, to) in &p.renames {
            out = replace_ident(&out, from, to);
        }
        if let Some((from, to)) = &param_rename {
            out = replace_ident(&out, from, to);
        }
        out
    };
    // A hyp name built from a var (`h<var>_lt`) follows its var's renaming.
    let rename_name = |p: &TransitionPathInfo, name: &str| -> String {
        let mut out = name.to_string();
        for (from, to) in &p.renames {
            out = out.replace(&format!("h{}_lt", from), &format!("h{}_lt", to));
        }
        if let Some((from, to)) = &param_rename {
            out = out.replace(&format!("h{}_lt", from), &format!("h{}_lt", to));
        }
        out
    };

    // ── Canonical binder union (order of first appearance) ──
    let mut vals: Vec<String> = Vec::new();
    let mut hyps: Vec<(String, String)> = Vec::new();
    for p in paths {
        for b in &p.bitems {
            match b {
                BItem::Val(v) => {
                    let cv = rename_all(p, v);
                    if !vals.contains(&cv) {
                        vals.push(cv);
                    }
                }
                BItem::Hyp { name, prop } => {
                    let cn = rename_name(p, name);
                    let cp = rename_all(p, prop);
                    if let Some((_, existing)) = hyps.iter().find(|(n2, _)| *n2 == cn) {
                        if *existing != cp {
                            eprintln!(
                                "transition bundle: hypothesis {:?} \
                                       conflicts across paths; skipping bundle",
                                cn
                            );
                            return None;
                        }
                    } else {
                        hyps.push((cn, cp));
                    }
                }
                BItem::Guard { .. } => {}
            }
        }
    }

    // ── Per-path conjuncts + proof terms ──
    let mut conjuncts: Vec<String> = Vec::new();
    let mut proofs: Vec<String> = Vec::new();
    for p in paths {
        let guards: Vec<String> = p
            .bitems
            .iter()
            .filter_map(|b| match b {
                BItem::Guard { prop } => Some(rename_all(p, prop)),
                _ => None,
            })
            .collect();
        let stmt = rename_all(p, &p.stmt);
        let obligation = format!("SVM.Solana.Abstract.{}\n{}", p.pred, stmt);
        let conjunct = if guards.is_empty() {
            obligation
        } else {
            format!("{} →\n      {}", guards.join(" →\n     "), obligation)
        };
        conjuncts.push(format!("({})", conjunct));

        // Application args in the corollary's signature order; guard binders
        // take the intro'd hypotheses hg0, hg1, ….
        let mut gi = 0usize;
        let args: Vec<String> = p
            .bitems
            .iter()
            .map(|b| match b {
                BItem::Val(v) => rename_all(p, v),
                BItem::Hyp { name, .. } => rename_name(p, name),
                BItem::Guard { .. } => {
                    let a = format!("hg{}", gi);
                    gi += 1;
                    a
                }
            })
            .collect();
        let lam = if gi == 0 {
            String::new()
        } else {
            format!(
                "fun {} =>\n      ",
                (0..gi)
                    .map(|i| format!("hg{}", i))
                    .collect::<Vec<_>>()
                    .join(" ")
            )
        };
        proofs.push(format!(
            "{}{}.{} {}",
            lam,
            p.namespace,
            p.corollary,
            args.join(" ")
        ));
    }

    let binders = {
        let mut s = format!("({} : Nat)", vals.join(" "));
        for (n2, p2) in &hyps {
            s.push_str(&format!("\n    ({} : {})", n2, p2));
        }
        s
    };
    let imports = path_modules
        .iter()
        .map(|m| format!("import Generated.{}Lifted", m))
        .collect::<Vec<_>>()
        .join("\n");

    let module = format!("{}Transition", stem_pascal);
    let lean = format!(
        "/-
  Whole-transition bundle for {stem_snake} (#40 gap 1). MECHANICALLY EMITTED
  by qedlift from the per-path trace-guided lifts (one discovered
  `{stem_snake}_<path>.pcs` trace per path) + the refinement descriptor. ONE
  statement covering every path: under each path's branch guards the program
  TERMINATES with that path's exit code (or FAULTS with its typed error) and
  the tracked account codec transitions accordingly (preservation and fault
  paths hold it fixed).
-/

{imports}

namespace Examples.{module}

open SVM SVM.SBPF SVM.SBPF.Memory SVM.Solana.Abstract

theorem {stem_snake}_transition
    {binders} :
    {conjuncts} :=
  ⟨{proofs}⟩

end Examples.{module}
",
        stem_snake = stem_snake,
        imports = imports,
        module = module,
        binders = binders,
        conjuncts = conjuncts.join(" ∧\n    "),
        proofs = proofs.join(",\n   ")
    );
    Some((module, lean))
}
// ════════════════════════════════════════════════════════════════
// Whole-transition codegen (#40 gap 1) — per-path `AsmRefinesTransitionPath`
// corollary (emitted inline in a trace-guided, descriptor-driven lift whose
// walk lands on the shared `.exit`) + the multi-path bundle theorem.
// ════════════════════════════════════════════════════════════════

/// Emit the per-path whole-transition corollary: the target running triple
/// (`*_balance_correct` when the mutated cell was overflow-cleaned, else
/// `*_lifted_spec`) composed with the shared `.exit` via
/// `cuTripleWithinMem_seq_exit`, stated as `AsmRefinesTransitionPath` over
/// the descriptor's account layout. On a path that does NOT perform the
/// descriptor's mutation, every tracked field is preserved: owned cells must
/// be unchanged, unowned cells are framed as field-named params — so
/// `preFields = postFields` is syntactic. Fail-closed (`None`) on anything
/// outside the wired shapes.
pub(super) fn emit_transition_path_impl(
    desc: &RefinementDescriptor,
    ctx: RefinementCtx<'_>,
    target: RefineTarget<'_>,
    m_bound: &str,
    cr: &str,
    rr: &str,
) -> Option<(String, TransitionPathInfo)> {
    let RefinementCtx {
        lift_module: module_name,
        pre,
        post: post_atoms,
        abs_subst,
        n_cu: n,
        start_pc,
        exit_pc,
        idl,
        sidecar_layouts,
        ..
    } = ctx;
    let RefineTarget {
        name: target_name,
        args: target_args,
        binders: target_binders,
        bitems: bitems_in,
    } = target;
    let fold = |e: &Expr| fold_abstractions(e.to_lean(), abs_subst);
    let layout = match desc.explicit_layout() {
        Some(l) => l,
        None => resolve_layout(sidecar_layouts, idl, &desc.account)?,
    };
    let mutated_off = layout
        .fields
        .iter()
        .find(|f| f.name == desc.mutated)?
        .offset as i64;

    // Exit code: the post's r0 value (the shared `.exit` returns it).
    let code = post_atoms.iter().find_map(|a| match a {
        Atom::Reg(0, v) => Some(fold(v)),
        _ => None,
    })?;

    // ── Mutation detection (mirrors `emit_descriptor_refinement`) ──
    let is_initmem = |e: &Expr| matches!(e, Expr::InitMem(_));
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
    // (base, cell off, pre value, post field value, param operand)
    let mut mutation: Option<(Expr, i64, String, String, Option<String>)> = None;
    for atom in post_atoms {
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
                match &desc.op {
                    DescriptorOp::AddConst { add_const } => {
                        if let (Expr::InitMem(_), Expr::Const(k)) = (a.as_ref(), b.as_ref()) {
                            if k == add_const {
                                mutation = Some((
                                    addr_base.clone(),
                                    *addr_off,
                                    fold(a),
                                    fold(value),
                                    None,
                                ));
                                break;
                            }
                        }
                    }
                    DescriptorOp::AddParam { .. } => {
                        if is_initmem(a) && is_initmem(b) {
                            let bl = addr_base.to_lean();
                            if let Some(pv) = pre_dword_val(&bl, *addr_off) {
                                let (al, blv) = (fold(a), fold(b));
                                let param = if al == pv {
                                    Some(blv.clone())
                                } else if blv == pv {
                                    Some(al.clone())
                                } else {
                                    None
                                };
                                if let Some(p) = param {
                                    mutation = Some((
                                        addr_base.clone(),
                                        *addr_off,
                                        pv,
                                        fold(value),
                                        Some(p),
                                    ));
                                    break;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    if let Some((_, off, _, _, _)) = &mutation {
        // The bytes must mutate the field the descriptor names (offset check
        // is against the account base derived from this very cell, so it is
        // the base-anchoring choice, not an independent fact — the real check
        // is that no OTHER tracked field changes, below).
        let _ = off;
    }

    // Account base: derived from the mutated cell when present; a
    // preservation path owns no mutated cell, so anchor at r1's entry value
    // (v1 convention — the loader input pointer).
    let (base_raw, base_expr, base_off) = match &mutation {
        Some((b, off, _, _, _)) => (b.to_lean(), fold(b), off - mutated_off),
        None => {
            let r1 = pre.iter().find_map(|a| match a {
                Atom::Reg(1, v) => Some(v.clone()),
                _ => None,
            })?;
            (r1.to_lean(), fold(&r1), 0)
        }
    };
    let base_arg = if base_off == 0 {
        base_expr.clone()
    } else {
        format!("({} + {})", base_expr, base_off)
    };

    // ── Walk the layout: owned scalars flow through; unowned are framed as
    //    field-named params; any off-op change to a tracked field fails. ──
    let mut bitems = bitems_in;
    let mut binders_extra = String::new();
    let mut pre_fields: Vec<String> = Vec::new();
    let mut post_fields: Vec<String> = Vec::new();
    let mut frame: Vec<String> = Vec::new();
    let mut owned: Vec<(String, i64, bool)> = Vec::new();
    let mut renames: Vec<(String, String)> = Vec::new();
    let taken = |name: &str, bitems: &[BItem]| {
        bitems.iter().any(|b| match b {
            BItem::Val(v) => v == name,
            BItem::Hyp { name: n2, .. } => n2 == name,
            BItem::Guard { .. } => false,
        })
    };
    let post_dword_val = |b: &str, off: i64| -> Option<String> {
        post_atoms.iter().find_map(|a| match a {
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
    for f in &layout.fields {
        let off = f.offset as i64;
        let abs = base_off + off;
        match &f.kind {
            FieldKind::U64 if off == mutated_off && mutation.is_some() => {
                let (_, _, pre_v, post_v, _) = mutation.as_ref().unwrap();
                pre_fields.push(format!("({}, .u64 {})", off, pre_v));
                post_fields.push(format!("({}, .u64 ({}))", off, post_v));
                owned.push((base_raw.clone(), abs, false));
                renames.push((pre_v.clone(), f.name.clone()));
            }
            FieldKind::U64 => {
                if let Some(v) = cell_val_dword(pre, &base_raw, abs) {
                    let pv = fold(v);
                    if let Some(pov) = post_dword_val(&base_raw, abs) {
                        if pov != pv {
                            eprintln!(
                                "transition: tracked field {:?} changes \
                                       outside the descriptor op; skipping path \
                                       corollary",
                                f.name
                            );
                            return None;
                        }
                    }
                    pre_fields.push(format!("({}, .u64 {})", off, pv));
                    post_fields.push(format!("({}, .u64 {})", off, pv));
                    owned.push((base_raw.clone(), abs, false));
                    renames.push((pv, f.name.clone()));
                } else {
                    if taken(&f.name, &bitems) {
                        eprintln!(
                            "transition: framed-field name {:?} collides \
                                   with a lift binder; skipping",
                            f.name
                        );
                        return None;
                    }
                    binders_extra.push_str(&format!("({} : Nat)\n    ", f.name));
                    bitems.push(BItem::Val(f.name.clone()));
                    pre_fields.push(format!("({}, .u64 {})", off, f.name));
                    post_fields.push(format!("({}, .u64 {})", off, f.name));
                    frame.push(format!(
                        "(effectiveAddr {} {} ↦U64 {})",
                        base_expr, abs, f.name
                    ));
                }
            }
            FieldKind::Byte => {
                if let Some(v) = cell_val(pre, &base_raw, abs, true) {
                    let pv = fold(v);
                    pre_fields.push(format!("({}, .byte {})", off, pv));
                    post_fields.push(format!("({}, .byte {})", off, pv));
                    owned.push((base_raw.clone(), abs, true));
                    renames.push((pv, f.name.clone()));
                } else {
                    if taken(&f.name, &bitems) {
                        return None;
                    }
                    binders_extra.push_str(&format!("({} : Nat)\n    ", f.name));
                    bitems.push(BItem::Val(f.name.clone()));
                    pre_fields.push(format!("({}, .byte {})", off, f.name));
                    post_fields.push(format!("({}, .byte {})", off, f.name));
                    frame.push(format!(
                        "(effectiveAddr {} {} ↦ₘ {})",
                        base_expr, abs, f.name
                    ));
                }
            }
            FieldKind::Pubkey => {
                // Framed only (v1): a lift-owned pubkey inside a transition
                // layout falls closed.
                if (0..4).any(|i| cell_val(pre, &base_raw, abs + 8 * i, false).is_some()) {
                    eprintln!(
                        "transition: owned pubkey field {:?} not wired; \
                               skipping path corollary",
                        f.name
                    );
                    return None;
                }
                let limbs: Vec<String> = (0..4).map(|i| format!("{}{}", f.name, i)).collect();
                for limb in &limbs {
                    if taken(limb, &bitems) {
                        return None;
                    }
                    binders_extra.push_str(&format!("({} : Nat)\n    ", limb));
                    bitems.push(BItem::Val(limb.clone()));
                }
                let rec = format!("⟨{}⟩", limbs.join(", "));
                pre_fields.push(format!("({}, .pubkey {})", off, rec));
                post_fields.push(format!("({}, .pubkey {})", off, rec));
                for (i, limb) in limbs.iter().enumerate() {
                    frame.push(format!(
                        "(effectiveAddr {} {} ↦U64 {})",
                        base_expr,
                        abs + 8 * i as i64,
                        limb
                    ));
                }
            }
            FieldKind::Bytes(_) => {
                eprintln!(
                    "transition: blob field {:?} not wired in the \
                           transition walker; skipping path corollary",
                    f.name
                );
                return None;
            }
        }
    }
    // Canonical names for untracked cells on the account base (`m<off>`), so
    // the bundle's binders line up across paths.
    for a in pre {
        if let Atom::Mem {
            addr_base,
            addr_off,
            ..
        } = a
        {
            if addr_base.to_lean() == base_raw
                && !owned
                    .iter()
                    .any(|(b, o, _)| b == addr_base.to_lean().as_str() && o == addr_off)
            {
                let v = match a {
                    Atom::Mem { value, .. } => fold(value),
                    _ => unreachable!(),
                };
                let rel = addr_off - base_off;
                if bitems.iter().any(|b| matches!(b, BItem::Val(x) if *x == v))
                    && !renames.iter().any(|(from, _)| *from == v)
                {
                    renames.push((v, format!("m{}", rel)));
                }
            }
        }
    }

    // ── Setup atoms: everything the codec does not own, minus r0 (it leads
    //    the transition post as the exit channel). ──
    let owned_set: std::collections::HashSet<(String, i64, bool)> = owned.iter().cloned().collect();
    let is_owned = |a: &Atom| match a {
        Atom::Mem {
            addr_base,
            addr_off,
            width,
            ..
        } => owned_set.contains(&(addr_base.to_lean(), *addr_off, matches!(width, Width::Byte))),
        _ => false,
    };
    let setup_pre: Vec<Atom> = pre.iter().filter(|a| !is_owned(a)).cloned().collect();
    let setup_post: Vec<Atom> = post_atoms
        .iter()
        .filter(|a| !is_owned(a) && !matches!(a, Atom::Reg(0, _)))
        .cloned()
        .collect();
    if setup_post.is_empty() {
        eprintln!("transition: empty setup post not wired; skipping path corollary");
        return None;
    }
    let setup_pre_s = atoms_to_lean(&setup_pre, abs_subst);
    let setup_post_s = atoms_to_lean(&setup_post, abs_subst);

    let frame_s = if frame.is_empty() {
        "callStackIs []".to_string()
    } else {
        format!("{} **\n      callStackIs []", frame.join(" **\n      "))
    };

    let handler = desc
        .handler
        .as_ref()
        .map(|h| format!(" (handler {})", h))
        .unwrap_or_default();
    let stmt = format!(
        "      (({cr}).union
        (CodeReq.singleton {exit_pc} .exit))
      ({n} + 1) ({m_bound}) {start_pc}
      (fun rt => {rr})
      ({code})
      [({base_arg},
        [{pre_list}],
        [{post_list}])]
      (({setup_pre}) **
       callStackIs [])
      ({setup_post})",
        cr = cr,
        exit_pc = exit_pc,
        n = n,
        m_bound = m_bound,
        start_pc = start_pc,
        rr = rr,
        code = code,
        base_arg = base_arg,
        pre_list = pre_fields.join(", "),
        post_list = post_fields.join(", "),
        setup_pre = setup_pre_s,
        setup_post = setup_post_s
    );

    let corollary = format!("{}_transition_path", module_name);
    let text = format!(
        "
/-! ## Whole-transition path corollary (#40)

One PATH of the account {account}{handler} transition: composed from the
running triple (`{target}`) and the shared `.exit` via
`cuTripleWithinMem_seq_exit` — the program TERMINATES with
`exitCode = some ({code})` and the tracked account codec goes
preFields → postFields (a preservation path has them equal, with cells
outside the path's footprint framed through the lift). -/

open Memory in
set_option maxHeartbeats 1600000 in
theorem {corollary}
    {binders}{binders_extra}: SVM.Solana.Abstract.AsmRefinesTransitionPath
{stmt} := by
  unfold SVM.Solana.Abstract.AsmRefinesTransitionPath
  simp only [SVM.Solana.Abstract.codecsPre, SVM.Solana.Abstract.codecsPost,
             codecCoarse, FieldVal.coarse, sepConj_emp_right_eq, Nat.add_zero]
  refine cuTripleWithinMem_seq_exit ?_ ?_
  · repeat' apply CodeReq.Disjoint_union_left
    all_goals exact CodeReq.singleton_disjoint_singleton _ _ (by decide)
  · have framed := cuTripleWithinMem_frame_right
      ( {frame} )
      (by sl_pcfree) ({target} {args})
    sl_exact framed
",
        account = desc.account,
        handler = handler,
        target = target_name,
        code = code,
        corollary = corollary,
        binders = target_binders,
        binders_extra = binders_extra,
        stmt = stmt,
        frame = frame_s,
        args = target_args
    );

    let param_cell = match (&desc.op, &mutation) {
        (DescriptorOp::AddParam { add_param }, Some((_, _, _, _, Some(p)))) => {
            // The param operand is a pre-read cell on the account base; find it.
            pre.iter().find_map(|a| match a {
                Atom::Mem {
                    addr_base,
                    addr_off,
                    width,
                    value,
                    ..
                } if matches!(width, Width::Dword)
                    && addr_base.to_lean() == base_raw
                    && fold(value) == *p =>
                {
                    Some((addr_off - base_off, add_param.clone()))
                }
                _ => None,
            })
        }
        _ => None,
    };

    Some((
        text,
        TransitionPathInfo {
            namespace: format!("Examples.Lifted.{}", module_name),
            pred: "AsmRefinesTransitionPath",
            corollary,
            stmt,
            bitems,
            renames,
            param_cell,
        },
    ))
}

/// Emit the per-path whole-transition FAULT corollary: the running prefix
/// (`*_balance_correct`/`*_lifted_spec`) composed with the terminal
/// abort/panic fault spec via `cuTripleWithinMem_seq_fault_pure`, stated as
/// `AsmRefinesTransitionFault` — typed fault channel, tracked account codecs
/// owned in the PRE (no post: a faulted instruction is rolled back
/// wholesale). Tracked cells outside the prefix footprint are framed as
/// field-named params. Fail-closed (`None`) outside the wired shapes.
pub(super) fn emit_transition_fault_impl(
    desc: &RefinementDescriptor,
    ctx: RefinementCtx<'_>,
    target: RefineTarget<'_>,
    m_bound: &str,
    cr: &str,
    rr: &str,
    tail: FaultTail<'_>,
) -> Option<(String, TransitionPathInfo)> {
    let RefinementCtx {
        lift_module: module_name,
        pre,
        post: post_atoms,
        abs_subst,
        n_cu: n,
        start_pc,
        exit_pc,
        idl,
        sidecar_layouts,
        ..
    } = ctx;
    let RefineTarget {
        name: target_name,
        args: target_args,
        binders: target_binders,
        bitems: bitems_in,
    } = target;
    let FaultTail {
        ctor: fault_ctor,
        spec: fault_spec,
        oob,
        target_post,
    } = tail;
    let fold = |e: &Expr| fold_abstractions(e.to_lean(), abs_subst);
    let layout = match desc.explicit_layout() {
        Some(l) => l,
        None => resolve_layout(sidecar_layouts, idl, &desc.account)?,
    };

    // A fault path owns no mutated cell: anchor the account at r1's entry
    // value (the same v1 convention as preservation exit paths).
    let r1 = pre.iter().find_map(|a| match a {
        Atom::Reg(1, v) => Some(v.clone()),
        _ => None,
    })?;
    let (base_raw, base_expr, base_off) = (r1.to_lean(), fold(&r1), 0i64);
    let base_arg = base_expr.clone();

    // ── Walk the layout PRE-only: owned scalars flow through, unowned are
    //    framed as field-named params. ──
    let mut bitems = bitems_in;
    let mut binders_extra = String::new();
    let mut pre_fields: Vec<String> = Vec::new();
    let mut frame: Vec<String> = Vec::new();
    let mut owned: Vec<(String, i64, bool)> = Vec::new();
    let mut renames: Vec<(String, String)> = Vec::new();
    let taken = |name: &str, bitems: &[BItem]| {
        bitems.iter().any(|b| match b {
            BItem::Val(v) => v == name,
            BItem::Hyp { name: n2, .. } => n2 == name,
            BItem::Guard { .. } => false,
        })
    };
    for f in &layout.fields {
        let off = f.offset as i64;
        let abs = base_off + off;
        match &f.kind {
            FieldKind::U64 => {
                if let Some(v) = cell_val_dword(pre, &base_raw, abs) {
                    let pv = fold(v);
                    pre_fields.push(format!("({}, .u64 {})", off, pv));
                    owned.push((base_raw.clone(), abs, false));
                    renames.push((pv, f.name.clone()));
                } else {
                    if taken(&f.name, &bitems) {
                        return None;
                    }
                    binders_extra.push_str(&format!("({} : Nat)\n    ", f.name));
                    bitems.push(BItem::Val(f.name.clone()));
                    pre_fields.push(format!("({}, .u64 {})", off, f.name));
                    frame.push(format!(
                        "(effectiveAddr {} {} ↦U64 {})",
                        base_expr, abs, f.name
                    ));
                }
            }
            FieldKind::Byte => {
                if let Some(v) = cell_val(pre, &base_raw, abs, true) {
                    let pv = fold(v);
                    pre_fields.push(format!("({}, .byte {})", off, pv));
                    owned.push((base_raw.clone(), abs, true));
                    renames.push((pv, f.name.clone()));
                } else {
                    if taken(&f.name, &bitems) {
                        return None;
                    }
                    binders_extra.push_str(&format!("({} : Nat)\n    ", f.name));
                    bitems.push(BItem::Val(f.name.clone()));
                    pre_fields.push(format!("({}, .byte {})", off, f.name));
                    frame.push(format!(
                        "(effectiveAddr {} {} ↦ₘ {})",
                        base_expr, abs, f.name
                    ));
                }
            }
            FieldKind::Pubkey => {
                if (0..4).any(|i| cell_val(pre, &base_raw, abs + 8 * i, false).is_some()) {
                    eprintln!(
                        "transition: owned pubkey field {:?} not wired; \
                               skipping fault-path corollary",
                        f.name
                    );
                    return None;
                }
                let limbs: Vec<String> = (0..4).map(|i| format!("{}{}", f.name, i)).collect();
                for limb in &limbs {
                    if taken(limb, &bitems) {
                        return None;
                    }
                    binders_extra.push_str(&format!("({} : Nat)\n    ", limb));
                    bitems.push(BItem::Val(limb.clone()));
                }
                let rec = format!("⟨{}⟩", limbs.join(", "));
                pre_fields.push(format!("({}, .pubkey {})", off, rec));
                for (i, limb) in limbs.iter().enumerate() {
                    frame.push(format!(
                        "(effectiveAddr {} {} ↦U64 {})",
                        base_expr,
                        abs + 8 * i as i64,
                        limb
                    ));
                }
            }
            FieldKind::Bytes(_) => {
                eprintln!(
                    "transition: blob field {:?} not wired in the \
                           transition walker; skipping fault-path corollary",
                    f.name
                );
                return None;
            }
        }
    }
    // Canonical names for untracked cells on the account base.
    for a in pre {
        if let Atom::Mem {
            addr_base,
            addr_off,
            value,
            ..
        } = a
        {
            if addr_base.to_lean() == base_raw
                && !owned
                    .iter()
                    .any(|(b, o, _)| *b == addr_base.to_lean() && o == addr_off)
            {
                let v = fold(value);
                let rel = addr_off - base_off;
                if bitems.iter().any(|b| matches!(b, BItem::Val(x) if *x == v))
                    && !renames.iter().any(|(from, _)| *from == v)
                {
                    renames.push((v, format!("m{}", rel)));
                }
            }
        }
    }
    // nCu binders for the fault terminal (mirrors the fault-correct corollary).
    bitems.push(BItem::Val("nCuAbort".to_string()));
    bitems.push(BItem::Hyp {
        name: "hCuAbort".to_string(),
        prop: format!(
            "∀ s : State,\n        (step (.call {}) s).cuConsumed ≤ s.cuConsumed + nCuAbort",
            fault_ctor
        ),
    });

    // OOB tail: the region register's post value (the fault condition's
    // address) and the post remainder framed into the tail spec's pre.
    let fold2 = |e: &Expr| fold_abstractions(e.to_lean(), abs_subst);
    let oob_parts: Option<(String, String, &'static str, i64)> = match oob {
        None => None,
        Some((reg, size, writable)) => {
            let r1v = post_atoms.iter().find_map(|a| match a {
                Atom::Reg(r, v) if *r == reg => Some(fold2(v)),
                _ => None,
            })?;
            let rest: Vec<Atom> = post_atoms
                .iter()
                .filter(|a| !matches!(a, Atom::Reg(r, _) if *r == reg))
                .cloned()
                .collect();
            let rest_s = atoms_to_lean(&rest, abs_subst);
            let pred: &'static str = if writable {
                "containsWritable"
            } else {
                "containsRange"
            };
            Some((r1v, rest_s, pred, size))
        }
    };

    let owned_set: std::collections::HashSet<(String, i64, bool)> = owned.iter().cloned().collect();
    let is_owned = |a: &Atom| match a {
        Atom::Mem {
            addr_base,
            addr_off,
            width,
            ..
        } => owned_set.contains(&(addr_base.to_lean(), *addr_off, matches!(width, Width::Byte))),
        _ => false,
    };
    let setup_pre: Vec<Atom> = pre.iter().filter(|a| !is_owned(a)).cloned().collect();
    let setup_pre_s = atoms_to_lean(&setup_pre, abs_subst);

    // Prefix post = the target triple's post, frame_right-extended by the
    // framed tracked cells; the terminal fault spec is P-parametric, so it is
    // applied at exactly that assertion.
    let (frame_s, prefix_post, prefix_have) = if frame.is_empty() {
        (
            String::new(),
            format!("({})", target_post),
            format!("have framed := {} {}", target_name, target_args),
        )
    } else {
        let fr = frame.join(" **\n      ");
        (fr.clone(),
         format!("(({}) **\n       ({}))", target_post, fr),
         format!("have framed := cuTripleWithinMem_frame_right\n      ( {} )\n      (by sl_pcfree) ({} {})",
            fr, target_name, target_args))
    };
    let _ = frame_s;

    let handler = desc
        .handler
        .as_ref()
        .map(|h| format!(" (handler {})", h))
        .unwrap_or_default();
    // Combined rr for an OOB tail: prefix requirement ∧ the region condition.
    let (vm_error, rr_full) = match &oob_parts {
        None => (".abort", format!("fun rt => {}", rr)),
        Some((r1v, _, pred, size)) => (
            ".accessViolation",
            format!(
                "fun rt => ({}) ∧ rt.{} ({}) {} = false",
                rr, pred, r1v, size
            ),
        ),
    };
    let stmt = format!(
        "      (({cr}).union
        (CodeReq.singleton {exit_pc} (.call {ctor})))
      ({n} + 1) ({m_bound} + nCuAbort) {start_pc}
      ({rr_full})
      ({vm_error})
      [({base_arg},
        [{pre_list}],
        [{pre_list}])]
      ({setup_pre})",
        cr = cr,
        exit_pc = exit_pc,
        ctor = fault_ctor,
        n = n,
        m_bound = m_bound,
        start_pc = start_pc,
        rr_full = rr_full,
        vm_error = vm_error,
        base_arg = base_arg,
        pre_list = pre_fields.join(", "),
        setup_pre = setup_pre_s
    );

    let corollary = format!("{}_transition_fault", module_name);
    // Tail composition: unconditional abort/panic = `seq_fault_pure` with the
    // P-parametric spec applied at the prefix post; OOB = the Mem-Mem
    // `seq_fault` with the single-register spec frame_right-extended to the
    // post remainder (+ framed tracked cells), prefix reshaped to lead with
    // the region register.
    let (tail_refine, h1_post) = match &oob_parts {
        None => (format!(
            "refine cuTripleWithinMem_seq_fault_pure ?_ ?_\n    ({spec} {prefix_post} {pc} nCuAbort hCuAbort)",
            spec = fault_spec, prefix_post = prefix_post, pc = exit_pc), None),
        Some((r1v, rest_s, _, _)) => {
            let rest_full = if frame.is_empty() { format!("({})", rest_s) }
                else { format!("(({}) **\n       ({}))", rest_s, frame.join(" **\n      ")) };
            (format!(
                "refine cuTripleWithinMem_seq_fault ?_ ?_\n    (cuTripleFaultsWithinMem_frame_right\n      {rest}\n      (by repeat' apply pcFree_sepConj\n          all_goals first\n            | exact pcFree_regIs _ _\n            | exact pcFree_memU64Is _ _\n            | exact pcFree_memU32Is _ _\n            | exact pcFree_memU16Is _ _\n            | exact pcFree_memByteIs _ _\n            | exact pcFree_memBytes32Is _ _\n            | exact pcFree_memBytesIs _ _)\n      ({spec} ({r1v}) {pc} nCuAbort hCuAbort))",
                rest = rest_full, spec = fault_spec, r1v = r1v, pc = exit_pc),
             Some(rest_full.clone()))
        }
    };
    let _ = h1_post;
    let text = format!(
        "
/-! ## Whole-transition FAULT-path corollary (#40)

One fault PATH of the account {account}{handler} transition: the running
prefix (`{target}`) composed with the terminal `{ctor}` fault — the program
FAULTS with the typed `{vm_error}` (`exitCode = some toSentinel ∧ vmError =
some {vm_error}`), the tracked account codec owned in the pre (no post: a
faulted instruction is rolled back wholesale; tracked cells outside the
prefix footprint are framed through it). -/

open Memory in
set_option maxHeartbeats 1600000 in
theorem {corollary}
    {binders}{binders_extra}(nCuAbort : Nat)
    (hCuAbort : ∀ s : State,
        (step (.call {ctor}) s).cuConsumed ≤ s.cuConsumed + nCuAbort)
    : SVM.Solana.Abstract.AsmRefinesTransitionFault
{stmt} := by
  unfold SVM.Solana.Abstract.AsmRefinesTransitionFault
  simp only [SVM.Solana.Abstract.codecsPre,
             codecCoarse, FieldVal.coarse, sepConj_emp_right_eq, Nat.add_zero]
  {tail_refine}
  · repeat' apply CodeReq.Disjoint_union_left
    all_goals exact CodeReq.singleton_disjoint_singleton _ _ (by decide)
  · {prefix_have}
    sl_exact framed
",
        account = desc.account,
        handler = handler,
        target = target_name,
        ctor = fault_ctor,
        corollary = corollary,
        binders = target_binders,
        binders_extra = binders_extra,
        stmt = stmt,
        vm_error = vm_error,
        tail_refine = tail_refine,
        prefix_have = prefix_have
    );

    Some((
        text,
        TransitionPathInfo {
            namespace: format!("Examples.Lifted.{}", module_name),
            pred: "AsmRefinesTransitionFault",
            corollary,
            stmt,
            bitems,
            renames,
            param_cell: None,
        },
    ))
}
