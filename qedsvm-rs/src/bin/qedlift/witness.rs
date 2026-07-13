use super::branch::{BranchHyp, BranchKind};
use super::core::{eval_expr, solve_expr, Expr};
use super::emit::replace_token;
use super::state::SymState;

/// Evaluate a branch hypothesis under a concrete assignment, mirroring EXACTLY `BranchHyp::lean_hyp`
/// semantics so `Some(true)` guarantees `native_decide` accepts the substituted hypothesis.
/// `None` = unmodeled kind (signed compares) — those lifts are skipped, never failed.
fn eval_branch(bh: &BranchHyp, env: &std::collections::BTreeMap<String, u64>) -> Option<bool> {
    use BranchKind::*;
    let dv = eval_expr(&bh.dst_value, env)?;
    let immu = bh.imm as u64;
    let sv = match &bh.src_value {
        Some(s) => Some(eval_expr(s, env)?),
        None => None,
    };
    let r = match (&bh.kind, bh.taken) {
        (JeqImm, true) | (JneImm, false) => dv == immu,
        (JeqImm, false) | (JneImm, true) => dv != immu,
        (JgtImm, true) => dv > immu,
        (JgtImm, false) => dv <= immu,
        (JltImm, true) => dv < immu,
        (JltImm, false) => dv >= immu,
        (JleImm, true) => dv <= immu,
        (JleImm, false) => dv > immu,
        (JgeImm, true) => dv >= immu,
        (JgeImm, false) => dv < immu,
        (JsetImm, true) => (dv & immu) != 0,
        (JsetImm, false) => (dv & immu) == 0,
        (JeqReg, true) | (JneReg, false) => dv == sv?,
        (JeqReg, false) | (JneReg, true) => dv != sv?,
        (JltReg, true) => dv < sv?,
        (JltReg, false) => dv >= sv?,
        (JgtReg, true) => dv > sv?,
        (JgtReg, false) => dv <= sv?,
        (JleReg, true) => dv <= sv?,
        (JleReg, false) => dv > sv?,
        (JgeReg, true) => dv >= sv?,
        (JgeReg, false) => dv < sv?,
        (JsetReg, true) => (dv & sv?) != 0,
        (JsetReg, false) => (dv & sv?) == 0,
        // Signed compares: `toSigned64 v` is two's-complement reinterpretation
        // = `v as i64`, so each Lean `toSigned64 a (op) toSigned64 b` matches
        // the Rust `(a as i64) (op) (b as i64)`.
        (JsgtImm, true) => (dv as i64) > (immu as i64),
        (JsgtImm, false) => (dv as i64) <= (immu as i64),
        (JsltImm, true) => (dv as i64) < (immu as i64),
        (JsltImm, false) => (dv as i64) >= (immu as i64),
        (JsleImm, true) => (dv as i64) <= (immu as i64),
        (JsleImm, false) => (dv as i64) > (immu as i64),
        (JsgeImm, true) => (dv as i64) >= (immu as i64),
        (JsgeImm, false) => (dv as i64) < (immu as i64),
        (JsgtReg, true) => (dv as i64) > (sv? as i64),
        (JsgtReg, false) => (dv as i64) <= (sv? as i64),
        (JsltReg, true) => (dv as i64) < (sv? as i64),
        (JsltReg, false) => (dv as i64) >= (sv? as i64),
        (JsleReg, true) => (dv as i64) <= (sv? as i64),
        (JsleReg, false) => (dv as i64) > (sv? as i64),
        (JsgeReg, true) => (dv as i64) >= (sv? as i64),
        (JsgeReg, false) => (dv as i64) < (sv? as i64),
    };
    Some(r)
}

/// Candidate `(dst_target, src_target?)` pairs that would satisfy the branch under the current
/// partial assignment. Driver tries in order, `solve_expr`-ing free variables, keeps first that
/// `eval_branch`-verifies. Empty = unmodeled kind (signed) => lift is skipped.
fn branch_candidates(
    bh: &BranchHyp,
    env: &std::collections::BTreeMap<String, u64>,
) -> Vec<(u64, Option<u64>)> {
    use BranchKind::*;
    let immu = bh.imm as u64;
    let sv = bh.src_value.as_ref().and_then(|s| eval_expr(s, env));
    let dv = eval_expr(&bh.dst_value, env);
    let ne_imm: Vec<(u64, Option<u64>)> = [immu.wrapping_add(1), immu.wrapping_sub(1), 0, 1, 2, 3]
        .into_iter()
        .filter(|t| *t != immu)
        .map(|t| (t, None))
        .collect();
    match (&bh.kind, bh.taken) {
        (JeqImm, true) | (JneImm, false) => vec![(immu, None)],
        (JeqImm, false) | (JneImm, true) => ne_imm,
        (JgtImm, true) => vec![(immu.wrapping_add(1), None)],
        (JgtImm, false) => vec![(0, None), (immu, None)],
        (JltImm, true) => {
            if immu > 0 {
                vec![(0, None), (immu - 1, None)]
            } else {
                vec![]
            }
        }
        (JltImm, false) => vec![(immu, None), (immu.wrapping_add(1), None)],
        (JleImm, true) => vec![(0, None), (immu, None)],
        (JleImm, false) => vec![(immu.wrapping_add(1), None)],
        (JgeImm, true) => vec![(immu, None), (immu.wrapping_add(1), None)],
        (JgeImm, false) => {
            if immu > 0 {
                vec![(0, None), (immu - 1, None)]
            } else {
                vec![]
            }
        }
        (JsetImm, true) => {
            if immu != 0 {
                vec![(immu, None)]
            } else {
                vec![]
            }
        }
        (JsetImm, false) => vec![(0, None)],
        // reg-form: couple the two sides.
        (JeqReg, true) | (JneReg, false) => match sv {
            Some(v) => vec![(v, None)],
            None => match dv {
                Some(v) => vec![(v, Some(v))],
                None => vec![(0, Some(0))],
            },
        },
        (JeqReg, false) | (JneReg, true) => match sv {
            Some(v) => vec![(v.wrapping_add(1), None), (v.wrapping_sub(1), None)],
            None => vec![(1, Some(0)), (0, Some(1))],
        },
        (JltReg, true) => match sv {
            Some(v) if v > 0 => vec![(v - 1, None), (0, None)],
            _ => vec![(0, Some(1))],
        },
        (JltReg, false) => match sv {
            // dst ≥ src
            Some(v) => vec![(v, None), (v.wrapping_add(1), None)],
            None => vec![(1, Some(0)), (0, Some(0))],
        },
        (JgtReg, true) => match sv {
            Some(v) => vec![(v.wrapping_add(1), None)],
            None => vec![(1, Some(0))],
        },
        (JgtReg, false) => match sv {
            // dst ≤ src
            Some(v) => vec![(v, None), (0, None)],
            None => vec![(0, Some(1)), (0, Some(0))],
        },
        (JleReg, true) => match sv {
            Some(v) => vec![(v, None), (0, None)],
            None => vec![(0, Some(0)), (0, Some(1))],
        },
        (JleReg, false) => match sv {
            // dst > src
            Some(v) => vec![(v.wrapping_add(1), None)],
            None => vec![(1, Some(0))],
        },
        (JgeReg, true) => match sv {
            Some(v) => vec![(v, None), (v.wrapping_add(1), None)],
            None => vec![(0, Some(0)), (1, Some(0))],
        },
        (JgeReg, false) => match sv {
            // dst < src
            Some(v) if v > 0 => vec![(v - 1, None), (0, None)],
            _ => vec![(0, Some(1))],
        },
        (JsetReg, true) => match sv {
            Some(v) if v != 0 => vec![(v, None)],
            _ => vec![(1, Some(1))],
        },
        (JsetReg, false) => vec![(0, None)],
        // Signed compares. For the small non-negative immediates these lifts
        // use (2/6/11/17), the witness values stay in the positive i64 range
        // where signed = unsigned, so the candidate VALUES match the unsigned
        // counterpart; the `256`/`65536` magnitudes let a byte-combo dst be
        // steered into a higher byte when its low byte is already pinned.
        (JsgtImm, true) => vec![(immu.wrapping_add(1), None), (256, None), (65536, None)],
        (JsgtImm, false) => vec![(0, None), (immu, None)],
        (JsleImm, true) => vec![(0, None), (immu, None)],
        (JsleImm, false) => vec![(immu.wrapping_add(1), None), (256, None), (65536, None)],
        (JsltImm, true) => {
            if immu > 0 {
                vec![(0, None), (immu - 1, None)]
            } else {
                vec![]
            }
        }
        (JsltImm, false) => vec![(immu, None), (immu.wrapping_add(1), None)],
        (JsgeImm, true) => vec![(immu, None), (immu.wrapping_add(1), None), (256, None)],
        (JsgeImm, false) => {
            if immu > 0 {
                vec![(0, None), (immu - 1, None)]
            } else {
                vec![]
            }
        }
        (JsgtReg, true) => match sv {
            Some(v) => vec![(v.wrapping_add(1), None)],
            None => vec![(1, Some(0))],
        },
        (JsgtReg, false) => match sv {
            Some(v) => vec![(v, None), (0, None)],
            None => vec![(0, Some(1)), (0, Some(0))],
        },
        (JsltReg, true) => match sv {
            Some(v) if v > 0 => vec![(v - 1, None), (0, None)],
            _ => vec![(0, Some(1))],
        },
        (JsltReg, false) => match sv {
            Some(v) => vec![(v, None), (v.wrapping_add(1), None)],
            None => vec![(1, Some(0)), (0, Some(0))],
        },
        (JsleReg, true) => match sv {
            Some(v) => vec![(v, None), (0, None)],
            None => vec![(0, Some(0)), (0, Some(1))],
        },
        (JsleReg, false) => match sv {
            Some(v) => vec![(v.wrapping_add(1), None)],
            None => vec![(1, Some(0))],
        },
        (JsgeReg, true) => match sv {
            Some(v) => vec![(v, None), (v.wrapping_add(1), None)],
            None => vec![(0, Some(0)), (1, Some(0))],
        },
        (JsgeReg, false) => match sv {
            Some(v) if v > 0 => vec![(v - 1, None), (0, None)],
            _ => vec![(0, Some(1))],
        },
    }
}

fn uf_find(parent: &mut std::collections::BTreeMap<String, String>, x: &str) -> String {
    let mut root = x.to_string();
    while let Some(p) = parent.get(&root) {
        if *p == root {
            break;
        }
        root = p.clone();
    }
    let mut cur = x.to_string();
    while cur != root {
        let next = parent.get(&cur).cloned().unwrap_or_else(|| root.clone());
        parent.insert(cur, root.clone());
        cur = next;
    }
    root
}

fn expr_vars(e: &Expr, out: &mut Vec<String>) {
    match e {
        Expr::InitReg(n) | Expr::InitMem(n) => out.push(n.clone()),
        Expr::ToU64(a)
        | Expr::Mod(a, _)
        | Expr::AndU64Imm(a, _)
        | Expr::LshU64Imm(a, _)
        | Expr::RshU64Imm(a, _) => expr_vars(a, out),
        Expr::WrapAdd(a, b)
        | Expr::WrapSub(a, b)
        | Expr::WrapMul(a, b)
        | Expr::NatAdd(a, b)
        | Expr::CleanSub(a, b) => {
            expr_vars(a, out);
            expr_vars(b, out);
        }
        Expr::ByteCombo(bs) => {
            for b in bs {
                expr_vars(b, out);
            }
        }
        Expr::Const(_)
        | Expr::StHalfImm(_)
        | Expr::StWordImm(_)
        | Expr::StDwordImm(_)
        | Expr::Raw(_)
        | Expr::RawConst(..) => {}
    }
}

/// Steerer priority (0 = most constraining): 0=byte-combo-eq (pins several cells), 1=scalar-eq,
/// 2=inequality (commits a value in range before a disequality can block it), 3=disequality.
fn branch_priority(bh: &BranchHyp) -> u8 {
    use BranchKind::*;
    let combo = matches!(&bh.dst_value, Expr::ByteCombo(_));
    match (&bh.kind, bh.taken) {
        (JeqImm, true) | (JneImm, false) | (JeqReg, true) | (JneReg, false) => {
            if combo {
                0
            } else {
                1
            }
        }
        (JeqImm, false) | (JneImm, true) | (JeqReg, false) | (JneReg, true) => 3,
        _ => 2,
    }
}

/// Phase 7 sub-item 1: branch-satisfiability witness (complements the H8 footprint witness).
/// `h_branch*` and `h*_lt` are uncertified parameters — an unsatisfiable conjunction makes the
/// triple vacuously true. Emits a concrete assignment satisfying every modeled hypothesis
/// simultaneously, kernel-checked by `native_decide`. Conservative: returns `None` (non-breaking)
/// when the steerer cannot satisfy every branch — never emits an unverified witness.
pub(super) fn build_branch_witness(state: &SymState, vars: &[String]) -> Option<String> {
    use std::collections::BTreeMap;
    if state.branch_hyps.is_empty() {
        return None;
    }

    let mut env: BTreeMap<String, u64> = BTreeMap::new();
    let mut order: Vec<usize> = (0..state.branch_hyps.len()).collect();
    order.sort_by_key(|&i| branch_priority(&state.branch_hyps[i]));

    for &i in &order {
        let bh = &state.branch_hyps[i];
        // Already satisfied by the partial assignment (e.g. pinned by an earlier branch).
        if eval_branch(bh, &env) == Some(true) {
            continue;
        }
        // Non-committing zero-fill probe (disequalities only): if the `≠` holds with free cells=0,
        // leave them free — committing 0 here would block a later `bN ≠ 0` on the same cell.
        // Inequalities are NOT probed: they define a range and must commit a value in range.
        if branch_priority(bh) == 3 {
            let mut bvars = Vec::new();
            expr_vars(&bh.dst_value, &mut bvars);
            if let Some(s) = &bh.src_value {
                expr_vars(s, &mut bvars);
            }
            let mut probe = env.clone();
            for v in &bvars {
                probe.entry(v.clone()).or_insert(0);
            }
            if eval_branch(bh, &probe) == Some(true) {
                continue;
            }
        }
        // Try both solve orders: src-first unlocks compound dst whose free sub-cell = src.
        let cands = branch_candidates(bh, &env);
        'cand: for (dt, st) in cands {
            for src_first in [false, true] {
                let mut trial = env.clone();
                let solve_src =
                    |tr: &mut std::collections::BTreeMap<String, u64>| match (&bh.src_value, st) {
                        (Some(s), Some(t)) => solve_expr(s, t, tr),
                        _ => true,
                    };
                let ok = if src_first {
                    solve_src(&mut trial) && solve_expr(&bh.dst_value, dt, &mut trial)
                } else {
                    solve_expr(&bh.dst_value, dt, &mut trial) && solve_src(&mut trial)
                };
                if ok && eval_branch(bh, &trial) == Some(true) {
                    env = trial;
                    break 'cand;
                }
            }
        }
        // If not steered (pinned by an earlier shared constraint), the repair pass handles it.
    }

    for v in vars {
        env.entry(v.clone()).or_insert(0);
    }

    // Repair pass: the greedy pass mis-handles multi-constraint cells (e.g. `≤2 ∧ ≠2 ∧ ≠0` => must be 1)
    // and reg-equality classes. Union equalities into UF classes, brute-force one shared value per class.
    {
        use std::collections::{BTreeMap, BTreeSet};
        let mut allvars: Vec<String> = Vec::new();
        for bh in &state.branch_hyps {
            expr_vars(&bh.dst_value, &mut allvars);
            if let Some(s) = &bh.src_value {
                expr_vars(s, &mut allvars);
            }
        }
        allvars.sort();
        allvars.dedup();
        let mut parent: BTreeMap<String, String> = BTreeMap::new();
        for v in &allvars {
            parent.insert(v.clone(), v.clone());
        }
        for bh in &state.branch_hyps {
            let is_eq = matches!(
                (&bh.kind, bh.taken),
                (BranchKind::JeqReg, true) | (BranchKind::JneReg, false)
            );
            if !is_eq {
                continue;
            }
            let mut dv = Vec::new();
            expr_vars(&bh.dst_value, &mut dv);
            let mut sv = Vec::new();
            if let Some(s) = &bh.src_value {
                expr_vars(s, &mut sv);
            }
            if dv.len() == 1 && sv.len() == 1 {
                let ra = uf_find(&mut parent, &dv[0]);
                let rb = uf_find(&mut parent, &sv[0]);
                if ra != rb {
                    parent.insert(ra, rb);
                }
            }
        }
        let mut classes: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for v in &allvars {
            let r = uf_find(&mut parent, v);
            classes.entry(r).or_default().push(v.clone());
        }
        let mut pool: Vec<u64> = (0u64..=256).collect();
        for bh in &state.branch_hyps {
            let im = bh.imm as u64;
            pool.push(im);
            pool.push(im.wrapping_add(1));
            pool.push(im.wrapping_sub(1));
        }
        for members in classes.values() {
            let mset: BTreeSet<&String> = members.iter().collect();
            let internal: Vec<usize> = state
                .branch_hyps
                .iter()
                .enumerate()
                .filter_map(|(i, bh)| {
                    let mut vs = Vec::new();
                    expr_vars(&bh.dst_value, &mut vs);
                    if let Some(s) = &bh.src_value {
                        expr_vars(s, &mut vs);
                    }
                    if !vs.is_empty() && vs.iter().all(|v| mset.contains(v)) {
                        Some(i)
                    } else {
                        None
                    }
                })
                .collect();
            if internal.is_empty() {
                continue;
            }
            let holds = |e: &BTreeMap<String, u64>| {
                internal
                    .iter()
                    .all(|&i| eval_branch(&state.branch_hyps[i], e) == Some(true))
            };
            if holds(&env) {
                continue;
            }
            for &cand in &pool {
                let mut trial = env.clone();
                for m in members {
                    trial.insert(m.clone(), cand);
                }
                if holds(&trial) {
                    env = trial;
                    break;
                }
            }
        }
    }

    for (i, bh) in state.branch_hyps.iter().enumerate() {
        if eval_branch(bh, &env) != Some(true) {
            if std::env::var("QEDLIFT_DEBUG_BRANCH").is_ok() {
                eprintln!(
                    "BRANCH-WITNESS skip: final verify failed h_branch{} : {}",
                    i,
                    bh.lean_hyp()
                );
            }
            return None;
        }
    }

    let sub = |s: &str| -> String {
        let mut out = s.to_string();
        for (k, val) in &env {
            out = replace_token(&out, k, &val.to_string());
        }
        out
    };
    let mut conjuncts: Vec<String> = Vec::new();
    for bh in &state.branch_hyps {
        conjuncts.push(format!("({})", sub(&bh.lean_hyp())));
    }
    for (v, k) in &state.u64_load_vars {
        let lit = env.get(v).copied().unwrap_or(0);
        conjuncts.push(format!("({} < 2 ^ {})", lit, k));
    }
    let mut w = String::new();
    w.push_str(
        "/-! ## Branch-satisfiability witness (Phase 7 sub-item 1)\n\n\
         The triple's value-level path hypotheses (`h_branch*`) and load\n\
         bounds (`h*_lt`) are uncertified parameters — an UNSATISFIABLE\n\
         conjunction of them would make the triple vacuously true. The\n\
         assignment below satisfies every (modeled) path hypothesis\n\
         SIMULTANEOUSLY; `native_decide` machine-checks it, so a\n\
         contradictory path-constraint set cannot ship silently. This\n\
         complements the H8 footprint witness above (disjoint variable\n\
         sets: address roots vs. discriminant/flag cells). -/\n\n",
    );
    // Split via `refine ⟨?_,…⟩` so each conjunct is decided individually —
    // a single `native_decide` over deeply-nested `And` fails Decidable-synth past ~60 conjuncts.
    let body = conjuncts.join(" ∧\n      ");
    if conjuncts.len() == 1 {
        w.push_str(&format!(
            "example :\n      {} := by native_decide\n\n",
            body
        ));
    } else {
        let holes = vec!["?_"; conjuncts.len()].join(", ");
        w.push_str(&format!(
            "example :\n      {} := by\n  refine ⟨{}⟩ <;> native_decide\n\n",
            body, holes
        ));
    }
    Some(w)
}

#[cfg(test)]
mod tests {
    use super::super::branch::{BranchHyp, BranchKind};
    use super::super::core::Expr;
    use super::super::state::SymState;
    use super::build_branch_witness;

    /// Phase 7 sub-item 1 negative test: a CONTRADICTORY branch-hypothesis set
    /// (`v = 1 ∧ v = 2` on the same cell) must yield NO witness — the steerer
    /// verifies the final assignment against every hypothesis and returns
    /// `None` rather than emitting an unverified (or vacuous) certificate.
    #[test]
    fn contradictory_branch_hyps_yield_no_witness() {
        let mut state = SymState::default();
        let v = Expr::InitReg("vR1Old".to_string());
        state.branch_hyps.push(BranchHyp {
            kind: BranchKind::JeqImm,
            dst_value: v.clone(),
            src_value: None,
            imm: 1,
            taken: true,
        });
        state.branch_hyps.push(BranchHyp {
            kind: BranchKind::JeqImm,
            dst_value: v,
            src_value: None,
            imm: 2,
            taken: true,
        });
        assert!(
            build_branch_witness(&state, &["vR1Old".to_string()]).is_none(),
            "an unsatisfiable branch-hypothesis conjunction must not produce a witness"
        );
    }

    /// The satisfiable sibling: the same shape with consistent targets DOES
    /// produce a witness (guards the negative test against a steerer that
    /// trivially returns `None`).
    #[test]
    fn consistent_branch_hyps_yield_a_witness() {
        let mut state = SymState::default();
        let v = Expr::InitReg("vR1Old".to_string());
        state.branch_hyps.push(BranchHyp {
            kind: BranchKind::JeqImm,
            dst_value: v,
            src_value: None,
            imm: 1,
            taken: true,
        });
        assert!(
            build_branch_witness(&state, &["vR1Old".to_string()]).is_some(),
            "a satisfiable branch-hypothesis set must produce a witness"
        );
    }
}
