use super::core::{
    canon_root_expr, eval_expr, lean_off, reg_initial_name, reg_lit, solve_expr, Atom, BytesVal,
    Expr, Width,
};
use super::state::SymState;

/// Concatenate atoms into a Lean `**`-separated SL expression (`emp` for empty list).
/// `subst` replaces rendered address-base expressions with their abstracted parameter name.
pub(super) fn atoms_to_lean(
    atoms: &[Atom],
    subst: &std::collections::BTreeMap<String, String>,
) -> String {
    if atoms.is_empty() { return "emp".to_string(); }
    let parts: Vec<String> = atoms.iter().map(|a| atom_to_lean_with_subst(a, subst)).collect();
    parts.join(" **\n      ")
}

/// Fold abstraction RHSes to parameter names inside a rendered string, including sub-expressions
/// (longest-first so parents fold before sub-terms). Mirrors `sl_rw_abs` so goal and chain atoms match.
pub(super) fn fold_abstractions(
    s: String,
    subst: &std::collections::BTreeMap<String, String>,
) -> String {
    let mut out = s;
    let mut keys: Vec<&String> = subst.keys().collect();
    keys.sort_by_key(|k| std::cmp::Reverse(k.len()));
    for k in keys {
        if let Some(p) = subst.get(k) {
            out = replace_token(&out, k, p);
        }
    }
    out
}

/// Word-boundary-aware replace: substitutes `needle` only where surrounding bytes aren't
/// alphanumeric/underscore — without this, `toU64 3` would corrupt `toU64 32` into `addr02`.
pub(super) fn replace_token(haystack: &str, needle: &str, repl: &str) -> String {
    if needle.is_empty() { return haystack.to_string(); }
    let is_word = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
    let hb = haystack.as_bytes();
    let nb = needle.as_bytes();
    let mut out = String::with_capacity(haystack.len());
    let mut i = 0usize;
    while i < hb.len() {
        if hb[i..].starts_with(nb) {
            let before_ok = i == 0 || !is_word(hb[i - 1]);
            let after = i + nb.len();
            let after_ok = after >= hb.len() || !is_word(hb[after]);
            if before_ok && after_ok {
                out.push_str(repl);
                i = after;
                continue;
            }
        }
        // Advance one UTF-8 char (handles the `↦`/`%`/`<<<` etc.).
        let ch = haystack[i..].chars().next().unwrap();
        out.push(ch);
        i += ch.len_utf8();
    }
    out
}

fn atom_to_lean_with_subst(
    atom: &Atom,
    subst: &std::collections::BTreeMap<String, String>,
) -> String {
    // Fold whole OR sub-expression abstractions to param names, matching the sl_rw_abs-rewritten goal.
    let sub = |e: &Expr| -> String {
        fold_abstractions(e.to_lean(), subst)
    };
    match atom {
        Atom::Reg(r, v) => {
            format!("(.{} ↦ᵣ {})", reg_lit(*r), sub(v))
        }
        Atom::Mem { addr_base, addr_off, width, value, delta } => {
            let rendered = addr_base.to_lean();
            let addr_str = subst.get(&rendered)
                .map(|p| p.clone())
                .unwrap_or_else(|| addr_base.atom_lean());
            if *delta != 0 {
                // Hot byte cell: `effectiveAddr base off + delta ↦ₘ v` — plain Nat add, the form `ldxdw_bytes_spec` uses.
                return format!(
                    "(effectiveAddr {} {} + {} {} {})",
                    addr_str,
                    if *addr_off < 0 { format!("({})", addr_off) } else { format!("{}", addr_off) },
                    delta, width.lean_arrow(), sub(value),
                );
            }
            format!(
                "(effectiveAddr {} {} {} {})",
                addr_str, lean_off(*addr_off), width.lean_arrow(), sub(value),
            )
        }
        Atom::Bytes { addr, value } => {
            // `memBytesIs` uses a bare Nat address (no effectiveAddr). Use `fold_abstractions` not
            // `subst.get` — the blob address may contain sub-expressions like `wrapAdd baseAddr 8`
            // that `subst.get` (whole-key lookup) misses; `fold_abstractions` matches inner `addrK`.
            format!("({} ↦Bytes {})", sub(addr), value.to_lean())
        }
        Atom::Bytes32 { addr, name } => {
            format!("({} ↦Bytes32 {})", sub(addr), name)
        }
        Atom::ReturnData { value } => {
            // Global returnData buffer — no address, no subst.
            format!("(↦ReturnData {})", value.to_lean())
        }
    }
}

/// Parse a recorded blob size to a concrete `u64` for the satisfiability witness.
/// Accepts a bare decimal (`"16"`) or a `toU64`-wrapped literal (`"(toU64 16)"`),
/// which a constant-count blob renders via `atom_lean()`. `toU64 n = n` for any
/// `n < 2^64`, so unwrapping is sound; a genuinely symbolic size returns `None`
/// (fail closed — no witness, so vacuity still can't ship).
fn const_blob_size(s: &str) -> Option<u64> {
    let t = s.trim();
    if let Ok(n) = t.parse::<u64>() {
        return Some(n);
    }
    let inner = t.strip_prefix('(')?.strip_suffix(')')?.trim();
    let after = inner.strip_prefix("toU64")?.trim();
    // Plain `toU64 N`.
    if let Ok(n) = after.parse::<u64>() {
        return Some(n);
    }
    // `toU64 N % 2 ^ (8 * 8)` — a dword store-immediate (`ST_DW_IMM`) render;
    // `% 2^64` is a no-op for the in-range immediate, so the size is N.
    after.strip_suffix("% 2 ^ (8 * 8)")?.trim().parse::<u64>().ok()
}

/// Build the H8 satisfiability-witness: a concrete variable assignment proving the precondition
/// is satisfiable, kernel-checked by `native_decide`. One guard pins each `addrK` literal to its
/// `h_addrK` equation; the `∃ s, pre s` example uses `SatWitness.sat_witness` with reflected
/// atoms tied to the real pre by defeq. An unsatisfiable pre fails here (fail closed) or fails
/// `lake build` — vacuity is structurally unshippable. Scope: heap/footprint overlap; value-level
/// `h_branch*` path hypotheses are outside the overlap-vacuity class. Address strategy: each
/// canonical root gets a far-apart 0x10000000-spaced base (0x400000000+); remaining vars = 0.
pub(super) fn build_sat_witness(
    pre: &[Atom],
    state: &SymState,
    abstractions: &[(String, String, String)],
    abs_subst: &std::collections::BTreeMap<String, String>,
    folded_rhs: &[String],
    vars: &[String],
) -> Result<String, String> {
    use std::collections::BTreeMap;

    // Abstraction param → the pre-atom addr_base whose rendering it captured.
    let mut param_expr: BTreeMap<String, Expr> = BTreeMap::new();
    for atom in pre {
        if let Atom::Mem { addr_base, .. } = atom {
            if let Some(p) = abs_subst.get(&addr_base.to_lean()) {
                param_expr.entry(p.clone()).or_insert_with(|| addr_base.clone());
            }
        }
    }

    let mut env: BTreeMap<String, u64> = BTreeMap::new();
    let mut next_base: u64 = 0x4_0000_0000;
    let mut alloc_base = || { let t = next_base; next_base += 0x1000_0000; t };

    let addr_exprs: Vec<&Expr> = pre.iter().filter_map(|a| match a {
        Atom::Mem { addr_base, .. } => Some(addr_base),
        Atom::Bytes { addr, .. } => Some(addr),
        Atom::Bytes32 { addr, .. } => Some(addr),
        Atom::Reg(..) => None,
        Atom::ReturnData { .. } => None,
    }).collect();

    // Pass 1: variable roots get bases directly.
    for e in &addr_exprs {
        if let (Some(Expr::InitReg(n)), _) | (Some(Expr::InitMem(n)), _) =
            canon_root_expr(e, 0)
        {
            if !env.contains_key(n) {
                let b = alloc_base();
                env.insert(n.clone(), b);
            }
        }
    }
    // Pass 2: opaque (derived) roots, steered via their free variable (atom order = creation order).
    let mut solved_roots: std::collections::BTreeSet<String> = Default::default();
    for e in &addr_exprs {
        if let (Some(root), _) = canon_root_expr(e, 0) {
            if matches!(root, Expr::InitReg(_) | Expr::InitMem(_)) { continue; }
            let key = root.to_lean();
            if !solved_roots.insert(key.clone()) { continue; }
            // A CLOSED root (no free variables — e.g. a constant rodata
            // table address built through `|||`/`arsh` chains, carried as
            // `Expr::RawConst`) needs no steering: its value is forced and
            // the witness evaluation below uses it directly.
            if eval_expr(root, &env).is_some() {
                continue;
            }
            let target = alloc_base();
            if !solve_expr(root, target, &mut env) {
                return Err(format!(
                    "cannot steer derived address root `{}` to a witness \
                     base (unsupported expression shape)", key));
            }
        }
    }
    // Pass 3: every remaining theorem variable is 0.
    for v in vars {
        env.entry(v.clone()).or_insert(0);
    }

    let mut param_vals: BTreeMap<String, u64> = BTreeMap::new();
    for (param, _, _) in abstractions {
        let e = param_expr.get(param).ok_or_else(|| format!(
            "no defining expression recorded for abstraction `{}`", param))?;
        let v = eval_expr(e, &env).ok_or_else(|| format!(
            "cannot evaluate abstraction `{}` under the witness assignment", param))?;
        param_vals.insert(param.clone(), v);
    }

    // `effectiveAddr base off (+ delta)` over u64/i64, mirroring
    // `Int.toNat (base + off)` (clamp at 0, no 2^64 wrap).
    let eff = |base: u64, off: i64, delta: i64| -> u64 {
        let a = (base as i128) + (off as i128);
        let a = if a < 0 { 0 } else { a as u128 };
        (a + delta as u128) as u64
    };

    struct Foot { mem: Option<(u64, u64)>, reg: Option<u8>, cs: bool, desc: String }
    let mut sat_atoms: Vec<String> = Vec::new();
    let mut feet: Vec<Foot> = Vec::new();
    let mut blob_subst: Vec<(String, String)> = Vec::new();
    for atom in pre {
        match atom {
            Atom::Reg(r, v) => {
                let vv = eval_expr(v, &env).ok_or_else(|| format!(
                    "cannot evaluate register r{} initial value", r))?;
                sat_atoms.push(format!(".reg .{} {}", reg_lit(*r), vv));
                feet.push(Foot { mem: None, reg: Some(*r), cs: false,
                                 desc: format!("r{}", r) });
            }
            Atom::Mem { addr_base, addr_off, width, value, delta } => {
                let base = eval_expr(addr_base, &env).ok_or_else(|| format!(
                    "cannot evaluate address base `{}`", addr_base.to_lean()))?;
                let a = eff(base, *addr_off, *delta);
                let vv = eval_expr(value, &env).ok_or_else(|| format!(
                    "cannot evaluate cell value `{}`", value.to_lean()))?;
                let (ctor, sz) = match width {
                    Width::Byte => (".byte", 1u64),
                    Width::Halfword => (".u16", 2),
                    Width::Word => (".u32", 4),
                    Width::Dword => (".u64", 8),
                };
                sat_atoms.push(format!("{} {} {}", ctor, a, vv));
                feet.push(Foot { mem: Some((a, sz)), reg: None, cs: false,
                                 desc: format!("{} cell at {}", ctor, a) });
            }
            Atom::Bytes { addr, value } => {
                let a = eval_expr(addr, &env).ok_or_else(|| format!(
                    "cannot evaluate blob address `{}`", addr.to_lean()))?;
                let name = match value {
                    BytesVal::Sym(n) => n,
                    BytesVal::Replicate { .. } => return Err(
                        "unexpected Replicate blob in a precondition".into()),
                };
                let size_s = state.memset_blobs.iter()
                    .find(|(n, _)| n == name).map(|(_, s)| s.clone())
                    .ok_or_else(|| format!("no size recorded for blob `{}`", name))?;
                let sz: u64 = const_blob_size(&size_s).ok_or_else(|| format!(
                    "blob `{}` has a non-constant size `{}`", name, size_s))?;
                let repl = format!("(replicateByte 0 {})", sz);
                sat_atoms.push(format!(".bytes {} {}", a, repl));
                blob_subst.push((name.clone(), repl));
                feet.push(Foot { mem: Some((a, sz)), reg: None, cs: false,
                                 desc: format!("blob `{}` at {}", name, a) });
            }
            Atom::Bytes32 { addr, name } => {
                let a = eval_expr(addr, &env).ok_or_else(|| format!(
                    "cannot evaluate Bytes32 address `{}`", addr.to_lean()))?;
                // A fresh symbolic 32-byte blob (e.g. sha256's old output) is
                // grounded to a concrete witness + substituted; a named constant
                // (a sysvar id) is used verbatim.
                if state.bytearray_vars.iter().any(|v| v == name) {
                    let repl = "(replicateByte 0 32)".to_string();
                    sat_atoms.push(format!(".bytes32 {} {}", a, repl));
                    blob_subst.push((name.clone(), repl));
                } else {
                    sat_atoms.push(format!(".bytes32 {} {}", a, name));
                }
                feet.push(Foot { mem: Some((a, 32)), reg: None, cs: false,
                                 desc: format!("`{}` at {}", name, a) });
            }
            Atom::ReturnData { value } => {
                // Old returnData is arbitrary (no size hyp): witness it as the
                // empty buffer and substitute the symbolic name accordingly so
                // `interp` stays defeq to the rendered pre. Owns no mem/reg.
                let name = match value {
                    BytesVal::Sym(n) => n,
                    BytesVal::Replicate { .. } => return Err(
                        "unexpected Replicate blob in a returnData precondition".into()),
                };
                sat_atoms.push(".retData ByteArray.empty".to_string());
                blob_subst.push((name.clone(), "ByteArray.empty".to_string()));
                feet.push(Foot { mem: None, reg: None, cs: false,
                                 desc: format!("returnData `{}`", name) });
            }
        }
    }
    if state.saw_call {
        sat_atoms.push(".callStack []".to_string());
        feet.push(Foot { mem: None, reg: None, cs: true,
                         desc: "callStack".to_string() });
    }

    // Rust-side pairwise disjointness (mirrored kernel-side by `satCheck`). Overlap = H8 vacuity; fail.
    for i in 0..feet.len() {
        for j in (i + 1)..feet.len() {
            let (x, y) = (&feet[i], &feet[j]);
            let mem_clash = match (x.mem, y.mem) {
                (Some((s1, n1)), Some((s2, n2))) =>
                    n1 > 0 && n2 > 0 && s1 + n1 > s2 && s2 + n2 > s1,
                _ => false,
            };
            let reg_clash = matches!((x.reg, y.reg), (Some(a), Some(b)) if a == b);
            if mem_clash || reg_clash || (x.cs && y.cs) {
                return Err(format!(
                    "precondition atoms overlap under the witness assignment \
                     ({} vs {}) — the theorem would be vacuous",
                    x.desc, y.desc));
            }
        }
    }

    let mut tokens: Vec<(String, String)> = Vec::new();
    for v in vars {
        tokens.push((v.clone(), env.get(v).copied().unwrap_or(0).to_string()));
    }
    for (p, val) in &param_vals {
        tokens.push((p.clone(), val.to_string()));
    }
    for (n, repl) in &blob_subst {
        tokens.push((n.clone(), repl.clone()));
    }
    let subst = |s: &str| -> String {
        let mut out = s.to_string();
        for (k, v) in &tokens {
            out = replace_token(&out, k, v);
        }
        out
    };

    let mut w = String::new();
    w.push_str(
        "/-! ## Satisfiability witness (soundness-audit H8)\n\n\
         The triple's precondition is SATISFIABLE at the concrete\n\
         assignment below — an overlapping (vacuous) sepConj would fail\n\
         `native_decide` here, so vacuity cannot ship. The guards pin\n\
         each `addrK` literal to its `h_addrK` defining equation at the\n\
         assignment; the witness goal is the theorem's precondition with\n\
         the variables instantiated, so the reflected `SatWitness` atoms\n\
         are tied to the real pre by the elaborator's defeq check.\n\
         Value-level path hypotheses (`h_branch*`) are not certified\n\
         consistent — they are outside the overlap-vacuity class this\n\
         guards against. -/\n\n");
    for (i, (param, _, _)) in abstractions.iter().enumerate() {
        w.push_str(&format!(
            "example : {} = {} := by native_decide\n",
            param_vals[param], subst(&folded_rhs[i])));
    }
    if !abstractions.is_empty() { w.push('\n'); }
    let cs = if state.saw_call { " ** callStackIs []" } else { "" };
    // `have` before `exact`: with an expected `∃ s, interp [..] s` type the unifier postpones
    // list metavariables and gets stuck; `have` elaborates the list closed, then `exact` unifies.
    w.push_str(&format!(
        "open Memory in\nexample : ∃ s,\n    ({}{}) s := by\n  \
         have w := SatWitness.sat_witness\n    [{}]\n    (by native_decide)\n  \
         exact w\n\n",
        subst(&atoms_to_lean(pre, abs_subst)), cs,
        sat_atoms.join(",\n     "),
    ));
    Ok(w)
}

/// The BPF program heap: `[MM_HEAP_START, MM_HEAP_START + 0x8000)`.
const HEAP_START_I: i64 = 0x300000000;
const HEAP_END_I:   i64 = 0x300000000 + 0x8000;

/// If `addr_base` is an `lddw`-loaded constant in `[MM_HEAP_START, MM_HEAP_END)`, return its
/// absolute address — used to fold heap cells into `heapBumpPtr`/`heapBlockU64` predicates.
pub(super) fn heap_cell_addr(addr_base: &Expr, off: i64) -> Option<i64> {
    let k = match addr_base {
        Expr::Const(k) => *k,
        Expr::ToU64(inner) => match inner.as_ref() {
            Expr::Const(k) => *k,
            _ => return None,
        },
        _ => return None,
    };
    let abs = k.checked_add(off)?;
    if (HEAP_START_I..HEAP_END_I).contains(&abs) { Some(abs) } else { None }
}

/// Render an atom for the heap corollary: the `u64` cell at `MM_HEAP_START` -> `heapBumpPtr v`;
/// any other heap cell -> `heapBlockU64 addr v`; everything else renders normally.
fn atom_to_lean_heap(
    atom: &Atom,
    subst: &std::collections::BTreeMap<String, String>,
) -> String {
    if let Atom::Mem { addr_base, addr_off, width, value, .. } = atom {
        if matches!(width, Width::Dword) {
            if let Some(abs) = heap_cell_addr(addr_base, *addr_off) {
                let v = fold_abstractions(value.to_lean(), subst);
                return if abs == HEAP_START_I {
                    format!("(heapBumpPtr ({}))", v)
                } else {
                    format!("(heapBlockU64 ({}) ({}))", addr_base.atom_lean(), v)
                };
            }
        }
    }
    atom_to_lean_with_subst(atom, subst)
}

pub(super) fn atoms_to_lean_heap(
    atoms: &[Atom],
    subst: &std::collections::BTreeMap<String, String>,
) -> String {
    atoms.iter()
        .map(|a| atom_to_lean_heap(a, subst))
        .collect::<Vec<_>>()
        .join(" **\n      ")
}

pub(super) fn post_atoms(initial_pre: &[Atom], state: &SymState) -> Vec<Atom> {
    let mut out = Vec::with_capacity(initial_pre.len());
    for atom in initial_pre {
        match atom {
            Atom::Reg(r, _) => {
                let v = state.regs.get(r).cloned()
                    .unwrap_or_else(|| Expr::InitReg(reg_initial_name(*r)));
                out.push(Atom::Reg(*r, v));
            }
            Atom::Mem { addr_base, addr_off, width, delta, .. } => {
                let key = (addr_base.to_lean(), *addr_off, *delta, *width as u8);
                let v = state.mem.iter()
                    .find(|c| c.key() == key)
                    .map(|c| c.value.clone())
                    .unwrap_or_else(|| Expr::InitMem("?".to_string()));
                out.push(Atom::Mem {
                    addr_base: addr_base.clone(),
                    addr_off:  *addr_off,
                    width:     *width,
                    value:     v,
                    delta:     *delta,
                });
            }
            Atom::Bytes { addr, value } => {
                // Look up post blob contents by rendered address (set by memory syscall emitters).
                let post_val = state.byte_blob_post.get(&addr.to_lean())
                    .cloned()
                    .unwrap_or_else(|| value.clone());
                out.push(Atom::Bytes { addr: addr.clone(), value: post_val });
            }
            Atom::Bytes32 { addr, name } => {
                // Default read-only (sysvar id) — unchanged. A digest-writing
                // syscall (sol_sha256) flips the post via `bytes32_post`.
                let post_name = state.bytes32_post.get(&addr.to_lean())
                    .cloned()
                    .unwrap_or_else(|| name.clone());
                out.push(Atom::Bytes32 { addr: addr.clone(), name: post_name });
            }
            Atom::ReturnData { value } => {
                // returnData flips to the syscall-set value (`returndata_post`).
                let post_val = state.returndata_post.clone()
                    .unwrap_or_else(|| value.clone());
                out.push(Atom::ReturnData { value: post_val });
            }
        }
    }
    out
}

/// Build the `rr` clause: `rt.containsRange`/`containsWritable` per walk-order atom.
pub(super) fn region_req(
    _pre: &[Atom],
    state: &SymState,
    subst: &std::collections::BTreeMap<String, String>,
) -> String {
    let mut clauses = Vec::new();
    // Per-clause group id: a fresh group at every index NOT in `rr_continuations`
    // (default = one clause per group = the flat left-fold). A multi-clause
    // syscall rr stays grouped so the goal matches `sl_block_iter`'s
    // per-instruction (`cuTripleWithinMem_seq`) composition.
    let mut group_ids: Vec<usize> = Vec::with_capacity(state.rr_walk.len());
    let mut gid = 0usize;
    for i in 0..state.rr_walk.len() {
        if i != 0 && !state.rr_continuations.contains(&i) {
            gid += 1;
        }
        group_ids.push(gid);
    }
    // Walk-order: load -> containsRange, store -> containsWritable; left-fold order matches slBlockIter.
    for (addr_base, addr_off, width, writable, raw) in &state.rr_walk {
        // H6 variable-length: `contains{Writable,Range} addr count` with raw (subst-folded, no
        // `effectiveAddr`) address — matches the rr from `call_sol_{memset,log}_*_spec` after sl_rw_abs.
        if let Some((addr, count)) = raw {
            let addr_str = fold_abstractions(addr.to_lean(), subst);
            let kind = if *writable { "containsWritable" } else { "containsRange" };
            clauses.push(format!(
                "rt.{} ({}) ({}) = true", kind, addr_str, count.to_lean()));
            continue;
        }
        let width_bytes = match width {
            Width::Byte => 1, Width::Halfword => 2, Width::Word => 4, Width::Dword => 8,
        };
        let addr_str = subst.get(&addr_base.to_lean())
            .map(|p| p.clone())
            .unwrap_or_else(|| addr_base.atom_lean());
        let addr = format!("effectiveAddr {} {}", addr_str, lean_off(*addr_off));
        let kind = if *writable { "containsWritable" } else { "containsRange" };
        clauses.push(format!("rt.{} ({}) {} = true", kind, addr, width_bytes));
    }
    if clauses.is_empty() {
        "True".to_string()
    } else {
        // Fold within each group left-assoc, then left-fold the groups — matches
        // sl_block_iter's per-instruction composition (`(prior) ∧ (syscall_rr)`),
        // which is isDefEq to the goal without extra rewrites. With no
        // continuations every clause is its own group = the flat left-fold.
        let mut groups: Vec<String> = Vec::new();
        let mut cur = clauses[0].clone();
        for i in 1..clauses.len() {
            if group_ids[i] == group_ids[i - 1] {
                cur = format!("({}) ∧\n                  {}", cur, clauses[i]);
            } else {
                groups.push(cur);
                cur = clauses[i].clone();
            }
        }
        groups.push(cur);
        let mut out = groups[0].clone();
        for g in groups.iter().skip(1) {
            out = format!("({}) ∧\n                  {}", out, g);
        }
        out
    }
}
