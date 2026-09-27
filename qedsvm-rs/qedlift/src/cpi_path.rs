//! CPI path composition: stitch a suffix lifted from `invokePc + 1` onto a
//! prefix that ends at a CPI invoke, and emit one caller-path theorem across
//! the CPI (`Cpi.cpiPathWithinMem`, proved by `Cpi.cpi_path_compose`).
//!
//! The suffix is lifted as an ordinary `arm_entry` path with fresh binders.
//! Stitching instantiates those binders from the prefix post: registers match
//! by number, memory cells by rendered address and width, and the suffix's
//! r0 becomes the callee's result code `r.code`. Suffix resources the prefix
//! never touched become extra framed atoms of the composed precondition.
//!
//! The callee contract is explicit ([`CpiCalleeContract`]): either memory
//! preservation (`Cpi.cpiTriple_of_mem_preserving`, zero-account or read-only
//! CPIs) or a byte footprint in the caller's input region the callee may write
//! (`Cpi.cpiTriple_of_writes`, account data write-back). Footprint bytes after
//! the CPI are `Cpi.committedByte r a old`: the callee's byte on success, the
//! caller's own on rollback; a suffix that reads them stitches to that value.

use std::collections::BTreeMap;

use crate::core::{Atom, BytesVal, Expr, Width};
use crate::diagnostic::{DiagnosticKind, LiftError};
use crate::emit::{atoms_to_lean, build_sat_witness};
use crate::lift::PathSummary;
use crate::state::SymState;

/// What the composed theorem assumes about the callee.
#[derive(Clone, Debug)]
pub enum CpiCalleeContract {
    /// The callee never changes caller memory (`hMem`).
    MemoryPreserving,
    /// The callee may write only these bytes, as offsets from the caller's
    /// input base (`r1` at entry, `baseAddr`), e.g. an account's data (`hW`).
    WritesInputBytes(Vec<i64>),
}

/// Replace every whole identifier token of `s` that `stitch` maps, in one
/// pass. Simultaneous: a replacement is never rewritten again, so suffix and
/// prefix binders that share a name (e.g. both call r1 `baseAddr`) cannot
/// chain into each other.
fn substitute(s: &str, stitch: &[(String, String)]) -> String {
    let map: BTreeMap<&str, &str> = stitch
        .iter()
        .map(|(k, v)| (k.as_str(), v.as_str()))
        .collect();
    let is_ident = |c: char| c.is_alphanumeric() || c == '_' || c == '\'';
    let mut out = String::with_capacity(s.len());
    let mut token = String::new();
    let mut prev_dot = false;
    let flush = |token: &mut String, out: &mut String, prev_dot: bool| {
        // A token after `.` is a field or namespace component, never a binder.
        match map.get(token.as_str()) {
            Some(repl) if !prev_dot => out.push_str(repl),
            _ => out.push_str(token),
        }
        token.clear();
    };
    for c in s.chars() {
        if is_ident(c) {
            token.push(c);
        } else {
            if !token.is_empty() {
                flush(&mut token, &mut out, prev_dot);
            }
            prev_dot = c == '.';
            out.push(c);
        }
    }
    if !token.is_empty() {
        flush(&mut token, &mut out, prev_dot);
    }
    out
}

/// Parenthesize a stitched value unless it is a single token.
fn wrap(v: &str) -> String {
    if v.contains(' ') {
        format!("({v})")
    } else {
        v.to_string()
    }
}

/// One rendered SL atom split into its resource key and its value.
struct RenderedAtom {
    /// Resource plus points-to token, e.g. `(.r7 ↦ᵣ` or
    /// `(effectiveAddr (toU64 12884901984) 0 ↦U64`.
    key: String,
    value: String,
}

impl RenderedAtom {
    fn parse(rendered: &str) -> Option<Self> {
        let arrow = rendered.find(" ↦")?;
        let key_end = rendered[arrow + 1..].find(' ')? + arrow + 1;
        let value = rendered[key_end + 1..].strip_suffix(')')?;
        Some(Self {
            key: rendered[..key_end].to_string(),
            value: value.to_string(),
        })
    }

    fn render(&self) -> String {
        format!("{} {})", self.key, self.value)
    }
}

fn unsupported(msg: impl Into<String>) -> LiftError {
    LiftError::new(DiagnosticKind::UnsupportedConstruct, msg.into())
}

fn render_atoms(
    atoms: &[Atom],
    subst: &BTreeMap<String, String>,
) -> Result<Vec<RenderedAtom>, LiftError> {
    atoms
        .iter()
        .map(|atom| {
            if !matches!(atom, Atom::Reg(..) | Atom::Mem { delta: 0, .. }) {
                return Err(unsupported(
                    "qedlift: CPI path composition supports register and aligned memory atoms only",
                ));
            }
            let rendered = atoms_to_lean(std::slice::from_ref(atom), subst);
            RenderedAtom::parse(&rendered)
                .ok_or_else(|| unsupported(format!("qedlift: cannot split atom {rendered}")))
        })
        .collect()
}

fn sep(atoms: &[String]) -> String {
    if atoms.is_empty() {
        "emp".to_string()
    } else {
        atoms.join(" **\n      ")
    }
}

/// `hG` projection for the `i`th of `n` right-nested conjuncts.
fn guard_projection(i: usize, n: usize) -> String {
    let mut out = "hG".to_string();
    for _ in 0..i {
        out.push_str(".2");
    }
    if i + 1 < n {
        out.push_str(".1");
    }
    out
}

/// Insert the composed CPI path theorem into the suffix module `suffix_lean`.
pub(crate) fn compose(
    prefix: &PathSummary,
    prefix_import: &str,
    suffix: &PathSummary,
    suffix_lean: &str,
    path_name: &str,
    contract: &CpiCalleeContract,
) -> Result<String, LiftError> {
    let kind = prefix.invoke_terminal.ok_or_else(|| {
        unsupported("qedlift: CPI path prefix must end at a sol_invoke_signed terminal")
    })?;
    let invoke_pc = prefix.exit_pc;
    if suffix.start_pc != invoke_pc + 1 {
        return Err(LiftError::new(
            DiagnosticKind::TraceInput,
            format!(
                "qedlift: CPI suffix starts at pc {}, expected {}",
                suffix.start_pc,
                invoke_pc + 1
            ),
        ));
    }
    if prefix.has_complex_binders || suffix.has_complex_binders {
        return Err(unsupported(
            "qedlift: CPI path composition supports plain variables, branch hypotheses \
             and load bounds (no abstractions, blobs, syscalls or call stack)",
        ));
    }

    render_atoms(&prefix.pre, &prefix.abs_subst)?; // validates atom kinds
    let prefix_post = render_atoms(&prefix.post, &prefix.abs_subst)?;
    let suffix_pre = render_atoms(&suffix.pre, &suffix.abs_subst)?;
    let suffix_post = render_atoms(&suffix.post, &suffix.abs_subst)?;

    let r0_key = "(.r0 ↦ᵣ";
    let prefix_r0 = prefix_post
        .iter()
        .find(|a| a.key == r0_key)
        .map(|a| a.value.clone());
    let r0_value = prefix_r0.clone().unwrap_or_else(|| "cpiR0Old".to_string());

    // Footprint cells: (address, key, old value, fresh old binder?, read by suffix?).
    struct FpCell {
        off: i64,
        addr: String,
        key: String,
        old: String,
        fresh: bool,
        read: bool,
    }
    let mut fp_consumed = vec![false; prefix_post.len()];
    let mut fp: Vec<FpCell> = Vec::new();
    if let CpiCalleeContract::WritesInputBytes(offs) = contract {
        if !prefix.vars.iter().any(|v| v == "baseAddr") {
            return Err(unsupported(
                "qedlift: an input-byte CPI footprint needs the prefix to read r1 (baseAddr)",
            ));
        }
        for (i, off) in offs.iter().enumerate() {
            let addr = if *off < 0 {
                format!("effectiveAddr baseAddr ({off})")
            } else {
                format!("effectiveAddr baseAddr {off}")
            };
            let key = format!("({addr} ↦ₘ");
            if fp.iter().any(|c| c.key == key) {
                return Err(unsupported(format!(
                    "qedlift: duplicate CPI footprint byte {off}"
                )));
            }
            let owned = prefix_post.iter().position(|p| p.key == key);
            let old = match owned {
                Some(j) => {
                    fp_consumed[j] = true;
                    prefix_post[j].value.clone()
                }
                None => format!("cpiFpOld{i}"),
            };
            fp.push(FpCell {
                off: *off,
                addr,
                key,
                old,
                fresh: owned.is_none(),
                read: false,
            });
        }
    }

    // Stitch suffix binders. Registers first: memory keys mention them.
    let mut stitch: Vec<(String, String)> = Vec::new();
    let apply = |s: &str, stitch: &[(String, String)]| -> String { substitute(s, stitch) };
    let mut stitch_expr: BTreeMap<String, Expr> = BTreeMap::new();
    let mut consumed = vec![false; prefix_post.len()];
    let mut suffix_reads_r0 = false;
    let mut extra_atoms: Vec<Atom> = Vec::new();
    let mut extra_vars: Vec<String> = Vec::new();
    let mut ordered: Vec<usize> = (0..suffix_pre.len())
        .filter(|&i| suffix_pre[i].key.starts_with("(.r"))
        .collect();
    ordered.extend((0..suffix_pre.len()).filter(|&i| !suffix_pre[i].key.starts_with("(.r")));
    for idx in ordered {
        let atom = &suffix_pre[idx];
        let var = atom.value.clone();
        if !suffix.vars.contains(&var) {
            return Err(unsupported(format!(
                "qedlift: CPI suffix precondition value {var} is not a variable"
            )));
        }
        if atom.key == r0_key {
            suffix_reads_r0 = true;
            stitch_expr.insert(var.clone(), Expr::Raw("r.code".to_string()));
            stitch.push((var, "r.code".to_string()));
            continue;
        }
        let key = apply(&atom.key, &stitch);
        if let Some(cell) = fp.iter_mut().find(|c| c.key == key) {
            cell.read = true;
            let committed = format!("(Cpi.committedByte r ({}) {})", cell.addr, wrap(&cell.old));
            stitch_expr.insert(var.clone(), Expr::Raw(committed.clone()));
            stitch.push((var, committed));
            continue;
        }
        if atom.key.contains("↦ₘ")
            && fp
                .iter()
                .any(|c| c.key.split(" ↦").next() == key.split(" ↦").next())
        {
            return Err(unsupported(
                "qedlift: CPI suffix reads a footprint byte at another width",
            ));
        }
        match prefix_post
            .iter()
            .enumerate()
            .position(|(j, p)| p.key == key && p.key != r0_key && !fp_consumed[j])
        {
            Some(i) => {
                consumed[i] = true;
                let value = match &prefix.post[i] {
                    Atom::Reg(_, v) | Atom::Mem { value: v, .. } => v.clone(),
                    _ => unreachable!("render_atoms admits registers and memory only"),
                };
                stitch_expr.insert(var.clone(), value);
                stitch.push((var, wrap(&prefix_post[i].value)));
            }
            None => {
                let fresh = format!("cpi_{var}");
                let extra_atom = match &suffix.pre[idx] {
                    Atom::Reg(r, _) => Atom::Reg(*r, Expr::InitReg(fresh.clone())),
                    Atom::Mem {
                        addr_base,
                        addr_off,
                        width,
                        delta,
                        ..
                    } => Atom::Mem {
                        addr_base: addr_base.substitute(&stitch_expr),
                        addr_off: *addr_off,
                        width: *width,
                        value: Expr::InitMem(fresh.clone()),
                        delta: *delta,
                    },
                    _ => unreachable!("render_atoms admits registers and memory only"),
                };
                extra_atoms.push(extra_atom);
                extra_vars.push(fresh.clone());
                stitch_expr.insert(var.clone(), Expr::InitMem(fresh.clone()));
                stitch.push((var, fresh));
            }
        }
    }

    // Composed binders beyond the prefix's own.
    let mut binders = String::from("(cpiRdOld : ByteArray)\n    ");
    if prefix_r0.is_none() {
        binders.push_str("(cpiR0Old : Nat)\n    ");
    }
    let fresh_old: Vec<String> = fp
        .iter()
        .filter(|c| c.fresh)
        .map(|c| c.old.clone())
        .collect();
    if !fresh_old.is_empty() {
        binders.push_str(&format!("({} : Nat)\n    ", fresh_old.join(" ")));
    }
    if !extra_vars.is_empty() {
        binders.push_str(&format!("({} : Nat)\n    ", extra_vars.join(" ")));
    }
    let mut suffix_args: Vec<String> = Vec::new();
    let n_guard = suffix.branch_hyps.len();
    for name in &suffix.param_names {
        if suffix.vars.contains(name) {
            let arg = apply(name, &stitch);
            suffix_args.push(if arg.starts_with('(') {
                arg
            } else {
                format!("({arg})")
            });
        } else if let Some((var, k)) = suffix
            .load_bounds
            .iter()
            .find(|(v, _)| &format!("h{v}_lt") == name)
        {
            let hyp = format!("hcpi_{var}_lt");
            binders.push_str(&format!(
                "({hyp} : {} < 2 ^ {k})\n    ",
                apply(var, &stitch)
            ));
            suffix_args.push(hyp);
        } else if let Some(i) = suffix.branch_hyps.iter().position(|(n, _)| n == name) {
            suffix_args.push(guard_projection(i, n_guard));
        } else {
            return Err(unsupported(format!(
                "qedlift: CPI suffix binder {name} is not supported"
            )));
        }
    }
    let guard = if n_guard == 0 {
        "True".to_string()
    } else {
        suffix
            .branch_hyps
            .iter()
            .map(|(_, prop)| format!("({})", apply(prop, &stitch)))
            .collect::<Vec<_>>()
            .join(" ∧ ")
    };

    // Frames and assertions.
    let r0_atom_pre = format!("(.r0 ↦ᵣ {r0_value})");
    let unconsumed: Vec<String> = prefix_post
        .iter()
        .enumerate()
        .filter(|(j, a)| !consumed[*j] && !fp_consumed[*j] && a.key != r0_key)
        .map(|(_, a)| a.render())
        .collect();
    let mut frame_atoms: Vec<String> = prefix_post
        .iter()
        .enumerate()
        .filter(|(j, a)| a.key != r0_key && !fp_consumed[*j])
        .map(|(_, a)| a.render())
        .collect();
    // The composed precondition is built as atoms and rendered once, so the
    // theorem and its satisfiability witness state the same assertion.
    let render = |atoms: &[Atom]| -> Vec<String> {
        atoms
            .iter()
            .map(|a| atoms_to_lean(std::slice::from_ref(a), &prefix.abs_subst))
            .collect()
    };
    let extra = render(&extra_atoms);
    frame_atoms.extend(extra.iter().cloned());
    let mut pre_frame_atoms: Vec<Atom> = Vec::new();
    if prefix_r0.is_none() {
        pre_frame_atoms.push(Atom::Reg(0, Expr::InitReg("cpiR0Old".to_string())));
    }
    pre_frame_atoms.push(Atom::ReturnData {
        value: BytesVal::Sym("cpiRdOld".to_string()),
    });
    for cell in fp.iter().filter(|c| c.fresh) {
        pre_frame_atoms.push(Atom::Mem {
            addr_base: Expr::InitReg("baseAddr".to_string()),
            addr_off: cell.off,
            width: Width::Byte,
            value: Expr::InitMem(cell.old.clone()),
            delta: 0,
        });
    }
    pre_frame_atoms.extend(extra_atoms.iter().cloned());
    let pre_frame = render(&pre_frame_atoms);
    let mut composed_pre_atoms: Vec<Atom> = prefix.pre.clone();
    composed_pre_atoms.extend(pre_frame_atoms.iter().cloned());
    let composed_pre = render(&composed_pre_atoms);
    let mut witness_vars: Vec<String> = prefix.vars.clone();
    if prefix_r0.is_none() {
        witness_vars.push("cpiR0Old".to_string());
    }
    witness_vars.extend(fp.iter().filter(|c| c.fresh).map(|c| c.old.clone()));
    witness_vars.extend(extra_vars.iter().cloned());
    let witness = build_sat_witness(
        &composed_pre_atoms,
        &SymState::default(),
        &[],
        &prefix.abs_subst,
        &[],
        &witness_vars,
    )
    .map_err(|e| e.with_context("qedlift: CPI path precondition witness failed — "))?;
    let mut suffix_frame = vec!["returnDataIs r.returnData".to_string()];
    if !suffix_reads_r0 {
        suffix_frame.push("(.r0 ↦ᵣ r.code)".to_string());
    }
    for cell in fp.iter().filter(|c| !c.read) {
        suffix_frame.push(format!(
            "{} Cpi.committedByte r ({}) {})",
            cell.key,
            cell.addr,
            wrap(&cell.old)
        ));
    }
    suffix_frame.extend(unconsumed.iter().cloned());

    // Contract-specific pieces.
    let cells = fp
        .iter()
        .map(|c| format!("({}, {})", c.addr, c.old))
        .collect::<Vec<_>>()
        .join(", ");
    let (contract_doc, contract_hyp, pc, qc, triple, pre_unfold, suf_unfold) = match contract {
        CpiCalleeContract::MemoryPreserving => (
            "memory preservation (`Cpi.cpiTriple_of_mem_preserving`)".to_string(),
            "(hMem : ∀ s r, callee s r → r.mem = s.mem)".to_string(),
            format!("{r0_atom_pre} ** returnDataIs cpiRdOld"),
            "fun r => (.r0 ↦ᵣ r.code) ** returnDataIs r.returnData".to_string(),
            format!("Cpi.cpiTriple_of_mem_preserving callee ({r0_value}) cpiRdOld hMem"),
            String::new(),
            "    dsimp only\n".to_string(),
        ),
        CpiCalleeContract::WritesInputBytes(_) => (
            "a write footprint (`Cpi.cpiTriple_of_writes`): the callee may change\n\
             only the listed input bytes"
                .to_string(),
            format!(
                "(hW : Cpi.writesOnly callee [{}])",
                fp.iter()
                    .map(|c| c.addr.clone())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            format!("{r0_atom_pre} ** returnDataIs cpiRdOld ** Cpi.bytesAt [{cells}]"),
            format!(
                "fun r => (.r0 ↦ᵣ r.code) ** returnDataIs r.returnData ** \
                 Cpi.bytesAt (Cpi.commitCells r [{cells}])"
            ),
            format!("Cpi.cpiTriple_of_writes callee ({r0_value}) cpiRdOld [{cells}] hW"),
            "    dsimp only [Cpi.bytesAt]\n".to_string(),
            "    dsimp only [Cpi.bytesAt, Cpi.commitCells, List.map]\n".to_string(),
        ),
    };
    let mut post: Vec<String> = suffix_post
        .iter()
        .map(|a| apply(&a.render(), &stitch))
        .collect();
    post.extend(suffix_frame.iter().cloned());

    let prefix_ns = format!("Examples.Lifted.{}", prefix.module_name);
    let theorem = format!(
        "/-! ## Caller path across the CPI ({path_name})

The prefix `{prefix_ns}.{prefix_lifted}` runs to the invoke at pc {invoke_pc};
the CPI commits (or rolls back) through `Cpi.applyResult`; the suffix above
runs from pc {suffix_start} under the guard on the callee's result. The callee
contract here is {contract_doc}. -/

open Memory in
theorem {suffix_module}_cpi_path
    {prefix_binders}{binders}(callee : Cpi.CalleeSemantics)
    {contract_hyp} :
    Cpi.cpiPathWithinMem {n1} {m1} {start1} {invoke_pc} {n2} {m2} {exit2}
      ({cr1})
      ({cr2})
      ({pre})
      (fun r => {post})
      (fun rt => {rr1})
      (fun rt => {rr2})
      {ctor} callee (fun r => {guard}) := by
  refine Cpi.cpi_path_compose
    (Pc := {pc})
    (F := {frame})
    (Qc := {qc})
    ?pre (by decide) (by sl_pcfree)
    ({triple}) ?suf {ctor}
  case pre =>
    have h := cuTripleWithinMem_frame_right ({pre_frame}) (by sl_pcfree)
      ({prefix_ns}.{prefix_lifted} {prefix_args})
{pre_unfold}    sl_exact h
  case suf =>
    intro r hG
    have h := cuTripleWithinMem_frame_right ({suffix_frame}) (by sl_pcfree)
      ({suffix_lifted} {suffix_args})
{suf_unfold}    sl_exact h

",
        prefix_lifted = prefix.lifted_name,
        suffix_start = suffix.start_pc,
        suffix_module = suffix.module_name,
        prefix_binders = prefix.theorem_binders,
        n1 = prefix.n,
        m1 = prefix.m_bound,
        start1 = prefix.start_pc,
        n2 = suffix.n,
        m2 = suffix.m_bound,
        exit2 = suffix.exit_pc,
        cr1 = prefix.cr_lean,
        cr2 = suffix.cr_lean,
        pre = sep(&composed_pre),
        post = sep(&post),
        rr1 = prefix.rr,
        rr2 = apply(&suffix.rr, &stitch),
        ctor = kind.ctor(),
        frame = sep(&frame_atoms),
        pre_frame = sep(&pre_frame),
        prefix_args = prefix.param_names.join(" "),
        suffix_frame = sep(&suffix_frame),
        suffix_lifted = suffix.lifted_name,
        suffix_args = suffix_args.join(" "),
    );

    let end = format!("end Examples.Lifted.{}\n", suffix.module_name);
    if !suffix_lean.contains(&end) {
        return Err(unsupported("qedlift: suffix module has no namespace end"));
    }
    Ok(suffix_lean
        .replacen(
            "import SVM.SBPF.SatWitness",
            &format!(
                "import SVM.SBPF.SatWitness\nimport SVM.SBPF.CpiContract\nimport {prefix_import}"
            ),
            1,
        )
        .replace(&end, &format!("{theorem}{witness}{end}")))
}
