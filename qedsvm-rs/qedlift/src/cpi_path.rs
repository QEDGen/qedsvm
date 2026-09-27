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
//! The callee contract is the memory-preserving one
//! (`Cpi.cpiTriple_of_mem_preserving`): the callee never changes caller
//! memory, as for zero-account or read-only CPIs.

use std::collections::BTreeMap;

use crate::core::Atom;
use crate::diagnostic::{DiagnosticKind, LiftError};
use crate::emit::{atoms_to_lean, replace_token};
use crate::lift::PathSummary;

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

    let prefix_pre = render_atoms(&prefix.pre, &prefix.abs_subst)?;
    let prefix_post = render_atoms(&prefix.post, &prefix.abs_subst)?;
    let suffix_pre = render_atoms(&suffix.pre, &suffix.abs_subst)?;
    let suffix_post = render_atoms(&suffix.post, &suffix.abs_subst)?;

    let r0_key = "(.r0 ↦ᵣ";
    let prefix_r0 = prefix_post
        .iter()
        .find(|a| a.key == r0_key)
        .map(|a| a.value.clone());
    let r0_value = prefix_r0.clone().unwrap_or_else(|| "cpiR0Old".to_string());

    // Stitch suffix binders. Registers first: memory keys mention them.
    let mut stitch: Vec<(String, String)> = Vec::new();
    let apply = |s: &str, stitch: &[(String, String)]| -> String {
        stitch.iter().fold(s.to_string(), |acc, (var, repl)| {
            replace_token(&acc, var, repl)
        })
    };
    let mut consumed = vec![false; prefix_post.len()];
    let mut suffix_reads_r0 = false;
    let mut extra: Vec<String> = Vec::new();
    let mut extra_vars: Vec<String> = Vec::new();
    let mut ordered: Vec<&RenderedAtom> = suffix_pre
        .iter()
        .filter(|a| a.key.starts_with("(.r"))
        .collect();
    ordered.extend(suffix_pre.iter().filter(|a| !a.key.starts_with("(.r")));
    for atom in ordered {
        let var = atom.value.clone();
        if !suffix.vars.contains(&var) {
            return Err(unsupported(format!(
                "qedlift: CPI suffix precondition value {var} is not a variable"
            )));
        }
        if atom.key == r0_key {
            suffix_reads_r0 = true;
            stitch.push((var, "r.code".to_string()));
            continue;
        }
        let key = apply(&atom.key, &stitch);
        match prefix_post
            .iter()
            .position(|p| p.key == key && p.key != r0_key)
        {
            Some(i) => {
                consumed[i] = true;
                stitch.push((var, format!("({})", prefix_post[i].value)));
            }
            None => {
                let fresh = format!("cpi_{var}");
                extra.push(format!("{key} {fresh})"));
                extra_vars.push(fresh.clone());
                stitch.push((var, fresh));
            }
        }
    }

    // Composed binders beyond the prefix's own.
    let mut binders = String::from("(cpiRdOld : ByteArray)\n    ");
    if prefix_r0.is_none() {
        binders.push_str("(cpiR0Old : Nat)\n    ");
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
        .zip(&consumed)
        .filter(|(a, used)| !**used && a.key != r0_key)
        .map(|(a, _)| a.render())
        .collect();
    let mut frame_atoms: Vec<String> = prefix_post
        .iter()
        .filter(|a| a.key != r0_key)
        .map(RenderedAtom::render)
        .collect();
    frame_atoms.extend(extra.iter().cloned());
    let mut pre_frame: Vec<String> = Vec::new();
    if prefix_r0.is_none() {
        pre_frame.push(r0_atom_pre.clone());
    }
    pre_frame.push("returnDataIs cpiRdOld".to_string());
    pre_frame.extend(extra.iter().cloned());
    let mut composed_pre: Vec<String> = prefix_pre.iter().map(RenderedAtom::render).collect();
    composed_pre.extend(pre_frame.iter().cloned());
    let mut suffix_frame = vec!["returnDataIs r.returnData".to_string()];
    if !suffix_reads_r0 {
        suffix_frame.push("(.r0 ↦ᵣ r.code)".to_string());
    }
    suffix_frame.extend(unconsumed.iter().cloned());
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
contract here is memory preservation (`Cpi.cpiTriple_of_mem_preserving`). -/

open Memory in
theorem {suffix_module}_cpi_path
    {prefix_binders}{binders}(callee : Cpi.CalleeSemantics)
    (hMem : ∀ s r, callee s r → r.mem = s.mem) :
    Cpi.cpiPathWithinMem {n1} {m1} {start1} {invoke_pc} {n2} {m2} {exit2}
      ({cr1})
      ({cr2})
      ({pre})
      (fun r => {post})
      (fun rt => {rr1})
      (fun rt => {rr2})
      {ctor} callee (fun r => {guard}) := by
  refine Cpi.cpi_path_compose
    (Pc := {r0_atom_pre} ** returnDataIs cpiRdOld)
    (F := {frame})
    (Qc := fun r => (.r0 ↦ᵣ r.code) ** returnDataIs r.returnData)
    ?pre (by decide) (by sl_pcfree)
    (Cpi.cpiTriple_of_mem_preserving callee ({r0_value}) cpiRdOld hMem) ?suf {ctor}
  case pre =>
    have h := cuTripleWithinMem_frame_right ({pre_frame}) (by sl_pcfree)
      ({prefix_ns}.{prefix_lifted} {prefix_args})
    sl_exact h
  case suf =>
    intro r hG
    have h := cuTripleWithinMem_frame_right ({suffix_frame}) (by sl_pcfree)
      ({suffix_lifted} {suffix_args})
    dsimp only
    sl_exact h

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
        .replace(&end, &format!("{theorem}{end}")))
}
