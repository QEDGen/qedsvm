//! CLI mode runners: transition / qedmeta / batch / single-arm dispatch and
//! the shared lift-output writer.

use super::*;

/// Discover per-path traces beside the .so: `<stem>_<path>.pcs`, sorted by
/// path label (deterministic bundle order). Each discovered trace is one
/// PATH of the program's transition (#40).
fn discover_path_traces(so: &Path) -> Vec<(String, std::path::PathBuf)> {
    let stem = so
        .file_stem()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_default();
    let dir = so.parent().unwrap_or_else(|| Path::new("."));
    let mut out = Vec::new();
    if let Ok(rd) = std::fs::read_dir(dir) {
        for e in rd.flatten() {
            let p = e.path();
            if p.extension().and_then(|x| x.to_str()) != Some("pcs") {
                continue;
            }
            if let Some(fs) = p.file_stem().and_then(|x| x.to_str()) {
                if let Some(label) = fs.strip_prefix(&format!("{}_", stem)) {
                    if !label.is_empty() {
                        out.push((label.to_string(), p.clone()));
                    }
                }
            }
        }
    }
    out.sort();
    out
}

/// Whole-transition emission (#40): lift every discovered path of `so`
/// (descriptor-driven, trace-guided; each lift carries its
/// `*_transition_path` corollary) and emit the bundle theorem. Returns the
/// per-path `(module, lean)` files and the `(module, lean)` bundle.
#[allow(clippy::type_complexity)]
pub(super) fn run_transition(
    so: &Path,
    ctx: &BinaryCtx,
    analysis: &Analysis<'_>,
    descriptor: &RefinementDescriptor,
    idl: Option<&serde_json::Value>,
) -> Result<(Vec<(String, String)>, (String, String)), Box<dyn std::error::Error>> {
    let traces = discover_path_traces(so);
    if traces.len() < 2 {
        return Err(format!(
            "--transition: need ≥ 2 discovered `<stem>_<path>.pcs` traces \
             beside {}, found {}",
            so.display(),
            traces.len()
        )
        .into());
    }
    let stem_snake = so
        .file_stem()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_else(|| "lifted".to_string());
    let stem_pascal = pascal_case(&stem_snake);
    let mut path_files: Vec<(String, String)> = Vec::new();
    let mut modules: Vec<String> = Vec::new();
    let mut infos: Vec<TransitionPathInfo> = Vec::new();
    for (label, pcs) in &traces {
        let module = format!("{}{}", stem_pascal, pascal_case(label));
        let trace = load_trace(pcs)?;
        let r = lift_one_with_layouts(
            so,
            ctx,
            analysis,
            LiftRequest {
                module_override: Some(module.clone()),
                trace: Some(&trace),
                idl,
                descriptor: Some(descriptor),
                ..LiftRequest::default()
            },
        )?;
        let info = r.transition.ok_or_else(|| {
            format!(
                "--transition: path {:?} produced no transition corollary \
             (see stderr for the fail-closed reason)",
                label
            )
        })?;
        path_files.push((module.clone(), r.lean));
        modules.push(module);
        infos.push(info);
    }
    let bundle = emit_transition_bundle(&stem_pascal, &stem_snake, &modules, &infos)
        .ok_or("transition bundle emission failed (binder conflict — see stderr)")?;
    Ok((path_files, bundle))
}

/// Profiling mode (`--profile`): symbolicate a `.pcs` trace against the
/// `<so>.debug` sidecar and print folded call stacks (flamegraph.pl / inferno
/// input) on stdout, with a per-function step summary on stderr. Does not lift
/// or emit Lean. Step-weighted, not CU-weighted (see `qed_analysis::profile`).
pub(super) fn run_profile_mode(
    args: &Args,
    ctx: &BinaryCtx,
    trace: Option<&[usize]>,
) -> Result<(), Box<dyn std::error::Error>> {
    let trace = trace.ok_or("--profile requires --trace <pcs>")?;

    // Prefer the `.debug` sidecar (tests/fixtures/build-fixture.sh); fall back
    // to the .so itself, which is stripped, so labels degrade to `fn@slot<N>`.
    let sidecar = args.so.with_extension("debug");
    let syms = if sidecar.exists() {
        SymbolIndex::from_path(&sidecar)?
    } else {
        eprintln!(
            "profile: no `{}` sidecar (run tests/fixtures/build-fixture.sh <name>); \
             falling back to the stripped .so, symbols will be unavailable.",
            sidecar.display()
        );
        SymbolIndex::from_path(&args.so)?
    };

    let folded = fold_trace(trace, &ctx.insns, |pc| syms.label_logical(pc, &ctx.pc_map));

    // Per-function self-steps (leaf frame only) for a quick human summary.
    let steps = symbolicate_trace(trace, &syms, &ctx.pc_map);
    let mut self_steps: std::collections::BTreeMap<&str, u64> = std::collections::BTreeMap::new();
    for s in &steps {
        *self_steps.entry(s.function.as_str()).or_insert(0) += 1;
    }
    let mut summary: Vec<(&str, u64)> = self_steps.into_iter().collect();
    summary.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(b.0)));

    eprintln!(
        "profile: {} steps across {} function(s){} (weight = instruction steps, not CU)",
        trace.len(),
        summary.len(),
        if syms.has_dwarf() {
            ", DWARF inline frames available"
        } else {
            ""
        },
    );
    for (func, n) in summary.iter().take(20) {
        eprintln!("  {n:>8}  {func}");
    }

    // Folded stacks to stdout: `qedlift --profile ... > out.folded`, then
    // `flamegraph.pl out.folded > out.svg`.
    for line in folded_lines(&folded) {
        println!("{line}");
    }
    Ok(())
}

/// Bucket a fail-closed lift reason into a coverage category. The frontier
/// families the report ranks: an unmodeled opcode (walker/ISA), a non-constant
/// (symbolic) syscall operand, an unsupported construct, a CU-budget miss, a
/// vacuity/witness failure, or a missing/bad trace input (not a real gap).
fn classify_lift_failure(reason: &str) -> &'static str {
    if reason.contains("unmodeled syscall") {
        // A syscall with no SYSCALLS-table row: the real "add a syscall" gap.
        "syscall-unmodeled"
    } else if reason.contains("modeled syscall") && reason.contains("static walk") {
        // A modeled syscall the no-trace static walk won't dispatch: needs a
        // trace, not new capability.
        "syscall-untraced"
    } else if reason.contains("unresolved internal call") {
        "call-unresolved"
    } else if reason.contains("not yet modelled") || reason.contains("not yet lifted") {
        "opcode-unmodeled"
    } else if reason.contains("exceeded") && reason.contains("steps")
        || reason.contains("back-branch")
    {
        // Static walk hit the step cap: a back-branch (loop) it can't follow
        // without a trace. Often "needs a trace", not an intrinsic gap.
        "walker-steps"
    } else if reason.contains("vacuous lift")
        || reason.contains("overlapping atom")
        || reason.contains("alias these at byte")
    {
        "byte-aliasing"
    } else if reason.contains("symbolic") {
        "symbolic-operand"
    } else if reason.contains("unsupported IDL")
        || reason.contains("hotUnsupported")
        || reason.contains("Replicate blob")
    {
        "unsupported-construct"
    } else if reason.contains("cu_budget") {
        "cu-budget-exceeded"
    } else if reason.contains("satisfiability witness") {
        "witness-failed"
    } else if reason.contains("trace") || reason.contains("no PCs") {
        "trace-input"
    } else {
        "other"
    }
}

/// One lift attempt, panic-safe: a survey must not die on a lift that panics
/// (internal `.expect`/`unwrap`) rather than returning `Err`, so catch it and
/// report it as a `panic:` reason. Returns `Ok(())` on a lifted triple.
fn attempt_lift(
    so: &Path,
    ctx: &BinaryCtx,
    analysis: &Analysis<'_>,
    trace: Option<&[usize]>,
) -> Result<(), String> {
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        lift_one_with_layouts(
            so,
            ctx,
            analysis,
            LiftRequest {
                trace,
                ..LiftRequest::default()
            },
        )
    }));
    match r {
        Ok(Ok(_)) => Ok(()),
        Ok(Err(e)) => Err(e.to_string()),
        Err(panic) => Err(format!(
            "panic: {}",
            panic
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| panic.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap_or_else(|| "<non-string panic>".to_string())
        )),
    }
}

/// Coverage mode (`--coverage`): attempt to lift every discovered
/// `<stem>_<path>.pcs` arm of the `.so` (or one static probe when none exist),
/// classify each fail-closed reason, and print a ranked report. Emits no Lean.
/// The frontier instrument: green pins read ~100%; the signal is which
/// untraced arms / real programs fail and why.
pub(super) fn run_coverage_mode(
    args: &Args,
    ctx: &BinaryCtx,
    analysis: &Analysis<'_>,
) -> Result<(), Box<dyn std::error::Error>> {
    let so = &args.so;
    let stem = so
        .file_stem()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_default();
    let traces = discover_path_traces(so);

    // Suppress the default panic hook (backtrace spam) during the survey.
    let prev_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));

    // (arm label, lift result) for each attempt.
    let attempts: Vec<(String, Result<(), String>)> = if traces.is_empty() {
        vec![(
            "<static>".to_string(),
            match args.trace.as_ref() {
                Some(p) => match load_trace(p) {
                    Ok(t) => attempt_lift(so, ctx, analysis, Some(&t)),
                    Err(e) => Err(format!("trace load: {e}")),
                },
                None => attempt_lift(so, ctx, analysis, None),
            },
        )]
    } else {
        traces
            .iter()
            .map(|(label, pcs)| {
                let r = match load_trace(pcs) {
                    Ok(t) => attempt_lift(so, ctx, analysis, Some(&t)),
                    Err(e) => Err(format!("trace load: {e}")),
                };
                (label.clone(), r)
            })
            .collect()
    };

    std::panic::set_hook(prev_hook);

    // Bucket the failures.
    let mut lifted = 0usize;
    let mut buckets: std::collections::BTreeMap<&'static str, Vec<(String, String)>> =
        std::collections::BTreeMap::new();
    for (label, r) in &attempts {
        match r {
            Ok(()) => lifted += 1,
            Err(reason) => buckets
                .entry(classify_lift_failure(reason))
                .or_default()
                .push((label.clone(), reason.clone())),
        }
    }

    let total = attempts.len();
    println!("coverage {stem}: {lifted}/{total} lifted");
    if lifted == total {
        println!("  (all attempted arms lift)");
        return Ok(());
    }

    // Ranked buckets, most failures first.
    let mut ranked: Vec<(&'static str, Vec<(String, String)>)> = buckets.into_iter().collect();
    ranked.sort_by(|a, b| b.1.len().cmp(&a.1.len()).then_with(|| a.0.cmp(b.0)));
    for (bucket, items) in &ranked {
        println!("  {:>3}  {}", items.len(), bucket);
        for (label, reason) in items {
            // First line of the reason keeps the report scannable.
            let first = reason.lines().next().unwrap_or(reason);
            println!("         {label}: {first}");
        }
    }
    Ok(())
}

/// Write a lift result's `.lean` under `out_path` (creating the parent
/// directory), plus its refinement sibling next to it when one was emitted.
/// Returns the refinement path, if written. The shared tail of every mode.
fn write_lift_result(
    result: &LiftOutput,
    out_path: &Path,
) -> Result<Option<std::path::PathBuf>, Box<dyn std::error::Error>> {
    if let Some(parent) = out_path.parent() {
        std::fs::create_dir_all(parent)?;
    }
    std::fs::write(out_path, &result.lean)?;
    // Shared-text module (batch dedup): identical for every arm of the same
    // binary, so re-writing it per arm is idempotent.
    if let Some((smod, slean)) = &result.shared_text {
        let spath = out_path.with_file_name(format!("{}.lean", smod));
        std::fs::write(&spath, slean)?;
    }
    if let Some((rmod, rlean)) = &result.refinement {
        let rpath = out_path.with_file_name(format!("{}.lean", rmod));
        std::fs::write(&rpath, rlean)?;
        return Ok(Some(rpath));
    }
    Ok(None)
}

/// --transition mode (#40): discovered per-path traces + descriptor →
/// per-path lifts (each with a `*_transition_path` corollary) + the bundle.
pub(super) fn run_transition_mode(
    args: &Args,
    ctx: &BinaryCtx,
    analysis: &Analysis<'_>,
    descriptor: Option<&RefinementDescriptor>,
    idl_value: Option<&serde_json::Value>,
) -> Result<(), Box<dyn std::error::Error>> {
    let desc = descriptor.ok_or("--transition needs --descriptor")?;
    let out_dir = args
        .output_dir
        .as_ref()
        .ok_or("--transition needs --output-dir")?;
    std::fs::create_dir_all(out_dir)?;
    let (paths, (bmod, blean)) = run_transition(&args.so, ctx, analysis, desc, idl_value)?;
    println!("=== qedlift (transition) ===");
    println!("  input  : {}", args.so.display());
    for (m, lean) in &paths {
        let p = out_dir.join(format!("{}Lifted.lean", m));
        std::fs::write(&p, lean)?;
        println!("  ✔ path   {:<26} → {}", m, p.display());
    }
    let bp = out_dir.join(format!("{}.lean", bmod));
    std::fs::write(&bp, &blean)?;
    println!("  ✔ bundle {:<26} → {}", bmod, bp.display());
    Ok(())
}

/// --qedmeta mode: targeting from qedrecover sidecar (disc + name), CU
/// cross-check, optional --target-name filter.
pub(super) fn run_qedmeta_mode(
    args: &Args,
    ctx: &BinaryCtx,
    analysis: &Analysis<'_>,
    meta_path: &Path,
    trace: Option<&[usize]>,
    idl_value: Option<&serde_json::Value>,
) -> Result<(), Box<dyn std::error::Error>> {
    let meta = load_qedmeta(meta_path)?;
    // #41 loop closure: consume qedrecover's emitted + validated account layouts as the
    // refinement-codegen layout source (falls back to `--idl` per-name when a layout is absent).
    let sidecar_layouts = sidecar_account_layouts(&meta);
    let so_stem = args
        .so
        .file_stem()
        .map(|s| pascal_case(&s.to_string_lossy()))
        .unwrap_or_else(|| "Lifted".to_string());

    let selected: Vec<_> = match args.target_name.as_ref() {
        Some(want) => meta
            .instructions
            .iter()
            .filter(|i| &i.name == want)
            .collect(),
        None => meta.instructions.iter().collect(),
    };
    if selected.is_empty() {
        return Err(format!(
            "--qedmeta {}: no in-scope instruction{}",
            meta_path.display(),
            args.target_name
                .as_ref()
                .map(|n| format!(" named {:?}", n))
                .unwrap_or_default()
        )
        .into());
    }

    println!("=== qedlift (qedmeta) ===");
    println!("  input  : {}", args.so.display());
    println!("  sidecar: {}", meta_path.display());
    println!("  arms   : {}", selected.len());

    let mut budget_fail = false;
    for ix in selected {
        let arm = pascal_case(&ix.name);
        let module_name = format!("{}{}", so_stem, arm);
        // #41 Phase 4: recovered arm_entry seeds no-trace walk / cross-checks trace.
        let arm_entry = ix.recovered.as_ref().map(|r| r.arm_entry_pc);
        let result = lift_one_with_layouts(
            &args.so,
            ctx,
            analysis,
            LiftRequest {
                target_disc: Some(ix.discriminator.value),
                module_override: Some(module_name.clone()),
                trace,
                arm_name: Some(&arm),
                idl: idl_value,
                arm_entry,
                sidecar_layouts: Some(&sidecar_layouts),
                shared_text: args.shared_text.as_deref(),
                ..LiftRequest::default()
            },
        )?;

        // Cross-check: cu_budget is upper bound; result.cu is the exact discharged CU.
        let budget_note = match ix.cu_budget {
            Some(b) if result.cu as u64 > b => {
                budget_fail = true;
                format!(" ✘ CU {} EXCEEDS budget {}", result.cu, b)
            }
            Some(b) => format!(" ✔ CU {} ≤ budget {}", result.cu, b),
            None => format!(" CU {} (no budget claimed)", result.cu),
        };

        let out_path = if let Some(o) = args.output.as_ref() {
            o.clone()
        } else if let Some(d) = args.output_dir.as_ref() {
            std::fs::create_dir_all(d)?;
            d.join(format!("{}Lifted.lean", module_name))
        } else {
            return Err("--qedmeta needs --output (single arm) or --output-dir".into());
        };
        let refined = if write_lift_result(&result, &out_path)?.is_some() {
            " (+refinement)"
        } else {
            ""
        };
        println!(
            "  ✔ {:<20} disc={:<4}{} → {}{}",
            ix.name,
            ix.discriminator.value,
            budget_note,
            out_path.display(),
            refined
        );
    }
    if budget_fail {
        return Err("one or more lifted triples exceeded the claimed cu_budget".into());
    }
    Ok(())
}

/// Batch mode: --idl + --output-dir, one lift per IDL instruction
/// (per-arm tolerance: unmodelled opcodes are reported+skipped — batch is a
/// coverage probe).
pub(super) fn run_batch_mode(
    args: &Args,
    ctx: &BinaryCtx,
    analysis: &Analysis<'_>,
    idl_path: &Path,
    output_dir: &Path,
    idl_value: Option<&serde_json::Value>,
) -> Result<(), Box<dyn std::error::Error>> {
    let idl = load_idl(idl_path)?;
    std::fs::create_dir_all(output_dir)?;

    let so_stem = args
        .so
        .file_stem()
        .map(|s| pascal_case(&s.to_string_lossy()))
        .unwrap_or_else(|| "Lifted".to_string());

    println!("=== qedlift (batch) ===");
    println!("  input  : {}", args.so.display());
    println!("  idl    : {}", idl_path.display());
    println!("  outdir : {}", output_dir.display());
    println!("  arms   : {}", idl.len());

    let mut lifted = 0usize;
    let mut skipped: Vec<(String, String)> = Vec::new();
    for ix in &idl {
        // Namespace Examples.Lifted.<SoStem><Name>; file <SoStem><Name>Lifted.lean.
        let module_name = format!("{}{}", so_stem, pascal_case(&ix.name));
        match lift_one_with_layouts(
            &args.so,
            ctx,
            analysis,
            LiftRequest {
                target_disc: Some(ix.discriminator),
                module_override: Some(module_name.clone()),
                arm_name: Some(&ix.name),
                idl: idl_value,
                shared_text: args.shared_text.as_deref(),
                ..LiftRequest::default()
            },
        ) {
            Ok(result) => {
                let out_path = output_dir.join(format!("{}Lifted.lean", module_name));
                let refined = if write_lift_result(&result, &out_path)?.is_some() {
                    " (+refinement)"
                } else {
                    ""
                };
                println!(
                    "  ✔ {:<24} disc={:<4} {} insns → {}{}",
                    ix.name,
                    ix.discriminator,
                    result.insn_count,
                    out_path.display(),
                    refined
                );
                lifted += 1;
            }
            Err(e) => {
                println!("  ✘ {:<24} disc={:<4} {}", ix.name, ix.discriminator, e);
                skipped.push((ix.name.clone(), e.to_string()));
            }
        }
    }
    println!("=== batch summary ===");
    println!("  lifted  : {}", lifted);
    println!("  skipped : {}", skipped.len());
    Ok(())
}

/// Single-arm mode: one lift (optionally trace-guided / descriptor-driven),
/// written to --output or streamed to stdout.
pub(super) fn run_single_mode(
    args: &Args,
    ctx: &BinaryCtx,
    analysis: &Analysis<'_>,
    trace: Option<&[usize]>,
    descriptor: Option<&RefinementDescriptor>,
    idl_value: Option<&serde_json::Value>,
) -> Result<(), Box<dyn std::error::Error>> {
    let result = lift_one_with_layouts(
        &args.so,
        ctx,
        analysis,
        LiftRequest {
            target_disc: args.target_disc,
            module_override: args.module.clone(),
            trace,
            arm_name: args.arm_name.as_deref(),
            idl: idl_value,
            descriptor,
            shared_text: args.shared_text.as_deref(),
            ..LiftRequest::default()
        },
    )?;
    match args.output.as_ref() {
        Some(path) => {
            let rpath = write_lift_result(&result, path)?;
            println!("=== qedlift ===");
            println!("  input  : {}", args.so.display());
            println!("  output : {}", path.display());
            println!(
                "  .text  : {} bytes ({} insns)",
                result.text_bytes, result.insn_count
            );
            println!("  module : Examples.Lifted.{}", result.module_name);
            if let Some(rpath) = rpath {
                println!("  refine : {}", rpath.display());
            }
        }
        None => {
            print!("{}", result.lean);
            if let Some((_, rlean)) = &result.refinement {
                println!("\n-- ╌╌ refinement ╌╌");
                print!("{}", rlean);
            }
        }
    }
    Ok(())
}
