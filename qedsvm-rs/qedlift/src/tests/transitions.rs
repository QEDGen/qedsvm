use super::super::*;

/// #40 OOB-fault-path variant: guarded_oob's guard-fail path performs an
/// out-of-bounds `sol_get_clock_sysvar` write, so its path corollary is
/// an `AsmRefinesTransitionFault … .accessViolation` composed via the
/// Mem-Mem `cuTripleWithinMem_seq_fault` (combined rr = prefix ∧ OOB).
#[test]
fn guarded_oob_transition_is_mechanically_emitted() {
    let so = std::path::Path::new("../tests/fixtures/guarded_oob.so");
    let ctx = load_binary(so).expect("load guarded_oob.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse guarded_oob.so");
    let desc = load_descriptor(std::path::Path::new(
        "../tests/fixtures/guarded_oob.descriptor.json",
    ))
    .expect("descriptor");
    let (paths, (bmod, blean)) = run_transition(so, &ctx, &analysis, &desc, None)
        .into_artifacts()
        .expect("transition emission");
    assert_eq!(paths.len(), 2, "expected the oob + success paths");
    let mut artifacts: Vec<(String, String)> = paths
        .iter()
        .map(|(m, l)| {
            (
                format!("../../examples/lean/Generated/{}Lifted.lean", m),
                l.clone(),
            )
        })
        .collect();
    artifacts.push((
        format!("../../examples/lean/Generated/{}.lean", bmod),
        blean,
    ));
    for (path, lean) in &artifacts {
        if std::env::var("QEDLIFT_BLESS").is_ok() {
            std::fs::write(path, lean).expect("write artifact");
        }
        let on_disk = std::fs::read_to_string(path).expect("read artifact");
        assert_eq!(
            lean, &on_disk,
            "{path} is out of sync with the qedlift transition emitter \
             (mechanically emitted, do not hand-edit)"
        );
    }
}

/// #40 fault-path variant: guarded_abort's guard-fail path ends in the
/// `abort` syscall, so its path corollary is `AsmRefinesTransitionFault`
/// (typed `.abort`, codecs owned in the pre) composed via
/// `cuTripleWithinMem_seq_fault_pure`; the bundle mixes obligation kinds.
#[test]
fn guarded_abort_transition_is_mechanically_emitted() {
    let so = std::path::Path::new("../tests/fixtures/guarded_abort.so");
    let ctx = load_binary(so).expect("load guarded_abort.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse guarded_abort.so");
    let desc = load_descriptor(std::path::Path::new(
        "../tests/fixtures/guarded_abort.descriptor.json",
    ))
    .expect("descriptor");
    let (paths, (bmod, blean)) = run_transition(so, &ctx, &analysis, &desc, None)
        .into_artifacts()
        .expect("transition emission");
    assert_eq!(paths.len(), 2, "expected the panic + success paths");
    let mut artifacts: Vec<(String, String)> = paths
        .iter()
        .map(|(m, l)| {
            (
                format!("../../examples/lean/Generated/{}Lifted.lean", m),
                l.clone(),
            )
        })
        .collect();
    artifacts.push((
        format!("../../examples/lean/Generated/{}.lean", bmod),
        blean,
    ));
    for (path, lean) in &artifacts {
        if std::env::var("QEDLIFT_BLESS").is_ok() {
            std::fs::write(path, lean).expect("write artifact");
        }
        let on_disk = std::fs::read_to_string(path).expect("read artifact");
        assert_eq!(
            lean, &on_disk,
            "{path} is out of sync with the qedlift transition emitter \
             (mechanically emitted, do not hand-edit)"
        );
    }
}

/// #40: the whole-transition emission, end-to-end — trace DISCOVERY
/// (`guarded_counter_{abort,success}.pcs` beside the .so), descriptor-driven
/// per-path lifts (each carrying its `*_transition_path` corollary) and the
/// bundle theorem, all pinned.
#[test]
fn guarded_counter_transition_is_mechanically_emitted() {
    let so = std::path::Path::new("../tests/fixtures/guarded_counter.so");
    let ctx = load_binary(so).expect("load guarded_counter.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse guarded_counter.so");
    let desc = load_descriptor(std::path::Path::new(
        "../tests/fixtures/guarded_counter.descriptor.json",
    ))
    .expect("descriptor");
    let (paths, (bmod, blean)) = run_transition(so, &ctx, &analysis, &desc, None)
        .into_artifacts()
        .expect("transition emission");
    assert_eq!(paths.len(), 2, "expected the abort + success paths");
    let mut artifacts: Vec<(String, String)> = paths
        .iter()
        .map(|(m, l)| {
            (
                format!("../../examples/lean/Generated/{}Lifted.lean", m),
                l.clone(),
            )
        })
        .collect();
    artifacts.push((
        format!("../../examples/lean/Generated/{}.lean", bmod),
        blean,
    ));
    for (path, lean) in &artifacts {
        // QEDLIFT_BLESS=1 re-blesses artifacts after an intentional emitter change.
        if std::env::var("QEDLIFT_BLESS").is_ok() {
            std::fs::write(path, lean).expect("write artifact");
        }
        let on_disk = std::fs::read_to_string(path).expect("read artifact");
        assert_eq!(
            lean, &on_disk,
            "{path} is out of sync with the qedlift transition emitter \
             (mechanically emitted, do not hand-edit)"
        );
    }
}

fn transition_outcome_json(so: &std::path::Path, descriptor: &str) -> serde_json::Value {
    let ctx = load_binary(so).expect("load .so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse .so");
    let desc = load_descriptor(std::path::Path::new(descriptor)).expect("descriptor");
    let run = run_transition(so, &ctx, &analysis, &desc, None);
    serde_json::to_value(&run.outcome).expect("serialize outcome")
}

/// #70: the `transition outcome:` JSON for every transition fixture. Covers
/// a non-zero clean return (guarded_counter's guard-fail path: exit 1, no
/// tracked write, NOT a fault) and both typed faults.
#[test]
fn transition_outcome_reports_each_path_kind() {
    let cases = [
        (
            "guarded_counter",
            r#"{"schema":1,"status":"emitted","bundle":"GuardedCounterTransition","paths":[
              {"label":"abort","module":"GuardedCounterAbort","status":"emitted","kind":"return","exit_code":1,"tracked_written":false},
              {"label":"success","module":"GuardedCounterSuccess","status":"emitted","kind":"return","exit_code":0,"tracked_written":true}]}"#,
        ),
        (
            "guarded_abort",
            r#"{"schema":1,"status":"emitted","bundle":"GuardedAbortTransition","paths":[
              {"label":"panic","module":"GuardedAbortPanic","status":"emitted","kind":"fault","vm_error":"abort"},
              {"label":"success","module":"GuardedAbortSuccess","status":"emitted","kind":"return","exit_code":0,"tracked_written":true}]}"#,
        ),
        (
            "guarded_oob",
            r#"{"schema":1,"status":"emitted","bundle":"GuardedOobTransition","paths":[
              {"label":"oob","module":"GuardedOobOob","status":"emitted","kind":"fault","vm_error":"access_violation"},
              {"label":"success","module":"GuardedOobSuccess","status":"emitted","kind":"return","exit_code":0,"tracked_written":true}]}"#,
        ),
    ];
    for (stem, want) in cases {
        let so = format!("../tests/fixtures/{stem}.so");
        let got = transition_outcome_json(
            std::path::Path::new(&so),
            &format!("../tests/fixtures/{stem}.descriptor.json"),
        );
        let want: serde_json::Value = serde_json::from_str(want).unwrap();
        assert_eq!(got, want, "{stem}");
    }
}

/// A scratch directory holding `guarded_counter.so` plus the named traces.
fn scratch_with_traces(tag: &str, traces: &[(&str, &str)]) -> std::path::PathBuf {
    let dir = std::env::temp_dir().join(format!("qedlift-70-{tag}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("mkdir");
    std::fs::copy(
        "../tests/fixtures/guarded_counter.so",
        dir.join("guarded_counter.so"),
    )
    .expect("copy .so");
    for (label, src) in traces {
        let dst = dir.join(format!("guarded_counter_{label}.pcs"));
        if let Some(fixture) = src.strip_prefix("fixture:") {
            std::fs::copy(format!("../tests/fixtures/{fixture}"), dst).expect("copy trace");
        } else {
            std::fs::write(dst, src).expect("write trace");
        }
    }
    dir
}

/// #70: fewer than two traces is a run-level `unsupported`, not a panic.
#[test]
fn transition_outcome_too_few_traces() {
    let dir = scratch_with_traces("few", &[("success", "fixture:guarded_counter_success.pcs")]);
    let got = transition_outcome_json(
        &dir.join("guarded_counter.so"),
        "../tests/fixtures/guarded_counter.descriptor.json",
    );
    let _ = std::fs::remove_dir_all(&dir);
    assert_eq!(got["status"], "unsupported");
    assert_eq!(got["reason"], "too_few_traces");
    assert_eq!(got["paths"], serde_json::json!([]));
}

/// #70: one bad path is reported per path, the others are still attempted
/// and reported emitted, and no bundle is produced.
#[test]
fn transition_outcome_reports_a_failed_path_without_stopping() {
    let dir = scratch_with_traces(
        "bad",
        &[
            ("abort", "fixture:guarded_counter_abort.pcs"),
            ("broken", "not a pc trace\n"),
            ("success", "fixture:guarded_counter_success.pcs"),
        ],
    );
    let so = dir.join("guarded_counter.so");
    let ctx = load_binary(&so).expect("load .so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse .so");
    let desc = load_descriptor(std::path::Path::new(
        "../tests/fixtures/guarded_counter.descriptor.json",
    ))
    .expect("descriptor");
    let run = run_transition(&so, &ctx, &analysis, &desc, None);
    let _ = std::fs::remove_dir_all(&dir);
    assert!(run.artifacts.is_none());
    let got = serde_json::to_value(&run.outcome).unwrap();
    assert_eq!(got["status"], "unsupported");
    assert!(got.get("bundle").is_none());
    let paths = got["paths"].as_array().unwrap();
    let labels: Vec<_> = paths.iter().map(|p| p["label"].as_str().unwrap()).collect();
    assert_eq!(labels, ["abort", "broken", "success"]);
    assert_eq!(paths[0]["status"], "emitted");
    assert_eq!(paths[1]["status"], "unsupported");
    assert_eq!(paths[1]["reason"], "trace_unreadable");
    assert!(paths[1]["message"].as_str().is_some_and(|m| !m.is_empty()));
    assert_eq!(paths[2]["status"], "emitted");
}
