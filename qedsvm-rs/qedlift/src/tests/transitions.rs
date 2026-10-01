use super::super::*;
use solana_sbpf::ebpf;

#[test]
fn authorized_vault_captures_every_runtime_reachable_branch_edge() {
    let fixtures = std::path::Path::new("../tests/fixtures");
    let so = fixtures.join("sbpfv3_vault_authorized.so");
    let ctx = load_binary(&so).unwrap();
    let analysis = Analysis::from_executable(&ctx.executable).unwrap();
    let mut edges = std::collections::BTreeSet::new();
    for entry in std::fs::read_dir(fixtures).unwrap() {
        let path = entry.unwrap().path();
        if path
            .file_name()
            .unwrap()
            .to_string_lossy()
            .starts_with("sbpfv3_vault_authorized_")
            && path.extension().is_some_and(|e| e == "pcs")
        {
            let trace = load_trace(&path).unwrap();
            edges.extend(trace.windows(2).map(|pair| (pair[0], pair[1])));
        }
    }
    let mut missing = Vec::new();
    for (pc, insn) in analysis.instructions.iter().enumerate() {
        if matches!(insn.opc & 7, 5 | 6)
            && !matches!(
                insn.opc,
                ebpf::JA | ebpf::CALL_IMM | ebpf::CALL_REG | ebpf::EXIT
            )
        {
            let target = (pc as i64 + 1 + i64::from(insn.off)) as usize;
            for next in [pc + 1, target] {
                // The runtime always serializes the first account with the
                // non-duplicate marker. This branch is excluded by the ABI,
                // and the Lean declared-layout theorem requires that marker.
                if (pc, next) != (4, 63) && !edges.contains(&(pc, next)) {
                    missing.push((pc, next));
                }
            }
        }
    }
    assert!(
        missing.is_empty(),
        "uncaptured runtime-reachable branch edges: {missing:?}"
    );
}

/// Reading owner limbs for authorization must preserve the complete pubkey
/// codec, including paths that reject before reading all four limbs.
#[test]
fn authorized_v3_vault_transitions_preserve_read_pubkeys() {
    let so = std::path::Path::new("../tests/fixtures/sbpfv3_vault_authorized.so");
    let ctx = load_binary(so).unwrap();
    let analysis = Analysis::from_executable(&ctx.executable).unwrap();
    let desc = load_descriptor(std::path::Path::new(
        "../tests/fixtures/sbpfv3_vault_authorized.descriptor.json",
    ))
    .unwrap();
    let idl = serde_json::from_str(
        &std::fs::read_to_string("../tests/fixtures/sbpfv3_vault_authorized.codama.json").unwrap(),
    )
    .unwrap();
    let run = run_transition(so, &ctx, &analysis, &desc, Some(&idl));
    let outcome = serde_json::to_value(&run.outcome).unwrap();
    assert_eq!(outcome["status"], "emitted", "{outcome}");
    let (mut paths, (bundle_name, bundle)) = run.into_artifacts().unwrap();
    assert_eq!(paths.len(), 21);
    assert!(
        bundle.contains("mNeg96"),
        "metadata before the account needs a legal Lean binder"
    );
    assert!(
        !bundle.contains("m-96"),
        "signed offsets must not become subtraction in binder names"
    );
    assert!(!bundle.split(" :\n").next().unwrap().contains("h_noovf"));
    paths.push((bundle_name, bundle));
    for (module, lean) in paths {
        let suffix = if module.ends_with("Transition") {
            ""
        } else {
            "Lifted"
        };
        let path = format!("../../examples/lean/Generated/{module}{suffix}.lean");
        if std::env::var("QEDLIFT_BLESS").is_ok() {
            std::fs::write(&path, &lean).unwrap();
        }
        assert_eq!(
            std::fs::read_to_string(&path).unwrap(),
            lean,
            "{path} is not mechanically emitted"
        );
    }
}

#[test]
fn authorized_vault_rejects_pubkey_mutations_and_partial_width_reads() {
    let fixtures = std::path::Path::new("../tests/fixtures");
    let original_so = fixtures.join("sbpfv3_vault_authorized.so");
    let original = load_binary(&original_so).unwrap();
    let analysis = Analysis::from_executable(&original.executable).unwrap();
    let (_, text) = original.executable.get_text_bytes();
    let bytes = std::fs::read(&original_so).unwrap();
    let start = bytes.windows(text.len()).position(|w| w == text).unwrap();
    let desc = load_descriptor(&fixtures.join("sbpfv3_vault_authorized.descriptor.json")).unwrap();
    let idl = serde_json::from_str(
        &std::fs::read_to_string(fixtures.join("sbpfv3_vault_authorized.codama.json")).unwrap(),
    )
    .unwrap();
    for (label, expected_reason) in [
        ("mutation", "mutation_mismatch"),
        ("partial_read", "unsupported_shape"),
    ] {
        let mut modified = bytes.clone();
        let pc = analysis
            .instructions
            .iter()
            .position(|i| {
                if label == "mutation" {
                    i.opc == ebpf::ST_DW_REG && i.dst == 1 && i.off == 128
                } else {
                    i.opc == ebpf::LD_DW_REG && i.src == 1 && i.off == 96
                }
            })
            .unwrap();
        if label == "mutation" {
            modified[start + pc * 8 + 2..start + pc * 8 + 4].copy_from_slice(&96i16.to_le_bytes());
        } else {
            modified[start + pc * 8] = ebpf::LD_B_REG;
        }
        let dir = std::env::temp_dir().join(format!("qedlift-auth-{label}-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let so = dir.join("sbpfv3_vault_authorized.so");
        std::fs::write(&so, modified).unwrap();
        for path in ["success", "wrong_owner_0"] {
            let name = format!("sbpfv3_vault_authorized_{path}.pcs");
            std::fs::copy(fixtures.join(&name), dir.join(&name)).unwrap();
        }
        let ctx = load_binary(&so).unwrap();
        let analysis = Analysis::from_executable(&ctx.executable).unwrap();
        let run = run_transition(&so, &ctx, &analysis, &desc, Some(&idl));
        assert!(run.artifacts.is_none(), "{label} must not emit a bundle");
        let outcome = serde_json::to_value(run.outcome).unwrap();
        assert!(
            outcome["paths"]
                .as_array()
                .unwrap()
                .iter()
                .any(|p| p["reason"] == expected_reason),
            "{label}: {outcome}"
        );
        std::fs::remove_dir_all(dir).unwrap();
    }
}

/// Real instruction data and account bytes must refer to the same vault on
/// mutating and rejecting paths. In particular, the overflow input must not
/// be excluded by a bundle-wide no-overflow premise.
#[test]
fn sbpfv3_vault_transition_binds_all_paths_to_serialized_account() {
    let so = std::path::Path::new("../tests/fixtures/sbpfv3_vault_deposit.so");
    let ctx = load_binary(so).unwrap();
    let analysis = Analysis::from_executable(&ctx.executable).unwrap();
    let desc = load_descriptor(std::path::Path::new(
        "../tests/fixtures/sbpfv3_vault_deposit.descriptor.json",
    ))
    .unwrap();
    let idl: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string("../tests/fixtures/sbpfv3_vault_deposit.codama.json").unwrap(),
    )
    .unwrap();
    let run = run_transition(so, &ctx, &analysis, &desc, Some(&idl));
    let outcome = serde_json::to_value(&run.outcome).unwrap();
    assert_eq!(outcome["status"], "emitted", "{outcome}");
    let (paths, (bundle_name, bundle)) = run.into_artifacts().unwrap();
    assert_eq!(paths.len(), 4);
    for (module, lean) in &paths {
        let corollary = lean
            .split("## Whole-transition path corollary")
            .nth(1)
            .unwrap();
        assert!(
            corollary.contains("[((baseAddr + 96),"),
            "{module} tracks the wrong account"
        );
    }
    let signature = bundle.split(" :\n").next().unwrap();
    assert!(
        !signature.contains("h_noovf"),
        "overflow must remain an admissible path"
    );
    assert!(
        !bundle.contains("m10408"),
        "the amount must have one IDL-bound name across paths"
    );
    assert!(
        !bundle.contains("m128"),
        "the vault total must have one name across paths"
    );
    let mut artifacts = paths;
    artifacts.push((bundle_name, bundle));
    for (module, lean) in artifacts {
        let suffix = if module.ends_with("Transition") {
            ""
        } else {
            "Lifted"
        };
        let path = format!("../../examples/lean/Generated/{module}{suffix}.lean");
        if std::env::var("QEDLIFT_BLESS").is_ok() {
            std::fs::write(&path, &lean).unwrap();
        }
        assert_eq!(
            std::fs::read_to_string(&path).unwrap(),
            lean,
            "{path} is not mechanically emitted"
        );
    }
}

#[test]
fn v3_transition_refuses_missing_and_incorrect_parameter_bindings() {
    let so = std::path::Path::new("../tests/fixtures/sbpfv3_vault_deposit.so");
    let ctx = load_binary(so).unwrap();
    let analysis = Analysis::from_executable(&ctx.executable).unwrap();
    let original: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string("../tests/fixtures/sbpfv3_vault_deposit.descriptor.json").unwrap(),
    )
    .unwrap();
    let idl: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string("../tests/fixtures/sbpfv3_vault_deposit.codama.json").unwrap(),
    )
    .unwrap();
    for (edit, status, reason) in [
        ("missing_layout", "unsupported", "missing_parameter_binding"),
        ("wrong_argument", "rejected", "parameter_mismatch"),
        ("wrong_field", "rejected", "mutation_mismatch"),
        ("short_account", "rejected", "invalid_layout"),
        ("wrong_index", "rejected", "invalid_parameter_binding"),
    ] {
        let mut descriptor = original.clone();
        match edit {
            "missing_layout" => {
                descriptor.as_object_mut().unwrap().remove("input_layout");
            }
            "wrong_argument" => descriptor["op"]["add_param"] = serde_json::json!("discriminator"),
            "wrong_field" => descriptor["mutated"] = serde_json::json!("bump"),
            "short_account" => {
                descriptor["input_layout"]["account_data_lengths"] = serde_json::json!([8])
            }
            "wrong_index" => descriptor["input_layout"]["account_index"] = serde_json::json!(1),
            _ => unreachable!(),
        }
        let descriptor = serde_json::from_value(descriptor).unwrap();
        let run = run_transition(so, &ctx, &analysis, &descriptor, Some(&idl));
        assert!(run.artifacts.is_none(), "{edit} must not produce a bundle");
        let outcome = serde_json::to_value(&run.outcome).unwrap();
        assert_eq!(outcome["status"], status, "{edit}: {outcome}");
        assert!(
            outcome["paths"]
                .as_array()
                .unwrap()
                .iter()
                .any(|p| p["reason"] == reason),
            "{edit}: {outcome}"
        );
    }
}

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

/// `guarded_counter` with its descriptor JSON edited by `edit`.
fn guarded_counter_outcome_with(edit: impl FnOnce(&mut serde_json::Value)) -> serde_json::Value {
    let mut d: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string("../tests/fixtures/guarded_counter.descriptor.json").unwrap(),
    )
    .unwrap();
    edit(&mut d);
    let path = std::env::temp_dir().join(format!(
        "qedlift-typed-{}-{}.json",
        std::process::id(),
        d.to_string().len()
    ));
    std::fs::write(&path, d.to_string()).unwrap();
    let got = transition_outcome_json(
        std::path::Path::new("../tests/fixtures/guarded_counter.so"),
        path.to_str().unwrap(),
    );
    let _ = std::fs::remove_file(&path);
    got
}

/// The `(status, reason, message)` of each path, in label order.
fn path_verdicts(outcome: &serde_json::Value) -> Vec<(String, String, String)> {
    let field = |p: &serde_json::Value, k: &str| p[k].as_str().unwrap_or("").to_string();
    outcome["paths"]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| (field(p, "status"), field(p, "reason"), field(p, "message")))
        .collect()
}

/// The transition emitter reports exactly why it fell closed on each path:
/// a descriptor the binary contradicts is `rejected`, an unwired shape or a
/// missing layout is `unsupported`, each with its own reason.
#[test]
fn transition_outcome_reports_exact_failure_reasons() {
    let v = |s: &str, r: &str, m: &str| (s.to_string(), r.to_string(), m.to_string());

    // Wrong constant: the success path's write is not `+7`, so `counter`
    // changes outside the descriptor op. The abort path is unaffected.
    let got = guarded_counter_outcome_with(|d| d["op"] = serde_json::json!({"add_const": 7}));
    assert_eq!(got["status"], "rejected");
    assert_eq!(
        path_verdicts(&got),
        [
            v("emitted", "", ""),
            v(
                "rejected",
                "mutation_mismatch",
                "tracked field \"counter\" changes outside the descriptor op"
            ),
        ]
    );

    // An opaque blob field in the tracked layout is not wired.
    let got = guarded_counter_outcome_with(|d| {
        d["layout"].as_array_mut().unwrap().push(
            serde_json::json!({"offset": 16, "kind": "bytes", "width_bytes": 8, "name": "blob"}),
        )
    });
    assert_eq!(got["status"], "unsupported");
    let blob = v(
        "unsupported",
        "unsupported_shape",
        "blob field \"blob\" not wired in the transition emitter",
    );
    assert_eq!(path_verdicts(&got), [blob.clone(), blob]);

    // No inline layout and no IDL: nothing to track.
    let got = guarded_counter_outcome_with(|d| {
        d.as_object_mut().unwrap().remove("layout");
    });
    let missing = v(
        "unsupported",
        "missing_layout",
        "no account layout for \"GuardedCounter\"",
    );
    assert_eq!(path_verdicts(&got), [missing.clone(), missing]);
}
