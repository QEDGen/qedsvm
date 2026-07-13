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
    let (paths, (bmod, blean)) =
        run_transition(so, &ctx, &analysis, &desc, None).expect("transition emission");
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
    let (paths, (bmod, blean)) =
        run_transition(so, &ctx, &analysis, &desc, None).expect("transition emission");
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
    let (paths, (bmod, blean)) =
        run_transition(so, &ctx, &analysis, &desc, None).expect("transition emission");
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
