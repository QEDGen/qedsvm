use super::super::*;

/// The real p_token sidecar's `arm_entry_pc` must parse as logical 304 (#41: the formerly-dropped `[instruction.recovered]` is now consumed).
#[test]
fn qedmeta_recovered_arm_is_parsed() {
    let meta = load_qedmeta(std::path::Path::new(
        "../tests/fixtures/p_token.qedmeta.toml",
    ))
    .expect("load p_token.qedmeta.toml");
    let transfer = meta
        .instructions
        .iter()
        .find(|i| i.name == "transfer")
        .expect("transfer instruction present in sidecar");
    let rec = transfer
        .recovered
        .as_ref()
        .expect("transfer carries [instruction.recovered] (dropped pre-#41)");
    assert_eq!(
        rec.arm_entry_pc, 304,
        "recovered arm entry must be logical 304"
    );
}

/// Recovered arm_entry_pc cross-checks that the trace reaches it and leaves emitted Lean byte-identical to the trace-only path.
#[test]
fn qedmeta_arm_entry_trace_lift_is_byte_identical() {
    let so = std::path::Path::new("../tests/fixtures/p_token.so");
    let ctx = load_binary(so).expect("load p_token.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse p_token.so");
    let trace = load_trace(std::path::Path::new(
        "../tests/fixtures/p_token_transfer.pcs",
    ))
    .expect("load transfer trace");
    let result = lift_one_with_layouts(
        so,
        &ctx,
        &analysis,
        LiftRequest {
            module_override: Some("PTokenTransfer".to_string()),
            trace: Some(&trace),
            arm_name: Some("Transfer"),
            arm_entry: Some(304),
            shared_text: Some("PToken"),
            ..LiftRequest::default()
        },
    )
    .expect("lift transfer with recovered arm");
    let on_disk =
        std::fs::read_to_string("../../examples/lean/Generated/PTokenTransferTracedLifted.lean")
            .expect("read PTokenTransferTracedLifted.lean");
    assert_eq!(
        result.lean, on_disk,
        "consuming arm_entry perturbed the trace-guided transfer lift"
    );
}

/// A recovered arm_entry_pc not on the execution trace must be rejected, not silently lifted against the wrong arm.
#[test]
fn qedmeta_arm_entry_off_trace_is_rejected() {
    let so = std::path::Path::new("../tests/fixtures/p_token.so");
    let ctx = load_binary(so).expect("load p_token.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse p_token.so");
    let trace = load_trace(std::path::Path::new(
        "../tests/fixtures/p_token_transfer.pcs",
    ))
    .expect("load transfer trace");
    let err = lift_one(
        so,
        &ctx,
        &analysis,
        None,
        Some("PTokenTransfer".to_string()),
        Some(&trace),
        Some("Transfer"),
        None,
        Some(999_999),
    );
    assert!(
        err.is_err(),
        "an off-trace recovered arm_entry must be rejected by the cross-check"
    );
}

/// Seeding the static walk at the natural entrypoint must reproduce the unseeded walk byte-for-byte, pinning `unwrap_or(entry_pc)` fallback.
#[test]
fn qedmeta_arm_entry_seed_at_entrypoint_is_noop() {
    let so = std::path::Path::new("../tests/fixtures/heap_alloc.so");
    let ctx = load_binary(so).expect("load heap_alloc.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse heap_alloc.so");
    let entry = ctx.executable.get_entrypoint_instruction_offset();
    let base = lift_one(
        so,
        &ctx,
        &analysis,
        None,
        Some("HeapAlloc".to_string()),
        None,
        None,
        None,
        None,
    )
    .expect("base lift");
    let seeded = lift_one(
        so,
        &ctx,
        &analysis,
        None,
        Some("HeapAlloc".to_string()),
        None,
        None,
        None,
        Some(entry),
    )
    .expect("seeded lift");
    assert_eq!(
        base.lean, seeded.lean,
        "seeding the walk at the entrypoint must equal the unseeded walk"
    );
}
