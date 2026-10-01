use super::super::*;

#[test]
fn v3_recovered_arm_consumes_the_real_instruction_trace() {
    let fixtures = std::path::Path::new("../tests/fixtures");
    let so = fixtures.join("sbpfv3_vault_deposit.so");
    let ctx = load_binary(&so).unwrap();
    let analysis = Analysis::from_executable(&ctx.executable).unwrap();
    let meta = load_qedmeta(&fixtures.join("sbpfv3_vault_deposit.qedmeta.toml")).unwrap();
    let arm = meta.instructions[0]
        .recovered
        .as_ref()
        .unwrap()
        .arm_entry_pc;
    let trace = load_trace(&fixtures.join("sbpfv3_vault_deposit_success.pcs")).unwrap();
    let layouts = sidecar_account_layouts(&meta);
    let result = lift_one_with_layouts(
        &so,
        &ctx,
        &analysis,
        LiftRequest {
            target_disc: Some(1),
            module_override: Some("Sbpfv3VaultDepositDeposit".into()),
            arm_name: Some("Deposit"),
            trace: Some(&trace),
            arm_entry: Some(arm),
            sidecar_layouts: Some(&layouts),
            ..LiftRequest::default()
        },
    )
    .unwrap();
    assert_eq!(
        result.lean.lines().skip(1).collect::<Vec<_>>(),
        std::fs::read_to_string(
            "../../examples/lean/Generated/Sbpfv3VaultDepositDepositLifted.lean"
        )
        .unwrap()
        .lines()
        .skip(1)
        .collect::<Vec<_>>()
    );
    let wrong_trace = load_trace(&fixtures.join("sbpfv3_vault_deposit_unknown.pcs")).unwrap();
    assert!(
        lift_one_with_layouts(
            &so,
            &ctx,
            &analysis,
            LiftRequest {
                trace: Some(&wrong_trace),
                arm_entry: Some(arm),
                ..LiftRequest::default()
            }
        )
        .is_err(),
        "a dispatcher rejection trace never enters the recovered deposit arm"
    );
}

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
