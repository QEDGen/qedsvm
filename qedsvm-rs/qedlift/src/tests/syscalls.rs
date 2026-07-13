use super::super::*;

/// Pins the typed-fault corollary emitter (Phase 7 sub-item 3): a happy
/// path ending in `.call .abort`. Beyond the running-prefix
/// `cuTripleWithinMem`, the lift emits `AbortCaller_fault_correct`
/// (`cuTripleFaultsWithinMem … .abort`), composing the prefix with
/// `call_abort_faults_spec` via `cuTripleWithinMem_seq_fault_pure`. Static
/// lift (the abort terminates the straight-line walk; no trace needed).
#[test]
fn abort_caller_fault_lift_is_mechanically_emitted() {
    let so = std::path::Path::new("../tests/fixtures/abort_caller.so");
    let ctx = load_binary(so).expect("load abort_caller.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse abort_caller.so");
    let result = lift_one(
        so,
        &ctx,
        &analysis,
        None,
        Some("AbortCaller".to_string()),
        None,
        None,
        None,
        None,
    )
    .expect("lift abort_caller.so");

    let path = "../../examples/lean/Generated/AbortCallerLifted.lean";
    if std::env::var("QEDLIFT_BLESS").is_ok() {
        std::fs::write(path, &result.lean).expect("write AbortCallerLifted.lean");
    }
    let on_disk = std::fs::read_to_string(path).expect("read AbortCallerLifted.lean");
    assert_eq!(
        result.lean, on_disk,
        "AbortCallerLifted.lean is out of sync with the qedlift emitter \
         (mechanically emitted, do not hand-edit)"
    );
}

/// Pins the OOB (H6) typed-fault corollary emitter (Phase 7 sub-item 3): a
/// happy path ending in an out-of-bounds `sol_secp256k1_recover`. The lift
/// emits `OobSecp256k1_fault_correct`
/// (`cuTripleFaultsWithinMem … .accessViolation`), composing the prefix with
/// `call_sol_secp256k1_recover_faults_oob_spec` (frame_right-extended to the
/// prefix post) via the Mem-Mem `cuTripleWithinMem_seq_fault`. Trace-driven
/// (the OOB terminal is detected by the syscall NOT returning to pc+1).
#[test]
fn oob_secp256k1_fault_lift_is_mechanically_emitted() {
    let so = std::path::Path::new("../tests/fixtures/oob_secp256k1.so");
    let ctx = load_binary(so).expect("load oob_secp256k1.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse oob_secp256k1.so");
    let trace = load_trace(std::path::Path::new("../tests/fixtures/oob_secp256k1.pcs"))
        .expect("load oob_secp256k1 trace");
    let result = lift_one(
        so,
        &ctx,
        &analysis,
        None,
        Some("OobSecp256k1".to_string()),
        Some(&trace),
        None,
        None,
        None,
    )
    .expect("lift oob_secp256k1.so");

    let path = "../../examples/lean/Generated/OobSecp256k1Lifted.lean";
    if std::env::var("QEDLIFT_BLESS").is_ok() {
        std::fs::write(path, &result.lean).expect("write OobSecp256k1Lifted.lean");
    }
    let on_disk = std::fs::read_to_string(path).expect("read OobSecp256k1Lifted.lean");
    assert_eq!(
        result.lean, on_disk,
        "OobSecp256k1Lifted.lean is out of sync with the qedlift emitter \
         (mechanically emitted, do not hand-edit)"
    );
}

/// Pins the WRITE-region OOB fault corollary (Phase 7 sub-item 3): an
/// out-of-bounds `sol_get_clock_sysvar`. Exercises `containsWritable` (vs the
/// secp read-region's `containsRange`) and the single-atom prefix post (the
/// fault spec applies bare, no `frame_right`) — the OOB arm across families.
#[test]
fn oob_clock_sysvar_fault_lift_is_mechanically_emitted() {
    let so = std::path::Path::new("../tests/fixtures/oob_clock_sysvar.so");
    let ctx = load_binary(so).expect("load oob_clock_sysvar.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse oob_clock_sysvar.so");
    let trace = load_trace(std::path::Path::new(
        "../tests/fixtures/oob_clock_sysvar.pcs",
    ))
    .expect("load oob_clock_sysvar trace");
    let result = lift_one(
        so,
        &ctx,
        &analysis,
        None,
        Some("OobClockSysvar".to_string()),
        Some(&trace),
        None,
        None,
        None,
    )
    .expect("lift oob_clock_sysvar.so");

    let path = "../../examples/lean/Generated/OobClockSysvarLifted.lean";
    if std::env::var("QEDLIFT_BLESS").is_ok() {
        std::fs::write(path, &result.lean).expect("write OobClockSysvarLifted.lean");
    }
    let on_disk = std::fs::read_to_string(path).expect("read OobClockSysvarLifted.lean");
    assert_eq!(
        result.lean, on_disk,
        "OobClockSysvarLifted.lean is out of sync with the qedlift emitter \
         (mechanically emitted, do not hand-edit)"
    );
}

/// Pins the rent-getter OOB fault corollary (H6 scale-out class (a)):
/// byte-identical recipe to the clock getter, over the de-simp'd 17-byte
/// `execRent` write. Validates the OobSyscall registry generalizes by
/// pure registration (no emitter changes).
#[test]
fn oob_rent_sysvar_fault_lift_is_mechanically_emitted() {
    let so = std::path::Path::new("../tests/fixtures/oob_rent_sysvar.so");
    let ctx = load_binary(so).expect("load oob_rent_sysvar.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse oob_rent_sysvar.so");
    let trace = load_trace(std::path::Path::new(
        "../tests/fixtures/oob_rent_sysvar.pcs",
    ))
    .expect("load oob_rent_sysvar trace");
    let result = lift_one(
        so,
        &ctx,
        &analysis,
        None,
        Some("OobRentSysvar".to_string()),
        Some(&trace),
        None,
        None,
        None,
    )
    .expect("lift oob_rent_sysvar.so");

    let path = "../../examples/lean/Generated/OobRentSysvarLifted.lean";
    if std::env::var("QEDLIFT_BLESS").is_ok() {
        std::fs::write(path, &result.lean).expect("write OobRentSysvarLifted.lean");
    }
    let on_disk = std::fs::read_to_string(path).expect("read OobRentSysvarLifted.lean");
    assert_eq!(
        result.lean, on_disk,
        "OobRentSysvarLifted.lean is out of sync with the qedlift emitter \
         (mechanically emitted, do not hand-edit)"
    );
}

/// Pins the register-sized-region OOB fault corollary (H6 scale-out class
/// (b)): `sol_set_return_data`'s guarded input slice is `[r1, r1+r2)`, so
/// the fault spec's pre is a two-atom sepConj and the region requirement
/// mentions both traced values; the literal length side conditions
/// discharge `by decide`.
#[test]
fn oob_set_return_data_fault_lift_is_mechanically_emitted() {
    let so = std::path::Path::new("../tests/fixtures/oob_set_return_data.so");
    let ctx = load_binary(so).expect("load oob_set_return_data.so");
    let analysis =
        Analysis::from_executable(&ctx.executable).expect("analyse oob_set_return_data.so");
    let trace = load_trace(std::path::Path::new(
        "../tests/fixtures/oob_set_return_data.pcs",
    ))
    .expect("load oob_set_return_data trace");
    let result = lift_one(
        so,
        &ctx,
        &analysis,
        None,
        Some("OobSetReturnData".to_string()),
        Some(&trace),
        None,
        None,
        None,
    )
    .expect("lift oob_set_return_data.so");

    let path = "../../examples/lean/Generated/OobSetReturnDataLifted.lean";
    if std::env::var("QEDLIFT_BLESS").is_ok() {
        std::fs::write(path, &result.lean).expect("write OobSetReturnDataLifted.lean");
    }
    let on_disk = std::fs::read_to_string(path).expect("read OobSetReturnDataLifted.lean");
    assert_eq!(
        result.lean, on_disk,
        "OobSetReturnDataLifted.lean is out of sync with the qedlift emitter \
         (mechanically emitted, do not hand-edit)"
    );
}

/// Pins the non-r1-region OOB fault corollary (H6 scale-out class (c)):
/// `sol_create_program_address`'s first guarded slice is the program_id
/// `[r3, r3+32)`, so the emitter rotates r3 to the front of the lifted
/// pre/post (frame_right arrangement) before composing the fault spec.
#[test]
fn oob_create_pda_fault_lift_is_mechanically_emitted() {
    let so = std::path::Path::new("../tests/fixtures/oob_create_pda.so");
    let ctx = load_binary(so).expect("load oob_create_pda.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse oob_create_pda.so");
    let trace = load_trace(std::path::Path::new("../tests/fixtures/oob_create_pda.pcs"))
        .expect("load oob_create_pda trace");
    let result = lift_one(
        so,
        &ctx,
        &analysis,
        None,
        Some("OobCreatePda".to_string()),
        Some(&trace),
        None,
        None,
        None,
    )
    .expect("lift oob_create_pda.so");

    let path = "../../examples/lean/Generated/OobCreatePdaLifted.lean";
    if std::env::var("QEDLIFT_BLESS").is_ok() {
        std::fs::write(path, &result.lean).expect("write OobCreatePdaLifted.lean");
    }
    let on_disk = std::fs::read_to_string(path).expect("read OobCreatePdaLifted.lean");
    assert_eq!(
        result.lean, on_disk,
        "OobCreatePdaLifted.lean is out of sync with the qedlift emitter \
         (mechanically emitted, do not hand-edit)"
    );
}

/// Pins the hash-family OOB fault corollary (H6 scale-out): `sol_sha256`'s
/// digest output `[r3, r3+32)` is `hashWrite`'s FIRST guard — the non-r1
/// rotation on the WRITE side.
#[test]
fn oob_sha256_fault_lift_is_mechanically_emitted() {
    let so = std::path::Path::new("../tests/fixtures/oob_sha256.so");
    let ctx = load_binary(so).expect("load oob_sha256.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse oob_sha256.so");
    let trace = load_trace(std::path::Path::new("../tests/fixtures/oob_sha256.pcs"))
        .expect("load oob_sha256 trace");
    let result = lift_one(
        so,
        &ctx,
        &analysis,
        None,
        Some("OobSha256".to_string()),
        Some(&trace),
        None,
        None,
        None,
    )
    .expect("lift oob_sha256.so");

    let path = "../../examples/lean/Generated/OobSha256Lifted.lean";
    if std::env::var("QEDLIFT_BLESS").is_ok() {
        std::fs::write(path, &result.lean).expect("write OobSha256Lifted.lean");
    }
    let on_disk = std::fs::read_to_string(path).expect("read OobSha256Lifted.lean");
    assert_eq!(
        result.lean, on_disk,
        "OobSha256Lifted.lean is out of sync with the qedlift emitter \
         (mechanically emitted, do not hand-edit)"
    );
}
/// Pins the `sol_memcpy_` happy-path lift (`call_sol_memcpy_spec`): two
/// `↦Bytes` atoms (src readable, dst writable), dst blob ← src, r0 := 0.
/// Trace-driven (syscall dispatch only fires on a trace).
#[test]
fn memcpy_lift_is_mechanically_emitted() {
    let so = std::path::Path::new("../tests/fixtures/memcpy_caller.so");
    let ctx = load_binary(so).expect("load memcpy_caller.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse memcpy_caller.so");
    let trace = load_trace(std::path::Path::new("../tests/fixtures/memcpy_caller.pcs"))
        .expect("load memcpy trace");
    let result = lift_one(
        so,
        &ctx,
        &analysis,
        None,
        Some("Memcpy".to_string()),
        Some(&trace),
        None,
        None,
        None,
    )
    .expect("lift memcpy_caller.so");

    let path = "../../examples/lean/Generated/MemcpyLifted.lean";
    if std::env::var("QEDLIFT_BLESS").is_ok() {
        std::fs::write(path, &result.lean).expect("write MemcpyLifted.lean");
    }
    let on_disk = std::fs::read_to_string(path).expect("read MemcpyLifted.lean");
    assert_eq!(
        result.lean, on_disk,
        "MemcpyLifted.lean is out of sync with the qedlift emitter \
         (mechanically emitted, re-bless with QEDLIFT_BLESS=1)"
    );
}

/// Pins the single-slice `sol_sha256` happy-path lift
/// (`call_sol_sha256_spec`): the program writes a one-entry SliceDesc, then
/// hashes the input slice into a 32-byte output. Trace-driven.
#[test]
fn sha256_lift_is_mechanically_emitted() {
    let so = std::path::Path::new("../tests/fixtures/sha256_caller.so");
    let ctx = load_binary(so).expect("load sha256_caller.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse sha256_caller.so");
    let trace = load_trace(std::path::Path::new("../tests/fixtures/sha256_caller.pcs"))
        .expect("load sha256 trace");
    let result = lift_one(
        so,
        &ctx,
        &analysis,
        None,
        Some("Sha256Caller".to_string()),
        Some(&trace),
        None,
        None,
        None,
    )
    .expect("lift sha256_caller.so");

    let path = "../../examples/lean/Generated/Sha256CallerLifted.lean";
    if std::env::var("QEDLIFT_BLESS").is_ok() {
        std::fs::write(path, &result.lean).expect("write Sha256CallerLifted.lean");
    }
    let on_disk = std::fs::read_to_string(path).expect("read Sha256CallerLifted.lean");
    assert_eq!(
        result.lean, on_disk,
        "Sha256CallerLifted.lean is out of sync with the qedlift emitter \
         (mechanically emitted, re-bless with QEDLIFT_BLESS=1)"
    );
}

/// Pins the single-seed `sol_create_program_address` happy-path lift
/// (`call_sol_create_program_address_spec`): the program writes a one-entry
/// SliceDesc, derives a PDA from seed + program_id. Trace-driven.
#[test]
fn pda_create_lift_is_mechanically_emitted() {
    let so = std::path::Path::new("../tests/fixtures/pda_create.so");
    let ctx = load_binary(so).expect("load pda_create.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse pda_create.so");
    let trace = load_trace(std::path::Path::new("../tests/fixtures/pda_create.pcs"))
        .expect("load pda_create trace");
    let result = lift_one(
        so,
        &ctx,
        &analysis,
        None,
        Some("PdaCreate".to_string()),
        Some(&trace),
        None,
        None,
        None,
    )
    .expect("lift pda_create.so");

    let path = "../../examples/lean/Generated/PdaCreateLifted.lean";
    if std::env::var("QEDLIFT_BLESS").is_ok() {
        std::fs::write(path, &result.lean).expect("write PdaCreateLifted.lean");
    }
    let on_disk = std::fs::read_to_string(path).expect("read PdaCreateLifted.lean");
    assert_eq!(
        result.lean, on_disk,
        "PdaCreateLifted.lean is out of sync with the qedlift emitter \
         (mechanically emitted, re-bless with QEDLIFT_BLESS=1)"
    );
}

/// Pins the `sol_memmove_` happy-path lift (`call_sol_memmove_spec`): the
/// `is_move` arm of the shared memcpy emitter. Trace-driven.
#[test]
fn memmove_lift_is_mechanically_emitted() {
    let so = std::path::Path::new("../tests/fixtures/memmove_caller.so");
    let ctx = load_binary(so).expect("load memmove_caller.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse memmove_caller.so");
    let trace = load_trace(std::path::Path::new("../tests/fixtures/memmove_caller.pcs"))
        .expect("load memmove trace");
    let result = lift_one(
        so,
        &ctx,
        &analysis,
        None,
        Some("Memmove".to_string()),
        Some(&trace),
        None,
        None,
        None,
    )
    .expect("lift memmove_caller.so");

    let path = "../../examples/lean/Generated/MemmoveLifted.lean";
    if std::env::var("QEDLIFT_BLESS").is_ok() {
        std::fs::write(path, &result.lean).expect("write MemmoveLifted.lean");
    }
    let on_disk = std::fs::read_to_string(path).expect("read MemmoveLifted.lean");
    assert_eq!(
        result.lean, on_disk,
        "MemmoveLifted.lean is out of sync with the qedlift emitter \
         (mechanically emitted, re-bless with QEDLIFT_BLESS=1)"
    );
}

/// Pins the `sol_memcmp_` happy-path lift (`call_sol_memcmp_spec`): two
/// `↦Bytes` inputs + one `↦U32` output, post value `memcmpResultU32`.
#[test]
fn memcmp_lift_is_mechanically_emitted() {
    let so = std::path::Path::new("../tests/fixtures/memcmp_caller.so");
    let ctx = load_binary(so).expect("load memcmp_caller.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse memcmp_caller.so");
    let trace = load_trace(std::path::Path::new("../tests/fixtures/memcmp_caller.pcs"))
        .expect("load memcmp trace");
    let result = lift_one(
        so,
        &ctx,
        &analysis,
        None,
        Some("Memcmp".to_string()),
        Some(&trace),
        None,
        None,
        None,
    )
    .expect("lift memcmp_caller.so");

    let path = "../../examples/lean/Generated/MemcmpLifted.lean";
    if std::env::var("QEDLIFT_BLESS").is_ok() {
        std::fs::write(path, &result.lean).expect("write MemcmpLifted.lean");
    }
    let on_disk = std::fs::read_to_string(path).expect("read MemcmpLifted.lean");
    assert_eq!(
        result.lean, on_disk,
        "MemcmpLifted.lean is out of sync with the qedlift emitter \
         (mechanically emitted, re-bless with QEDLIFT_BLESS=1)"
    );
}

/// Pins the `sol_set_return_data` happy-path lift
/// (`call_sol_set_return_data_spec`): one `↦Bytes` input + the framed
/// `↦ReturnData` atom (flips old → input blob), r0 := 0. Trace-driven.
#[test]
fn set_return_data_lift_is_mechanically_emitted() {
    let so = std::path::Path::new("../tests/fixtures/set_return_data_caller.so");
    let ctx = load_binary(so).expect("load set_return_data_caller.so");
    let analysis =
        Analysis::from_executable(&ctx.executable).expect("analyse set_return_data_caller.so");
    let trace = load_trace(std::path::Path::new(
        "../tests/fixtures/set_return_data_caller.pcs",
    ))
    .expect("load set_return_data trace");
    let result = lift_one(
        so,
        &ctx,
        &analysis,
        None,
        Some("SetReturnData".to_string()),
        Some(&trace),
        None,
        None,
        None,
    )
    .expect("lift set_return_data_caller.so");

    let path = "../../examples/lean/Generated/SetReturnDataLifted.lean";
    if std::env::var("QEDLIFT_BLESS").is_ok() {
        std::fs::write(path, &result.lean).expect("write SetReturnDataLifted.lean");
    }
    let on_disk = std::fs::read_to_string(path).expect("read SetReturnDataLifted.lean");
    assert_eq!(
        result.lean, on_disk,
        "SetReturnDataLifted.lean is out of sync with the qedlift emitter \
         (mechanically emitted, re-bless with QEDLIFT_BLESS=1)"
    );
}
/// #40 gap 4: a caller that hand-builds the Rust-ABI `StableInstruction`
/// on the heap and invokes it. The walk TERMINATES at the invoke
/// (`AbortKind::Invoke` — proof-side CPI is the fail-closed `Cpi.exec`
/// stub), so the lifted prefix's post owns exactly the envelope cells;
/// `examples/lean/CpiEnvelopeDemo.lean` reshapes them into
/// `SVM.Solana.cpiEnvelope` — the per-call-site envelope theorem.
#[test]
fn cpi_envelope_caller_is_mechanically_emitted() {
    let so = std::path::Path::new("../tests/fixtures/cpi_envelope_caller.so");
    let ctx = load_binary(so).expect("load cpi_envelope_caller.so");
    let analysis =
        Analysis::from_executable(&ctx.executable).expect("analyse cpi_envelope_caller.so");
    let result = lift_one(
        so,
        &ctx,
        &analysis,
        None,
        Some("CpiEnvelopeCaller".to_string()),
        None,
        None,
        None,
        None,
    )
    .expect("lift cpi_envelope_caller");
    let path = "../../examples/lean/Generated/CpiEnvelopeCallerLifted.lean";
    if std::env::var("QEDLIFT_BLESS").is_ok() {
        std::fs::write(path, &result.lean).expect("write lift");
    }
    let on_disk = std::fs::read_to_string(path).expect("read lift");
    assert_eq!(
        result.lean, on_disk,
        "{path} is out of sync with the qedlift emitter \
         (mechanically emitted, do not hand-edit)"
    );
}
