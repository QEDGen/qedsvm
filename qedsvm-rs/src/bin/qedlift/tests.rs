use super::*;
use qed_analysis::layout::{parse_account_layout, FieldKind};

/// Diffs the emitter output on `counter.so` against both on-disk artifacts, guarding the counter-codec (non-token) path.
#[test]
fn counter_refinement_is_mechanically_emitted() {
    let so = std::path::Path::new("tests/fixtures/counter.so");
    let ctx = load_binary(so).expect("load counter.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse counter.so");
    let result = lift_one(
        so,
        &ctx,
        &analysis,
        None,
        Some("Counter".to_string()),
        None,
        Some("counterIncrement"),
        None,
        None,
    )
    .expect("lift counter.so");

    let lift_on_disk =
        std::fs::read_to_string("../examples/lean/Generated/CounterTracedLifted.lean")
            .expect("read CounterTracedLifted.lean");
    assert_eq!(
        result.lean, lift_on_disk,
        "CounterTracedLifted.lean is out of sync with the qedlift emitter \
         (mechanically emitted, do not hand-edit)"
    );

    let (_, rlean) = result.refinement.expect("counter refinement emitted");
    let refine_on_disk =
        std::fs::read_to_string("../examples/lean/Generated/CounterRefinement.lean")
            .expect("read CounterRefinement.lean");
    assert_eq!(
        rlean, refine_on_disk,
        "CounterRefinement.lean is out of sync with the qedlift emitter \
         (mechanically emitted, do not hand-edit)"
    );
}

/// Spec-driven descriptor path (the qedspec seam): the refinement is built from a
/// `*.descriptor.json` (layout + mutated field + op), bypassing `refine_registry`, and
/// targets the layout-general `AsmRefinesFieldUpdate`. Two fixtures pin both shapes:
/// counter (single u64 @ 0, empty frame) and vault (multi-field, pubkey + byte framing).
#[test]
fn descriptor_refinement_is_mechanically_emitted() {
    // (a) counter.so — single u64 field at offset 0, empty frame (no refine_registry entry).
    let desc = load_descriptor(std::path::Path::new(
        "tests/fixtures/counter.descriptor.json",
    ))
    .expect("load counter descriptor");
    let so = std::path::Path::new("tests/fixtures/counter.so");
    let ctx = load_binary(so).expect("load counter.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse counter.so");
    let result = lift_one_with_layouts(
        so,
        &ctx,
        &analysis,
        LiftRequest {
            module_override: Some("CounterDescriptor".to_string()),
            descriptor: Some(&desc),
            ..LiftRequest::default()
        },
    )
    .expect("lift counter.so via descriptor");
    let (_, rlean) = result
        .refinement
        .expect("descriptor refinement emitted (counter)");
    let on_disk =
        std::fs::read_to_string("../examples/lean/Generated/CounterDescriptorRefinement.lean")
            .expect("read CounterDescriptorRefinement.lean");
    assert_eq!(
        rlean, on_disk,
        "CounterDescriptorRefinement.lean is out of sync with the qedlift descriptor \
         emitter (mechanically emitted, do not hand-edit)"
    );

    // (b) vault.so — multi-field {owner:Pubkey, total:u64, bump:u8}; `total` mutated.
    // Name-level descriptor (no inline layout, no registry entry): the shape is resolved
    // from the IDL by account name, exactly the path `resolve_layout` uses.
    let vdesc = load_descriptor(std::path::Path::new("tests/fixtures/vault.descriptor.json"))
        .expect("load vault descriptor");
    let vidl: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string("tests/fixtures/vault.codama.json")
            .expect("read vault.codama.json"),
    )
    .expect("parse vault IDL");
    let vso = std::path::Path::new("tests/fixtures/vault.so");
    let vctx = load_binary(vso).expect("load vault.so");
    let vanalysis = Analysis::from_executable(&vctx.executable).expect("analyse vault.so");
    let vresult = lift_one_with_layouts(
        vso,
        &vctx,
        &vanalysis,
        LiftRequest {
            module_override: Some("VaultDescriptor".to_string()),
            idl: Some(&vidl),
            descriptor: Some(&vdesc),
            ..LiftRequest::default()
        },
    )
    .expect("lift vault.so via descriptor");
    let (_, vrlean) = vresult
        .refinement
        .expect("descriptor refinement emitted (vault)");
    let von_disk =
        std::fs::read_to_string("../examples/lean/Generated/VaultDescriptorRefinement.lean")
            .expect("read VaultDescriptorRefinement.lean");
    assert_eq!(
        vrlean, von_disk,
        "VaultDescriptorRefinement.lean is out of sync with the qedlift descriptor \
         emitter (mechanically emitted, do not hand-edit)"
    );
}

/// Descriptor path with a NON-1 constant delta (`total += 5`): the first refinement
/// off the `+1` class. Same vault shape (IDL-resolved), but `op.add_const = 5`, so the
/// lift cleans the credit via `wrapAdd_const_of_lt` instead of `wrapAdd_one_of_lt`.
/// Pins that the arbitrary-literal path is mechanically emitted.
#[test]
fn descriptor_literal_delta_is_mechanically_emitted() {
    let desc = load_descriptor(std::path::Path::new(
        "tests/fixtures/vault_add5.descriptor.json",
    ))
    .expect("load vault_add5 descriptor");
    let idl: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string("tests/fixtures/vault.codama.json")
            .expect("read vault.codama.json"),
    )
    .expect("parse vault IDL");
    let so = std::path::Path::new("tests/fixtures/vault_add5.so");
    let ctx = load_binary(so).expect("load vault_add5.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse vault_add5.so");
    let result = lift_one_with_layouts(
        so,
        &ctx,
        &analysis,
        LiftRequest {
            module_override: Some("VaultAdd5".to_string()),
            idl: Some(&idl),
            descriptor: Some(&desc),
            ..LiftRequest::default()
        },
    )
    .expect("lift vault_add5.so via descriptor");
    let (_, rlean) = result
        .refinement
        .expect("descriptor refinement emitted (vault_add5)");
    let on_disk = std::fs::read_to_string("../examples/lean/Generated/VaultAdd5Refinement.lean")
        .expect("read VaultAdd5Refinement.lean");
    assert_eq!(
        rlean, on_disk,
        "VaultAdd5Refinement.lean is out of sync with the qedlift descriptor \
         emitter (mechanically emitted, do not hand-edit)"
    );
}

/// Descriptor path with a PARAMETER delta (`total += amount`, schema v2): the first
/// refinement with a runtime (non-constant) delta. The lift adds two memory reads,
/// cleaned by `wrapAdd_of_lt`; `op.add_param` matches the second read as the credited
/// amount and binds it in the `ensures`. Pins the parameter path is mechanically emitted.
#[test]
fn descriptor_param_delta_is_mechanically_emitted() {
    let desc = load_descriptor(std::path::Path::new(
        "tests/fixtures/vault_deposit.descriptor.json",
    ))
    .expect("load vault_deposit descriptor");
    let idl: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string("tests/fixtures/vault.codama.json")
            .expect("read vault.codama.json"),
    )
    .expect("parse vault IDL");
    let so = std::path::Path::new("tests/fixtures/vault_deposit.so");
    let ctx = load_binary(so).expect("load vault_deposit.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse vault_deposit.so");
    let result = lift_one_with_layouts(
        so,
        &ctx,
        &analysis,
        LiftRequest {
            module_override: Some("VaultDeposit".to_string()),
            idl: Some(&idl),
            descriptor: Some(&desc),
            ..LiftRequest::default()
        },
    )
    .expect("lift vault_deposit.so via descriptor");
    let (_, rlean) = result
        .refinement
        .expect("descriptor refinement emitted (vault_deposit)");
    let on_disk = std::fs::read_to_string("../examples/lean/Generated/VaultDepositRefinement.lean")
        .expect("read VaultDepositRefinement.lean");
    assert_eq!(
        rlean, on_disk,
        "VaultDepositRefinement.lean is out of sync with the qedlift descriptor \
         emitter (mechanically emitted, do not hand-edit)"
    );
}

/// The descriptor is a versioned cross-tool contract: a schema newer than this qedlift
/// understands must be refused fail-closed (mirrors `load_qedmeta`), never silently consumed.
#[test]
fn descriptor_rejects_newer_schema() {
    let err = load_descriptor(std::path::Path::new(
        "tests/fixtures/descriptor_future_schema.json",
    ))
    .expect_err("a future descriptor schema must be refused");
    assert!(
        err.to_string().contains("schema_version"),
        "fail-closed error should name the schema_version mismatch, got: {err}"
    );
}

/// Diffs the emitter output on `vault.so` + `vault.codama.json` against both on-disk artifacts, guarding the layout-general account-codec path.
#[test]
fn vault_refinement_is_mechanically_emitted() {
    let so = std::path::Path::new("tests/fixtures/vault.so");
    let idl: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string("tests/fixtures/vault.codama.json")
            .expect("read vault.codama.json"),
    )
    .expect("parse vault IDL");
    let ctx = load_binary(so).expect("load vault.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse vault.so");
    let result = lift_one(
        so,
        &ctx,
        &analysis,
        None,
        Some("Vault".to_string()),
        None,
        Some("VaultIncrement"),
        Some(&idl),
        None,
    )
    .expect("lift vault.so");

    let lift_on_disk = std::fs::read_to_string("../examples/lean/Generated/VaultTracedLifted.lean")
        .expect("read VaultTracedLifted.lean");
    assert_eq!(
        result.lean, lift_on_disk,
        "VaultTracedLifted.lean is out of sync with the qedlift emitter \
         (mechanically emitted, do not hand-edit)"
    );

    let (_, rlean) = result.refinement.expect("vault refinement emitted");
    let refine_on_disk = std::fs::read_to_string("../examples/lean/Generated/VaultRefinement.lean")
        .expect("read VaultRefinement.lean");
    assert_eq!(
        rlean, refine_on_disk,
        "VaultRefinement.lean is out of sync with the qedlift emitter \
         (mechanically emitted, do not hand-edit)"
    );
}

/// #41 loop closure: qedlift consumes qedrecover's emitted account layout. The vault
/// refinement *requires* a layout (it returns `None` without one), so it cleanly
/// distinguishes "layout consumed" from "fell back to a hardcoded default". Feeding the
/// layout through the sidecar channel (no `--idl`) must reproduce the IDL-derived
/// refinement exactly, and dropping every layout source must suppress the refinement.
#[test]
fn vault_refinement_consumes_sidecar_layout() {
    let so = std::path::Path::new("tests/fixtures/vault.so");
    let idl: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string("tests/fixtures/vault.codama.json")
            .expect("read vault.codama.json"),
    )
    .expect("parse vault IDL");
    let ctx = load_binary(so).expect("load vault.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse vault.so");

    // (a) IDL path — the existing, blessed behaviour.
    let via_idl = lift_one_with_layouts(
        so,
        &ctx,
        &analysis,
        LiftRequest {
            module_override: Some("Vault".to_string()),
            arm_name: Some("VaultIncrement"),
            idl: Some(&idl),
            ..LiftRequest::default()
        },
    )
    .expect("lift via idl");

    // (b) Sidecar path — layout supplied as qedrecover emits it; NO `--idl`.
    let layouts = vec![parse_account_layout(&idl, "vault").expect("vault layout")];
    let via_sidecar = lift_one_with_layouts(
        so,
        &ctx,
        &analysis,
        LiftRequest {
            module_override: Some("Vault".to_string()),
            arm_name: Some("VaultIncrement"),
            sidecar_layouts: Some(&layouts),
            ..LiftRequest::default()
        },
    )
    .expect("lift via sidecar");

    // (c) No layout source at all.
    let via_none = lift_one_with_layouts(
        so,
        &ctx,
        &analysis,
        LiftRequest {
            module_override: Some("Vault".to_string()),
            arm_name: Some("VaultIncrement"),
            ..LiftRequest::default()
        },
    )
    .expect("lift with no layout");

    assert_eq!(
        via_idl.refinement, via_sidecar.refinement,
        "sidecar-supplied layout must reproduce the IDL-derived vault refinement"
    );
    assert!(
        via_sidecar.refinement.is_some(),
        "sidecar layout must drive the vault refinement codegen"
    );
    assert!(
        via_none.refinement.is_none(),
        "vault refinement needs a layout source — the sidecar is what supplies it"
    );
}

/// The sidecar `[[account_layout]]` → `AccountLayout` converter is the exact inverse of
/// qedrecover's emitter (`kind` + `width_bytes` round-trip). Pins the SPL token/mint shapes.
#[test]
fn sidecar_account_layout_roundtrip() {
    let meta = load_qedmeta(std::path::Path::new(
        "tests/fixtures/p_token.transfer.recovered.qedmeta.toml",
    ))
    .expect("load recovered sidecar");
    let layouts = sidecar_account_layouts(&meta);

    let token = layouts
        .iter()
        .find(|l| l.name == "token")
        .expect("token layout");
    assert_eq!(token.size, 165);
    let f = |n: &str| token.fields.iter().find(|f| f.name == n).expect("field");
    assert_eq!(
        (f("mint").offset, f("mint").kind.clone()),
        (0, FieldKind::Pubkey)
    );
    assert_eq!(
        (f("amount").offset, f("amount").kind.clone()),
        (64, FieldKind::U64)
    );
    assert_eq!(
        (f("state").offset, f("state").kind.clone()),
        (108, FieldKind::Byte)
    );
    // opaque region keeps its width (`bytes` + `width_bytes` round-trip).
    assert_eq!(f("delegate").kind, FieldKind::Bytes(36));

    let mint = layouts
        .iter()
        .find(|l| l.name == "mint")
        .expect("mint account layout");
    let supply = mint
        .fields
        .iter()
        .find(|f| f.name == "supply")
        .expect("supply field");
    assert_eq!((supply.offset, supply.kind.clone()), (36, FieldKind::U64));
}

/// `vault.so` with a `[u8;32]` owner field: framed as opaque `.blob [.gap g]` (`↦Bytes`), exercising the `memBytesIs_segs` blob aggregation path.
#[test]
fn vault_blob_refinement_is_mechanically_emitted() {
    let so = std::path::Path::new("tests/fixtures/vault.so");
    let idl: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string("tests/fixtures/vault_blob.codama.json")
            .expect("read vault_blob.codama.json"),
    )
    .expect("parse vault_blob IDL");
    let ctx = load_binary(so).expect("load vault.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse vault.so");
    let result = lift_one(
        so,
        &ctx,
        &analysis,
        None,
        Some("VaultBlob".to_string()),
        None,
        Some("VaultIncrement"),
        Some(&idl),
        None,
    )
    .expect("lift vault.so (blob)");

    let lift_on_disk =
        std::fs::read_to_string("../examples/lean/Generated/VaultBlobTracedLifted.lean")
            .expect("read VaultBlobTracedLifted.lean");
    assert_eq!(
        result.lean, lift_on_disk,
        "VaultBlobTracedLifted.lean is out of sync with the qedlift emitter \
         (mechanically emitted, do not hand-edit)"
    );

    let (_, rlean) = result.refinement.expect("vault blob refinement emitted");
    let refine_on_disk =
        std::fs::read_to_string("../examples/lean/Generated/VaultBlobRefinement.lean")
            .expect("read VaultBlobRefinement.lean");
    assert_eq!(
        rlean, refine_on_disk,
        "VaultBlobRefinement.lean is out of sync with the qedlift emitter \
         (mechanically emitted, do not hand-edit)"
    );
}

/// `vault_split.so` owns `owner[5]`, forcing the blob to split into `[.gap, .byte, .gap]` — the multisig-style partial-blob path.
#[test]
fn vault_split_refinement_is_mechanically_emitted() {
    let so = std::path::Path::new("tests/fixtures/vault_split.so");
    let idl: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string("tests/fixtures/vault_blob.codama.json")
            .expect("read vault_blob.codama.json"),
    )
    .expect("parse vault_blob IDL");
    let ctx = load_binary(so).expect("load vault_split.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse vault_split.so");
    let result = lift_one(
        so,
        &ctx,
        &analysis,
        None,
        Some("VaultSplit".to_string()),
        None,
        Some("VaultIncrement"),
        Some(&idl),
        None,
    )
    .expect("lift vault_split.so");

    let lift_path = "../examples/lean/Generated/VaultSplitTracedLifted.lean";
    let refine_path = "../examples/lean/Generated/VaultSplitRefinement.lean";
    if std::env::var("QEDLIFT_BLESS").is_ok() {
        std::fs::write(lift_path, &result.lean).expect("write lift");
        if let Some((_, rlean)) = result.refinement.as_ref() {
            std::fs::write(refine_path, rlean).expect("write refinement");
        }
    }
    assert_eq!(
        result.lean,
        std::fs::read_to_string(lift_path).expect("read lift"),
        "VaultSplitTracedLifted.lean is out of sync with the qedlift emitter"
    );
    let (_, rlean) = result.refinement.expect("vault split refinement emitted");
    assert_eq!(
        rlean,
        std::fs::read_to_string(refine_path).expect("read refinement"),
        "VaultSplitRefinement.lean is out of sync with the qedlift emitter"
    );
}

/// Guards the heap-corollary codegen: `heapBumpPtr`/`heapBlockU64` fold + conditional `HeapSL` import.
#[test]
fn heap_alloc_lift_is_mechanically_emitted() {
    let so = std::path::Path::new("tests/fixtures/heap_alloc.so");
    let ctx = load_binary(so).expect("load heap_alloc.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse heap_alloc.so");
    let result = lift_one(
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
    .expect("lift heap_alloc.so");

    let on_disk = std::fs::read_to_string("../examples/lean/Generated/HeapAllocLifted.lean")
        .expect("read HeapAllocLifted.lean");
    assert_eq!(
        result.lean, on_disk,
        "HeapAllocLifted.lean is out of sync with the qedlift emitter \
         (mechanically emitted, do not hand-edit)"
    );
}

/// Pins the typed-fault corollary emitter (Phase 7 sub-item 3): a happy
/// path ending in `.call .abort`. Beyond the running-prefix
/// `cuTripleWithinMem`, the lift emits `AbortCaller_fault_correct`
/// (`cuTripleFaultsWithinMem … .abort`), composing the prefix with
/// `call_abort_faults_spec` via `cuTripleWithinMem_seq_fault_pure`. Static
/// lift (the abort terminates the straight-line walk; no trace needed).
#[test]
fn abort_caller_fault_lift_is_mechanically_emitted() {
    let so = std::path::Path::new("tests/fixtures/abort_caller.so");
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

    let path = "../examples/lean/Generated/AbortCallerLifted.lean";
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
    let so = std::path::Path::new("tests/fixtures/oob_secp256k1.so");
    let ctx = load_binary(so).expect("load oob_secp256k1.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse oob_secp256k1.so");
    let trace = load_trace(std::path::Path::new("tests/fixtures/oob_secp256k1.pcs"))
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

    let path = "../examples/lean/Generated/OobSecp256k1Lifted.lean";
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
    let so = std::path::Path::new("tests/fixtures/oob_clock_sysvar.so");
    let ctx = load_binary(so).expect("load oob_clock_sysvar.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse oob_clock_sysvar.so");
    let trace = load_trace(std::path::Path::new("tests/fixtures/oob_clock_sysvar.pcs"))
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

    let path = "../examples/lean/Generated/OobClockSysvarLifted.lean";
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
    let so = std::path::Path::new("tests/fixtures/oob_rent_sysvar.so");
    let ctx = load_binary(so).expect("load oob_rent_sysvar.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse oob_rent_sysvar.so");
    let trace = load_trace(std::path::Path::new("tests/fixtures/oob_rent_sysvar.pcs"))
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

    let path = "../examples/lean/Generated/OobRentSysvarLifted.lean";
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
    let so = std::path::Path::new("tests/fixtures/oob_set_return_data.so");
    let ctx = load_binary(so).expect("load oob_set_return_data.so");
    let analysis =
        Analysis::from_executable(&ctx.executable).expect("analyse oob_set_return_data.so");
    let trace = load_trace(std::path::Path::new(
        "tests/fixtures/oob_set_return_data.pcs",
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

    let path = "../examples/lean/Generated/OobSetReturnDataLifted.lean";
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
    let so = std::path::Path::new("tests/fixtures/oob_create_pda.so");
    let ctx = load_binary(so).expect("load oob_create_pda.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse oob_create_pda.so");
    let trace = load_trace(std::path::Path::new("tests/fixtures/oob_create_pda.pcs"))
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

    let path = "../examples/lean/Generated/OobCreatePdaLifted.lean";
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
    let so = std::path::Path::new("tests/fixtures/oob_sha256.so");
    let ctx = load_binary(so).expect("load oob_sha256.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse oob_sha256.so");
    let trace = load_trace(std::path::Path::new("tests/fixtures/oob_sha256.pcs"))
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

    let path = "../examples/lean/Generated/OobSha256Lifted.lean";
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

/// Pins the p-token Transfer ERROR-PATH lift (pattern library Layer 3,
/// ENFORCES direction): from an insufficient-balance pre (the violated
/// check surfaces as the taken-`jlt` branch hypothesis), the real bytecode
/// runs dispatch → checks → error handler → TokenError logging → the
/// ProgramError encoder → the shared exit, with the account cells
/// untouched and r0 = the error code. The happy-path arm REQUIRES the
/// check; this lift proves the program ENFORCES it.
#[test]
fn p_token_transfer_insufficient_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_transfer_insufficient.pcs",
        "PTokenTransferInsufficient",
        None,
        "../examples/lean/Generated/PTokenTransferInsufficientLifted.lean",
        None,
    );
}

/// Pins the p-token Transfer FROZEN-SOURCE error-path lift (pattern
/// library Layer 3, ENFORCES direction for the frozen check): the taken
/// `jeq state, 2` diverts to the same error handler with
/// TokenError::AccountFrozen (17) in r7 → r0 at the shared exit.
#[test]
fn p_token_transfer_frozen_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_transfer_frozen.pcs",
        "PTokenTransferFrozen",
        None,
        "../examples/lean/Generated/PTokenTransferFrozenLifted.lean",
        None,
    );
}

/// Pins the p-token Transfer FROZEN-DEST error-path lift: the sibling of
/// the frozen-source lift, one `jeq` later (pc 4012, `jeq r5, 2`), same
/// error handler, TokenError::AccountFrozen (17) at the shared exit.
#[test]
fn p_token_transfer_dest_frozen_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_transfer_dest_frozen.pcs",
        "PTokenTransferDestFrozen",
        None,
        "../examples/lean/Generated/PTokenTransferDestFrozenLifted.lean",
        None,
    );
}

/// Pins the p-token Transfer MINT-MISMATCH error-path lift: the mint
/// compare's first dword limb (`jne` at pc 4019, src mint limb0 vs dest
/// mint limb0) diverts through pc 4724 to the error handler,
/// TokenError::MintMismatch (3) at the shared exit. The first
/// pubkey-INEQUALITY lift; the trace exercises limb 0 (the fixture mints
/// differ in their first 8 bytes).
#[test]
fn p_token_transfer_mint_mismatch_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_transfer_mint_mismatch.pcs",
        "PTokenTransferMintMismatch",
        None,
        "../examples/lean/Generated/PTokenTransferMintMismatchLifted.lean",
        None,
    );
}

/// Pins the batch-2 p-token Transfer ERROR-PATH lifts (pattern library
/// Layer 3, ENFORCES direction) — all violating traces of the same
/// Transfer dispatch window, each diverting at a different check:
/// uninitialized src/dest (jeq state,0 at 4005/4008 → the 5080
/// UninitializedAccount path), invalid state byte src/dest (jgt state,2
/// at 4004/4007 → 4725 with the ProgramError::InvalidAccountData
/// encoding r6=3), short instruction data (jlt ix_len,9 at 3998 → the
/// 312 hub, TokenError::InvalidInstruction 12), and the mint-compare
/// limbs 1-3 (the jne at 4022/4025/4028 → 4724, MintMismatch 3 —
/// completing pubkey inequality alongside the limb-0 lift).
#[test]
fn p_token_transfer_src_uninit_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_transfer_src_uninit.pcs",
        "PTokenTransferSrcUninit",
        None,
        "../examples/lean/Generated/PTokenTransferSrcUninitLifted.lean",
        None,
    );
}

#[test]
fn p_token_transfer_dest_uninit_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_transfer_dest_uninit.pcs",
        "PTokenTransferDestUninit",
        None,
        "../examples/lean/Generated/PTokenTransferDestUninitLifted.lean",
        None,
    );
}

#[test]
fn p_token_transfer_src_bad_state_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_transfer_src_bad_state.pcs",
        "PTokenTransferSrcBadState",
        None,
        "../examples/lean/Generated/PTokenTransferSrcBadStateLifted.lean",
        None,
    );
}

#[test]
fn p_token_transfer_dest_bad_state_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_transfer_dest_bad_state.pcs",
        "PTokenTransferDestBadState",
        None,
        "../examples/lean/Generated/PTokenTransferDestBadStateLifted.lean",
        None,
    );
}

#[test]
fn p_token_transfer_short_ix_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_transfer_short_ix.pcs",
        "PTokenTransferShortIx",
        None,
        "../examples/lean/Generated/PTokenTransferShortIxLifted.lean",
        None,
    );
}

#[test]
fn p_token_transfer_mint_mismatch_limb1_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_transfer_mint_mismatch_limb1.pcs",
        "PTokenTransferMintMismatchLimb1",
        None,
        "../examples/lean/Generated/PTokenTransferMintMismatchLimb1Lifted.lean",
        None,
    );
}

#[test]
fn p_token_transfer_mint_mismatch_limb2_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_transfer_mint_mismatch_limb2.pcs",
        "PTokenTransferMintMismatchLimb2",
        None,
        "../examples/lean/Generated/PTokenTransferMintMismatchLimb2Lifted.lean",
        None,
    );
}

#[test]
fn p_token_transfer_mint_mismatch_limb3_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_transfer_mint_mismatch_limb3.pcs",
        "PTokenTransferMintMismatchLimb3",
        None,
        "../examples/lean/Generated/PTokenTransferMintMismatchLimb3Lifted.lean",
        None,
    );
}

/// Pins the batch-3 p-token Transfer ERROR-PATH lifts: the authority
/// tri-case (owner-but-not-signer and delegate-but-not-signer →
/// ProgramError::MissingRequiredSignature 8<<32; neither owner nor
/// delegate → TokenError::OwnerMismatch 4) plus the delegated-amount
/// allowance check (delegate signs but allowance < amount →
/// TokenError::InsufficientFunds 1, a distinct check from the
/// source-balance one). Together these close the deferred "signer guard"
/// item honestly: each leg's violation is a separate EnforcedError, so
/// the delegate alternative is modeled instead of over-promised away.
#[test]
fn p_token_transfer_owner_not_signer_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_transfer_owner_not_signer.pcs",
        "PTokenTransferOwnerNotSigner",
        None,
        "../examples/lean/Generated/PTokenTransferOwnerNotSignerLifted.lean",
        None,
    );
}

#[test]
fn p_token_transfer_delegate_not_signer_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_transfer_delegate_not_signer.pcs",
        "PTokenTransferDelegateNotSigner",
        None,
        "../examples/lean/Generated/PTokenTransferDelegateNotSignerLifted.lean",
        None,
    );
}

#[test]
fn p_token_transfer_owner_mismatch_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_transfer_owner_mismatch.pcs",
        "PTokenTransferOwnerMismatch",
        None,
        "../examples/lean/Generated/PTokenTransferOwnerMismatchLifted.lean",
        None,
    );
}

#[test]
fn p_token_transfer_delegate_insufficient_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_transfer_delegate_insufficient.pcs",
        "PTokenTransferDelegateInsufficient",
        None,
        "../examples/lean/Generated/PTokenTransferDelegateInsufficientLifted.lean",
        None,
    );
}

/// Pins the fan-out p-token ERROR-PATH lifts (pattern library Layer 3,
/// ENFORCES direction) across the MintTo / Burn / TransferChecked /
/// CloseAccount arms. Headline: MintTo supply-overflow IS enforced
/// (TokenError::Overflow 14) — the invariant the absent Transfer
/// dest-overflow check leans on, so both sides of the supply invariant
/// are in the catalog. Others: MintTo fixed-supply (5), MintTo
/// authority-mismatch (4), MintTo mint-mismatch (3), MintTo dest-frozen
/// (17), Burn insufficient (1), Burn frozen (17), TransferChecked
/// decimals-mismatch (18) + explicit-mint mismatch (3), CloseAccount
/// nonzero balance (11).
#[test]
fn p_token_mint_to_supply_overflow_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_mint_to_supply_overflow.pcs",
        "PTokenMintToSupplyOverflow",
        None,
        "../examples/lean/Generated/PTokenMintToSupplyOverflowLifted.lean",
        None,
    );
}

#[test]
fn p_token_mint_to_fixed_supply_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_mint_to_fixed_supply.pcs",
        "PTokenMintToFixedSupply",
        None,
        "../examples/lean/Generated/PTokenMintToFixedSupplyLifted.lean",
        None,
    );
}

#[test]
fn p_token_mint_to_authority_mismatch_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_mint_to_authority_mismatch.pcs",
        "PTokenMintToAuthorityMismatch",
        None,
        "../examples/lean/Generated/PTokenMintToAuthorityMismatchLifted.lean",
        None,
    );
}

#[test]
fn p_token_mint_to_mint_mismatch_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_mint_to_mint_mismatch.pcs",
        "PTokenMintToMintMismatch",
        None,
        "../examples/lean/Generated/PTokenMintToMintMismatchLifted.lean",
        None,
    );
}

#[test]
fn p_token_mint_to_dest_frozen_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_mint_to_dest_frozen.pcs",
        "PTokenMintToDestFrozen",
        None,
        "../examples/lean/Generated/PTokenMintToDestFrozenLifted.lean",
        None,
    );
}

#[test]
fn p_token_burn_insufficient_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_burn_insufficient.pcs",
        "PTokenBurnInsufficient",
        None,
        "../examples/lean/Generated/PTokenBurnInsufficientLifted.lean",
        None,
    );
}

#[test]
fn p_token_burn_frozen_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_burn_frozen.pcs",
        "PTokenBurnFrozen",
        None,
        "../examples/lean/Generated/PTokenBurnFrozenLifted.lean",
        None,
    );
}

#[test]
fn p_token_transfer_checked_decimals_mismatch_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_transfer_checked_decimals_mismatch.pcs",
        "PTokenTransferCheckedDecimalsMismatch",
        None,
        "../examples/lean/Generated/PTokenTransferCheckedDecimalsMismatchLifted.lean",
        None,
    );
}

#[test]
fn p_token_transfer_checked_mint_mismatch_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_transfer_checked_mint_mismatch.pcs",
        "PTokenTransferCheckedMintMismatch",
        None,
        "../examples/lean/Generated/PTokenTransferCheckedMintMismatchLifted.lean",
        None,
    );
}

#[test]
fn p_token_close_account_nonzero_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_close_account_nonzero.pcs",
        "PTokenCloseAccountNonzero",
        None,
        "../examples/lean/Generated/PTokenCloseAccountNonzeroLifted.lean",
        None,
    );
}

/// Pins the batch-5 p-token ERROR-PATH lifts across the Approve /
/// Revoke / SetAuthority / FreezeAccount / ThawAccount arms: approve
/// frozen (17) + owner-mismatch (4), revoke frozen (17) +
/// owner-mismatch (4), set-authority owner-mismatch (4) + unsupported
/// authority type (15), freeze on a no-freeze-authority mint (16) +
/// freeze-authority mismatch (4) + already-frozen (13), thaw
/// not-frozen (13).
#[test]
fn p_token_approve_frozen_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_approve_frozen.pcs",
        "PTokenApproveFrozen",
        None,
        "../examples/lean/Generated/PTokenApproveFrozenLifted.lean",
        None,
    );
}

#[test]
fn p_token_approve_owner_mismatch_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_approve_owner_mismatch.pcs",
        "PTokenApproveOwnerMismatch",
        None,
        "../examples/lean/Generated/PTokenApproveOwnerMismatchLifted.lean",
        None,
    );
}

#[test]
fn p_token_revoke_frozen_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_revoke_frozen.pcs",
        "PTokenRevokeFrozen",
        None,
        "../examples/lean/Generated/PTokenRevokeFrozenLifted.lean",
        None,
    );
}

#[test]
fn p_token_revoke_owner_mismatch_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_revoke_owner_mismatch.pcs",
        "PTokenRevokeOwnerMismatch",
        None,
        "../examples/lean/Generated/PTokenRevokeOwnerMismatchLifted.lean",
        None,
    );
}

#[test]
fn p_token_set_authority_owner_mismatch_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_set_authority_owner_mismatch.pcs",
        "PTokenSetAuthorityOwnerMismatch",
        None,
        "../examples/lean/Generated/PTokenSetAuthorityOwnerMismatchLifted.lean",
        None,
    );
}

#[test]
fn p_token_set_authority_bad_type_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_set_authority_bad_type.pcs",
        "PTokenSetAuthorityBadType",
        None,
        "../examples/lean/Generated/PTokenSetAuthorityBadTypeLifted.lean",
        None,
    );
}

#[test]
fn p_token_freeze_cannot_freeze_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_freeze_cannot_freeze.pcs",
        "PTokenFreezeCannotFreeze",
        None,
        "../examples/lean/Generated/PTokenFreezeCannotFreezeLifted.lean",
        None,
    );
}

#[test]
fn p_token_freeze_authority_mismatch_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_freeze_authority_mismatch.pcs",
        "PTokenFreezeAuthorityMismatch",
        None,
        "../examples/lean/Generated/PTokenFreezeAuthorityMismatchLifted.lean",
        None,
    );
}

#[test]
fn p_token_freeze_already_frozen_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_freeze_already_frozen.pcs",
        "PTokenFreezeAlreadyFrozen",
        None,
        "../examples/lean/Generated/PTokenFreezeAlreadyFrozenLifted.lean",
        None,
    );
}

#[test]
fn p_token_thaw_not_frozen_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_thaw_not_frozen.pcs",
        "PTokenThawNotFrozen",
        None,
        "../examples/lean/Generated/PTokenThawNotFrozenLifted.lean",
        None,
    );
}

/// Pins the `sol_memcpy_` happy-path lift (`call_sol_memcpy_spec`): two
/// `↦Bytes` atoms (src readable, dst writable), dst blob ← src, r0 := 0.
/// Trace-driven (syscall dispatch only fires on a trace).
#[test]
fn memcpy_lift_is_mechanically_emitted() {
    let so = std::path::Path::new("tests/fixtures/memcpy_caller.so");
    let ctx = load_binary(so).expect("load memcpy_caller.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse memcpy_caller.so");
    let trace = load_trace(std::path::Path::new("tests/fixtures/memcpy_caller.pcs"))
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

    let path = "../examples/lean/Generated/MemcpyLifted.lean";
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
    let so = std::path::Path::new("tests/fixtures/sha256_caller.so");
    let ctx = load_binary(so).expect("load sha256_caller.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse sha256_caller.so");
    let trace = load_trace(std::path::Path::new("tests/fixtures/sha256_caller.pcs"))
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

    let path = "../examples/lean/Generated/Sha256CallerLifted.lean";
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
    let so = std::path::Path::new("tests/fixtures/pda_create.so");
    let ctx = load_binary(so).expect("load pda_create.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse pda_create.so");
    let trace = load_trace(std::path::Path::new("tests/fixtures/pda_create.pcs"))
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

    let path = "../examples/lean/Generated/PdaCreateLifted.lean";
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
    let so = std::path::Path::new("tests/fixtures/memmove_caller.so");
    let ctx = load_binary(so).expect("load memmove_caller.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse memmove_caller.so");
    let trace = load_trace(std::path::Path::new("tests/fixtures/memmove_caller.pcs"))
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

    let path = "../examples/lean/Generated/MemmoveLifted.lean";
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
    let so = std::path::Path::new("tests/fixtures/memcmp_caller.so");
    let ctx = load_binary(so).expect("load memcmp_caller.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse memcmp_caller.so");
    let trace = load_trace(std::path::Path::new("tests/fixtures/memcmp_caller.pcs"))
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

    let path = "../examples/lean/Generated/MemcmpLifted.lean";
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
    let so = std::path::Path::new("tests/fixtures/set_return_data_caller.so");
    let ctx = load_binary(so).expect("load set_return_data_caller.so");
    let analysis =
        Analysis::from_executable(&ctx.executable).expect("analyse set_return_data_caller.so");
    let trace = load_trace(std::path::Path::new(
        "tests/fixtures/set_return_data_caller.pcs",
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

    let path = "../examples/lean/Generated/SetReturnDataLifted.lean";
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

/// Pins ldxh/stxh and ST_H_IMM (`sth_spec`) on real cargo-build-sbf bytecode.
#[test]
fn halfword_store_lift_is_mechanically_emitted() {
    let so = std::path::Path::new("tests/fixtures/halfword_store.so");
    let ctx = load_binary(so).expect("load halfword_store.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse halfword_store.so");
    let result = lift_one(
        so,
        &ctx,
        &analysis,
        None,
        Some("HalfwordStore".to_string()),
        None,
        None,
        None,
        None,
    )
    .expect("lift halfword_store.so");

    let on_disk = std::fs::read_to_string("../examples/lean/Generated/HalfwordStoreLifted.lean")
        .expect("read HalfwordStoreLifted.lean");
    assert_eq!(
        result.lean, on_disk,
        "HalfwordStoreLifted.lean is out of sync with the qedlift emitter \
         (mechanically emitted, do not hand-edit)"
    );
}

/// The real p_token sidecar's `arm_entry_pc` must parse as logical 304 (#41: the formerly-dropped `[instruction.recovered]` is now consumed).
#[test]
fn qedmeta_recovered_arm_is_parsed() {
    let meta = load_qedmeta(std::path::Path::new("tests/fixtures/p_token.qedmeta.toml"))
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
    let so = std::path::Path::new("tests/fixtures/p_token.so");
    let ctx = load_binary(so).expect("load p_token.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse p_token.so");
    let trace = load_trace(std::path::Path::new("tests/fixtures/p_token_transfer.pcs"))
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
        std::fs::read_to_string("../examples/lean/Generated/PTokenTransferTracedLifted.lean")
            .expect("read PTokenTransferTracedLifted.lean");
    assert_eq!(
        result.lean, on_disk,
        "consuming arm_entry perturbed the trace-guided transfer lift"
    );
}

/// A recovered arm_entry_pc not on the execution trace must be rejected, not silently lifted against the wrong arm.
#[test]
fn qedmeta_arm_entry_off_trace_is_rejected() {
    let so = std::path::Path::new("tests/fixtures/p_token.so");
    let ctx = load_binary(so).expect("load p_token.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse p_token.so");
    let trace = load_trace(std::path::Path::new("tests/fixtures/p_token_transfer.pcs"))
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
    let so = std::path::Path::new("tests/fixtures/heap_alloc.so");
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

/// Re-emit one p_token arm and diff lift + refinement against on-disk artifacts. Every arm is pinned: H8 vacuity shipped unnoticed without these pins.
fn pin_p_token_arm(
    pcs: &str,
    module: &str,
    arm: Option<&str>,
    lift_path: &str,
    refine_path: Option<&str>,
) {
    let so = std::path::Path::new("tests/fixtures/p_token.so");
    let ctx = load_binary(so).expect("load p_token.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse p_token.so");
    let trace = load_trace(std::path::Path::new(pcs)).expect("load trace");
    // All p_token arms share the binary → shared-text dedup: the arm imports
    // `Generated.PTokenText` instead of re-embedding the ~100KB `.text`.
    let result = lift_one_with_layouts(
        so,
        &ctx,
        &analysis,
        LiftRequest {
            module_override: Some(module.to_string()),
            trace: Some(&trace),
            arm_name: arm,
            shared_text: Some("PToken"),
            ..LiftRequest::default()
        },
    )
    .expect("lift p_token arm");

    // QEDLIFT_BLESS=1 re-blesses artifacts after an intentional emitter change.
    if std::env::var("QEDLIFT_BLESS").is_ok() {
        std::fs::write(lift_path, &result.lean).expect("write lift");
        if let (Some(rp), Some((_, rlean))) = (refine_path, result.refinement.as_ref()) {
            std::fs::write(rp, rlean).expect("write refinement");
        }
    }
    let on_disk = std::fs::read_to_string(lift_path).expect("read lift");
    assert_eq!(
        result.lean, on_disk,
        "{lift_path} is out of sync with the qedlift emitter \
         (mechanically emitted, do not hand-edit)"
    );
    if let Some(rp) = refine_path {
        let (_, rlean) = result.refinement.expect("refinement emitted");
        let r_on_disk = std::fs::read_to_string(rp).expect("read refinement");
        assert_eq!(
            rlean, r_on_disk,
            "{rp} is out of sync with the qedlift refinement codegen \
             (mechanically emitted, do not hand-edit)"
        );
    }

    // The shared `.text` module is generated output too: every arm pin also
    // pins `Generated/PTokenText.lean` (identical for all arms of the binary).
    let (smod, slean) = result.shared_text.expect("shared text module emitted");
    assert_eq!(smod, "PTokenText");
    let spath = "../examples/lean/Generated/PTokenText.lean";
    if std::env::var("QEDLIFT_BLESS").is_ok() {
        std::fs::write(spath, &slean).expect("write shared text module");
    }
    let s_on_disk = std::fs::read_to_string(spath).expect("read shared text module");
    assert_eq!(
        slean, s_on_disk,
        "{spath} is out of sync with the qedlift shared-text emitter \
         (mechanically emitted, do not hand-edit)"
    );
}

#[test]
fn p_token_transfer_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_transfer.pcs",
        "PTokenTransfer",
        Some("Transfer"),
        "../examples/lean/Generated/PTokenTransferTracedLifted.lean",
        Some("../examples/lean/PToken/TransferRefinement.lean"),
    );
}

#[test]
fn p_token_transfer_checked_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_transfer_checked.pcs",
        "PTokenTransferChecked",
        Some("TransferChecked"),
        "../examples/lean/Generated/PTokenTransferCheckedTracedLifted.lean",
        Some("../examples/lean/PToken/TransferCheckedRefinement.lean"),
    );
}

/// Regenerated 2026-06-12 after H8: Phase A canonical aliasing (r10 spills) + Phase B byte demotion (`ldxdw_bytes_spec`).
#[test]
fn p_token_mint_to_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_mint_to.pcs",
        "PTokenMintTo",
        Some("MintTo"),
        "../examples/lean/Generated/PTokenMintToTracedLifted.lean",
        Some("../examples/lean/PToken/MintToRefinement.lean"),
    );
}

/// Regenerated 2026-06-12 after H8 Phase C-1: pre-split memset specs (`↦U64` cells; blob never overlaps).
#[test]
fn p_token_close_account_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_close_account.pcs",
        "PTokenCloseAccount",
        None,
        "../examples/lean/Generated/PTokenCloseAccountTracedLifted.lean",
        None,
    );
}

/// Full H8 gauntlet: `sol_get_sysvar` (cells17), stw tail-zeroing (byte demotion), rent dword read. Trace re-captured under H7-faithful VM.
#[test]
fn p_token_initialize_mint2_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_initialize_mint2.pcs",
        "PTokenInitializeMint2",
        None,
        "../examples/lean/Generated/PTokenInitializeMint2TracedLifted.lean",
        None,
    );
}

#[test]
fn p_token_burn_is_mechanically_emitted() {
    pin_p_token_arm(
        "tests/fixtures/p_token_burn.pcs",
        "PTokenBurn",
        Some("Burn"),
        "../examples/lean/Generated/PTokenBurnTracedLifted.lean",
        Some("../examples/lean/PToken/BurnRefinement.lean"),
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
    let so = std::path::Path::new("tests/fixtures/cpi_envelope_caller.so");
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
    let path = "../examples/lean/Generated/CpiEnvelopeCallerLifted.lean";
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

/// #40 OOB-fault-path variant: guarded_oob's guard-fail path performs an
/// out-of-bounds `sol_get_clock_sysvar` write, so its path corollary is
/// an `AsmRefinesTransitionFault … .accessViolation` composed via the
/// Mem-Mem `cuTripleWithinMem_seq_fault` (combined rr = prefix ∧ OOB).
#[test]
fn guarded_oob_transition_is_mechanically_emitted() {
    let so = std::path::Path::new("tests/fixtures/guarded_oob.so");
    let ctx = load_binary(so).expect("load guarded_oob.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse guarded_oob.so");
    let desc = load_descriptor(std::path::Path::new(
        "tests/fixtures/guarded_oob.descriptor.json",
    ))
    .expect("descriptor");
    let (paths, (bmod, blean)) =
        run_transition(so, &ctx, &analysis, &desc, None).expect("transition emission");
    assert_eq!(paths.len(), 2, "expected the oob + success paths");
    let mut artifacts: Vec<(String, String)> = paths
        .iter()
        .map(|(m, l)| {
            (
                format!("../examples/lean/Generated/{}Lifted.lean", m),
                l.clone(),
            )
        })
        .collect();
    artifacts.push((format!("../examples/lean/Generated/{}.lean", bmod), blean));
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
    let so = std::path::Path::new("tests/fixtures/guarded_abort.so");
    let ctx = load_binary(so).expect("load guarded_abort.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse guarded_abort.so");
    let desc = load_descriptor(std::path::Path::new(
        "tests/fixtures/guarded_abort.descriptor.json",
    ))
    .expect("descriptor");
    let (paths, (bmod, blean)) =
        run_transition(so, &ctx, &analysis, &desc, None).expect("transition emission");
    assert_eq!(paths.len(), 2, "expected the panic + success paths");
    let mut artifacts: Vec<(String, String)> = paths
        .iter()
        .map(|(m, l)| {
            (
                format!("../examples/lean/Generated/{}Lifted.lean", m),
                l.clone(),
            )
        })
        .collect();
    artifacts.push((format!("../examples/lean/Generated/{}.lean", bmod), blean));
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
    let so = std::path::Path::new("tests/fixtures/guarded_counter.so");
    let ctx = load_binary(so).expect("load guarded_counter.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse guarded_counter.so");
    let desc = load_descriptor(std::path::Path::new(
        "tests/fixtures/guarded_counter.descriptor.json",
    ))
    .expect("descriptor");
    let (paths, (bmod, blean)) =
        run_transition(so, &ctx, &analysis, &desc, None).expect("transition emission");
    assert_eq!(paths.len(), 2, "expected the abort + success paths");
    let mut artifacts: Vec<(String, String)> = paths
        .iter()
        .map(|(m, l)| {
            (
                format!("../examples/lean/Generated/{}Lifted.lean", m),
                l.clone(),
            )
        })
        .collect();
    artifacts.push((format!("../examples/lean/Generated/{}.lean", bmod), blean));
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
