use super::super::*;
use qed_analysis::layout::{parse_account_layout, FieldKind};

/// Diffs the emitter output on `counter.so` against both on-disk artifacts, guarding the counter-codec (non-token) path.
#[test]
fn counter_refinement_is_mechanically_emitted() {
    let so = std::path::Path::new("../tests/fixtures/counter.so");
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
        std::fs::read_to_string("../../examples/lean/Generated/CounterTracedLifted.lean")
            .expect("read CounterTracedLifted.lean");
    assert_eq!(
        result.lean, lift_on_disk,
        "CounterTracedLifted.lean is out of sync with the qedlift emitter \
         (mechanically emitted, do not hand-edit)"
    );

    let (_, rlean) = result.refinement.expect("counter refinement emitted");
    let refine_on_disk =
        std::fs::read_to_string("../../examples/lean/Generated/CounterRefinement.lean")
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
        "../tests/fixtures/counter.descriptor.json",
    ))
    .expect("load counter descriptor");
    let so = std::path::Path::new("../tests/fixtures/counter.so");
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
        std::fs::read_to_string("../../examples/lean/Generated/CounterDescriptorRefinement.lean")
            .expect("read CounterDescriptorRefinement.lean");
    assert_eq!(
        rlean, on_disk,
        "CounterDescriptorRefinement.lean is out of sync with the qedlift descriptor \
         emitter (mechanically emitted, do not hand-edit)"
    );

    // (b) vault.so — multi-field {owner:Pubkey, total:u64, bump:u8}; `total` mutated.
    // Name-level descriptor (no inline layout, no registry entry): the shape is resolved
    // from the IDL by account name, exactly the path `resolve_layout` uses.
    let vdesc = load_descriptor(std::path::Path::new(
        "../tests/fixtures/vault.descriptor.json",
    ))
    .expect("load vault descriptor");
    let vidl: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string("../tests/fixtures/vault.codama.json")
            .expect("read vault.codama.json"),
    )
    .expect("parse vault IDL");
    let vso = std::path::Path::new("../tests/fixtures/vault.so");
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
        std::fs::read_to_string("../../examples/lean/Generated/VaultDescriptorRefinement.lean")
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
        "../tests/fixtures/vault_add5.descriptor.json",
    ))
    .expect("load vault_add5 descriptor");
    let idl: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string("../tests/fixtures/vault.codama.json")
            .expect("read vault.codama.json"),
    )
    .expect("parse vault IDL");
    let so = std::path::Path::new("../tests/fixtures/vault_add5.so");
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
    let on_disk = std::fs::read_to_string("../../examples/lean/Generated/VaultAdd5Refinement.lean")
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
        "../tests/fixtures/vault_deposit.descriptor.json",
    ))
    .expect("load vault_deposit descriptor");
    let idl: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string("../tests/fixtures/vault.codama.json")
            .expect("read vault.codama.json"),
    )
    .expect("parse vault IDL");
    let so = std::path::Path::new("../tests/fixtures/vault_deposit.so");
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
    let on_disk =
        std::fs::read_to_string("../../examples/lean/Generated/VaultDepositRefinement.lean")
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
        "../tests/fixtures/descriptor_future_schema.json",
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
    let so = std::path::Path::new("../tests/fixtures/vault.so");
    let idl: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string("../tests/fixtures/vault.codama.json")
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

    let lift_on_disk =
        std::fs::read_to_string("../../examples/lean/Generated/VaultTracedLifted.lean")
            .expect("read VaultTracedLifted.lean");
    assert_eq!(
        result.lean, lift_on_disk,
        "VaultTracedLifted.lean is out of sync with the qedlift emitter \
         (mechanically emitted, do not hand-edit)"
    );

    let (_, rlean) = result.refinement.expect("vault refinement emitted");
    let refine_on_disk =
        std::fs::read_to_string("../../examples/lean/Generated/VaultRefinement.lean")
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
    let so = std::path::Path::new("../tests/fixtures/vault.so");
    let idl: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string("../tests/fixtures/vault.codama.json")
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
        "../tests/fixtures/p_token.transfer.recovered.qedmeta.toml",
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
    let so = std::path::Path::new("../tests/fixtures/vault.so");
    let idl: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string("../tests/fixtures/vault_blob.codama.json")
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
        std::fs::read_to_string("../../examples/lean/Generated/VaultBlobTracedLifted.lean")
            .expect("read VaultBlobTracedLifted.lean");
    assert_eq!(
        result.lean, lift_on_disk,
        "VaultBlobTracedLifted.lean is out of sync with the qedlift emitter \
         (mechanically emitted, do not hand-edit)"
    );

    let (_, rlean) = result.refinement.expect("vault blob refinement emitted");
    let refine_on_disk =
        std::fs::read_to_string("../../examples/lean/Generated/VaultBlobRefinement.lean")
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
    let so = std::path::Path::new("../tests/fixtures/vault_split.so");
    let idl: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string("../tests/fixtures/vault_blob.codama.json")
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

    let lift_path = "../../examples/lean/Generated/VaultSplitTracedLifted.lean";
    let refine_path = "../../examples/lean/Generated/VaultSplitRefinement.lean";
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
