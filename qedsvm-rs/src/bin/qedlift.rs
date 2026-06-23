//! qedlift — takes a compiled `.so`, symbolically executes the decoded eBPF,
//! and emits a Lean `cuTripleWithinMem` Hoare triple with pre/post conditions
//! derived from the execution, discharged by `sl_block_auto`. Also emits
//! aggregation modules and asm-refines theorems for known program shapes.

use std::path::Path;

use solana_sbpf::{
    ebpf,
    static_analysis::Analysis,
};

#[path = "qedlift/input.rs"]
mod input;
#[path = "qedlift/aggregation.rs"]
mod aggregation;
#[path = "qedlift/branch.rs"]
mod branch;
#[path = "qedlift/core.rs"]
mod core;
#[path = "qedlift/emit.rs"]
mod emit;
#[path = "qedlift/isa.rs"]
mod isa;
#[path = "qedlift/refinement.rs"]
mod refinement;
#[path = "qedlift/render.rs"]
mod render;
#[path = "qedlift/state.rs"]
mod state;
#[path = "qedlift/syscalls.rs"]
mod syscalls;
#[path = "qedlift/witness.rs"]
mod witness;

use core::{
    arsh_render, canon_addr, lean_off, reg_initial_name, Atom, Expr, Width,
};
use emit::{
    atoms_to_lean, atoms_to_lean_heap, build_sat_witness, fold_abstractions, heap_cell_addr,
    post_atoms, region_req,
};
use aggregation::write_aggregation;
#[cfg(test)]
use aggregation::{render_mint_agg_module, render_token_agg_module};
use branch::{BranchHyp, BranchKind};
use input::{
    BinaryCtx, RefinementDescriptor, load_binary, load_descriptor, load_idl, load_idl_value,
    load_qedmeta, load_trace, parse_args, pascal_case, sidecar_account_layouts,
};
use isa::{
    function_registry, function_registry_lean, insn_to_lean, insn_to_lean_full,
    render_callstack, resolve_call_target_logical, resolve_jump_target,
};
use refinement::{emit_descriptor_refinement, emit_refinement, is_const_delta_arm};
use state::SymState;
use syscalls::{
    emit_r0_syscall, emit_sol_create_program_address, emit_sol_get_sysvar, emit_sol_log,
    emit_sol_memcmp, emit_sol_memcpy, emit_sol_memset, emit_sol_set_return_data, emit_sol_sha256,
};
use witness::build_branch_witness;
use qed_analysis::layout::AccountLayout;
#[cfg(test)]
use qed_analysis::layout::{parse_account_layout, FieldKind};

#[cfg(test)]
mod layout_tests {
    use super::*;

    #[test]
    fn transfer_aggregation_is_mechanically_emitted() {
        let m = render_token_agg_module(
            "Examples.PTokenTransferAggregation",
            &[("src_account_eq", true,  vec![72, 108, 109]),
              ("dst_account_eq", false, vec![108])],
            72, 165);
        let path = "../examples/lean/PToken/TransferAggregation.lean";
        // QEDLIFT_BLESS=1 re-blesses after an intentional emitter change (e.g. comment drift).
        if std::env::var("QEDLIFT_BLESS").is_ok() {
            std::fs::write(path, &m).expect("write TransferAggregation.lean");
        }
        let on_disk = std::fs::read_to_string(path).expect("read TransferAggregation.lean");
        assert_eq!(m, on_disk,
            "TransferAggregation.lean is out of sync with the qedlift emitter — \
             regenerate it (the file is mechanically emitted, do not hand-edit)");
    }

    #[test]
    fn mint_aggregation_is_mechanically_emitted() {
        let m = render_mint_agg_module(
            "Examples.PTokenMintAggregation", 36, 44, 82, 72, 165);
        let on_disk = std::fs::read_to_string("../examples/lean/PToken/MintAggregation.lean")
            .expect("read MintAggregation.lean");
        assert_eq!(m, on_disk,
            "MintAggregation.lean is out of sync with the qedlift emitter \
             (mechanically emitted, do not hand-edit)");
    }

    /// Diffs the emitter output on `counter.so` against both on-disk artifacts, guarding the counter-codec (non-token) path.
    #[test]
    fn counter_refinement_is_mechanically_emitted() {
        let so = std::path::Path::new("tests/fixtures/counter.so");
        let ctx = load_binary(so).expect("load counter.so");
        let analysis = Analysis::from_executable(&ctx.executable).expect("analyse counter.so");
        let result = lift_one(so, &ctx, &analysis, None, Some("Counter".to_string()),
            None, Some("counterIncrement"), None, None).expect("lift counter.so");

        let lift_on_disk =
            std::fs::read_to_string("../examples/lean/Generated/CounterTracedLifted.lean")
                .expect("read CounterTracedLifted.lean");
        assert_eq!(result.lean, lift_on_disk,
            "CounterTracedLifted.lean is out of sync with the qedlift emitter \
             (mechanically emitted, do not hand-edit)");

        let (_, rlean) = result.refinement.expect("counter refinement emitted");
        let refine_on_disk =
            std::fs::read_to_string("../examples/lean/Generated/CounterRefinement.lean")
                .expect("read CounterRefinement.lean");
        assert_eq!(rlean, refine_on_disk,
            "CounterRefinement.lean is out of sync with the qedlift emitter \
             (mechanically emitted, do not hand-edit)");
    }

    /// Spec-driven descriptor path (the qedspec seam): the refinement is built from a
    /// `*.descriptor.json` (layout + mutated field + op), bypassing `refine_registry`, and
    /// targets the layout-general `AsmRefinesFieldUpdate`. Two fixtures pin both shapes:
    /// counter (single u64 @ 0, empty frame) and vault (multi-field, pubkey + byte framing).
    #[test]
    fn descriptor_refinement_is_mechanically_emitted() {
        // (a) counter.so — single u64 field at offset 0, empty frame (no refine_registry entry).
        let desc = load_descriptor(std::path::Path::new("tests/fixtures/counter.descriptor.json"))
            .expect("load counter descriptor");
        let so = std::path::Path::new("tests/fixtures/counter.so");
        let ctx = load_binary(so).expect("load counter.so");
        let analysis = Analysis::from_executable(&ctx.executable).expect("analyse counter.so");
        let result = lift_one_with_layouts(so, &ctx, &analysis, None,
            Some("CounterDescriptor".to_string()), None, None, None, None, None, Some(&desc))
            .expect("lift counter.so via descriptor");
        let (_, rlean) = result.refinement.expect("descriptor refinement emitted (counter)");
        let on_disk = std::fs::read_to_string(
            "../examples/lean/Generated/CounterDescriptorRefinement.lean")
            .expect("read CounterDescriptorRefinement.lean");
        assert_eq!(rlean, on_disk,
            "CounterDescriptorRefinement.lean is out of sync with the qedlift descriptor \
             emitter (mechanically emitted, do not hand-edit)");

        // (b) vault.so — multi-field {owner:Pubkey, total:u64, bump:u8}; `total` mutated.
        // Name-level descriptor (no inline layout, no registry entry): the shape is resolved
        // from the IDL by account name, exactly the path `resolve_layout` uses.
        let vdesc = load_descriptor(std::path::Path::new("tests/fixtures/vault.descriptor.json"))
            .expect("load vault descriptor");
        let vidl: serde_json::Value = serde_json::from_str(
            &std::fs::read_to_string("tests/fixtures/vault.codama.json")
                .expect("read vault.codama.json")).expect("parse vault IDL");
        let vso = std::path::Path::new("tests/fixtures/vault.so");
        let vctx = load_binary(vso).expect("load vault.so");
        let vanalysis = Analysis::from_executable(&vctx.executable).expect("analyse vault.so");
        let vresult = lift_one_with_layouts(vso, &vctx, &vanalysis, None,
            Some("VaultDescriptor".to_string()), None, None, Some(&vidl), None, None, Some(&vdesc))
            .expect("lift vault.so via descriptor");
        let (_, vrlean) = vresult.refinement.expect("descriptor refinement emitted (vault)");
        let von_disk = std::fs::read_to_string(
            "../examples/lean/Generated/VaultDescriptorRefinement.lean")
            .expect("read VaultDescriptorRefinement.lean");
        assert_eq!(vrlean, von_disk,
            "VaultDescriptorRefinement.lean is out of sync with the qedlift descriptor \
             emitter (mechanically emitted, do not hand-edit)");
    }

    /// Descriptor path with a NON-1 constant delta (`total += 5`): the first refinement
    /// off the `+1` class. Same vault shape (IDL-resolved), but `op.add_const = 5`, so the
    /// lift cleans the credit via `wrapAdd_const_of_lt` instead of `wrapAdd_one_of_lt`.
    /// Pins that the arbitrary-literal path is mechanically emitted.
    #[test]
    fn descriptor_literal_delta_is_mechanically_emitted() {
        let desc = load_descriptor(std::path::Path::new("tests/fixtures/vault_add5.descriptor.json"))
            .expect("load vault_add5 descriptor");
        let idl: serde_json::Value = serde_json::from_str(
            &std::fs::read_to_string("tests/fixtures/vault.codama.json")
                .expect("read vault.codama.json")).expect("parse vault IDL");
        let so = std::path::Path::new("tests/fixtures/vault_add5.so");
        let ctx = load_binary(so).expect("load vault_add5.so");
        let analysis = Analysis::from_executable(&ctx.executable).expect("analyse vault_add5.so");
        let result = lift_one_with_layouts(so, &ctx, &analysis, None,
            Some("VaultAdd5".to_string()), None, None, Some(&idl), None, None, Some(&desc))
            .expect("lift vault_add5.so via descriptor");
        let (_, rlean) = result.refinement.expect("descriptor refinement emitted (vault_add5)");
        let on_disk = std::fs::read_to_string(
            "../examples/lean/Generated/VaultAdd5Refinement.lean")
            .expect("read VaultAdd5Refinement.lean");
        assert_eq!(rlean, on_disk,
            "VaultAdd5Refinement.lean is out of sync with the qedlift descriptor \
             emitter (mechanically emitted, do not hand-edit)");
    }

    /// Descriptor path with a PARAMETER delta (`total += amount`, schema v2): the first
    /// refinement with a runtime (non-constant) delta. The lift adds two memory reads,
    /// cleaned by `wrapAdd_of_lt`; `op.add_param` matches the second read as the credited
    /// amount and binds it in the `ensures`. Pins the parameter path is mechanically emitted.
    #[test]
    fn descriptor_param_delta_is_mechanically_emitted() {
        let desc = load_descriptor(std::path::Path::new("tests/fixtures/vault_deposit.descriptor.json"))
            .expect("load vault_deposit descriptor");
        let idl: serde_json::Value = serde_json::from_str(
            &std::fs::read_to_string("tests/fixtures/vault.codama.json")
                .expect("read vault.codama.json")).expect("parse vault IDL");
        let so = std::path::Path::new("tests/fixtures/vault_deposit.so");
        let ctx = load_binary(so).expect("load vault_deposit.so");
        let analysis = Analysis::from_executable(&ctx.executable).expect("analyse vault_deposit.so");
        let result = lift_one_with_layouts(so, &ctx, &analysis, None,
            Some("VaultDeposit".to_string()), None, None, Some(&idl), None, None, Some(&desc))
            .expect("lift vault_deposit.so via descriptor");
        let (_, rlean) = result.refinement.expect("descriptor refinement emitted (vault_deposit)");
        let on_disk = std::fs::read_to_string(
            "../examples/lean/Generated/VaultDepositRefinement.lean")
            .expect("read VaultDepositRefinement.lean");
        assert_eq!(rlean, on_disk,
            "VaultDepositRefinement.lean is out of sync with the qedlift descriptor \
             emitter (mechanically emitted, do not hand-edit)");
    }

    /// The descriptor is a versioned cross-tool contract: a schema newer than this qedlift
    /// understands must be refused fail-closed (mirrors `load_qedmeta`), never silently consumed.
    #[test]
    fn descriptor_rejects_newer_schema() {
        let err = load_descriptor(std::path::Path::new(
            "tests/fixtures/descriptor_future_schema.json"))
            .expect_err("a future descriptor schema must be refused");
        assert!(err.to_string().contains("schema_version"),
            "fail-closed error should name the schema_version mismatch, got: {err}");
    }

    /// Diffs the emitter output on `vault.so` + `vault.codama.json` against both on-disk artifacts, guarding the layout-general account-codec path.
    #[test]
    fn vault_refinement_is_mechanically_emitted() {
        let so = std::path::Path::new("tests/fixtures/vault.so");
        let idl: serde_json::Value = serde_json::from_str(
            &std::fs::read_to_string("tests/fixtures/vault.codama.json")
                .expect("read vault.codama.json")).expect("parse vault IDL");
        let ctx = load_binary(so).expect("load vault.so");
        let analysis = Analysis::from_executable(&ctx.executable).expect("analyse vault.so");
        let result = lift_one(so, &ctx, &analysis, None, Some("Vault".to_string()),
            None, Some("VaultIncrement"), Some(&idl), None).expect("lift vault.so");

        let lift_on_disk =
            std::fs::read_to_string("../examples/lean/Generated/VaultTracedLifted.lean")
                .expect("read VaultTracedLifted.lean");
        assert_eq!(result.lean, lift_on_disk,
            "VaultTracedLifted.lean is out of sync with the qedlift emitter \
             (mechanically emitted, do not hand-edit)");

        let (_, rlean) = result.refinement.expect("vault refinement emitted");
        let refine_on_disk =
            std::fs::read_to_string("../examples/lean/Generated/VaultRefinement.lean")
                .expect("read VaultRefinement.lean");
        assert_eq!(rlean, refine_on_disk,
            "VaultRefinement.lean is out of sync with the qedlift emitter \
             (mechanically emitted, do not hand-edit)");
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
                .expect("read vault.codama.json")).expect("parse vault IDL");
        let ctx = load_binary(so).expect("load vault.so");
        let analysis = Analysis::from_executable(&ctx.executable).expect("analyse vault.so");

        // (a) IDL path — the existing, blessed behaviour.
        let via_idl = lift_one_with_layouts(so, &ctx, &analysis, None, Some("Vault".to_string()),
            None, Some("VaultIncrement"), Some(&idl), None, None, None).expect("lift via idl");

        // (b) Sidecar path — layout supplied as qedrecover emits it; NO `--idl`.
        let layouts = vec![parse_account_layout(&idl, "vault").expect("vault layout")];
        let via_sidecar = lift_one_with_layouts(so, &ctx, &analysis, None, Some("Vault".to_string()),
            None, Some("VaultIncrement"), None, None, Some(&layouts), None).expect("lift via sidecar");

        // (c) No layout source at all.
        let via_none = lift_one_with_layouts(so, &ctx, &analysis, None, Some("Vault".to_string()),
            None, Some("VaultIncrement"), None, None, None, None).expect("lift with no layout");

        assert_eq!(via_idl.refinement, via_sidecar.refinement,
            "sidecar-supplied layout must reproduce the IDL-derived vault refinement");
        assert_eq!(via_idl.aggregation, via_sidecar.aggregation);
        assert!(via_sidecar.refinement.is_some(),
            "sidecar layout must drive the vault refinement codegen");
        assert!(via_none.refinement.is_none(),
            "vault refinement needs a layout source — the sidecar is what supplies it");
    }

    /// The sidecar `[[account_layout]]` → `AccountLayout` converter is the exact inverse of
    /// qedrecover's emitter (`kind` + `width_bytes` round-trip). Pins the SPL token/mint shapes.
    #[test]
    fn sidecar_account_layout_roundtrip() {
        let meta = load_qedmeta(std::path::Path::new(
            "tests/fixtures/p_token.transfer.recovered.qedmeta.toml"))
            .expect("load recovered sidecar");
        let layouts = sidecar_account_layouts(&meta);

        let token = layouts.iter().find(|l| l.name == "token").expect("token layout");
        assert_eq!(token.size, 165);
        let f = |n: &str| token.fields.iter().find(|f| f.name == n).expect("field");
        assert_eq!((f("mint").offset,   f("mint").kind.clone()),   (0,  FieldKind::Pubkey));
        assert_eq!((f("amount").offset, f("amount").kind.clone()), (64, FieldKind::U64));
        assert_eq!((f("state").offset,  f("state").kind.clone()),  (108, FieldKind::Byte));
        // opaque region keeps its width (`bytes` + `width_bytes` round-trip).
        assert_eq!(f("delegate").kind, FieldKind::Bytes(36));

        let mint = layouts.iter().find(|l| l.name == "mint").expect("mint account layout");
        let supply = mint.fields.iter().find(|f| f.name == "supply").expect("supply field");
        assert_eq!((supply.offset, supply.kind.clone()), (36, FieldKind::U64));
    }

    /// `vault.so` with a `[u8;32]` owner field: framed as opaque `.blob [.gap g]` (`↦Bytes`), exercising the `memBytesIs_segs` blob aggregation path.
    #[test]
    fn vault_blob_refinement_is_mechanically_emitted() {
        let so = std::path::Path::new("tests/fixtures/vault.so");
        let idl: serde_json::Value = serde_json::from_str(
            &std::fs::read_to_string("tests/fixtures/vault_blob.codama.json")
                .expect("read vault_blob.codama.json")).expect("parse vault_blob IDL");
        let ctx = load_binary(so).expect("load vault.so");
        let analysis = Analysis::from_executable(&ctx.executable).expect("analyse vault.so");
        let result = lift_one(so, &ctx, &analysis, None, Some("VaultBlob".to_string()),
            None, Some("VaultIncrement"), Some(&idl), None).expect("lift vault.so (blob)");

        let lift_on_disk =
            std::fs::read_to_string("../examples/lean/Generated/VaultBlobTracedLifted.lean")
                .expect("read VaultBlobTracedLifted.lean");
        assert_eq!(result.lean, lift_on_disk,
            "VaultBlobTracedLifted.lean is out of sync with the qedlift emitter \
             (mechanically emitted, do not hand-edit)");

        let (_, rlean) = result.refinement.expect("vault blob refinement emitted");
        let refine_on_disk =
            std::fs::read_to_string("../examples/lean/Generated/VaultBlobRefinement.lean")
                .expect("read VaultBlobRefinement.lean");
        assert_eq!(rlean, refine_on_disk,
            "VaultBlobRefinement.lean is out of sync with the qedlift emitter \
             (mechanically emitted, do not hand-edit)");
    }

    /// `vault_split.so` owns `owner[5]`, forcing the blob to split into `[.gap, .byte, .gap]` — the multisig-style partial-blob path.
    #[test]
    fn vault_split_refinement_is_mechanically_emitted() {
        let so = std::path::Path::new("tests/fixtures/vault_split.so");
        let idl: serde_json::Value = serde_json::from_str(
            &std::fs::read_to_string("tests/fixtures/vault_blob.codama.json")
                .expect("read vault_blob.codama.json")).expect("parse vault_blob IDL");
        let ctx = load_binary(so).expect("load vault_split.so");
        let analysis = Analysis::from_executable(&ctx.executable).expect("analyse vault_split.so");
        let result = lift_one(so, &ctx, &analysis, None, Some("VaultSplit".to_string()),
            None, Some("VaultIncrement"), Some(&idl), None).expect("lift vault_split.so");

        let lift_path = "../examples/lean/Generated/VaultSplitTracedLifted.lean";
        let refine_path = "../examples/lean/Generated/VaultSplitRefinement.lean";
        if std::env::var("QEDLIFT_BLESS").is_ok() {
            std::fs::write(lift_path, &result.lean).expect("write lift");
            if let Some((_, rlean)) = result.refinement.as_ref() {
                std::fs::write(refine_path, rlean).expect("write refinement");
            }
        }
        assert_eq!(result.lean, std::fs::read_to_string(lift_path).expect("read lift"),
            "VaultSplitTracedLifted.lean is out of sync with the qedlift emitter");
        let (_, rlean) = result.refinement.expect("vault split refinement emitted");
        assert_eq!(rlean, std::fs::read_to_string(refine_path).expect("read refinement"),
            "VaultSplitRefinement.lean is out of sync with the qedlift emitter");
    }

    /// Guards the heap-corollary codegen: `heapBumpPtr`/`heapBlockU64` fold + conditional `HeapSL` import.
    #[test]
    fn heap_alloc_lift_is_mechanically_emitted() {
        let so = std::path::Path::new("tests/fixtures/heap_alloc.so");
        let ctx = load_binary(so).expect("load heap_alloc.so");
        let analysis = Analysis::from_executable(&ctx.executable).expect("analyse heap_alloc.so");
        let result = lift_one(so, &ctx, &analysis, None, Some("HeapAlloc".to_string()),
            None, None, None, None).expect("lift heap_alloc.so");

        let on_disk =
            std::fs::read_to_string("../examples/lean/Generated/HeapAllocLifted.lean")
                .expect("read HeapAllocLifted.lean");
        assert_eq!(result.lean, on_disk,
            "HeapAllocLifted.lean is out of sync with the qedlift emitter \
             (mechanically emitted, do not hand-edit)");
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
        let result = lift_one(so, &ctx, &analysis, None, Some("Memcpy".to_string()),
            Some(&trace), None, None, None).expect("lift memcpy_caller.so");

        let path = "../examples/lean/Generated/MemcpyLifted.lean";
        if std::env::var("QEDLIFT_BLESS").is_ok() {
            std::fs::write(path, &result.lean).expect("write MemcpyLifted.lean");
        }
        let on_disk = std::fs::read_to_string(path).expect("read MemcpyLifted.lean");
        assert_eq!(result.lean, on_disk,
            "MemcpyLifted.lean is out of sync with the qedlift emitter \
             (mechanically emitted, re-bless with QEDLIFT_BLESS=1)");
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
        let result = lift_one(so, &ctx, &analysis, None, Some("Sha256Caller".to_string()),
            Some(&trace), None, None, None).expect("lift sha256_caller.so");

        let path = "../examples/lean/Generated/Sha256CallerLifted.lean";
        if std::env::var("QEDLIFT_BLESS").is_ok() {
            std::fs::write(path, &result.lean).expect("write Sha256CallerLifted.lean");
        }
        let on_disk = std::fs::read_to_string(path).expect("read Sha256CallerLifted.lean");
        assert_eq!(result.lean, on_disk,
            "Sha256CallerLifted.lean is out of sync with the qedlift emitter \
             (mechanically emitted, re-bless with QEDLIFT_BLESS=1)");
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
        let result = lift_one(so, &ctx, &analysis, None, Some("PdaCreate".to_string()),
            Some(&trace), None, None, None).expect("lift pda_create.so");

        let path = "../examples/lean/Generated/PdaCreateLifted.lean";
        if std::env::var("QEDLIFT_BLESS").is_ok() {
            std::fs::write(path, &result.lean).expect("write PdaCreateLifted.lean");
        }
        let on_disk = std::fs::read_to_string(path).expect("read PdaCreateLifted.lean");
        assert_eq!(result.lean, on_disk,
            "PdaCreateLifted.lean is out of sync with the qedlift emitter \
             (mechanically emitted, re-bless with QEDLIFT_BLESS=1)");
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
        let result = lift_one(so, &ctx, &analysis, None, Some("Memmove".to_string()),
            Some(&trace), None, None, None).expect("lift memmove_caller.so");

        let path = "../examples/lean/Generated/MemmoveLifted.lean";
        if std::env::var("QEDLIFT_BLESS").is_ok() {
            std::fs::write(path, &result.lean).expect("write MemmoveLifted.lean");
        }
        let on_disk = std::fs::read_to_string(path).expect("read MemmoveLifted.lean");
        assert_eq!(result.lean, on_disk,
            "MemmoveLifted.lean is out of sync with the qedlift emitter \
             (mechanically emitted, re-bless with QEDLIFT_BLESS=1)");
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
        let result = lift_one(so, &ctx, &analysis, None, Some("Memcmp".to_string()),
            Some(&trace), None, None, None).expect("lift memcmp_caller.so");

        let path = "../examples/lean/Generated/MemcmpLifted.lean";
        if std::env::var("QEDLIFT_BLESS").is_ok() {
            std::fs::write(path, &result.lean).expect("write MemcmpLifted.lean");
        }
        let on_disk = std::fs::read_to_string(path).expect("read MemcmpLifted.lean");
        assert_eq!(result.lean, on_disk,
            "MemcmpLifted.lean is out of sync with the qedlift emitter \
             (mechanically emitted, re-bless with QEDLIFT_BLESS=1)");
    }

    /// Pins the `sol_set_return_data` happy-path lift
    /// (`call_sol_set_return_data_spec`): one `↦Bytes` input + the framed
    /// `↦ReturnData` atom (flips old → input blob), r0 := 0. Trace-driven.
    #[test]
    fn set_return_data_lift_is_mechanically_emitted() {
        let so = std::path::Path::new("tests/fixtures/set_return_data_caller.so");
        let ctx = load_binary(so).expect("load set_return_data_caller.so");
        let analysis = Analysis::from_executable(&ctx.executable)
            .expect("analyse set_return_data_caller.so");
        let trace = load_trace(
            std::path::Path::new("tests/fixtures/set_return_data_caller.pcs"))
            .expect("load set_return_data trace");
        let result = lift_one(so, &ctx, &analysis, None,
            Some("SetReturnData".to_string()),
            Some(&trace), None, None, None).expect("lift set_return_data_caller.so");

        let path = "../examples/lean/Generated/SetReturnDataLifted.lean";
        if std::env::var("QEDLIFT_BLESS").is_ok() {
            std::fs::write(path, &result.lean).expect("write SetReturnDataLifted.lean");
        }
        let on_disk = std::fs::read_to_string(path).expect("read SetReturnDataLifted.lean");
        assert_eq!(result.lean, on_disk,
            "SetReturnDataLifted.lean is out of sync with the qedlift emitter \
             (mechanically emitted, re-bless with QEDLIFT_BLESS=1)");
    }

    /// Pins ldxh/stxh and ST_H_IMM (`sth_spec`) on real cargo-build-sbf bytecode.
    #[test]
    fn halfword_store_lift_is_mechanically_emitted() {
        let so = std::path::Path::new("tests/fixtures/halfword_store.so");
        let ctx = load_binary(so).expect("load halfword_store.so");
        let analysis = Analysis::from_executable(&ctx.executable).expect("analyse halfword_store.so");
        let result = lift_one(so, &ctx, &analysis, None, Some("HalfwordStore".to_string()),
            None, None, None, None).expect("lift halfword_store.so");

        let on_disk =
            std::fs::read_to_string("../examples/lean/Generated/HalfwordStoreLifted.lean")
                .expect("read HalfwordStoreLifted.lean");
        assert_eq!(result.lean, on_disk,
            "HalfwordStoreLifted.lean is out of sync with the qedlift emitter \
             (mechanically emitted, do not hand-edit)");
    }

    /// The real p_token sidecar's `arm_entry_pc` must parse as logical 304 (#41: the formerly-dropped `[instruction.recovered]` is now consumed).
    #[test]
    fn qedmeta_recovered_arm_is_parsed() {
        let meta = load_qedmeta(std::path::Path::new("tests/fixtures/p_token.qedmeta.toml"))
            .expect("load p_token.qedmeta.toml");
        let transfer = meta.instructions.iter().find(|i| i.name == "transfer")
            .expect("transfer instruction present in sidecar");
        let rec = transfer.recovered.as_ref()
            .expect("transfer carries [instruction.recovered] (dropped pre-#41)");
        assert_eq!(rec.arm_entry_pc, 304, "recovered arm entry must be logical 304");
    }

    /// Recovered arm_entry_pc cross-checks that the trace reaches it and leaves emitted Lean byte-identical to the trace-only path.
    #[test]
    fn qedmeta_arm_entry_trace_lift_is_byte_identical() {
        let so = std::path::Path::new("tests/fixtures/p_token.so");
        let ctx = load_binary(so).expect("load p_token.so");
        let analysis = Analysis::from_executable(&ctx.executable).expect("analyse p_token.so");
        let trace = load_trace(std::path::Path::new("tests/fixtures/p_token_transfer.pcs"))
            .expect("load transfer trace");
        let result = lift_one(so, &ctx, &analysis, None,
            Some("PTokenTransfer".to_string()), Some(&trace), Some("Transfer"),
            None, Some(304)).expect("lift transfer with recovered arm");
        let on_disk = std::fs::read_to_string(
            "../examples/lean/Generated/PTokenTransferTracedLifted.lean")
            .expect("read PTokenTransferTracedLifted.lean");
        assert_eq!(result.lean, on_disk,
            "consuming arm_entry perturbed the trace-guided transfer lift");
    }

    /// A recovered arm_entry_pc not on the execution trace must be rejected, not silently lifted against the wrong arm.
    #[test]
    fn qedmeta_arm_entry_off_trace_is_rejected() {
        let so = std::path::Path::new("tests/fixtures/p_token.so");
        let ctx = load_binary(so).expect("load p_token.so");
        let analysis = Analysis::from_executable(&ctx.executable).expect("analyse p_token.so");
        let trace = load_trace(std::path::Path::new("tests/fixtures/p_token_transfer.pcs"))
            .expect("load transfer trace");
        let err = lift_one(so, &ctx, &analysis, None,
            Some("PTokenTransfer".to_string()), Some(&trace), Some("Transfer"),
            None, Some(999_999));
        assert!(err.is_err(),
            "an off-trace recovered arm_entry must be rejected by the cross-check");
    }

    /// Seeding the static walk at the natural entrypoint must reproduce the unseeded walk byte-for-byte, pinning `unwrap_or(entry_pc)` fallback.
    #[test]
    fn qedmeta_arm_entry_seed_at_entrypoint_is_noop() {
        let so = std::path::Path::new("tests/fixtures/heap_alloc.so");
        let ctx = load_binary(so).expect("load heap_alloc.so");
        let analysis = Analysis::from_executable(&ctx.executable).expect("analyse heap_alloc.so");
        let entry = ctx.executable.get_entrypoint_instruction_offset();
        let base = lift_one(so, &ctx, &analysis, None, Some("HeapAlloc".to_string()),
            None, None, None, None).expect("base lift");
        let seeded = lift_one(so, &ctx, &analysis, None, Some("HeapAlloc".to_string()),
            None, None, None, Some(entry)).expect("seeded lift");
        assert_eq!(base.lean, seeded.lean,
            "seeding the walk at the entrypoint must equal the unseeded walk");
    }

    /// Re-emit one p_token arm and diff lift + refinement against on-disk artifacts. Every arm is pinned: H8 vacuity shipped unnoticed without these pins.
    fn pin_p_token_arm(
        pcs: &str, module: &str, arm: Option<&str>,
        lift_path: &str, refine_path: Option<&str>,
    ) {
        let so = std::path::Path::new("tests/fixtures/p_token.so");
        let ctx = load_binary(so).expect("load p_token.so");
        let analysis = Analysis::from_executable(&ctx.executable)
            .expect("analyse p_token.so");
        let trace = load_trace(std::path::Path::new(pcs)).expect("load trace");
        let result = lift_one(so, &ctx, &analysis, None,
            Some(module.to_string()), Some(&trace), arm, None, None)
            .expect("lift p_token arm");

        // QEDLIFT_BLESS=1 re-blesses artifacts after an intentional emitter change.
        if std::env::var("QEDLIFT_BLESS").is_ok() {
            std::fs::write(lift_path, &result.lean).expect("write lift");
            if let (Some(rp), Some((_, rlean))) = (refine_path, result.refinement.as_ref()) {
                std::fs::write(rp, rlean).expect("write refinement");
            }
        }
        let on_disk = std::fs::read_to_string(lift_path).expect("read lift");
        assert_eq!(result.lean, on_disk,
            "{lift_path} is out of sync with the qedlift emitter \
             (mechanically emitted, do not hand-edit)");
        if let Some(rp) = refine_path {
            let (_, rlean) = result.refinement.expect("refinement emitted");
            let r_on_disk = std::fs::read_to_string(rp).expect("read refinement");
            assert_eq!(rlean, r_on_disk,
                "{rp} is out of sync with the qedlift refinement codegen \
                 (mechanically emitted, do not hand-edit)");
        }
    }

    #[test]
    fn p_token_transfer_is_mechanically_emitted() {
        pin_p_token_arm("tests/fixtures/p_token_transfer.pcs",
            "PTokenTransfer", Some("Transfer"),
            "../examples/lean/Generated/PTokenTransferTracedLifted.lean",
            Some("../examples/lean/PToken/TransferRefinement.lean"));
    }

    #[test]
    fn p_token_transfer_checked_is_mechanically_emitted() {
        pin_p_token_arm("tests/fixtures/p_token_transfer_checked.pcs",
            "PTokenTransferChecked", Some("TransferChecked"),
            "../examples/lean/Generated/PTokenTransferCheckedTracedLifted.lean",
            Some("../examples/lean/PToken/TransferCheckedRefinement.lean"));
    }

    /// Regenerated 2026-06-12 after H8: Phase A canonical aliasing (r10 spills) + Phase B byte demotion (`ldxdw_bytes_spec`).
    #[test]
    fn p_token_mint_to_is_mechanically_emitted() {
        pin_p_token_arm("tests/fixtures/p_token_mint_to.pcs",
            "PTokenMintTo", Some("MintTo"),
            "../examples/lean/Generated/PTokenMintToTracedLifted.lean",
            Some("../examples/lean/PToken/MintToRefinement.lean"));
    }

    /// Regenerated 2026-06-12 after H8 Phase C-1: pre-split memset specs (`↦U64` cells; blob never overlaps).
    #[test]
    fn p_token_close_account_is_mechanically_emitted() {
        pin_p_token_arm("tests/fixtures/p_token_close_account.pcs",
            "PTokenCloseAccount", None,
            "../examples/lean/Generated/PTokenCloseAccountTracedLifted.lean",
            None);
    }

    /// Full H8 gauntlet: `sol_get_sysvar` (cells17), stw tail-zeroing (byte demotion), rent dword read. Trace re-captured under H7-faithful VM.
    #[test]
    fn p_token_initialize_mint2_is_mechanically_emitted() {
        pin_p_token_arm("tests/fixtures/p_token_initialize_mint2.pcs",
            "PTokenInitializeMint2", None,
            "../examples/lean/Generated/PTokenInitializeMint2TracedLifted.lean",
            None);
    }

    #[test]
    fn p_token_burn_is_mechanically_emitted() {
        pin_p_token_arm("tests/fixtures/p_token_burn.pcs",
            "PTokenBurn", Some("Burn"),
            "../examples/lean/Generated/PTokenBurnTracedLifted.lean",
            Some("../examples/lean/PToken/BurnRefinement.lean"));
    }
}

/// One emitted `have h_<pc> := <spec_name> <args>` line; used by `sl_block_iter` proof bodies when `sl_block_auto` diverges (call_local programs).
#[derive(Clone, Debug)]
struct SpecCall {
    hyp_name: String,
    have_line: String,
}

/// Build the `have h_<pc> := <spec_name> <args>` line for one insn,
/// using `state` as the pre-state (the symbolic values BEFORE the
/// insn applies). Side conditions like `(by decide)` and value-bound
/// hypotheses (`< 2^64`) are filled in based on the spec's signature.
/// Returns `None` for opcodes not in the table (caller can fall back).
/// `branch_taken` (when `Some`) tells the emitter which variant of
/// the conditional-jump spec to use for the current insn:
///   - `Some(true)`  → use `jXX_imm_taken_spec`     (post-PC = target)
///   - `Some(false)` → use `jXX_imm_not_taken_spec` (post-PC = pc+1)
///   - `None`        → not applicable (non-branch instruction)
fn spec_call_for(
    state: &SymState,
    insn: &ebpf::Insn,
    pc: usize,
    call_target: Option<usize>,
    branch_hyp_name: Option<&str>,
    branch_taken: Option<bool>,
    jump_target: Option<i64>,
) -> Option<SpecCall> {
    use ebpf::*;
    let dst = insn.dst;
    let src = insn.src;
    let off = insn.off as i64;
    // Parenthesise negatives: `ldxb_same_spec .r10 -8` would parse as `.r10 - 8`.
    let offl = lean_off(off);
    // slot→logical resolved by caller.
    let jt = jump_target.unwrap_or((pc as i64) + 1 + off);
    // Parenthesise negative imm: `and64_imm_spec .r1 -8` would parse as `(and64_imm_spec .r1) - 8`.
    let imm = lean_off(insn.imm);
    let hyp_name = format!("h_{}", pc);
    let reg = |r: u8| -> String {
        match r {
            0 => ".r0".into(), 1 => ".r1".into(), 2 => ".r2".into(), 3 => ".r3".into(),
            4 => ".r4".into(), 5 => ".r5".into(), 6 => ".r6".into(), 7 => ".r7".into(),
            8 => ".r8".into(), 9 => ".r9".into(), 10 => ".r10".into(),
            _ => ".r0".into(),
        }
    };
    // Lean string for register r; falls back to initial-name convention (`baseAddr` for r1, `vR<N>Old` otherwise).
    let reg_val_lean = |r: u8| -> String {
        match state.regs.get(&r) {
            Some(e) => e.to_lean(),
            None    => reg_initial_name(r),
        }
    };
    // Expr form of register r, for canon-aware cell lookups.
    let reg_val_expr = |r: u8| -> Expr {
        state.regs.get(&r).cloned()
            .unwrap_or_else(|| Expr::InitReg(reg_initial_name(r)))
    };
    // Phase A aliasing (QEDLIFT_ALIASING_DESIGN.md): same cell under different rendering
    // → append a `rw [h_alias_<pc>]` so the chain composes on ONE atom (not two overlapping unsatisfiable ones).
    let alias_suffix = |lookup: &Option<(usize, bool)>| -> String {
        match lookup {
            Some((_, true)) => format!("\n  rw [h_alias_{}] at {}", pc, hyp_name),
            _ => String::new(),
        }
    };
    let have_line = match insn.opc {
        LD_B_REG => {
            // ldxb_spec dst src off vOldDst baseAddr v pc hne (no < 2^64 bound — bytes always fit).
            // Re-read reuses existing cell value; first access allocates oldMemB_<fresh>.
            let base_addr = reg_val_lean(src);
            let lookup = state.lookup_cell_aliased(&reg_val_expr(src), off, Width::Byte);
            let v_name = lookup
                .map(|(i, _)| state.mem[i].value.atom_lean())
                .unwrap_or_else(|| format!("oldMemB_{}", state.fresh));
            let alias = alias_suffix(&lookup);
            if dst == src {
                // dst == src: generic ldxb_spec would emit two `r ↦ᵣ` atoms (unsatisfiable); use ldxb_same_spec.
                format!(
                    "have {} := ldxb_same_spec {} {} ({}) {} {} (by decide){}",
                    hyp_name, reg(dst), offl, base_addr, v_name, pc, alias,
                )
            } else {
                let v_old_dst = state.regs.get(&dst)
                    .map(|e| e.to_lean())
                    .unwrap_or_else(|| reg_initial_name(dst));
                format!(
                    "have {} := ldxb_spec {} {} {} ({}) ({}) {} {} (by decide){}",
                    hyp_name, reg(dst), reg(src), offl,
                    v_old_dst, base_addr, v_name, pc, alias,
                )
            }
        }
        LD_DW_REG => {
            // ldxdw_spec dst src off vOldDst baseAddr v pc hne hv.
            // Runs BEFORE step()'s read_mem; predicts fresh name `oldMemD_{state.fresh}`, bound `h<var>_lt`.
            let base_addr = reg_val_lean(src);
            // Hot (byte-demoted) region: use `ldxdw_bytes_spec` (H8 Phase B); predictions mirror `read_hot_wide`.
            {
                let bexpr = reg_val_expr(src);
                let (root, lo) = canon_addr(&bexpr, off);
                if dst != src && state.hot_covers(&root, lo, lo + 8) {
                    let mut args = String::new();
                    let mut addrs = String::new();
                    let mut bounds = String::new();
                    let mut haddrs = String::new();
                    let mut n_alias = 0usize;
                    let mut fresh = state.fresh;
                    for k in 0..8i64 {
                        let found = state.mem.iter().find(|c| {
                            matches!(c.width, Width::Byte) && {
                                let (cr, cd) = canon_addr(&c.addr_base, c.addr_off);
                                cr == root && cd + c.delta == lo + k
                            }
                        });
                        match found {
                            Some(c) => {
                                let render_ok = c.addr_base.to_lean() == bexpr.to_lean()
                                    && c.addr_off == off
                                    && ((k == 0 && c.delta == 0) || c.delta == k);
                                if render_ok {
                                    addrs.push_str(&format!(" ({})",
                                        SymState::slot_expected_render(&bexpr, off, k)));
                                    haddrs.push_str(" rfl");
                                } else {
                                    addrs.push_str(&format!(" ({})",
                                        SymState::cell_render(c)));
                                    haddrs.push_str(&format!(
                                        " h_alias_{}_{}", pc, n_alias));
                                    n_alias += 1;
                                }
                                args.push_str(&format!(" {}", c.value.atom_lean()));
                                match &c.value {
                                    Expr::InitMem(n) =>
                                        bounds.push_str(&format!(" h{}_lt", n)),
                                    _ => bounds.push_str(" (by omega)"),
                                }
                            }
                            None => {
                                let n = format!("oldMemB_{}", fresh);
                                fresh += 1;
                                addrs.push_str(&format!(" ({})",
                                    SymState::slot_expected_render(&bexpr, off, k)));
                                haddrs.push_str(" rfl");
                                args.push_str(&format!(" {}", n));
                                bounds.push_str(&format!(" h{}_lt", n));
                            }
                        }
                    }
                    let v_old_dst = state.regs.get(&dst)
                        .map(|e| e.to_lean())
                        .unwrap_or_else(|| reg_initial_name(dst));
                    return Some(SpecCall {
                        hyp_name: hyp_name.clone(),
                        have_line: format!(
                            "have {} := ldxdw_bytes_spec {} {} {} ({}) ({}){}{} {} (by decide){}{}",
                            hyp_name, reg(dst), reg(src), offl,
                            v_old_dst, base_addr, args, addrs, pc, bounds, haddrs,
                        ),
                    });
                }
            }
            // Re-read: reuse existing cell value. First access allocates oldMemD_<fresh> with h<var>_lt.
            // Reloaded compound (spilled reg) surfaces `hReloadLt_<pc>` as the hv bound.
            let lookup = state.lookup_cell_aliased(&reg_val_expr(src), off, Width::Dword);
            let cell_val = lookup.map(|(i, _)| state.mem[i].value.clone());
            let alias = alias_suffix(&lookup);
            let (v_arg, hv) = match &cell_val {
                Some(Expr::InitMem(name)) => (name.clone(), format!("h{}_lt", name)),
                Some(v) => (v.atom_lean(), format!("hReloadLt_{}", pc)),
                None => { let n = format!("oldMemD_{}", state.fresh); (n.clone(), format!("h{}_lt", n)) }
            };
            if dst == src {
                // dst == src: use ldxdw_same_spec.
                format!(
                    "have {} := ldxdw_same_spec {} {} ({}) {} {} (by decide) {}{}",
                    hyp_name, reg(dst), offl, base_addr, v_arg, pc, hv, alias,
                )
            } else {
                let v_old_dst = state.regs.get(&dst)
                    .map(|e| e.to_lean())
                    .unwrap_or_else(|| reg_initial_name(dst));
                format!(
                    "have {} := ldxdw_spec {} {} {} ({}) ({}) {} {} (by decide) {}{}",
                    hyp_name, reg(dst), reg(src), offl,
                    v_old_dst, base_addr, v_arg, pc, hv, alias,
                )
            }
        }
        // Word / halfword loads (dst ≠ src): `ldx{w,h}_spec dst src off
        // vOldDst baseAddr v pc hne hv`, hv = `v < 2^{32,16}` surfaced as
        // `h<var>_lt`. Post is `dst ↦ᵣ v` (the ↦U32/↦U16 cell value, raw).
        LD_W_REG | LD_H_REG => {
            let (spec, w, pfx) = if insn.opc == LD_W_REG {
                ("ldxw_spec", Width::Word, "oldMemW")
            } else { ("ldxh_spec", Width::Halfword, "oldMemH") };
            let base_addr = reg_val_lean(src);
            let lookup = state.lookup_cell_aliased(&reg_val_expr(src), off, w);
            let cell_val = lookup.map(|(i, _)| state.mem[i].value.clone());
            let alias = alias_suffix(&lookup);
            let (v_arg, hv) = match &cell_val {
                Some(Expr::InitMem(name)) => (name.clone(), format!("h{}_lt", name)),
                Some(v) => (v.atom_lean(), format!("hReloadLt_{}", pc)),
                None => { let n = format!("{}_{}", pfx, state.fresh); (n.clone(), format!("h{}_lt", n)) }
            };
            let v_old_dst = state.regs.get(&dst)
                .map(|e| e.to_lean())
                .unwrap_or_else(|| reg_initial_name(dst));
            format!(
                "have {} := {} {} {} {} ({}) ({}) {} {} (by decide) {}{}",
                hyp_name, spec, reg(dst), reg(src), offl,
                v_old_dst, base_addr, v_arg, pc, hv, alias,
            )
        }
        ST_B_REG | ST_H_REG | ST_W_REG | ST_DW_REG => {
            // stx{b,h,w,dw}_spec baseReg valReg off baseAddr vSrc oldV pc — all four share this shape.
            let (spec, w, pfx) = match insn.opc {
                ST_B_REG  => ("stxb_spec",  Width::Byte,     "oldMemB"),
                ST_H_REG  => ("stxh_spec",  Width::Halfword, "oldMemH"),
                ST_W_REG  => ("stxw_spec",  Width::Word,     "oldMemW"),
                ST_DW_REG => ("stxdw_spec", Width::Dword,    "oldMemD"),
                _ => unreachable!(),
            };
            let base_addr = reg_val_lean(dst);
            let v_src = reg_val_lean(src);
            // atom_lean() parenthesises compound prior values, leaving bare `oldMem*_N` unparenthesised.
            let lookup = state.lookup_cell_aliased(&reg_val_expr(dst), off, w);
            let old_v = lookup
                .map(|(i, _)| state.mem[i].value.atom_lean())
                // First access: step()'s write_mem allocates `oldMem*_{fresh}`; predict that name.
                .unwrap_or_else(|| format!("{}_{}", pfx, state.fresh));
            let alias = alias_suffix(&lookup);
            format!(
                "have {} := {} {} {} {} ({}) ({}) {} {}{}",
                hyp_name, spec, reg(dst), reg(src), offl,
                base_addr, v_src, old_v, pc, alias,
            )
        }
        ADD64_IMM => {
            let v_old = reg_val_lean(dst);
            format!(
                "have {} := add64_imm_spec {} {} ({}) {} (by decide)",
                hyp_name, reg(dst), imm, v_old, pc,
            )
        }
        AND64_IMM => {
            let v_old = reg_val_lean(dst);
            format!(
                "have {} := and64_imm_spec {} {} ({}) {} (by decide)",
                hyp_name, reg(dst), imm, v_old, pc,
            )
        }
        LSH64_IMM => {
            let v_old = reg_val_lean(dst);
            format!(
                "have {} := lsh64_imm_spec {} {} ({}) {} (by decide)",
                hyp_name, reg(dst), imm, v_old, pc,
            )
        }
        RSH64_IMM => {
            let v_old = reg_val_lean(dst);
            format!(
                "have {} := rsh64_imm_spec {} {} ({}) {} (by decide)",
                hyp_name, reg(dst), imm, v_old, pc,
            )
        }
        // Bitwise/mul imm-form ALU: `<op>_imm_spec dst imm vOld pc hne`.
        OR64_IMM | XOR64_IMM | MUL64_IMM => {
            let v_old = reg_val_lean(dst);
            let spec = match insn.opc {
                OR64_IMM => "or64_imm_spec", XOR64_IMM => "xor64_imm_spec",
                MUL64_IMM => "mul64_imm_spec", _ => unreachable!(),
            };
            format!(
                "have {} := {} {} {} ({}) {} (by decide)",
                hyp_name, spec, reg(dst), imm, v_old, pc,
            )
        }
        // Div/mod imm-form: extra `hnz : toU64 imm ≠ 0` discharged by `(by decide)` (fails on literal div-by-zero).
        DIV64_IMM | MOD64_IMM => {
            let v_old = reg_val_lean(dst);
            let spec = if insn.opc == DIV64_IMM { "div64_imm_spec" } else { "mod64_imm_spec" };
            format!(
                "have {} := {} {} {} ({}) {} (by decide) (by decide)",
                hyp_name, spec, reg(dst), imm, v_old, pc,
            )
        }
        NEG64 => {
            let v_old = reg_val_lean(dst);
            format!(
                "have {} := neg64_spec {} ({}) {} (by decide)",
                hyp_name, reg(dst), v_old, pc,
            )
        }
        // div/mod reg-form: symbolic divisor → spec's `hnz` surfaced as theorem hyp `hnz_<pc>` (registered by step).
        DIV64_REG | MOD64_REG | DIV32_REG | MOD32_REG => {
            let v_old = reg_val_lean(dst);
            let v_src = reg_val_lean(src);
            let spec = match insn.opc {
                DIV64_REG => "div64_reg_spec", MOD64_REG => "mod64_reg_spec",
                DIV32_REG => "div32_reg_spec", MOD32_REG => "mod32_reg_spec",
                _ => unreachable!(),
            };
            format!(
                "have {} := {} {} {} ({}) ({}) {} (by decide) hnz_{}",
                hyp_name, spec, reg(dst), reg(src), v_old, v_src, pc, pc,
            )
        }
        // 32-bit imm ALU: `<op>32_imm_spec dst imm vOld pc hne`.
        ADD32_IMM | SUB32_IMM | MUL32_IMM | OR32_IMM | AND32_IMM | XOR32_IMM
        | LSH32_IMM | RSH32_IMM | MOV32_IMM => {
            let v_old = reg_val_lean(dst);
            let spec = match insn.opc {
                ADD32_IMM => "add32_imm_spec", SUB32_IMM => "sub32_imm_spec",
                MUL32_IMM => "mul32_imm_spec", OR32_IMM => "or32_imm_spec",
                AND32_IMM => "and32_imm_spec", XOR32_IMM => "xor32_imm_spec",
                LSH32_IMM => "lsh32_imm_spec", RSH32_IMM => "rsh32_imm_spec",
                MOV32_IMM => "mov32_imm_spec", _ => unreachable!(),
            };
            format!(
                "have {} := {} {} {} ({}) {} (by decide)",
                hyp_name, spec, reg(dst), imm, v_old, pc,
            )
        }
        // 32-bit div/mod imm: extra `toU64 imm % U32_MODULUS ≠ 0` (literal → decide).
        DIV32_IMM | MOD32_IMM => {
            let v_old = reg_val_lean(dst);
            let spec = if insn.opc == DIV32_IMM { "div32_imm_spec" } else { "mod32_imm_spec" };
            format!(
                "have {} := {} {} {} ({}) {} (by decide) (by decide)",
                hyp_name, spec, reg(dst), imm, v_old, pc,
            )
        }
        NEG32 => {
            let v_old = reg_val_lean(dst);
            format!(
                "have {} := neg32_spec {} ({}) {} (by decide)",
                hyp_name, reg(dst), v_old, pc,
            )
        }
        // 32-bit reg ALU: `<op>32_reg_spec dst src vOld v pc hne`.
        ADD32_REG | SUB32_REG | MUL32_REG | OR32_REG | AND32_REG | XOR32_REG
        | LSH32_REG | RSH32_REG | MOV32_REG => {
            let v_old = reg_val_lean(dst);
            let v_src = reg_val_lean(src);
            let spec = match insn.opc {
                ADD32_REG => "add32_reg_spec", SUB32_REG => "sub32_reg_spec",
                MUL32_REG => "mul32_reg_spec", OR32_REG => "or32_reg_spec",
                AND32_REG => "and32_reg_spec", XOR32_REG => "xor32_reg_spec",
                LSH32_REG => "lsh32_reg_spec", RSH32_REG => "rsh32_reg_spec",
                MOV32_REG => "mov32_reg_spec", _ => unreachable!(),
            };
            format!(
                "have {} := {} {} {} ({}) ({}) {} (by decide)",
                hyp_name, spec, reg(dst), reg(src), v_old, v_src, pc,
            )
        }
        // arsh (arithmetic shift right), imm + reg, 32 + 64-bit.
        ARSH64_IMM | ARSH32_IMM => {
            let v_old = reg_val_lean(dst);
            let spec = if insn.opc == ARSH64_IMM { "arsh64_imm_spec" } else { "arsh32_imm_spec" };
            format!(
                "have {} := {} {} {} ({}) {} (by decide)",
                hyp_name, spec, reg(dst), imm, v_old, pc,
            )
        }
        ARSH64_REG | ARSH32_REG => {
            let v_old = reg_val_lean(dst);
            let v_src = reg_val_lean(src);
            let spec = if insn.opc == ARSH64_REG { "arsh64_reg_spec" } else { "arsh32_reg_spec" };
            format!(
                "have {} := {} {} {} ({}) ({}) {} (by decide)",
                hyp_name, spec, reg(dst), reg(src), v_old, v_src, pc,
            )
        }
        ST_B_IMM => {
            // stb_spec baseReg off imm baseAddr oldByteVal pc
            let base_addr = reg_val_lean(dst);
            let lookup = state.lookup_cell_aliased(&reg_val_expr(dst), off, Width::Byte);
            let old_v = lookup
                .map(|(i, _)| state.mem[i].value.atom_lean())
                .unwrap_or_else(|| format!("oldMemB_{}", state.fresh));
            let alias = alias_suffix(&lookup);
            format!(
                "have {} := stb_spec {} {} {} ({}) ({}) {}{}",
                hyp_name, reg(dst), offl, imm, base_addr, old_v, pc, alias,
            )
        }
        ST_H_IMM => {
            // sth_spec baseReg off imm baseAddr oldHalfVal pc
            let base_addr = reg_val_lean(dst);
            let lookup = state.lookup_cell_aliased(&reg_val_expr(dst), off, Width::Halfword);
            let old_v = lookup
                .map(|(i, _)| state.mem[i].value.atom_lean())
                .unwrap_or_else(|| format!("oldMemH_{}", state.fresh));
            let alias = alias_suffix(&lookup);
            format!(
                "have {} := sth_spec {} {} {} ({}) ({}) {}{}",
                hyp_name, reg(dst), offl, imm, base_addr, old_v, pc, alias,
            )
        }
        ST_W_IMM => {
            // stw_spec baseReg off imm baseAddr oldWordVal pc
            let base_addr = reg_val_lean(dst);
            // Hot region: `stw_bytes_spec` over 4 byte atoms, LE post bytes by decide; mirrors `write_hot_word_imm`.
            {
                let bexpr = reg_val_expr(dst);
                let (root, lo) = canon_addr(&bexpr, off);
                if state.hot_covers(&root, lo, lo + 4) {
                    let mut bargs = String::new();
                    let mut addrs = String::new();
                    let mut bounds = String::new();
                    let mut haddrs = String::new();
                    let mut n_alias = 0usize;
                    let mut fresh = state.fresh;
                    for k in 0..4i64 {
                        let found = state.mem.iter().find(|c| {
                            matches!(c.width, Width::Byte) && {
                                let (cr, cd) = canon_addr(&c.addr_base, c.addr_off);
                                cr == root && cd + c.delta == lo + k
                            }
                        });
                        match found {
                            Some(c) => {
                                let render_ok = c.addr_base.to_lean() == bexpr.to_lean()
                                    && c.addr_off == off
                                    && ((k == 0 && c.delta == 0) || c.delta == k);
                                if render_ok {
                                    addrs.push_str(&format!(" ({})",
                                        SymState::slot_expected_render(&bexpr, off, k)));
                                    haddrs.push_str(" rfl");
                                } else {
                                    addrs.push_str(&format!(" ({})",
                                        SymState::cell_render(c)));
                                    haddrs.push_str(&format!(
                                        " h_alias_{}_{}", pc, n_alias));
                                    n_alias += 1;
                                }
                                bargs.push_str(&format!(" {}", c.value.atom_lean()));
                                match &c.value {
                                    Expr::InitMem(n) =>
                                        bounds.push_str(&format!(" h{}_lt", n)),
                                    _ => bounds.push_str(" (by omega)"),
                                }
                            }
                            None => {
                                let n = format!("oldMemB_{}", fresh);
                                fresh += 1;
                                addrs.push_str(&format!(" ({})",
                                    SymState::slot_expected_render(&bexpr, off, k)));
                                haddrs.push_str(" rfl");
                                bargs.push_str(&format!(" {}", n));
                                bounds.push_str(&format!(" h{}_lt", n));
                            }
                        }
                    }
                    let w = insn.imm as u32; // toU64 imm % 2^32
                    let cb = w.to_le_bytes();
                    return Some(SpecCall {
                        hyp_name: hyp_name.clone(),
                        have_line: format!(
                            "have {} := stw_bytes_spec {} {} {} ({}){} {} {} {} {}{} {}{} \
(by decide) (by decide) (by decide) (by decide){}",
                            hyp_name, reg(dst), offl, imm, base_addr, bargs,
                            cb[0], cb[1], cb[2], cb[3], addrs, pc, bounds, haddrs,
                        ),
                    });
                }
            }
            let lookup = state.lookup_cell_aliased(&reg_val_expr(dst), off, Width::Word);
            let old_v = lookup
                .map(|(i, _)| state.mem[i].value.atom_lean())
                .unwrap_or_else(|| format!("oldMemW_{}", state.fresh));
            let alias = alias_suffix(&lookup);
            format!(
                "have {} := stw_spec {} {} {} ({}) ({}) {}{}",
                hyp_name, reg(dst), offl, imm, base_addr, old_v, pc, alias,
            )
        }
        ST_DW_IMM => {
            // stdw_spec baseReg off imm baseAddr oldDwordVal pc
            let base_addr = reg_val_lean(dst);
            let lookup = state.lookup_cell_aliased(&reg_val_expr(dst), off, Width::Dword);
            let old_v = lookup
                .map(|(i, _)| state.mem[i].value.atom_lean())
                .unwrap_or_else(|| format!("oldMemD_{}", state.fresh));
            let alias = alias_suffix(&lookup);
            format!(
                "have {} := stdw_spec {} {} {} ({}) ({}) {}{}",
                hyp_name, reg(dst), offl, imm, base_addr, old_v, pc, alias,
            )
        }
        ADD64_REG => {
            let v_old = reg_val_lean(dst);
            let v_src = reg_val_lean(src);
            format!(
                "have {} := add64_reg_spec {} {} ({}) ({}) {} (by decide)",
                hyp_name, reg(dst), reg(src), v_old, v_src, pc,
            )
        }
        SUB64_REG => {
            let v_old = reg_val_lean(dst);
            let v_src = reg_val_lean(src);
            format!(
                "have {} := sub64_reg_spec {} {} ({}) ({}) {} (by decide)",
                hyp_name, reg(dst), reg(src), v_old, v_src, pc,
            )
        }
        // Wrapping/bitwise reg-form ALU: `<op>_reg_spec dst src vOld v pc hne` (hne : dst ≠ .r10).
        MUL64_REG | OR64_REG | AND64_REG | XOR64_REG | LSH64_REG | RSH64_REG => {
            let v_old = reg_val_lean(dst);
            let v_src = reg_val_lean(src);
            let spec = match insn.opc {
                MUL64_REG => "mul64_reg_spec", OR64_REG  => "or64_reg_spec",
                AND64_REG => "and64_reg_spec", XOR64_REG => "xor64_reg_spec",
                LSH64_REG => "lsh64_reg_spec", RSH64_REG => "rsh64_reg_spec",
                _ => unreachable!(),
            };
            format!(
                "have {} := {} {} {} ({}) ({}) {} (by decide)",
                hyp_name, spec, reg(dst), reg(src), v_old, v_src, pc,
            )
        }
        MOV64_REG => {
            let v_old = reg_val_lean(dst);
            let v_src = reg_val_lean(src);
            format!(
                "have {} := mov64_reg_spec {} {} ({}) ({}) {} (by decide)",
                hyp_name, reg(dst), reg(src), v_old, v_src, pc,
            )
        }
        MOV64_IMM => {
            let v_old = reg_val_lean(dst);
            format!(
                "have {} := mov64_imm_spec {} {} ({}) {} (by decide)",
                hyp_name, reg(dst), imm, v_old, pc,
            )
        }
        LD_DW_IMM => {
            // lddw_spec dst imm vOld pc hne — same shape as mov64_imm.
            let v_old = reg_val_lean(dst);
            format!(
                "have {} := lddw_spec {} {} ({}) {} (by decide)",
                hyp_name, reg(dst), imm, v_old, pc,
            )
        }
        CALL_IMM => {
            // call_local_spec target cs r6V r7V r8V r9V r10V pc.
            // `cs` = pre-call stack (push happens in step(), not here); empty at top-level.
            let target = call_target.unwrap_or(0);
            let r6 = reg_val_lean(6); let r7 = reg_val_lean(7);
            let r8 = reg_val_lean(8); let r9 = reg_val_lean(9);
            let r10 = reg_val_lean(10);
            let cs = render_callstack(&state.call_stack);
            format!(
                "have {} := call_local_spec {} {} ({}) ({}) ({}) ({}) ({}) {}",
                hyp_name, target, cs, r6, r7, r8, r9, r10, pc,
            )
        }
        EXIT => {
            // exit_pops_spec frame cs r6Old r7Old r8Old r9Old r10Old pc.
            // r6Old..r10Old are the CURRENT (exit-time) register values in the exit_pops PRE.
            let r6 = reg_val_lean(6); let r7 = reg_val_lean(7);
            let r8 = reg_val_lean(8); let r9 = reg_val_lean(9);
            let r10 = reg_val_lean(10);
            // `frame`: retPc = `<callpc> + 1`, savedR6..savedR10 = CALL-TIME snapshot (NOT current — callee may clobber).
            // `cs` = stack below frame (empty at top-level).
            let n = state.call_stack.len();
            let (call_pc, saved) = state.call_stack.last()
                .map(|(p, s)| (*p, s.clone()))
                .unwrap_or((0, std::array::from_fn(|_| Expr::InitReg("?".into()))));
            let (sv6, sv7, sv8, sv9, sv10) = (
                saved[0].atom_lean(), saved[1].atom_lean(), saved[2].atom_lean(),
                saved[3].atom_lean(), saved[4].atom_lean());
            let cs = render_callstack(&state.call_stack[..n.saturating_sub(1)]);
            // `dsimp` forces iota reduction on `frame.savedR6..savedR10` fields (sl_block_iter doesn't run it).
            format!(
                "have {0} := exit_pops_spec ⟨{1} + 1, ({2}), ({3}), ({4}), ({5}), ({6})⟩ {7} ({8}) ({9}) ({10}) ({11}) ({12}) {13}\n  \
                 dsimp only at {0}",
                hyp_name,
                call_pc, sv6, sv7, sv8, sv9, sv10, cs,
                r6, r7, r8, r9, r10, pc,
            )
        }
        JEQ64_IMM | JEQ32_IMM => {
            let v_dst = reg_val_lean(dst);
            let target = jt;
            let h = branch_hyp_name.unwrap_or("h_branch?");
            let spec = if branch_taken == Some(true) {
                "jeq_imm_taken_spec"
            } else {
                "jeq_imm_not_taken_spec"
            };
            format!(
                "have {} := {} {} {} ({}) {} {} {}",
                hyp_name, spec, reg(dst), imm, v_dst, pc, target, h,
            )
        }
        JNE64_IMM | JNE32_IMM => {
            let v_dst = reg_val_lean(dst);
            let target = jt;
            let h = branch_hyp_name.unwrap_or("h_branch?");
            let spec = if branch_taken == Some(true) {
                "jne_imm_taken_spec"
            } else {
                "jne_imm_not_taken_spec"
            };
            format!(
                "have {} := {} {} {} ({}) {} {} {}",
                hyp_name, spec, reg(dst), imm, v_dst, pc, target, h,
            )
        }
        JGT64_IMM | JGT32_IMM => {
            let v_dst = reg_val_lean(dst);
            let target = jt;
            let h = branch_hyp_name.unwrap_or("h_branch?");
            let spec = if branch_taken == Some(true) {
                "jgt_imm_taken_spec"
            } else {
                "jgt_imm_not_taken_spec"
            };
            format!(
                "have {} := {} {} {} ({}) {} {} {}",
                hyp_name, spec, reg(dst), imm, v_dst, pc, target, h,
            )
        }
        JSGT64_IMM | JSGT32_IMM => {
            let v_dst = reg_val_lean(dst);
            let target = jt;
            let h = branch_hyp_name.unwrap_or("h_branch?");
            let spec = if branch_taken == Some(true) {
                "jsgt_imm_taken_spec"
            } else {
                "jsgt_imm_not_taken_spec"
            };
            format!(
                "have {} := {} {} {} ({}) {} {} {}",
                hyp_name, spec, reg(dst), imm, v_dst, pc, target, h,
            )
        }
        JSLE64_IMM | JSLE32_IMM => {
            let v_dst = reg_val_lean(dst);
            let target = jt;
            let h = branch_hyp_name.unwrap_or("h_branch?");
            let spec = if branch_taken == Some(true) {
                "jsle_imm_taken_spec"
            } else {
                "jsle_imm_not_taken_spec"
            };
            format!(
                "have {} := {} {} {} ({}) {} {} {}",
                hyp_name, spec, reg(dst), imm, v_dst, pc, target, h,
            )
        }
        JLT64_IMM | JLT32_IMM => {
            let v_dst = reg_val_lean(dst);
            let target = jt;
            let h = branch_hyp_name.unwrap_or("h_branch?");
            let spec = if branch_taken == Some(true) {
                "jlt_imm_taken_spec"
            } else {
                "jlt_imm_not_taken_spec"
            };
            format!(
                "have {} := {} {} {} ({}) {} {} {}",
                hyp_name, spec, reg(dst), imm, v_dst, pc, target, h,
            )
        }
        JLE64_IMM | JLE32_IMM => {
            let v_dst = reg_val_lean(dst);
            let target = jt;
            let h = branch_hyp_name.unwrap_or("h_branch?");
            let spec = if branch_taken == Some(true) {
                "jle_imm_taken_spec"
            } else {
                "jle_imm_not_taken_spec"
            };
            format!(
                "have {} := {} {} {} ({}) {} {} {}",
                hyp_name, spec, reg(dst), imm, v_dst, pc, target, h,
            )
        }
        JSLT64_IMM | JSLT32_IMM => {
            let v_dst = reg_val_lean(dst);
            let target = jt;
            let h = branch_hyp_name.unwrap_or("h_branch?");
            let spec = if branch_taken == Some(true) {
                "jslt_imm_taken_spec"
            } else {
                "jslt_imm_not_taken_spec"
            };
            format!(
                "have {} := {} {} {} ({}) {} {} {}",
                hyp_name, spec, reg(dst), imm, v_dst, pc, target, h,
            )
        }
        JEQ64_REG | JEQ32_REG => {
            let v_dst = reg_val_lean(dst);
            let v_src = reg_val_lean(src);
            let target = jt;
            let h = branch_hyp_name.unwrap_or("h_branch?");
            let spec = if branch_taken == Some(true) {
                "jeq_reg_taken_spec"
            } else {
                "jeq_reg_not_taken_spec"
            };
            format!(
                "have {} := {} {} {} ({}) ({}) {} {} {}",
                hyp_name, spec, reg(dst), reg(src), v_dst, v_src, pc, target, h,
            )
        }
        JNE64_REG | JNE32_REG => {
            let v_dst = reg_val_lean(dst);
            let v_src = reg_val_lean(src);
            let target = jt;
            let h = branch_hyp_name.unwrap_or("h_branch?");
            let spec = if branch_taken == Some(true) {
                "jne_reg_taken_spec"
            } else {
                "jne_reg_not_taken_spec"
            };
            format!(
                "have {} := {} {} {} ({}) ({}) {} {} {}",
                hyp_name, spec, reg(dst), reg(src), v_dst, v_src, pc, target, h,
            )
        }
        JLT64_REG | JLT32_REG => {
            let v_dst = reg_val_lean(dst);
            let v_src = reg_val_lean(src);
            let target = jt;
            let h = branch_hyp_name.unwrap_or("h_branch?");
            let spec = if branch_taken == Some(true) {
                "jlt_reg_taken_spec"
            } else {
                "jlt_reg_not_taken_spec"
            };
            format!(
                "have {} := {} {} {} ({}) ({}) {} {} {}",
                hyp_name, spec, reg(dst), reg(src), v_dst, v_src, pc, target, h,
            )
        }
        JSLE64_REG | JSLE32_REG => {
            let v_dst = reg_val_lean(dst);
            let v_src = reg_val_lean(src);
            let target = jt;
            let h = branch_hyp_name.unwrap_or("h_branch?");
            let spec = if branch_taken == Some(true) {
                "jsle_reg_taken_spec"
            } else {
                "jsle_reg_not_taken_spec"
            };
            format!(
                "have {} := {} {} {} ({}) ({}) {} {} {}",
                hyp_name, spec, reg(dst), reg(src), v_dst, v_src, pc, target, h,
            )
        }
        JGT64_REG | JGT32_REG | JLE64_REG | JLE32_REG | JSGE64_REG | JSGE32_REG
        | JGE64_REG | JGE32_REG | JSGT64_REG | JSGT32_REG | JSLT64_REG | JSLT32_REG
        | JSET64_REG | JSET32_REG => {
            let v_dst = reg_val_lean(dst);
            let v_src = reg_val_lean(src);
            let target = jt;
            let h = branch_hyp_name.unwrap_or("h_branch?");
            let stem = match insn.opc {
                JGT64_REG | JGT32_REG => "jgt_reg",
                JLE64_REG | JLE32_REG => "jle_reg",
                JSGE64_REG | JSGE32_REG => "jsge_reg",
                JGE64_REG | JGE32_REG => "jge_reg",
                JSGT64_REG | JSGT32_REG => "jsgt_reg",
                JSLT64_REG | JSLT32_REG => "jslt_reg",
                JSET64_REG | JSET32_REG => "jset_reg",
                _ => unreachable!(),
            };
            let suffix = if branch_taken == Some(true) { "taken_spec" } else { "not_taken_spec" };
            format!(
                "have {} := {}_{} {} {} ({}) ({}) {} {} {}",
                hyp_name, stem, suffix, reg(dst), reg(src), v_dst, v_src, pc, target, h,
            )
        }
        JGE64_IMM | JGE32_IMM | JSGE64_IMM | JSGE32_IMM | JSET64_IMM | JSET32_IMM => {
            let v_dst = reg_val_lean(dst);
            let target = jt;
            let h = branch_hyp_name.unwrap_or("h_branch?");
            let stem = match insn.opc {
                JGE64_IMM | JGE32_IMM => "jge_imm",
                JSGE64_IMM | JSGE32_IMM => "jsge_imm",
                JSET64_IMM | JSET32_IMM => "jset_imm",
                _ => unreachable!(),
            };
            let suffix = if branch_taken == Some(true) { "taken_spec" } else { "not_taken_spec" };
            format!(
                "have {} := {}_{} {} {} ({}) {} {} {}",
                hyp_name, stem, suffix, reg(dst), imm, v_dst, pc, target, h,
            )
        }
        JA => {
            let target = jt;
            format!("have {} := ja_spec {} {}", hyp_name, target, pc)
        }
        _ => return None,
    };
    Some(SpecCall { hyp_name, have_line })
}

/// Step one instruction's effect through `state`. Returns Ok(true) if
/// the instruction was a recognised non-terminator; Ok(false) if it
/// was `exit` (slice terminates); Err for opcodes the executor
/// doesn't model yet. `pc` is the analysis-PC of `insn` (only used
/// to resolve relative jump targets). `branch_taken` (when `Some`)
/// records the walker's branch decision so the path hypothesis is
/// the right shape (taken vs fall-through).
fn step(state: &mut SymState, insn: &ebpf::Insn, pc: Option<usize>,
        branch_taken: Option<bool>) -> Result<bool, String> {
    use ebpf::*;
    let (dst, src, off, imm) = (insn.dst, insn.src, insn.off as i64, insn.imm);
    match insn.opc {
        LD_B_REG => {
            let raw = state.read_mem(src, off, Width::Byte);
            state.write_reg(dst, Expr::Mod(Box::new(raw), 256));
        }
        LD_H_REG => {
            // `ldxh_spec` post is raw ↦U16 value (like ldxdw, not ldxb); reloaded compound → `hReloadLt_<pc>` side hyp.
            let raw = state.read_mem(src, off, Width::Halfword);
            if !matches!(raw, Expr::InitMem(_)) {
                let pcn = pc.unwrap_or(0);
                state.side_hyps.push((
                    format!("hReloadLt_{}", pcn),
                    format!("{} < 2 ^ 16", raw.to_lean()),
                ));
            }
            state.write_reg(dst, raw);
        }
        LD_W_REG => {
            let raw = state.read_mem(src, off, Width::Word);
            if !matches!(raw, Expr::InitMem(_)) {
                let pcn = pc.unwrap_or(0);
                state.side_hyps.push((
                    format!("hReloadLt_{}", pcn),
                    format!("{} < 2 ^ 32", raw.to_lean()),
                ));
            }
            state.write_reg(dst, raw);
        }
        LD_DW_REG => {
            let raw = state.read_mem(src, off, Width::Dword);
            // Reloaded compound (not fresh `oldMemD_N`): register `hReloadLt_<pc>` as the spec's `hv`.
            if !matches!(raw, Expr::InitMem(_) | Expr::ByteCombo(_)) {
                let pcn = pc.unwrap_or(0);
                state.side_hyps.push((
                    format!("hReloadLt_{}", pcn),
                    format!("{} < 2 ^ 64", raw.to_lean()),
                ));
            }
            state.write_reg(dst, raw);
        }
        ST_B_REG => {
            let cur = state.read_reg(src);
            state.write_mem(dst, off, Width::Byte, Expr::Mod(Box::new(cur), 256));
        }
        ST_H_REG => {
            let cur = state.read_reg(src);
            state.write_mem(dst, off, Width::Halfword, cur);
        }
        ST_W_REG => {
            let cur = state.read_reg(src);
            state.write_mem(dst, off, Width::Word, cur);
        }
        ST_DW_REG => {
            let cur = state.read_reg(src);
            state.write_mem(dst, off, Width::Dword, cur);
        }
        ADD64_IMM => {
            let cur = state.read_reg(dst);
            state.write_reg(dst, Expr::WrapAdd(
                Box::new(cur),
                Box::new(Expr::ToU64(Box::new(Expr::Const(imm)))),
            ));
        }
        AND64_IMM => {
            let cur = state.read_reg(dst);
            state.write_reg(dst, Expr::AndU64Imm(Box::new(cur), imm));
        }
        LSH64_IMM => {
            let cur = state.read_reg(dst);
            state.write_reg(dst, Expr::LshU64Imm(Box::new(cur), imm));
        }
        RSH64_IMM => {
            let cur = state.read_reg(dst);
            state.write_reg(dst, Expr::RshU64Imm(Box::new(cur), imm));
        }
        ST_B_IMM => {
            state.write_mem(dst, off, Width::Byte,
                Expr::Mod(Box::new(Expr::ToU64(Box::new(Expr::Const(imm)))), 256));
        }
        ST_H_IMM => {
            state.write_mem(dst, off, Width::Halfword, Expr::StHalfImm(imm));
        }
        ST_W_IMM => {
            state.write_mem(dst, off, Width::Word, Expr::StWordImm(imm));
        }
        ST_DW_IMM => {
            state.write_mem(dst, off, Width::Dword, Expr::StDwordImm(imm));
        }
        SUB64_IMM => {
            let cur = state.read_reg(dst);
            state.write_reg(dst, Expr::WrapSub(
                Box::new(cur),
                Box::new(Expr::ToU64(Box::new(Expr::Const(imm)))),
            ));
        }
        MOV64_IMM => {
            state.write_reg(dst, Expr::ToU64(Box::new(Expr::Const(imm))));
        }
        LD_DW_IMM => {
            // lddw = mov64-from-immediate (merged 64-bit value already in `imm`).
            state.write_reg(dst, Expr::ToU64(Box::new(Expr::Const(imm))));
        }
        MOV64_REG => {
            let v = state.read_reg(src);
            state.write_reg(dst, v);
        }
        ADD64_REG => {
            let a = state.read_reg(dst);
            let b = state.read_reg(src);
            state.write_reg(dst, Expr::WrapAdd(Box::new(a), Box::new(b)));
        }
        SUB64_REG => {
            let a = state.read_reg(dst);
            let b = state.read_reg(src);
            state.write_reg(dst, Expr::WrapSub(Box::new(a), Box::new(b)));
        }
        MUL64_REG => {
            let a = state.read_reg(dst);
            let b = state.read_reg(src);
            state.write_reg(dst, Expr::WrapMul(Box::new(a), Box::new(b)));
        }
        OR64_REG | AND64_REG | XOR64_REG | LSH64_REG | RSH64_REG => {
            let a = state.read_reg(dst).atom_lean();
            let b = state.read_reg(src).atom_lean();
            let r = match insn.opc {
                OR64_REG  => format!("({} ||| {}) % U64_MODULUS", a, b),
                AND64_REG => format!("({} &&& {}) % U64_MODULUS", a, b),
                XOR64_REG => format!("({} ^^^ {}) % U64_MODULUS", a, b),
                LSH64_REG => format!("({} <<< ({} % 64)) % U64_MODULUS", a, b),
                RSH64_REG => format!("{} >>> ({} % 64)", a, b),
                _ => unreachable!(),
            };
            state.write_reg(dst, Expr::Raw(r));
        }
        OR64_IMM | XOR64_IMM | MUL64_IMM | DIV64_IMM | MOD64_IMM | NEG64 => {
            let a = state.read_reg(dst).atom_lean();
            let i = lean_off(imm);
            let r = match insn.opc {
                OR64_IMM  => format!("({} ||| toU64 {}) % U64_MODULUS", a, i),
                XOR64_IMM => format!("({} ^^^ toU64 {}) % U64_MODULUS", a, i),
                MUL64_IMM => format!("wrapMul {} (toU64 {})", a, i),
                DIV64_IMM => format!("({} / toU64 {}) % U64_MODULUS", a, i),
                MOD64_IMM => format!("{} % toU64 {}", a, i),
                NEG64     => format!("wrapNeg {}", a),
                _ => unreachable!(),
            };
            state.write_reg(dst, Expr::Raw(r));
        }
        ADD32_IMM | SUB32_IMM | MUL32_IMM | OR32_IMM | AND32_IMM | XOR32_IMM
        | LSH32_IMM | RSH32_IMM | MOV32_IMM | DIV32_IMM | MOD32_IMM | NEG32 => {
            let a = state.read_reg(dst).atom_lean();
            let i = lean_off(imm);
            let r = match insn.opc {
                ADD32_IMM => format!("wrapAdd32 {} (toU64 {})", a, i),
                SUB32_IMM => format!("wrapSub32 {} (toU64 {})", a, i),
                MUL32_IMM => format!("wrapMul32 {} (toU64 {})", a, i),
                OR32_IMM  => format!("({} ||| toU64 {}) % U32_MODULUS", a, i),
                AND32_IMM => format!("({} &&& toU64 {}) % U32_MODULUS", a, i),
                XOR32_IMM => format!("({} ^^^ toU64 {}) % U32_MODULUS", a, i),
                LSH32_IMM => format!("({} <<< (toU64 {} % 32)) % U32_MODULUS", a, i),
                RSH32_IMM => format!("({} % U32_MODULUS) >>> (toU64 {} % 32)", a, i),
                MOV32_IMM => format!("toU64 {} % U32_MODULUS", i),
                DIV32_IMM => format!("({} % U32_MODULUS / (toU64 {} % U32_MODULUS)) % U32_MODULUS", a, i),
                MOD32_IMM => format!("{} % U32_MODULUS % (toU64 {} % U32_MODULUS)", a, i),
                NEG32     => format!("wrapNeg32 {}", a),
                _ => unreachable!(),
            };
            state.write_reg(dst, Expr::Raw(r));
        }
        // arsh (arithmetic shift right) — let/if/else post via arsh_render.
        ARSH64_IMM | ARSH32_IMM => {
            let a = state.read_reg(dst).atom_lean();
            let bits = if insn.opc == ARSH64_IMM { 64 } else { 32 };
            state.write_reg(dst, Expr::Raw(arsh_render(&a, &format!("toU64 {}", lean_off(imm)), bits)));
        }
        ARSH64_REG | ARSH32_REG => {
            let a = state.read_reg(dst).atom_lean();
            let b = state.read_reg(src).atom_lean();
            let bits = if insn.opc == ARSH64_REG { 64 } else { 32 };
            state.write_reg(dst, Expr::Raw(arsh_render(&a, &b, bits)));
        }
        ADD32_REG | SUB32_REG | MUL32_REG | OR32_REG | AND32_REG | XOR32_REG
        | LSH32_REG | RSH32_REG | MOV32_REG => {
            let a = state.read_reg(dst).atom_lean();
            let b = state.read_reg(src).atom_lean();
            let r = match insn.opc {
                ADD32_REG => format!("wrapAdd32 {} {}", a, b),
                SUB32_REG => format!("wrapSub32 {} {}", a, b),
                MUL32_REG => format!("wrapMul32 {} {}", a, b),
                OR32_REG  => format!("({} ||| {}) % U32_MODULUS", a, b),
                AND32_REG => format!("({} &&& {}) % U32_MODULUS", a, b),
                XOR32_REG => format!("({} ^^^ {}) % U32_MODULUS", a, b),
                LSH32_REG => format!("({} <<< ({} % 32)) % U32_MODULUS", a, b),
                RSH32_REG => format!("({} % U32_MODULUS) >>> ({} % 32)", a, b),
                MOV32_REG => format!("{} % U32_MODULUS", b),
                _ => unreachable!(),
            };
            state.write_reg(dst, Expr::Raw(r));
        }
        // div/mod reg-form: surface divisor non-zeroness as `hnz_<pc>` hyp; read src before dst write so rendering matches spec arg.
        DIV64_REG | MOD64_REG | DIV32_REG | MOD32_REG => {
            let a = state.read_reg(dst).atom_lean();
            let b = state.read_reg(src).atom_lean();
            let pcn = pc.unwrap_or(0);
            let prop = match insn.opc {
                DIV64_REG | MOD64_REG => format!("{} ≠ 0", b),
                _ /* 32-bit */        => format!("{} % U32_MODULUS ≠ 0", b),
            };
            state.side_hyps.push((format!("hnz_{}", pcn), prop));
            let r = match insn.opc {
                DIV64_REG => format!("({} / {}) % U64_MODULUS", a, b),
                MOD64_REG => format!("{} % {}", a, b),
                DIV32_REG => format!("({} % U32_MODULUS / ({} % U32_MODULUS)) % U32_MODULUS", a, b),
                MOD32_REG => format!("{} % U32_MODULUS % ({} % U32_MODULUS)", a, b),
                _ => unreachable!(),
            };
            state.write_reg(dst, Expr::Raw(r));
        }
        // Conditional jumps: record path hyp (taken or fall-through); no reg/mem change. Default = fall-through (common guard shape).
        JEQ64_IMM | JEQ32_IMM => {
            let r = state.read_reg(dst);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JeqImm, dst_value: r, src_value: None, imm,
                taken: branch_taken.unwrap_or(false),            });
        }
        JNE64_IMM | JNE32_IMM => {
            let r = state.read_reg(dst);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JneImm, dst_value: r, src_value: None, imm,
                taken: branch_taken.unwrap_or(false),            });
        }
        JGT64_IMM | JGT32_IMM => {
            let r = state.read_reg(dst);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JgtImm, dst_value: r, src_value: None, imm,
                taken: branch_taken.unwrap_or(false),            });
        }
        JSGT64_IMM | JSGT32_IMM => {
            let r = state.read_reg(dst);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JsgtImm, dst_value: r, src_value: None, imm,
                taken: branch_taken.unwrap_or(false),            });
        }
        JSLE64_IMM | JSLE32_IMM => {
            let r = state.read_reg(dst);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JsleImm, dst_value: r, src_value: None, imm,
                taken: branch_taken.unwrap_or(false),            });
        }
        JLT64_IMM | JLT32_IMM => {
            let r = state.read_reg(dst);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JltImm, dst_value: r, src_value: None, imm,
                taken: branch_taken.unwrap_or(false),            });
        }
        JLE64_IMM | JLE32_IMM => {
            let r = state.read_reg(dst);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JleImm, dst_value: r, src_value: None, imm,
                taken: branch_taken.unwrap_or(false),            });
        }
        JSLT64_IMM | JSLT32_IMM => {
            let r = state.read_reg(dst);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JsltImm, dst_value: r, src_value: None, imm,
                taken: branch_taken.unwrap_or(false),            });
        }
        JGE64_IMM | JGE32_IMM | JSGE64_IMM | JSGE32_IMM | JSET64_IMM | JSET32_IMM => {
            let r = state.read_reg(dst);
            let kind = match insn.opc {
                JGE64_IMM | JGE32_IMM => BranchKind::JgeImm,
                JSGE64_IMM | JSGE32_IMM => BranchKind::JsgeImm,
                JSET64_IMM | JSET32_IMM => BranchKind::JsetImm,
                _ => unreachable!(),
            };
            state.branch_hyps.push(BranchHyp {
                kind, dst_value: r, src_value: None, imm,
                taken: branch_taken.unwrap_or(false),            });
        }
        JEQ64_REG | JEQ32_REG => {
            let rd = state.read_reg(dst);
            let rs = state.read_reg(src);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JeqReg, dst_value: rd, src_value: Some(rs), imm: 0,
                taken: branch_taken.unwrap_or(false),            });
        }
        JNE64_REG | JNE32_REG => {
            let rd = state.read_reg(dst);
            let rs = state.read_reg(src);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JneReg, dst_value: rd, src_value: Some(rs), imm: 0,
                taken: branch_taken.unwrap_or(false),            });
        }
        JLT64_REG | JLT32_REG => {
            let rd = state.read_reg(dst);
            let rs = state.read_reg(src);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JltReg, dst_value: rd, src_value: Some(rs), imm: 0,
                taken: branch_taken.unwrap_or(false),            });
        }
        JSLE64_REG | JSLE32_REG => {
            let rd = state.read_reg(dst);
            let rs = state.read_reg(src);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JsleReg, dst_value: rd, src_value: Some(rs), imm: 0,
                taken: branch_taken.unwrap_or(false),            });
        }
        JGT64_REG | JGT32_REG | JLE64_REG | JLE32_REG | JSGE64_REG | JSGE32_REG
        | JGE64_REG | JGE32_REG | JSGT64_REG | JSGT32_REG | JSLT64_REG | JSLT32_REG
        | JSET64_REG | JSET32_REG => {
            let rd = state.read_reg(dst);
            let rs = state.read_reg(src);
            let kind = match insn.opc {
                JGT64_REG | JGT32_REG => BranchKind::JgtReg,
                JLE64_REG | JLE32_REG => BranchKind::JleReg,
                JSGE64_REG | JSGE32_REG => BranchKind::JsgeReg,
                JGE64_REG | JGE32_REG => BranchKind::JgeReg,
                JSGT64_REG | JSGT32_REG => BranchKind::JsgtReg,
                JSLT64_REG | JSLT32_REG => BranchKind::JsltReg,
                JSET64_REG | JSET32_REG => BranchKind::JsetReg,
                _ => unreachable!(),
            };
            state.branch_hyps.push(BranchHyp {
                kind, dst_value: rd, src_value: Some(rs), imm: 0,
                taken: branch_taken.unwrap_or(false),            });
        }
        JA => { /* unconditional fall-through reset is handled by the caller's PC walk */ }
        // call_local: bumps r10 by 0x1000 and pushes frame; PC redirect handled by walker.
        CALL_IMM => {
            state.saw_call = true;
            // Snapshot call-time r6..r10 — the frame call_local pushes and exit_pops must restore.
            let r6 = state.read_reg(6); let r7 = state.read_reg(7);
            let r8 = state.read_reg(8); let r9 = state.read_reg(9);
            // Nat.add (not wrapAdd) to match call_local_spec's `r10V + 0x1000` so chains compose.
            let r10_old = state.read_reg(10);
            state.write_reg(10, Expr::NatAdd(
                Box::new(r10_old.clone()),
                Box::new(Expr::Const(0x1000)),
            ));
            // Frame retPc renders as `<callpc> + 1` (Lean keeps unreduced); resume PC is callpc + 1.
            let call_pc = pc.unwrap_or(0);
            state.call_stack.push((call_pc, [r6, r7, r8, r9, r10_old]));
        }
        EXIT => {
            if state.call_stack.is_empty() {
                return Ok(false);
            } else {
                // Nested exit: pop frame + undo r10's +0x1000 bump. Callee must not touch r6..r9 (Solana ABI);
                // ABI violation → chain won't compose → sl_block_iter residual.
                let _ = state.call_stack.pop();
                let r10_cur = state.read_reg(10);
                state.write_reg(10, Expr::WrapSub(
                    Box::new(r10_cur),
                    Box::new(Expr::Const(0x1000)),
                ));
            }
        }
        opc => return Err(format!("symbolic executor: opcode 0x{:02x} not yet modelled", opc)),
    }
    Ok(true)
}

struct LiftOutput {
    lean:        String,
    module_name: String,
    text_bytes:  usize,
    insn_count:  usize,
    /// CU count of the lifted triple (`n` in `cuTripleWithinMem n …`).
    /// Surfaced so `--qedmeta` can cross-check the claimed `cu_budget`.
    cu:          usize,
    /// Optional asm-refines-intrinsic theorem `(module_name, lean)`,
    /// emitted when the arm matches the refinement registry.
    refinement:  Option<(String, String)>,
    /// Optional aggregation module `(import_module, lean)` the refinement
    /// imports (e.g. `PToken.TransferAggregation`), mechanically emitted
    /// from the lift's owned-byte pattern. Written to its canonical
    /// `examples/lean/<module-path>.lean` location.
    aggregation: Option<(String, String)>,
}

/// Lift without a qedrecover layout sidecar (tests, batch, single-arm `--idl`): refinement
/// codegen resolves account layouts from the IDL only. `--qedmeta` runs call
/// `lift_one_with_layouts` directly so the sidecar's `[[account_layout]]` is the layout source.
/// True if `imm` is the hash of a syscall the lift emits an effect spec for.
/// Such a call must take the decode-pins path (so `syscall_pcs` resolves it to
/// `.call <ctor>`) and the `sl_block_iter` proof body (so the `call_<name>_spec`
/// preamble is threaded); the small `decodeProgram` bridge and bare `sl_block_auto`
/// can't handle a syscall. Mirrors the trace dispatch in `lift_one_with_layouts`.
fn imm_is_modeled_syscall(imm: u32) -> bool {
    const NAMES: [&[u8]; 11] = [
        b"sol_memset_", b"sol_memcpy_", b"sol_memmove_", b"sol_memcmp_",
        b"sol_log_", b"sol_get_sysvar", b"sol_set_return_data", b"sol_sha256",
        b"sol_create_program_address",
        b"sol_invoke_signed_rust", b"sol_invoke_signed_c",
    ];
    NAMES.iter().any(|name| imm == ebpf::hash_symbol_name(name))
}

fn lift_one(
    so_path:         &Path,
    ctx:             &BinaryCtx,
    analysis:        &Analysis<'_>,
    target_disc:     Option<i64>,
    module_override: Option<String>,
    trace:           Option<&[usize]>,
    arm_name:        Option<&str>,
    idl:             Option<&serde_json::Value>,
    arm_entry:       Option<usize>,
) -> Result<LiftOutput, Box<dyn std::error::Error>> {
    lift_one_with_layouts(so_path, ctx, analysis, target_disc, module_override,
        trace, arm_name, idl, arm_entry, None, None)
}

#[allow(clippy::too_many_arguments)]
fn lift_one_with_layouts(
    so_path:         &Path,
    ctx:             &BinaryCtx,
    analysis:        &Analysis<'_>,
    target_disc:     Option<i64>,
    module_override: Option<String>,
    trace:           Option<&[usize]>,
    arm_name:        Option<&str>,
    idl:             Option<&serde_json::Value>,
    // Recovered arm-entry PC from qedrecover sidecar (#41 Phase 4): seeds no-trace static walk
    // and cross-checks trace walk. `None` = prior behaviour (disc-walk / trace as-is).
    arm_entry:       Option<usize>,
    // qedrecover-emitted account layouts (#41 loop closure): preferred over `idl` in the
    // refinement codegen. `None` = resolve layouts from `idl` (the wrapper's behaviour).
    sidecar_layouts: Option<&[AccountLayout]>,
    // Spec-driven refinement descriptor (the seam to qedspec). When `Some`, the refinement
    // codegen builds `AsmRefinesFieldUpdate` from the descriptor and IGNORES `arm_name` /
    // `refine_registry`. `None` = the registry-driven path (unchanged).
    descriptor:      Option<&RefinementDescriptor>,
) -> Result<LiftOutput, Box<dyn std::error::Error>> {
    let executable  = &ctx.executable;
    let text_offset = ctx.text_offset;
    let text_bytes  = ctx.text_bytes.as_slice();
    let insns       = &ctx.insns;

    eprintln!("=== decoded insns ===");
    for (i, ins) in insns.iter().enumerate() {
        let rendered = insn_to_lean(ins, i).unwrap_or_else(|e| format!("?? ({})", e));
        eprintln!("  pc={:3}  opc=0x{:02x}  {}", i, ins.opc, rendered);
    }
    eprintln!();

    let so_stem = so_path.file_stem()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_else(|| "lifted".to_string());
    let module_name = module_override.unwrap_or_else(|| {
        // PascalCase: byte_increment → ByteIncrement
        let mut out = String::new();
        let mut up = true;
        for c in so_stem.chars() {
            if c == '_' || c == '-' { up = true; continue; }
            if up { out.extend(c.to_uppercase()); up = false; }
            else  { out.push(c); }
        }
        format!("{}Lifted", out)
    });

    // NOT load-bearing for the Hoare triple. Large binaries blow `maxRecDepth` as a ByteArray
    // literal — emit per-PC decode pins (hex-string, H8) above 4096 bytes; small binaries get the full bridge.
    // A modeled syscall ALSO forces the pins path: the small `decodeProgram` bridge renders the raw
    // decode (`.call_local <unresolved>`) for a syscall hash, whereas the pins path threads `syscall_pcs`
    // to render `.call <ctor>` at the syscall PC (matching the spec-call preamble).
    const DECODE_BRIDGE_MAX_BYTES: usize = 4096;
    let has_modeled_syscall = insns.iter().any(|ins|
        ins.opc == ebpf::CALL_IMM && imm_is_modeled_syscall(ins.imm as u32));
    let emit_decode_bridge =
        text_bytes.len() <= DECODE_BRIDGE_MAX_BYTES && !has_modeled_syscall;

    let decode_claim = render::decode_claim(emit_decode_bridge);
    let mut out = render::module_intro(so_path, decode_claim, &so_stem, &module_name);

    if emit_decode_bridge {
        out.push_str(&render::text_bytearray_defs(&module_name, text_bytes, text_offset));
    } else {
        out.push_str(&render::decode_bridge_omitted_note(&module_name, text_bytes.len()));
    }

    // Render the full `.text` as `Array Insn` (sanity, not load-bearing for the Hoare triple).
    // Skip if any opcode can't be rendered — lets us lift a good arm from a partially-modelled binary.
    let mut rendered_insns: Vec<String> = Vec::with_capacity(insns.len());
    let mut decode_skip_reason: Option<String> = None;
    if emit_decode_bridge {
        for (i, insn) in insns.iter().enumerate() {
            let tgt = resolve_call_target_logical(ctx, &analysis, insn);
            let jtgt = Some(resolve_jump_target(ctx, i, insn.off as i64));
            match insn_to_lean_full(insn, i, tgt, jtgt) {
                Ok(s)  => rendered_insns.push(s),
                Err(e) => { decode_skip_reason = Some(format!("pc={} opc=0x{:02x}: {}", i, insn.opc, e)); break; }
            }
        }
    }
    if !emit_decode_bridge {
    } else if let Some(reason) = decode_skip_reason {
        out.push_str(&render::decode_renderer_skip_note(&module_name, &reason));
    } else {
        // H2: registry resolves call murmur3 imm → .call_local; empty registry fail-closes to .unknown.
        let reg = function_registry(ctx);
        out.push_str(&render::decoded_insns_section(
            &module_name,
            &rendered_insns,
            &function_registry_lean(&reg),
        ));
    }

    let entry_pc: usize = executable.get_entrypoint_instruction_offset();
    // Hot regions: grow monotonically across walk retries (H8 Phase B); attempt cap is a safety net.
    let mut hot_regions: std::collections::BTreeMap<String, Vec<(i64, i64)>> =
        Default::default();
    let mut blob_splits: std::collections::BTreeMap<(String, i64), i64> =
        Default::default();
    let mut walk_attempts = 0usize;
    let (mut state, spec_calls, block_pcs, exit_pc) = loop {
    walk_attempts += 1;
    if walk_attempts > 8 {
        return Err("qedlift: hot-region demotion did not converge after 8 \
                    walk retries".into());
    }
    let mut spec_calls: Vec<SpecCall> = Vec::new();

    // CFG walk + symbolic execution: straight-line→pc+1, ja→target, cond-jump→fall-through,
    // call_local→push+jump, exit/empty-stack→done, exit/non-empty→pop+resume.
    // Starts at ELF entrypoint (NOT analysis PC 0: linker may place helpers before it).
    let mut block_pcs: Vec<usize> = Vec::new();
    let exit_pc: usize;
    let mut state = SymState::default();
    state.hot_regions = hot_regions.clone();
    state.blob_splits = blob_splits.clone();
    {
        let mut ti: usize = 0; // trace cursor; pc_iter mirrors trace[ti] in trace mode
        let mut pc_iter: usize = match trace {
            Some(t) => {
                // #41 Phase 4: cross-check sidecar arm_entry_pc is on the trace (mismatch → fail-closed).
                if let Some(arm) = arm_entry {
                    if !t.contains(&arm) {
                        return Err(format!(
                            "qedmeta/trace mismatch: recovered arm_entry_pc {} \
                             is not on the execution trace (the sidecar describes \
                             a different arm than the trace executes)", arm).into());
                    }
                }
                t[0] // load_trace guarantees non-empty
            }
            // #41 Phase 4: seed from recovered arm_entry (no disc-cascade nav); fallback = entry_pc.
            None => arm_entry.unwrap_or(entry_pc),
        };
        // Walk cap: prevents runaway on unmodelled back-branches; generous for deep dispatcher cascades.
        let walk_cap: usize = match trace { Some(t) => t.len() + 8, None => 1024 };
        let mut walk_steps: usize = 0;
        loop {
            walk_steps += 1;
            if walk_steps > walk_cap {
                return Err(format!(
                    "walker exceeded {} steps at pc={} (likely back-branch \
                     defaulted to fall-through)", walk_cap, pc_iter).into());
            }
            if let Some(t) = trace {
                if ti >= t.len() { exit_pc = pc_iter; break; }
                pc_iter = t[ti];
            }
            if pc_iter >= insns.len() { exit_pc = pc_iter; break; }
            let ins = &insns[pc_iter];

            // EXIT: nested return (pop call stack + restore r6..r10) or top-level terminator.
            if ins.opc == ebpf::EXIT {
                if state.call_stack.is_empty() {
                    exit_pc = pc_iter;
                    break;
                } else {
                    block_pcs.push(pc_iter);
                    // Emit spec call BEFORE popping (r6..r10 still at callee-frame values).
                    if let Some(sc) = spec_call_for(&state, ins, pc_iter, None, None, None, None) {
                        spec_calls.push(sc);
                    }
                    let (call_pc, saved) = state.call_stack.pop().unwrap();
                    // Mirror exit_pops_spec: restore saved r6..r10 so post-state matches (callee may have clobbered them).
                    for (i, r) in (6u8..=10).enumerate() {
                        state.write_reg(r, saved[i].clone());
                    }
                    // Trace: next PC from trace; static: jump to callpc+1.
                    if trace.is_some() { ti += 1; } else { pc_iter = call_pc + 1; }
                    continue;
                }
            }

            // Syscall (trace): call_imm returning to pc+1 (no BPF frame push) → dispatch on hash.
            if ins.opc == ebpf::CALL_IMM {
                if let Some(t) = trace {
                    if t.get(ti + 1).copied() == Some(pc_iter + 1) {
                        let imm = ins.imm as u32;
                        if imm == ebpf::hash_symbol_name(b"sol_memset_") {
                            emit_sol_memset(&mut state, &mut spec_calls,
                                            &mut block_pcs, pc_iter);
                            ti += 1;
                            continue;
                        }
                        if imm == ebpf::hash_symbol_name(b"sol_get_sysvar") {
                            // H8 Phase C-2: faithful buffer-write (rent/offset 0/length 17; else fail-closed).
                            emit_sol_get_sysvar(&mut state, &mut spec_calls,
                                &mut block_pcs, pc_iter, ctx)?;
                            ti += 1;
                            continue;
                        }
                        if imm == ebpf::hash_symbol_name(b"sol_log_") {
                            emit_sol_log(&mut state, &mut spec_calls, &mut block_pcs,
                                pc_iter);
                            ti += 1;
                            continue;
                        }
                        if imm == ebpf::hash_symbol_name(b"sol_memcpy_") {
                            emit_sol_memcpy(&mut state, &mut spec_calls, &mut block_pcs,
                                pc_iter, false);
                            ti += 1;
                            continue;
                        }
                        if imm == ebpf::hash_symbol_name(b"sol_memmove_") {
                            emit_sol_memcpy(&mut state, &mut spec_calls, &mut block_pcs,
                                pc_iter, true);
                            ti += 1;
                            continue;
                        }
                        if imm == ebpf::hash_symbol_name(b"sol_memcmp_") {
                            emit_sol_memcmp(&mut state, &mut spec_calls, &mut block_pcs,
                                pc_iter);
                            ti += 1;
                            continue;
                        }
                        if imm == ebpf::hash_symbol_name(b"sol_set_return_data") {
                            emit_sol_set_return_data(&mut state, &mut spec_calls,
                                &mut block_pcs, pc_iter);
                            ti += 1;
                            continue;
                        }
                        if imm == ebpf::hash_symbol_name(b"sol_sha256") {
                            // H6: single-slice hash — descriptor cells consumed
                            // from the program's stores, input/output introduced.
                            emit_sol_sha256(&mut state, &mut spec_calls,
                                &mut block_pcs, pc_iter)?;
                            ti += 1;
                            continue;
                        }
                        if imm == ebpf::hash_symbol_name(b"sol_create_program_address") {
                            // H6: single-seed PDA — descriptor from stores, seed +
                            // program_id + output introduced; off-curve surfaced.
                            emit_sol_create_program_address(&mut state, &mut spec_calls,
                                &mut block_pcs, pc_iter)?;
                            ti += 1;
                            continue;
                        }
                        // CPI: step-level stub (Cpi.exec = r0:=0) — effect-free on invoked accounts; callee writes not captured. See call_sol_invoke_signed_spec.
                        if imm == ebpf::hash_symbol_name(b"sol_invoke_signed_rust") {
                            emit_r0_syscall(&mut state, &mut spec_calls, &mut block_pcs,
                                pc_iter, "call_sol_invoke_signed_spec", ".sol_invoke_signed", "InvokeSigned");
                            ti += 1;
                            continue;
                        }
                        if imm == ebpf::hash_symbol_name(b"sol_invoke_signed_c") {
                            emit_r0_syscall(&mut state, &mut spec_calls, &mut block_pcs,
                                pc_iter, "call_sol_invoke_signed_c_spec", ".sol_invoke_signed_c", "InvokeSignedC");
                            ti += 1;
                            continue;
                        }
                        return Err(format!(
                            "call_imm at pc {} is a syscall (trace returns to {} \
                             without a frame push) with imm hash 0x{:08x}, but only \
                             sol_memset_ / sol_memcpy_ / sol_memmove_ / sol_memcmp_ / \
                             sol_get_sysvar / sol_log_ / sol_set_return_data / \
                             sol_invoke_signed{{,_c}} are modelled so far. \
                             This arm needs a syscall-effect spec for that hash.",
                            pc_iter, pc_iter + 1, imm).into());
                    }
                }
            }

            block_pcs.push(pc_iter);
            let call_target = resolve_call_target_logical(ctx, &analysis, ins);
            // Branch hyp name indexed by number of branches seen so far.
            let branch_idx = state.branch_hyps.len();
            let branch_hyp = format!("h_branch{}", branch_idx);
            let is_cond_jump = matches!(ins.opc,
                ebpf::JEQ64_IMM | ebpf::JEQ32_IMM |
                ebpf::JNE64_IMM | ebpf::JNE32_IMM |
                ebpf::JGT64_IMM | ebpf::JGT32_IMM |
                ebpf::JSGT64_IMM | ebpf::JSGT32_IMM |
                ebpf::JSLE64_IMM | ebpf::JSLE32_IMM |
                ebpf::JLT64_IMM | ebpf::JLT32_IMM |
                ebpf::JLE64_IMM | ebpf::JLE32_IMM |
                ebpf::JSLT64_IMM | ebpf::JSLT32_IMM |
                ebpf::JGE64_IMM | ebpf::JGE32_IMM |
                ebpf::JSGE64_IMM | ebpf::JSGE32_IMM |
                ebpf::JSET64_IMM | ebpf::JSET32_IMM |
                ebpf::JEQ64_REG | ebpf::JEQ32_REG |
                ebpf::JNE64_REG | ebpf::JNE32_REG |
                ebpf::JLT64_REG | ebpf::JLT32_REG |
                ebpf::JSLE64_REG | ebpf::JSLE32_REG |
                ebpf::JGT64_REG | ebpf::JGT32_REG |
                ebpf::JLE64_REG | ebpf::JLE32_REG |
                ebpf::JSGE64_REG | ebpf::JSGE32_REG |
                ebpf::JGE64_REG | ebpf::JGE32_REG |
                ebpf::JSGT64_REG | ebpf::JSGT32_REG |
                ebpf::JSLT64_REG | ebpf::JSLT32_REG |
                ebpf::JSET64_REG | ebpf::JSET32_REG);
            let branch_hyp_for_call = if is_cond_jump {
                Some(branch_hyp.as_str())
            } else { None };
            // Slot-relative offset → logical PC (handles lddw 2-slot encoding); shared by spec + walk.
            let jtgt = resolve_jump_target(ctx, pc_iter, ins.off as i64);
            // Trace: taken iff next PC ≠ pc+1; target mismatch vs decoded offset = fail-closed.
            // Static: discriminator-driven where possible, else fall-through.
            let branch_taken: Option<bool> = if let Some(t) = trace {
                if is_cond_jump {
                    let next = t.get(ti + 1).copied();
                    let taken = next != Some(pc_iter + 1);
                    if taken {
                        if let Some(n) = next {
                            if n as i64 != jtgt {
                                return Err(format!(
                                    "trace/decoder mismatch at pc {}: trace goes to {} \
                                     but the decoded jump target is {} (off={})",
                                    pc_iter, n, jtgt, ins.off).into());
                            }
                        }
                    }
                    Some(taken)
                } else { None }
            } else {
                match (ins.opc, target_disc) {
                    (ebpf::JEQ64_IMM, Some(td)) | (ebpf::JEQ32_IMM, Some(td)) => {
                        Some(ins.imm == td)
                    }
                    (ebpf::JNE64_IMM, Some(td)) | (ebpf::JNE32_IMM, Some(td)) => {
                        Some(ins.imm != td)
                    }
                    // JGT: take branch when td > imm (disc > N → upper_half pattern).
                    (ebpf::JGT64_IMM, Some(td)) | (ebpf::JGT32_IMM, Some(td)) => {
                        Some(td > ins.imm)
                    }
                    _ if is_cond_jump => Some(false), // default: not-taken
                    _ => None,
                }
            };
            if let Some(sc) = spec_call_for(&state, ins, pc_iter, call_target,
                                            branch_hyp_for_call, branch_taken, Some(jtgt)) {
                spec_calls.push(sc);
            }
            step(&mut state, ins, Some(pc_iter), branch_taken)?;
            // Phase A aliasing: surface address equation for same-cell different-rendering (consumed by rw [h_alias_<pc>]).
            if let Some((lhs, rhs)) = state.pending_alias.take() {
                state.side_hyps.push((
                    format!("h_alias_{}", pc_iter),
                    format!("{} = {}", lhs, rhs),
                ));
            }
            for (i, (lhs, rhs)) in state.pending_slot_aliases.drain(..).enumerate() {
                state.side_hyps.push((
                    format!("h_alias_{}_{}", pc_iter, i),
                    format!("{} = {}", lhs, rhs),
                ));
            }

            if trace.is_some() {
                ti += 1;
                continue;
            }
            match ins.opc {
                ebpf::JA => {
                    pc_iter = jtgt as usize;
                }
                ebpf::JEQ64_IMM | ebpf::JEQ32_IMM |
                ebpf::JNE64_IMM | ebpf::JNE32_IMM |
                ebpf::JGT64_IMM | ebpf::JGT32_IMM |
                ebpf::JSGT64_IMM | ebpf::JSGT32_IMM |
                ebpf::JSLE64_IMM | ebpf::JSLE32_IMM |
                ebpf::JLT64_IMM | ebpf::JLT32_IMM |
                ebpf::JLE64_IMM | ebpf::JLE32_IMM |
                ebpf::JEQ64_REG | ebpf::JEQ32_REG |
                ebpf::JNE64_REG | ebpf::JNE32_REG |
                ebpf::JLT64_REG | ebpf::JLT32_REG |
                ebpf::JSLE64_REG | ebpf::JSLE32_REG
                    if branch_taken == Some(true) => {
                    pc_iter = jtgt as usize;
                }
                ebpf::CALL_IMM => {
                    // CALL_IMM: imm is a Murmur3 hash; registry maps it to a logical PC.
                    pc_iter = resolve_call_target_logical(ctx, &analysis, ins).ok_or_else(|| {
                        format!(
                            "qedlift: call_local at pc {} has imm 0x{:x} \
                             but no matching function in the symbol table. \
                             Recompile with symbols, or extend the resolver.",
                            pc_iter, ins.imm as u32)
                    })?;
                }
                _ => { pc_iter += 1; }
            }
        }
    }

    // Blob tail-splits requested: record and re-walk.
    if !state.new_blob_splits.is_empty() {
        for (root, lo, n) in state.new_blob_splits.drain(..) {
            blob_splits.insert((root, lo), n);
        }
        continue;
    }
    // Demotion requested: merge new spans into hot set and re-walk (this pass discarded).
    if !state.new_hot.is_empty() {
        for (root, lo, hi) in state.new_hot.drain(..) {
            let v = hot_regions.entry(root).or_default();
            let (mut nlo, mut nhi) = (lo, hi);
            v.retain(|(l, h)| {
                if *l <= nhi && nlo <= *h {
                    nlo = nlo.min(*l); nhi = nhi.max(*h); false
                } else { true }
            });
            v.push((nlo, nhi));
        }
        continue;
    }
    // H8 FAIL CLOSED: overlapping atom footprints make precondition's sepConj unsatisfiable (vacuous).
    if !state.overlap_errors.is_empty() {
        return Err(format!(
            "qedlift: refusing to emit a vacuous lift — overlapping atom \
             footprints would make the precondition's sepConj \
             unsatisfiable. The walker does not yet alias these at byte \
             granularity (soundness-audit H8, \
             docs/QEDLIFT_ALIASING_DESIGN.md):\n  - {}",
            state.overlap_errors.join("\n  - ")).into());
    }
    break (state, spec_calls, block_pcs, exit_pc);
    };
    let out_patched = out.replace("@@HEARTBEATS@@",
        if state.hot_regions.is_empty() { "4000000" } else { "16000000" });
    let mut out = out_patched;

    // CR must be a literal `union`-of-`singleton`s (sl_block_auto walks the AST), so inline not def.
    let cr_lean: String = if block_pcs.is_empty() {
        "CodeReq.empty".to_string()
    } else {
        let mut s = String::new();
        let opens = "(".repeat(block_pcs.len().saturating_sub(1));
        s.push_str(&opens);
        for (i, &pc) in block_pcs.iter().enumerate() {
            // Syscall renders as `.call <ctor>` (not `.call_local`) to match syscall spec's CR singleton.
            let lean_insn = if let Some(ctor) = state.syscall_pcs.get(&pc) {
                format!(".call {}", ctor)
            } else {
                let tgt = resolve_call_target_logical(ctx, &analysis, &insns[pc]);
                let jtgt = Some(resolve_jump_target(ctx, pc, insns[pc].off as i64));
                insn_to_lean_full(&insns[pc], pc, tgt, jtgt)?
            };
            if i == 0 {
                s.push_str(&format!("(CodeReq.singleton {} ({}))", pc, lean_insn));
            } else {
                s.push_str(&format!(".union\n        (CodeReq.singleton {} ({})))", pc, lean_insn));
            }
        }
        s
    };

    // H8 + H2: full bridge omitted for large binaries; pin each walked PC's decode via hex-string embedding
    // + buildSlotMap + native_decide, including call_local PCs resolved through the function registry.
    if !emit_decode_bridge && !block_pcs.is_empty() {
        let mut pin_offs: Vec<String> = Vec::new();
        let mut pin_exps: Vec<String> = Vec::new();
        for &pc in &block_pcs {
            let lean_insn = if let Some(ctor) = state.syscall_pcs.get(&pc) {
                format!(".call {}", ctor)
            } else {
                let tgt = resolve_call_target_logical(ctx, &analysis, &insns[pc]);
                let jtgt = Some(resolve_jump_target(ctx, pc, insns[pc].off as i64));
                insn_to_lean_full(&insns[pc], pc, tgt, jtgt)?
            };
            let byte_off = ctx.pc_map.logical_to_slot(pc).expect("logical pc in range") * 8;
            let sz = if insns[pc].opc == 0x18 { 16 } else { 8 };
            pin_offs.push(byte_off.to_string());
            pin_exps.push(format!("some ({}, {})", lean_insn, sz));
        }

        // H2: registry resolves call imms to .call_local targets in the pins below.
        let reg = function_registry(ctx);
        out.push_str(&render::large_text_decode_section(
            &module_name,
            text_bytes,
            &function_registry_lean(&reg),
            &pin_offs,
            &pin_exps,
        ));
    }

    // Phase 2: Hoare-triple emission. Symbolic execution already done inline above; `state` is ready.
    out.push_str(render::lifted_triple_section_header());
    let pre  = state.pre.clone();
    let post = post_atoms(&pre, &state);

    // Drop `< 2^k` bounds for cells only STORED to (stxdw_spec takes but doesn't bound them).
    state.u64_load_vars.retain(|(v, _)| {
        let h = format!("h{}_lt", v);
        spec_calls.iter().any(|sc| sc.have_line.contains(&h))
    });

    // Complex addresses (non-InitReg) → opaque Nat params + bridging equalities, so the chain
    // composes over clean atoms (see pda_n1_stack_macro_spec in SVM/SBPF/Macros.lean).
    let mut abstractions: Vec<(String, String, String)> = Vec::new(); // (param, bridge_hyp, raw_expr)
    {
        let mut seen: std::collections::BTreeMap<String, usize> =
            std::collections::BTreeMap::new();
        // Flat const address (e.g. lddw heap base) is NOT complex: sl_block_auto re-derives it; abstracting breaks unification.
        let is_const_addr = |e: &Expr| matches!(e, Expr::Const(_))
            || matches!(e, Expr::ToU64(inner) if matches!(inner.as_ref(), Expr::Const(_)));
        for atom in &pre {
            if let Atom::Mem { addr_base, .. } = atom {
                if !matches!(addr_base, Expr::InitReg(_)) && !is_const_addr(addr_base) {
                    let rendered = addr_base.to_lean();
                    if !seen.contains_key(&rendered) {
                        let idx = seen.len();
                        seen.insert(rendered.clone(), idx);
                        abstractions.push((
                            format!("addr{}", idx),
                            format!("h_addr{}", idx),
                            rendered,
                        ));
                    }
                }
            }
        }
    }
    let abs_subst: std::collections::BTreeMap<String, String> =
        abstractions.iter()
            .map(|(p, _, e)| (e.clone(), p.clone()))
            .collect();
    let rr = region_req(&pre, &state, &abs_subst);
    // call_local requires `callStackIs []` in pre+post (call_local_spec takes it, exit_pops_spec returns it).
    // Net change = none, but sl_block_iter must thread it through the chain.
    let cs_atom = if state.saw_call { " ** callStackIs []" } else { "" };

    let mut vars: Vec<String> = Vec::new();
    let push_var = |v: &Expr, vars: &mut Vec<String>| {
        if let Expr::InitReg(n) | Expr::InitMem(n) = v {
            if !vars.contains(n) { vars.push(n.clone()); }
        }
    };
    for atom in &pre {
        match atom {
            Atom::Reg(_, v) => push_var(v, &mut vars),
            Atom::Mem { addr_base, value, .. } => {
                push_var(addr_base, &mut vars);
                push_var(value, &mut vars);
            }
            Atom::Bytes32 { addr, .. } => push_var(addr, &mut vars),
            // The blob's `Sym` name is a `ByteArray` (surfaced via
            // `memset_blobs`, not here); the address's Nat leaves were
            // already collected when the syscall's registers were read.
            Atom::Bytes { addr, .. } => push_var(addr, &mut vars),
            // The returnData buffer has no address; its `ByteArray` name is
            // bound via `bytearray_vars`.
            Atom::ReturnData { .. } => {}
        }
    }
    let vars_sig = if vars.is_empty() { String::new() }
                   else { format!("({} : Nat)\n    ", vars.join(" ")) };
    // u64-load bounds: ldxdw_spec leaves `< 2^64` residuals; surface as hyps, discharge with `<;> assumption`.
    let mut u64_hyps = String::new();
    for (v, k) in &state.u64_load_vars {
        u64_hyps.push_str(&format!("(h{}_lt : {} < 2 ^ {})\n    ", v, v, k));
    }
    // Path hyps for conditional jumps (e.g. JeqImm fall-through: `dst ≠ toU64 imm`).
    let mut branch_hyps_sig = String::new();
    for (i, bh) in state.branch_hyps.iter().enumerate() {
        branch_hyps_sig.push_str(&format!("({} : {})\n    ", bh.name(i), bh.lean_hyp()));
    }
    // Memset: ByteArray param + `.size = count` hyp (spec's hbs) + nCu + CU-bound hyp (honest model assumption).
    // Side-condition hyps (e.g. div/mod divisor ≠ 0).
    let mut side_hyps_sig = String::new();
    for (name, prop) in &state.side_hyps {
        side_hyps_sig.push_str(&format!("({} : {})\n    ", name, prop));
    }
    let mut syscall_sig = String::new();
    // Bare `ByteArray` params with no size constraint (e.g. sol_set_return_data's old buffer).
    for ba in &state.bytearray_vars {
        syscall_sig.push_str(&format!("({} : ByteArray)\n    ", ba));
    }
    for (bs, size) in &state.memset_blobs {
        syscall_sig.push_str(&format!("({} : ByteArray)\n    ", bs));
        syscall_sig.push_str(&format!("(h{}_sz : {}.size = {})\n    ", bs, bs, size));
    }
    // Hyps referencing the blob params (e.g. PDA pid.size / off-curve) — after
    // the blob decls so the forward references resolve.
    for (name, prop) in &state.blob_side_hyps {
        syscall_sig.push_str(&format!("({} : {})\n    ", name, prop));
    }
    for (ncu, hcu, ctor) in &state.syscall_cu_vars {
        syscall_sig.push_str(&format!("({} : Nat)\n    ", ncu));
        syscall_sig.push_str(&format!(
            "({} : ∀ s : State, (step (.call {}) s).cuConsumed \
             ≤ s.cuConsumed + {})\n    ",
            hcu, ctor, ncu,
        ));
    }
    // CU bound M = sum of nCu vars; sl_block_iter's cuTripleWithinMem_cast closes via omega.
    let m_bound: String = if state.syscall_cu_vars.is_empty() {
        "0".to_string()
    } else {
        state.syscall_cu_vars.iter().map(|(n, _, _)| n.clone())
            .collect::<Vec<_>>().join(" + ")
    };
    // `sl_block_auto` now dispatches conditional jumps to their
    // `_not_taken` variants in InstructionSpecs/Jump.lean (see
    // SVM/SBPF/SpecGen.lean), surfacing the path hypothesis as a
    // residual side goal. `<;> assumption` closes them against the
    // theorem's `h_branchK` hypotheses, alongside any u64-load
    // `< 2^64` residuals.
    let needs_assumption = !state.branch_hyps.is_empty()
                        || !state.u64_load_vars.is_empty();
    // Use sl_block_iter when: call_local crossed (sl_block_auto diverges on wrapAdd addresses),
    // any cond-jump taken (SpecGen.mkSpec only has _not_taken; taken arms need explicit spec calls),
    // or a syscall was walked (SpecGen has no `.call <Syscall>` dispatch — the effect is supplied by
    // the emitted `call_<name>_spec` preamble, which only sl_block_iter threads).
    let any_taken = state.branch_hyps.iter().any(|b| b.taken);
    let use_block_iter = state.saw_call || any_taken || !state.syscall_pcs.is_empty();

    // Value abstraction: sl_block_iter re-reduces complex values (wrapAdd/shift/etc.) at every step
    // (transferChecked: 178ms→>15min). Generalize to opaque Nat; theorem statement stays concrete.
    let value_gens: Vec<String> = if use_block_iter {
        let is_complex = |e: &Expr| match e {
            // All-constant ByteCombo is closed: generalizing triggers kabstract whnf blowup. Leave inline.
            Expr::ByteCombo(vs) =>
                vs.iter().any(|v| !matches!(v, Expr::Const(_))),
            Expr::WrapAdd(..) | Expr::WrapSub(..) | Expr::WrapMul(..)
            | Expr::NatAdd(..) | Expr::Mod(..) | Expr::AndU64Imm(..)
            | Expr::LshU64Imm(..) | Expr::RshU64Imm(..)
            | Expr::StHalfImm(..) | Expr::StWordImm(..)
            | Expr::StDwordImm(..) | Expr::Raw(..) => true,
            _ => false,
        };
        let mut seen = std::collections::BTreeSet::new();
        let mut gens = Vec::new();
        for atom in pre.iter().chain(post.iter()) {
            // ↦Bytes blobs have no Nat Expr value (BytesVal, constants only) — skip.
            let v = match atom {
                Atom::Reg(_, v) => v,
                Atom::Mem { value, .. } => value,
                Atom::Bytes { .. } | Atom::Bytes32 { .. }
                    | Atom::ReturnData { .. } => continue,
            };
            if is_complex(v) {
                // Fold sub-expr abstractions first so generalize target matches the sl_rw_abs-folded proof term.
                let r = fold_abstractions(v.to_lean(), &abs_subst);
                // Skip address abstractions: generalizing an address rewrites it everywhere, breaking post/rr matching.
                let is_addr_abs = abs_subst.contains_key(&r)
                    || abs_subst.values().any(|p| *p == r);
                // Skip values a syscall spec pins concretely (e.g. sha256's `len`).
                let is_pinned = state.gen_exclude.contains(&r);
                if !is_addr_abs && !is_pinned && seen.insert(r.clone()) {
                    gens.push(r);
                }
            }
        }
        // Longest first: generalize parent before sub-terms to avoid premature clobbering.
        gens.sort_by_key(|e| std::cmp::Reverse(e.len()));
        gens
    } else {
        Vec::new()
    };

    let tactic: String = if use_block_iter {
        let mut t = String::new();
        for sc in &spec_calls {
            t.push_str("  ");
            t.push_str(&sc.have_line);
            t.push('\n');
        }
        // sl_rw_abs: apply innermost-first (shortest raw expr) so inner folds land before outer rw [← h_addrN] can match.
        if !abstractions.is_empty() {
            let mut ordered: Vec<&(String, String, String)> =
                abstractions.iter().collect();
            ordered.sort_by_key(|(_, _, e)| e.len());
            let abs_names = ordered.iter()
                .map(|(_, h, _)| h.clone()).collect::<Vec<_>>().join(", ");
            let hyp_names = spec_calls.iter()
                .map(|sc| sc.hyp_name.clone()).collect::<Vec<_>>().join(", ");
            t.push_str(&format!(
                "  sl_rw_abs [{}] at [{}]\n", abs_names, hyp_names,
            ));
        }
        // Value abstraction as `generalizing [...]` clause — opaque-ification lives in the library tactic.
        let hyp_names = spec_calls.iter()
            .map(|sc| sc.hyp_name.clone()).collect::<Vec<_>>().join(", ");
        if value_gens.is_empty() {
            t.push_str(&format!("  sl_block_iter [{}]", hyp_names));
        } else {
            t.push_str(&format!(
                "  sl_block_iter [{}] generalizing [{}]",
                hyp_names, value_gens.join(", "),
            ));
        }
        t
    } else if needs_assumption {
        // 2-space indent: bare col-0 tactic is absorbed by `open Memory in` as a combinator; indent avoids it.
        "  sl_block_auto <;> assumption".to_string()
    } else {
        "  sl_block_auto".to_string()
    };
    let tactic: &str = Box::leak(tactic.into_boxed_str());

    // Fold inner abstractions inside each bridge RHS so sl_rw_abs doesn't get stuck on partially-expanded
    // patterns (e.g. addr3 = wrapAdd <addr0-expansion> k → wrapAdd addr0 k). Longest-first, strictly-shorter only.
    let folded_rhs: Vec<String> = abstractions.iter().map(|(_, _, expr)| {
        let mut inner: Vec<(&String, &String)> = abstractions.iter()
            .filter(|(_, _, e)| e.len() < expr.len())
            .map(|(p, _, e)| (e, p))
            .collect();
        inner.sort_by_key(|(e, _)| std::cmp::Reverse(e.len()));
        let mut out = expr.clone();
        for (e, p) in inner {
            out = out.replace(e.as_str(), p.as_str());
        }
        out
    }).collect();

    // Abstraction signature (params + bridge equality hyps) for sl_block_iter programs.
    let abs_sig: String = if use_block_iter && !abstractions.is_empty() {
        let mut s = String::new();
        for (param, _, _) in &abstractions {
            s.push_str(&format!("({} : Nat)\n    ", param));
        }
        for (i, (param, h, _)) in abstractions.iter().enumerate() {
            s.push_str(&format!("({} : {} = {})\n    ", h, param, folded_rhs[i]));
        }
        s
    } else {
        String::new()
    };
    let n = block_pcs.len();
    // Start PC = first walked instruction (trace first / static entrypoint / entry_pc fallback).
    let start_pc = block_pcs.first().copied().unwrap_or(entry_pc);

    let theorem_binders = format!(
        "{}{}{}{}{}{}",
        vars_sig, abs_sig, u64_hyps, branch_hyps_sig, side_hyps_sig, syscall_sig,
    );
    let lifted_name = format!("{}_lifted_spec", module_name);
    let lifted_pre = format!("{}{}", atoms_to_lean(&pre, &abs_subst), cs_atom);
    let lifted_post = format!("{}{}", atoms_to_lean(&post, &abs_subst), cs_atom);
    out.push_str(&render::cu_triple_theorem(&render::TripleTheorem {
        name: &lifted_name,
        binders: &theorem_binders,
        n,
        m_bound: &m_bound,
        start_pc,
        exit_pc,
        cr: &cr_lean,
        pre: &lifted_pre,
        post: &lifted_post,
        rr: &rr,
        proof: tactic,
    }));

    // H8 satisfiability witness: fail-closed if precondition can't be witnessed satisfiable.
    match build_sat_witness(&pre, &state, &abstractions, &abs_subst,
                            &folded_rhs, &vars) {
        Ok(w) => out.push_str(&w),
        Err(e) => return Err(format!(
            "qedlift: satisfiability witness construction failed — {}", e).into()),
    }

    // Branch-satisfiability witness (Phase 7.1): certifies h_branch* / h*_lt jointly satisfiable
    // at a concrete assignment (native_decide), closing branch-vacuity. Conservative (non-breaking).
    if let Some(w) = build_branch_witness(&state, &vars) {
        out.push_str(&w);
    }

    // Heap-allocation corollary: re-express heap cells via heapBumpPtr/heapBlockU64 predicates
    // (unfold to same memU64Is, so `exact` closes after `simp`). Gated on heap cells; non-heap arms byte-identical.
    let has_heap = pre.iter().chain(post.iter()).any(|a|
        matches!(a, Atom::Mem { addr_base, addr_off, width, .. }
            if matches!(width, Width::Dword) && heap_cell_addr(addr_base, *addr_off).is_some()));
    if has_heap {
        // Parameter list in declaration order (mirrors the lift theorem's signature).
        let mut names: Vec<String> = vars.clone();
        if use_block_iter && !abstractions.is_empty() {
            for (p, _, _) in &abstractions { names.push(p.clone()); }
            for (_, h, _) in &abstractions { names.push(h.clone()); }
        }
        for (v, _) in &state.u64_load_vars { names.push(format!("h{}_lt", v)); }
        for i in 0..state.branch_hyps.len() { names.push(format!("h_branch{}", i)); }
        for (name, _) in &state.side_hyps { names.push(name.clone()); }
        // Mirror `syscall_sig` order: bytearray_vars, memset blobs, blob hyps, CU.
        for ba in &state.bytearray_vars { names.push(ba.clone()); }
        for (bs, _) in &state.memset_blobs {
            names.push(bs.clone());
            names.push(format!("h{}_sz", bs));
        }
        for (name, _) in &state.blob_side_hyps { names.push(name.clone()); }
        for (ncu, hcu, _) in &state.syscall_cu_vars {
            names.push(ncu.clone());
            names.push(hcu.clone());
        }
        out = out.replacen("import SVM.SBPF.Macros\n",
            "import SVM.SBPF.Macros\nimport SVM.SBPF.HeapSL\n", 1);
        let alloc_name = format!("{}_allocates", module_name);
        let alloc_pre = format!("{}{}", atoms_to_lean_heap(&pre, &abs_subst), cs_atom);
        let alloc_post = format!("{}{}", atoms_to_lean_heap(&post, &abs_subst), cs_atom);
        let alloc_proof = format!(
            "  simp only [heapBumpPtr, heapBlockU64]\n  exact {}_lifted_spec {}",
            module_name,
            names.join(" "),
        );
        out.push_str(&render::cu_triple_theorem(&render::TripleTheorem {
            name: &alloc_name,
            binders: &theorem_binders,
            n,
            m_bound: &m_bound,
            start_pc,
            exit_pc,
            cr: &cr_lean,
            pre: &alloc_pre,
            post: &alloc_post,
            rr: &rr,
            proof: &alloc_proof,
        }));
    }

    // Balance-correctness corollary: re-expose wrapSub/wrapAdd as Nat arithmetic under
    // funds/no-overflow guards. Only cells wrapping two InitMem values qualify (excludes reg/addr arithmetic).
    enum Shift { Sub(Expr, Expr), Add(Expr, Expr), AddConst(Expr, i64) }
    let is_initmem = |e: &Expr| matches!(e, Expr::InitMem(_));
    // A constant immediate delta `toU64 k` (e.g. `add64 r2, 1`).
    let const_delta = |e: &Expr| -> Option<i64> {
        if let Expr::ToU64(inner) = e {
            if let Expr::Const(k) = inner.as_ref() { return Some(*k); }
        }
        None
    };
    // Only counter/vault arms (is_const_delta_arm) — or a spec-driven descriptor, whose
    // `op.add_const` is exactly this const-delta case — get the constant +k cleaning; others stay wrapAdd.
    let counter_arm = is_const_delta_arm(arm_name) || descriptor.is_some();
    let mut shifts: Vec<Shift> = Vec::new();
    let mut post_clean: Vec<Atom> = Vec::with_capacity(post.len());
    for atom in &post {
        if let Atom::Mem { addr_base, addr_off, width, value, delta } = atom {
            if let Expr::WrapSub(a, b) = value {
                if is_initmem(a) && is_initmem(b) {
                    shifts.push(Shift::Sub((**a).clone(), (**b).clone()));
                    post_clean.push(Atom::Mem { addr_base: addr_base.clone(),
                        addr_off: *addr_off, width: *width,
                        value: Expr::CleanSub(a.clone(), b.clone()), delta: *delta });
                    continue;
                }
            }
            if let Expr::WrapAdd(a, b) = value {
                if is_initmem(a) && is_initmem(b) {
                    shifts.push(Shift::Add((**a).clone(), (**b).clone()));
                    post_clean.push(Atom::Mem { addr_base: addr_base.clone(),
                        addr_off: *addr_off, width: *width,
                        value: Expr::NatAdd(a.clone(), b.clone()), delta: *delta });
                    continue;
                }
                if counter_arm && is_initmem(a) {
                    if let Some(k) = const_delta(b) {
                        shifts.push(Shift::AddConst((**a).clone(), k));
                        post_clean.push(Atom::Mem { addr_base: addr_base.clone(),
                            addr_off: *addr_off, width: *width,
                            value: Expr::NatAdd(a.clone(), Box::new(Expr::Const(k))), delta: *delta });
                        continue;
                    }
                }
            }
        }
        post_clean.push(atom.clone());
    }

    if !shifts.is_empty() {
        // Param names in signature order (vars → abstraction params/hyps → u64 bounds → branch hyps → syscall).
        let mut names: Vec<String> = vars.clone();
        if use_block_iter && !abstractions.is_empty() {
            for (p, _, _) in &abstractions { names.push(p.clone()); }
            for (_, h, _) in &abstractions { names.push(h.clone()); }
        }
        for (v, _) in &state.u64_load_vars { names.push(format!("h{}_lt", v)); }
        for i in 0..state.branch_hyps.len() { names.push(format!("h_branch{}", i)); }
        for (name, _) in &state.side_hyps { names.push(name.clone()); }
        // Mirror `syscall_sig` order: bytearray_vars, memset blobs, blob hyps, CU.
        for ba in &state.bytearray_vars { names.push(ba.clone()); }
        for (bs, _) in &state.memset_blobs {
            names.push(bs.clone());
            names.push(format!("h{}_sz", bs));
        }
        for (name, _) in &state.blob_side_hyps { names.push(name.clone()); }
        for (ncu, hcu, _) in &state.syscall_cu_vars {
            names.push(ncu.clone());
            names.push(hcu.clone());
        }

        let mut extra_hyps = String::new();
        let mut rw_terms: Vec<String> = Vec::new();
        for (k, sh) in shifts.iter().enumerate() {
            match sh {
                Shift::Sub(a, b) => {
                    let al = fold_abstractions(a.to_lean(), &abs_subst);
                    let bl = fold_abstractions(b.to_lean(), &abs_subst);
                    extra_hyps.push_str(&format!("(h_funds{} : {} ≤ {})\n    ", k, bl, al));
                    extra_hyps.push_str(&format!("(h_src_lt{} : {} < 2 ^ 64)\n    ", k, al));
                    rw_terms.push(format!("← wrapSub_of_le h_funds{} h_src_lt{}", k, k));
                }
                Shift::Add(a, b) => {
                    let al = fold_abstractions(a.to_lean(), &abs_subst);
                    let bl = fold_abstractions(b.to_lean(), &abs_subst);
                    extra_hyps.push_str(&format!("(h_noovf{} : {} + {} < 2 ^ 64)\n    ", k, al, bl));
                    rw_terms.push(format!("← wrapAdd_of_lt h_noovf{}", k));
                }
                Shift::AddConst(a, c) => {
                    // Clean `wrapAdd a (toU64 k) → a + k` under the no-overflow hyp.
                    // `+1` keeps the specialized `wrapAdd_one_of_lt` so every existing
                    // +1 lift stays byte-identical; any other positive literal uses the
                    // general `wrapAdd_const_of_lt`.
                    let al = fold_abstractions(a.to_lean(), &abs_subst);
                    extra_hyps.push_str(&format!("(h_noovf{} : {} + {} < 2 ^ 64)\n    ", k, al, c));
                    if *c == 1 {
                        rw_terms.push(format!("← wrapAdd_one_of_lt h_noovf{}", k));
                    } else {
                        rw_terms.push(format!("← wrapAdd_const_of_lt h_noovf{}", k));
                    }
                }
            }
        }

        let balance_name = format!("{}_balance_correct", module_name);
        let balance_binders = format!("{}{}", theorem_binders, extra_hyps);
        let balance_pre = format!("{}{}", atoms_to_lean(&pre, &abs_subst), cs_atom);
        let balance_post = format!("{}{}", atoms_to_lean(&post_clean, &abs_subst), cs_atom);
        let balance_proof = format!(
            "  have h := {}_lifted_spec {}\n  rw [{}]\n  exact h",
            module_name,
            names.join(" "),
            rw_terms.join(", "),
        );
        out.push_str(&render::cu_triple_theorem(&render::TripleTheorem {
            name: &balance_name,
            binders: &balance_binders,
            n,
            m_bound: &m_bound,
            start_pc,
            exit_pc,
            cr: &cr_lean,
            pre: &balance_pre,
            post: &balance_post,
            rr: &rr,
            proof: &balance_proof,
        }));
    }

    out.push_str(&render::end_namespace(&module_name));

    // ── Asm-refines-intrinsic theorem (mechanized recipe) ───────────
    // Spec-driven descriptor wins when present (the qedspec seam): build the
    // layout-general `AsmRefinesFieldUpdate` straight from the descriptor,
    // bypassing the hardcoded `refine_registry`. Otherwise the registry path.
    let refine_emit = match descriptor {
        Some(desc) => emit_descriptor_refinement(
            desc, &module_name, &pre, &post_clean, &abs_subst, &vars, n, start_pc, exit_pc,
            idl, sidecar_layouts),
        None => arm_name.and_then(|arm| emit_refinement(
            arm, &module_name, &pre, &post_clean, &abs_subst, &vars, n, start_pc, exit_pc, idl,
            sidecar_layouts)),
    };
    let aggregation = refine_emit.as_ref().and_then(|(_, _, a)| a.clone());
    let refinement = refine_emit.map(|(m, l, _)| (m, l));

    Ok(LiftOutput {
        lean: out,
        module_name,
        text_bytes: text_bytes.len(),
        insn_count: insns.len(),
        cu: n,
        refinement,
        aggregation,
    })
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = parse_args().map_err(|e| -> Box<dyn std::error::Error> { e.into() })?;

    // Load once: amortises parse+CFG build across batch arms (~28 arms × ~10s → a few ms each).
    let ctx = load_binary(&args.so)?;
    let analysis = Analysis::from_executable(&ctx.executable)?;

    let idl_value = args.idl.as_ref().and_then(|p| load_idl_value(p));

    let trace: Option<Vec<usize>> = match args.trace.as_ref() {
        Some(p) => Some(load_trace(p)?),
        None => None,
    };

    // Spec-driven refinement descriptor (single-arm only). The seam to qedspec.
    let descriptor: Option<RefinementDescriptor> = match args.descriptor.as_ref() {
        Some(p) => Some(load_descriptor(p)?),
        None => None,
    };

    // --qedmeta mode: targeting from qedrecover sidecar (disc + name), CU cross-check, optional --target-name filter.
    if let Some(meta_path) = args.qedmeta.as_ref() {
        let meta = load_qedmeta(meta_path)?;
        // #41 loop closure: consume qedrecover's emitted + validated account layouts as the
        // refinement-codegen layout source (falls back to `--idl` per-name when a layout is absent).
        let sidecar_layouts = sidecar_account_layouts(&meta);
        let so_stem = args.so.file_stem()
            .map(|s| pascal_case(&s.to_string_lossy()))
            .unwrap_or_else(|| "Lifted".to_string());

        let selected: Vec<_> = match args.target_name.as_ref() {
            Some(want) => meta.instructions.iter().filter(|i| &i.name == want).collect(),
            None       => meta.instructions.iter().collect(),
        };
        if selected.is_empty() {
            return Err(format!("--qedmeta {}: no in-scope instruction{}",
                meta_path.display(),
                args.target_name.as_ref()
                    .map(|n| format!(" named {:?}", n)).unwrap_or_default()).into());
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
            let result = lift_one_with_layouts(&args.so, &ctx, &analysis,
                Some(ix.discriminator.value), Some(module_name.clone()),
                trace.as_deref(), Some(&arm), idl_value.as_ref(), arm_entry,
                Some(&sidecar_layouts), None)?;

            // Cross-check: cu_budget is upper bound; result.cu is the exact discharged CU.
            let budget_note = match ix.cu_budget {
                Some(b) if result.cu as u64 > b => {
                    budget_fail = true;
                    format!(" ✘ CU {} EXCEEDS budget {}", result.cu, b)
                }
                Some(b) => format!(" ✔ CU {} ≤ budget {}", result.cu, b),
                None    => format!(" CU {} (no budget claimed)", result.cu),
            };

            let out_path = if let Some(o) = args.output.as_ref() {
                o.clone()
            } else if let Some(d) = args.output_dir.as_ref() {
                std::fs::create_dir_all(d)?;
                d.join(format!("{}Lifted.lean", module_name))
            } else {
                return Err("--qedmeta needs --output (single arm) or --output-dir".into());
            };
            std::fs::write(&out_path, &result.lean)?;
            let refined = if let Some((rmod, rlean)) = &result.refinement {
                let rpath = out_path.with_file_name(format!("{}.lean", rmod));
                std::fs::write(&rpath, rlean)?;
                " (+refinement)"
            } else { "" };
            let agg = write_aggregation(&result.aggregation)?;
            println!("  ✔ {:<20} disc={:<4}{} → {}{}{}",
                ix.name, ix.discriminator.value, budget_note, out_path.display(), refined, agg);
        }
        if budget_fail {
            return Err("one or more lifted triples exceeded the claimed cu_budget".into());
        }
        return Ok(());
    }

    // Batch mode: --idl + --output-dir. Without --output-dir falls through to single-arm.
    if let (Some(idl_path), Some(output_dir)) =
        (args.idl.as_ref(), args.output_dir.as_ref())
    {
        let idl = load_idl(idl_path)?;
        std::fs::create_dir_all(output_dir)?;

        let so_stem = args.so.file_stem()
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
            // Per-arm tolerance: unmodelled opcodes are reported+skipped (batch = coverage probe).
            match lift_one(&args.so, &ctx, &analysis, Some(ix.discriminator), Some(module_name.clone()), None, Some(&ix.name), idl_value.as_ref(), None) {
                Ok(result) => {
                    let out_path = output_dir.join(format!("{}Lifted.lean", module_name));
                    if let Some(parent) = out_path.parent() {
                        std::fs::create_dir_all(parent)?;
                    }
                    std::fs::write(&out_path, &result.lean)?;
                    let refined = if let Some((rmod, rlean)) = &result.refinement {
                        let rpath = output_dir.join(format!("{}.lean", rmod));
                        std::fs::write(&rpath, rlean)?;
                        " (+refinement)"
                    } else { "" };
                    let agg = write_aggregation(&result.aggregation)?;
                    println!("  ✔ {:<24} disc={:<4} {} insns → {}{}{}",
                        ix.name, ix.discriminator, result.insn_count, out_path.display(), refined, agg);
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
        return Ok(());
    }

    let result = lift_one_with_layouts(&args.so, &ctx, &analysis, args.target_disc,
                          args.module.clone(), trace.as_deref(), args.arm_name.as_deref(),
                          idl_value.as_ref(), None, None, descriptor.as_ref())?;
    match args.output {
        Some(path) => {
            if let Some(parent) = path.parent() {
                std::fs::create_dir_all(parent)?;
            }
            std::fs::write(&path, &result.lean)?;
            println!("=== qedlift ===");
            println!("  input  : {}", args.so.display());
            println!("  output : {}", path.display());
            println!("  .text  : {} bytes ({} insns)", result.text_bytes, result.insn_count);
            println!("  module : Examples.Lifted.{}", result.module_name);
            if let Some((rmod, rlean)) = &result.refinement {
                let rpath = path.with_file_name(format!("{}.lean", rmod));
                std::fs::write(&rpath, rlean)?;
                println!("  refine : {}", rpath.display());
            }
            if write_aggregation(&result.aggregation)? == " (+agg)" {
                if let Some((m, _)) = &result.aggregation {
                    println!("  agg    : examples/lean/{}.lean", m.replace('.', "/"));
                }
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
