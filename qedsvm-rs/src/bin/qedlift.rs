//! qedlift — takes a compiled `.so`, symbolically executes the decoded eBPF,
//! and emits a Lean `cuTripleWithinMem` Hoare triple with pre/post conditions
//! derived from the execution, discharged by `sl_block_auto`. Also emits
//! aggregation modules and asm-refines theorems for known program shapes.

use std::path::{Path, PathBuf};
use std::sync::Arc;

use solana_sbpf::{
    ebpf,
    elf::Executable,
    program::BuiltinProgram,
    static_analysis::Analysis,
    vm::ContextObject,
};

use qed_analysis::PcMap;

struct NoopCtx;
impl ContextObject for NoopCtx {
    fn consume(&mut self, _amount: u64) {}
    fn get_remaining(&self) -> u64 { 0 }
}

struct Args {
    so:          PathBuf,
    output:      Option<PathBuf>,
    module:      Option<String>,
    /// Discriminator value to target. When set, the walker resolves
    /// each conditional jump on the discriminator register (the dst
    /// of an `ldxb r?, [r1+0]` load) by taking the direction
    /// consistent with `disc_byte == target_disc`. Each such jump
    /// adds a path hypothesis to the theorem signature.
    target_disc: Option<i64>,
    /// IDL file (TOML). When given, qedlift loops over the IDL's
    /// instructions and emits one Lean file per instruction. The
    /// per-instruction module names are derived from the IDL's
    /// instruction names; the output directory is `--output-dir`.
    idl:         Option<PathBuf>,
    output_dir:  Option<PathBuf>,
    /// Execution-trace file: one decimal logical PC per line, in the
    /// order the instructions were executed on a concrete run (capture
    /// via the Lean runner's `TRACE_STEPS`). When given, the walker
    /// follows this exact path instead of its static branch policy —
    /// branch directions and (for taken jumps) targets come from the
    /// trace, so the lift covers the *real* happy path (e.g. the
    /// balance debit/credit a static fall-through walk skips). Applies
    /// to single-arm mode (`--so` without `--idl`).
    trace:       Option<PathBuf>,
    /// IDL instruction name for the refinement codegen (single-arm
    /// mode). When given and recognised by the refinement registry,
    /// qedlift also emits the `<module>Refinement.lean` asm-refines
    /// theorem. Batch mode derives this from the IDL automatically.
    arm_name:    Option<String>,
    /// qedrecover sidecar (`*.qedmeta.toml`). When given, qedlift reads
    /// `{discriminator.value, name, cu_budget}` for each in-scope
    /// instruction and drives targeting from the sidecar instead of the
    /// manual `--target-disc`/`--arm-name` flags, cross-checking each
    /// lifted triple's CU against the claimed `cu_budget`.
    qedmeta:     Option<PathBuf>,
    /// Restrict a `--qedmeta` run to a single instruction by name.
    target_name: Option<String>,
}

// qedmeta sidecar (#41 Phase 4): v2 adds [instruction.recovered] arm
// decomposition; serde ignores unknown fields so v0.1 sidecars still parse.

/// Newest sidecar schema qedlift understands; v1 = targeting only, v2 = recovered arm. Older sidecars fall back to disc-guided walk.
const QEDMETA_SCHEMA_MAX: u32 = 2;

#[derive(Debug, serde::Deserialize)]
struct QedMeta {
    #[serde(default)]
    schema_version: u32,
    #[serde(rename = "instruction")]
    instructions: Vec<QedMetaIx>,
    /// `[[account_layout]]` tables emitted by qedrecover (#41 Phase 2). Consumed as the
    /// refinement-codegen layout source so qedlift trusts qedrecover's validated layout
    /// instead of re-parsing the IDL. `default` so pre-layout sidecars still load.
    #[serde(default, rename = "account_layout")]
    account_layouts: Vec<QedMetaAccountLayout>,
}

#[derive(Debug, serde::Deserialize)]
struct QedMetaAccountLayout {
    name: String,
    size: usize,
    #[serde(default, rename = "field")]
    fields: Vec<QedMetaField>,
}

#[derive(Debug, serde::Deserialize)]
struct QedMetaField {
    name:   String,
    offset: usize,
    kind:   String,
    /// Present only for `kind = "bytes"` (opaque region width); mirrors `field_kind_name`.
    #[serde(default)]
    width_bytes: Option<usize>,
}

#[derive(Debug, serde::Deserialize)]
struct QedMetaIx {
    name:          String,
    cu_budget:     Option<u64>,
    discriminator: QedMetaDisc,
    /// `[instruction.recovered]` from qedrecover; consumed (#41 "lossy handoff"). `None` for pre-v2 sidecars.
    #[serde(default)]
    recovered: Option<QedMetaRecovered>,
}

#[derive(Debug, serde::Deserialize)]
struct QedMetaDisc {
    value: i64,
}

/// Sub-table from qedrecover; only `arm_entry_pc` is consumed, other keys silently ignored.
#[derive(Debug, serde::Deserialize)]
struct QedMetaRecovered {
    /// Logical (decoded-array) arm-entry PC — same space as walker / `.pcs` traces, NOT a raw slot.
    arm_entry_pc: usize,
}

/// Reconstruct the shared `AccountLayout`s from a sidecar's `[[account_layout]]` tables.
/// Inverse of qedrecover's emitter (`field_kind_name` + `width_bytes`); the round-trip is
/// exact for the codecs qedlift consumes (pubkey/u64/byte/bytes).
fn sidecar_account_layouts(meta: &QedMeta) -> Vec<AccountLayout> {
    meta.account_layouts.iter().map(|l| AccountLayout {
        name: l.name.clone(),
        size: l.size,
        fields: l.fields.iter().map(|f| AccountField {
            name:   f.name.clone(),
            offset: f.offset,
            kind: match f.kind.as_str() {
                "pubkey" => FieldKind::Pubkey,
                "u64"    => FieldKind::U64,
                "byte"   => FieldKind::Byte,
                // "bytes" (or any unknown) → opaque region; width_bytes carries the size.
                _        => FieldKind::Bytes(f.width_bytes.unwrap_or(0)),
            },
        }).collect(),
    }).collect()
}

/// Resolve an account layout by name, preferring qedrecover's sidecar tables over a fresh
/// IDL parse. Sidecar layouts are validated + emitted by qedrecover; the IDL fallback keeps
/// non-qedmeta runs (batch / single-arm `--idl`) byte-identical to the prior behaviour.
fn resolve_layout(
    sidecar: Option<&[AccountLayout]>,
    idl:     Option<&serde_json::Value>,
    name:    &str,
) -> Option<AccountLayout> {
    sidecar
        .and_then(|ls| ls.iter().find(|l| l.name == name).cloned())
        .or_else(|| idl.and_then(|v| parse_account_layout(v, name).ok()))
}

fn load_qedmeta(path: &Path) -> Result<QedMeta, Box<dyn std::error::Error>> {
    let text = std::fs::read_to_string(path)?;
    let meta: QedMeta = toml::from_str(&text)?;
    // Newer schema may carry semantics we'd silently mis-consume — fail closed.
    if meta.schema_version > QEDMETA_SCHEMA_MAX {
        return Err(format!(
            "--qedmeta {}: schema_version {} is newer than this qedlift \
             understands (max {})",
            path.display(), meta.schema_version, QEDMETA_SCHEMA_MAX).into());
    }
    Ok(meta)
}

// IDL parsing: .toml (minimal in-tree fixture schema) or .json (Codama); both flatten to Vec<IdlInstruction>.

#[derive(Debug)]
struct IdlInstruction {
    name:          String,
    discriminator: i64,
}

#[derive(Debug, serde::Deserialize)]
struct IdlToml {
    instruction: Vec<IdlInstructionToml>,
}

#[derive(Debug, serde::Deserialize)]
struct IdlInstructionToml {
    name:          String,
    discriminator: i64,
}

fn load_idl(path: &Path) -> Result<Vec<IdlInstruction>, Box<dyn std::error::Error>> {
    let text = std::fs::read_to_string(path)?;
    match path.extension().and_then(|e| e.to_str()) {
        Some("toml") => {
            let raw: IdlToml = toml::from_str(&text)?;
            Ok(raw.instruction.into_iter()
                .map(|i| IdlInstruction { name: i.name, discriminator: i.discriminator })
                .collect())
        }
        Some("json") => load_codama(&text),
        ext => Err(format!("unsupported IDL extension: {:?}", ext).into()),
    }
}

// Only fieldDiscriminatorNode at offset 0 is handled (covers SPL Token / p-token); Anchor 8-byte sighashes unsupported.
fn load_codama(text: &str) -> Result<Vec<IdlInstruction>, Box<dyn std::error::Error>> {
    let root: serde_json::Value = serde_json::from_str(text)?;
    let instructions = root.pointer("/program/instructions")
        .and_then(|v| v.as_array())
        .ok_or("codama: /program/instructions missing or not an array")?;
    let mut out = Vec::new();
    let mut skipped = Vec::new();
    for ix in instructions {
        let name = ix.get("name").and_then(|v| v.as_str()).unwrap_or("?").to_string();
        let discs = match ix.get("discriminators").and_then(|v| v.as_array()) {
            Some(d) if !d.is_empty() => d,
            _ => { skipped.push((name, "no discriminators")); continue; }
        };
        let d0 = &discs[0];
        let d_kind   = d0.get("kind").and_then(|v| v.as_str()).unwrap_or("");
        let d_name   = d0.get("name").and_then(|v| v.as_str()).unwrap_or("").to_string();
        let d_offset = d0.get("offset").and_then(|v| v.as_i64()).unwrap_or(-1);
        if d_kind != "fieldDiscriminatorNode" {
            skipped.push((name, "non-field discriminator")); continue;
        }
        if d_offset != 0 {
            skipped.push((name, "non-zero discriminator offset")); continue;
        }
        let args = ix.get("arguments").and_then(|v| v.as_array());
        let value = args.and_then(|a| a.iter().find(|a| a.get("name").and_then(|v| v.as_str()) == Some(&d_name)))
            .and_then(|a| a.get("defaultValue"))
            .and_then(|v| v.get("number"))
            .and_then(|v| v.as_i64());
        match value {
            Some(n) => out.push(IdlInstruction { name, discriminator: n }),
            None    => skipped.push((name, "missing default value")),
        }
    }
    if !skipped.is_empty() {
        eprintln!("codama: skipped {} instruction(s):", skipped.len());
        for (n, why) in &skipped { eprintln!("  - {:<24} {}", n, why); }
    }
    Ok(out)
}

/// Load a Codama `.json` IDL as a raw `Value` for layout extraction; returns `None` for `.toml` or parse error.
fn load_idl_value(path: &Path) -> Option<serde_json::Value> {
    if path.extension().and_then(|e| e.to_str()) != Some("json") { return None; }
    let text = std::fs::read_to_string(path).ok()?;
    serde_json::from_str(&text).ok()
}

// Account layout types live in the shared `qed-analysis` crate (#41 Phase 2) so qedrecover shares field names/offsets.
use qed_analysis::layout::{AccountField, AccountLayout, FieldKind, parse_account_layout};

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
            None, Some("VaultIncrement"), Some(&idl), None, None).expect("lift via idl");

        // (b) Sidecar path — layout supplied as qedrecover emits it; NO `--idl`.
        let layouts = vec![parse_account_layout(&idl, "vault").expect("vault layout")];
        let via_sidecar = lift_one_with_layouts(so, &ctx, &analysis, None, Some("Vault".to_string()),
            None, Some("VaultIncrement"), None, None, Some(&layouts)).expect("lift via sidecar");

        // (c) No layout source at all.
        let via_none = lift_one_with_layouts(so, &ctx, &analysis, None, Some("Vault".to_string()),
            None, Some("VaultIncrement"), None, None, None).expect("lift with no layout");

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

fn parse_args() -> Result<Args, String> {
    let mut so:          Option<PathBuf> = None;
    let mut output:      Option<PathBuf> = None;
    let mut module:      Option<String>  = None;
    let mut target_disc: Option<i64>     = None;
    let mut idl:         Option<PathBuf> = None;
    let mut output_dir:  Option<PathBuf> = None;
    let mut trace:       Option<PathBuf> = None;
    let mut arm_name:    Option<String>  = None;
    let mut qedmeta:     Option<PathBuf> = None;
    let mut target_name: Option<String>  = None;
    let mut it = std::env::args().skip(1);
    while let Some(a) = it.next() {
        match a.as_str() {
            "--so"          => so          = Some(it.next().ok_or("--so needs a path")?.into()),
            "--output"      => output      = Some(it.next().ok_or("--output needs a path")?.into()),
            "--module"      => module      = Some(it.next().ok_or("--module needs a name")?),
            "--target-disc" => target_disc = Some(
                it.next().ok_or("--target-disc needs an integer")?
                  .parse().map_err(|e| format!("--target-disc: {}", e))?),
            "--idl"         => idl         = Some(it.next().ok_or("--idl needs a path")?.into()),
            "--output-dir"  => output_dir  = Some(it.next().ok_or("--output-dir needs a path")?.into()),
            "--trace"       => trace       = Some(it.next().ok_or("--trace needs a path")?.into()),
            "--arm-name"    => arm_name    = Some(it.next().ok_or("--arm-name needs a name")?),
            "--qedmeta"     => qedmeta     = Some(it.next().ok_or("--qedmeta needs a path")?.into()),
            "--target-name" => target_name = Some(it.next().ok_or("--target-name needs a name")?),
            other           => return Err(format!("unknown arg: {}", other)),
        }
    }
    Ok(Args {
        so: so.ok_or("missing --so")?,
        output, module, target_disc, idl, output_dir, trace, arm_name,
        qedmeta, target_name,
    })
}

/// Convert an sBPF `Insn` to Lean constructor syntax. `call_target` provides the resolved callee PC (raw imm is a Murmur3 hash); `jump_target` is the caller-resolved logical target for conditional jumps.
fn insn_to_lean_full(insn: &ebpf::Insn, pc: usize, call_target: Option<usize>,
                     jump_target: Option<i64>) -> Result<String, String> {
    use ebpf::*;
    let (dst, src, off, imm) = (insn.dst, insn.src, insn.off as i64, insn.imm);
    // Caller-resolved logical target; falls back to raw slot-relative sum.
    let jt = || jump_target.unwrap_or((pc as i64) + 1 + off);
    let reg = |n: u8| match n {
        0 => ".r0", 1 => ".r1", 2 => ".r2", 3 => ".r3",
        4 => ".r4", 5 => ".r5", 6 => ".r6", 7 => ".r7",
        8 => ".r8", 9 => ".r9", 10 => ".r10",
        _ => "?reg",
    };
    // Negative offsets need parens in Lean syntax (`.r10 -2072` parses as subtraction).
    let offl = lean_off(off);
    Ok(match insn.opc {
        LD_B_REG    => format!(".ldx .byte {} {} {}",     reg(dst), reg(src), offl),
        LD_H_REG    => format!(".ldx .half {} {} {}", reg(dst), reg(src), offl),
        LD_W_REG    => format!(".ldx .word {} {} {}",     reg(dst), reg(src), offl),
        LD_DW_REG   => format!(".ldx .dword {} {} {}",    reg(dst), reg(src), offl),
        ST_B_REG    => format!(".stx .byte {} {} {}",     reg(dst), offl, reg(src)),
        ST_H_REG    => format!(".stx .half {} {} {}", reg(dst), offl, reg(src)),
        ST_W_REG    => format!(".stx .word {} {} {}",     reg(dst), offl, reg(src)),
        ST_DW_REG   => format!(".stx .dword {} {} {}",    reg(dst), offl, reg(src)),
        ADD64_IMM   => format!(".add64 {} (.imm ({}))",     reg(dst), imm),
        SUB64_IMM   => format!(".sub64 {} (.imm ({}))",     reg(dst), imm),
        MOV64_IMM   => format!(".mov64 {} (.imm ({}))",     reg(dst), imm),
        AND64_IMM   => format!(".and64 {} (.imm ({}))",     reg(dst), imm),
        LSH64_IMM   => format!(".lsh64 {} (.imm ({}))",     reg(dst), imm),
        LD_DW_IMM   => format!(".lddw {} ({})",             reg(dst), imm),
        ST_B_IMM    => format!(".st .byte {} {} ({})",      reg(dst), offl, imm),
        ST_H_IMM    => format!(".st .half {} {} ({})",      reg(dst), offl, imm),
        ST_W_IMM    => format!(".st .word {} {} ({})",      reg(dst), offl, imm),
        ST_DW_IMM   => format!(".st .dword {} {} ({})",     reg(dst), offl, imm),
        ADD64_REG   => format!(".add64 {} (.reg {})",     reg(dst), reg(src)),
        SUB64_REG   => format!(".sub64 {} (.reg {})",     reg(dst), reg(src)),
        MUL64_REG   => format!(".mul64 {} (.reg {})",     reg(dst), reg(src)),
        OR64_REG    => format!(".or64 {} (.reg {})",      reg(dst), reg(src)),
        AND64_REG   => format!(".and64 {} (.reg {})",     reg(dst), reg(src)),
        XOR64_REG   => format!(".xor64 {} (.reg {})",     reg(dst), reg(src)),
        LSH64_REG   => format!(".lsh64 {} (.reg {})",     reg(dst), reg(src)),
        RSH64_REG   => format!(".rsh64 {} (.reg {})",     reg(dst), reg(src)),
        MOV64_REG   => format!(".mov64 {} (.reg {})",     reg(dst), reg(src)),
        EXIT        => ".exit".to_string(),
        JEQ64_IMM | JEQ32_IMM => {
            let t = jt(); format!(".jeq {} (.imm ({})) {}", reg(dst), imm, t)
        }
        JNE64_IMM | JNE32_IMM => {
            let t = jt(); format!(".jne {} (.imm ({})) {}", reg(dst), imm, t)
        }
        JGT64_IMM | JGT32_IMM => {
            let t = jt(); format!(".jgt {} (.imm ({})) {}", reg(dst), imm, t)
        }
        JGE64_IMM | JGE32_IMM => {
            let t = jt(); format!(".jge {} (.imm ({})) {}", reg(dst), imm, t)
        }
        JLT64_IMM | JLT32_IMM => {
            let t = jt(); format!(".jlt {} (.imm ({})) {}", reg(dst), imm, t)
        }
        JLE64_IMM | JLE32_IMM => {
            let t = jt(); format!(".jle {} (.imm ({})) {}", reg(dst), imm, t)
        }
        RSH64_IMM   => format!(".rsh64 {} (.imm ({}))",     reg(dst), imm),
        OR64_IMM    => format!(".or64 {} (.imm ({}))",      reg(dst), imm),
        XOR64_IMM   => format!(".xor64 {} (.imm ({}))",     reg(dst), imm),
        MUL64_IMM   => format!(".mul64 {} (.imm ({}))",     reg(dst), imm),
        DIV64_IMM   => format!(".div64 {} (.imm ({}))",     reg(dst), imm),
        MOD64_IMM   => format!(".mod64 {} (.imm ({}))",     reg(dst), imm),
        NEG64       => format!(".neg64 {}",                 reg(dst)),
        ADD32_IMM   => format!(".add32 {} (.imm ({}))",    reg(dst), imm),
        SUB32_IMM   => format!(".sub32 {} (.imm ({}))",    reg(dst), imm),
        MUL32_IMM   => format!(".mul32 {} (.imm ({}))",    reg(dst), imm),
        DIV32_IMM   => format!(".div32 {} (.imm ({}))",    reg(dst), imm),
        MOD32_IMM   => format!(".mod32 {} (.imm ({}))",    reg(dst), imm),
        OR32_IMM    => format!(".or32 {} (.imm ({}))",     reg(dst), imm),
        AND32_IMM   => format!(".and32 {} (.imm ({}))",    reg(dst), imm),
        XOR32_IMM   => format!(".xor32 {} (.imm ({}))",    reg(dst), imm),
        LSH32_IMM   => format!(".lsh32 {} (.imm ({}))",    reg(dst), imm),
        RSH32_IMM   => format!(".rsh32 {} (.imm ({}))",    reg(dst), imm),
        MOV32_IMM   => format!(".mov32 {} (.imm ({}))",    reg(dst), imm),
        NEG32       => format!(".neg32 {}",                reg(dst)),
        ADD32_REG   => format!(".add32 {} (.reg {})",      reg(dst), reg(src)),
        SUB32_REG   => format!(".sub32 {} (.reg {})",      reg(dst), reg(src)),
        MUL32_REG   => format!(".mul32 {} (.reg {})",      reg(dst), reg(src)),
        OR32_REG    => format!(".or32 {} (.reg {})",       reg(dst), reg(src)),
        AND32_REG   => format!(".and32 {} (.reg {})",      reg(dst), reg(src)),
        XOR32_REG   => format!(".xor32 {} (.reg {})",      reg(dst), reg(src)),
        LSH32_REG   => format!(".lsh32 {} (.reg {})",      reg(dst), reg(src)),
        RSH32_REG   => format!(".rsh32 {} (.reg {})",      reg(dst), reg(src)),
        MOV32_REG   => format!(".mov32 {} (.reg {})",      reg(dst), reg(src)),
        ARSH64_IMM  => format!(".arsh64 {} (.imm ({}))",   reg(dst), imm),
        ARSH64_REG  => format!(".arsh64 {} (.reg {})",     reg(dst), reg(src)),
        ARSH32_IMM  => format!(".arsh32 {} (.imm ({}))",   reg(dst), imm),
        ARSH32_REG  => format!(".arsh32 {} (.reg {})",     reg(dst), reg(src)),
        JA          => {
            let t = jt(); format!(".ja {}", t)
        }
        JSGT64_IMM | JSGT32_IMM => {
            let t = jt(); format!(".jsgt {} (.imm ({})) {}", reg(dst), imm, t)
        }
        JSLE64_IMM | JSLE32_IMM => {
            let t = jt(); format!(".jsle {} (.imm ({})) {}", reg(dst), imm, t)
        }
        JSLT64_IMM | JSLT32_IMM => {
            let t = jt(); format!(".jslt {} (.imm ({})) {}", reg(dst), imm, t)
        }
        JEQ64_REG | JEQ32_REG => {
            let t = jt(); format!(".jeq {} (.reg {}) {}", reg(dst), reg(src), t)
        }
        JNE64_REG | JNE32_REG => {
            let t = jt(); format!(".jne {} (.reg {}) {}", reg(dst), reg(src), t)
        }
        JLT64_REG | JLT32_REG => {
            let t = jt(); format!(".jlt {} (.reg {}) {}", reg(dst), reg(src), t)
        }
        JSLE64_REG | JSLE32_REG => {
            let t = jt(); format!(".jsle {} (.reg {}) {}", reg(dst), reg(src), t)
        }
        JGT64_REG | JGT32_REG => {
            let t = jt(); format!(".jgt {} (.reg {}) {}", reg(dst), reg(src), t)
        }
        JLE64_REG | JLE32_REG => {
            let t = jt(); format!(".jle {} (.reg {}) {}", reg(dst), reg(src), t)
        }
        JSGE64_REG | JSGE32_REG => {
            let t = jt(); format!(".jsge {} (.reg {}) {}", reg(dst), reg(src), t)
        }
        JGE64_REG | JGE32_REG => {
            let t = jt(); format!(".jge {} (.reg {}) {}", reg(dst), reg(src), t)
        }
        JSGT64_REG | JSGT32_REG => {
            let t = jt(); format!(".jsgt {} (.reg {}) {}", reg(dst), reg(src), t)
        }
        JSLT64_REG | JSLT32_REG => {
            let t = jt(); format!(".jslt {} (.reg {}) {}", reg(dst), reg(src), t)
        }
        JSET64_REG | JSET32_REG => {
            let t = jt(); format!(".jset {} (.reg {}) {}", reg(dst), reg(src), t)
        }
        JSGE64_IMM | JSGE32_IMM => {
            let t = jt(); format!(".jsge {} (.imm ({})) {}", reg(dst), imm, t)
        }
        JSET64_IMM | JSET32_IMM => {
            let t = jt(); format!(".jset {} (.imm ({})) {}", reg(dst), imm, t)
        }
        // call_local imm is a Murmur3 hash, not an offset; caller must pre-resolve via Analysis::cfg_nodes.
        CALL_IMM    => match call_target {
            Some(t) => format!(".call_local {}", t),
            None    => ".call_local TARGET_PC_NOT_RESOLVED".to_string(),
        },
        opc         => return Err(format!("opcode 0x{:02x} not yet lifted to Lean", opc)),
    })
}

/// Wrapper for callers without a resolved call target; renders call_local with a placeholder.
fn insn_to_lean(insn: &ebpf::Insn, pc: usize) -> Result<String, String> {
    insn_to_lean_full(insn, pc, None, None)
}

/// Resolve CALL_IMM to its callee slot PC by reversing the Murmur3-hash immediate via `analysis.functions`.
fn resolve_call_target(analysis: &Analysis, insn: &ebpf::Insn) -> Option<usize> {
    if insn.opc != ebpf::CALL_IMM { return None; }
    let target_hash = insn.imm as u32;
    analysis.functions.iter()
        .find_map(|(&pc, (h, _name))| if *h == target_hash { Some(pc) } else { None })
}

/// Like `resolve_call_target` but converts the slot-based result to a logical index. `lddw` counts as two slots but one logical insn, so a callee past any `lddw` would be off by the lddw count without this (e.g. p_token: logical 10836, slot 11537).
fn resolve_call_target_logical(
    ctx: &BinaryCtx, analysis: &Analysis, insn: &ebpf::Insn,
) -> Option<usize> {
    let slot = resolve_call_target(analysis, insn)?;
    // out of range / mid-lddw: fall back to slot so downstream fails loudly.
    Some(ctx.pc_map.slot_to_logical(slot).unwrap_or(slot))
}

/// Render call stack as a Lean `List CallFrame` literal, newest-frame first (`frame :: cs` per `call_local_spec`). Each frame: `⟨callpc+1, r6..r10⟩`.
fn render_callstack(frames: &[(usize, [Expr; 5])]) -> String {
    if frames.is_empty() { return "[]".to_string(); }
    let items: Vec<String> = frames.iter().rev().map(|(cp, regs)| {
        format!("⟨{} + 1, {}, {}, {}, {}, {}⟩", cp,
            regs[0].atom_lean(), regs[1].atom_lean(), regs[2].atom_lean(),
            regs[3].atom_lean(), regs[4].atom_lean())
    }).collect();
    format!("[{}]", items.join(", "))
}

// Symbolic executor: walks decoded eBPF insns, synthesizes pre/post for `cuTripleWithinMem n 0 0 n cr PRE POST RR`, discharged by `sl_block_auto`.

/// Symbolic Nat expression during execution; stringified to Lean source via `to_lean`.
#[derive(Clone, Debug)]
enum Expr {
    InitReg(String),
    InitMem(String),
    Const(i64),
    ToU64(Box<Expr>),
    Mod(Box<Expr>, u64),
    WrapAdd(Box<Expr>, Box<Expr>),
    WrapSub(Box<Expr>, Box<Expr>),
    WrapMul(Box<Expr>, Box<Expr>),
    /// Plain `Nat.add a b` — `call_local_spec`'s `r10 + 0x1000` uses Nat add, not `wrapAdd`.
    NatAdd(Box<Expr>, Box<Expr>),
    /// `(a &&& toU64 imm) % U64_MODULUS` — output of `and64_imm_spec`; `toU64 imm` rendered inside `to_lean`.
    AndU64Imm(Box<Expr>, i64),
    /// `(a <<< (toU64 imm % 64)) % U64_MODULUS` — output of `lsh64_imm_spec`.
    LshU64Imm(Box<Expr>, i64),
    /// `toU64 imm % 2 ^ (2 * 8)` — matches `sth_spec`'s post.
    StHalfImm(i64),
    /// `toU64 imm % 2 ^ (4 * 8)` — matches `stw_spec`'s post (`writeByWidth` truncates to 32 bits).
    StWordImm(i64),
    /// `toU64 imm % 2 ^ (8 * 8)` — matches `stdw_spec`'s post.
    StDwordImm(i64),
    /// `a >>> (toU64 imm % 64)` — output of `rsh64_imm_spec`; no `% U64_MODULUS` (right shift never grows).
    RshU64Imm(Box<Expr>, i64),
    /// Render-only `a - b` (Nat sub): exposes a `wrapSub` debit cleanly in the balance corollary (justified by `wrapSub_of_le`).
    CleanSub(Box<Expr>, Box<Expr>),
    /// LE Horner combination of 8 byte cells from `ldxdw` over a hot (byte-demoted) region; matches `ldxdw_bytes_spec`'s post.
    ByteCombo(Vec<Expr>),
    /// Pre-rendered Lean term for ALU results without a bespoke variant (or/xor/div/mod/neg, reg shifts, 32-bit ops). Opaque to the balance corollary; always parenthesised as a function argument.
    Raw(String),
}

impl Expr {
    fn to_lean(&self) -> String {
        match self {
            Expr::Raw(s) => s.clone(),
            Expr::InitReg(n) | Expr::InitMem(n) => n.clone(),
            Expr::Const(n) => format!("{}", n),
            Expr::ToU64(e) => format!("toU64 {}", e.atom_lean()),
            Expr::Mod(e, m) => format!("{} % {}", e.atom_lean(), m),
            Expr::WrapAdd(a, b) => format!("wrapAdd {} {}", a.atom_lean(), b.atom_lean()),
            Expr::WrapSub(a, b) => format!("wrapSub {} {}", a.atom_lean(), b.atom_lean()),
            Expr::WrapMul(a, b) => format!("wrapMul {} {}", a.atom_lean(), b.atom_lean()),
            Expr::NatAdd(a, b) => format!("{} + {}", a.atom_lean(), b.atom_lean()),
            Expr::AndU64Imm(a, imm) => {
                let imm_lean = if *imm < 0 { format!("({})", imm) } else { format!("{}", imm) };
                format!("({} &&& toU64 {}) % U64_MODULUS", a.atom_lean(), imm_lean)
            }
            Expr::LshU64Imm(a, imm) => {
                let imm_lean = if *imm < 0 { format!("({})", imm) } else { format!("{}", imm) };
                format!("({} <<< (toU64 {} % 64)) % U64_MODULUS", a.atom_lean(), imm_lean)
            }
            Expr::StHalfImm(imm) => {
                let imm_lean = if *imm < 0 { format!("({})", imm) } else { format!("{}", imm) };
                format!("toU64 {} % 2 ^ (2 * 8)", imm_lean)
            }
            Expr::StWordImm(imm) => {
                let imm_lean = if *imm < 0 { format!("({})", imm) } else { format!("{}", imm) };
                format!("toU64 {} % 2 ^ (4 * 8)", imm_lean)
            }
            Expr::StDwordImm(imm) => {
                let imm_lean = if *imm < 0 { format!("({})", imm) } else { format!("{}", imm) };
                format!("toU64 {} % 2 ^ (8 * 8)", imm_lean)
            }
            Expr::RshU64Imm(a, imm) => {
                let imm_lean = if *imm < 0 { format!("({})", imm) } else { format!("{}", imm) };
                format!("{} >>> (toU64 {} % 64)", a.atom_lean(), imm_lean)
            }
            Expr::CleanSub(a, b) => format!("{} - {}", a.atom_lean(), b.atom_lean()),
            Expr::ByteCombo(bs) => {
                // Horner fold: innermost pair unparenthesised, matching `ldxdw_bytes_spec`'s post.
                let mut it = bs.iter().rev();
                let mut s = it.next().map(|e| e.atom_lean()).unwrap_or_default();
                let mut first = true;
                for b in it {
                    if first {
                        s = format!("{} + 256 * {}", b.atom_lean(), s);
                        first = false;
                    } else {
                        s = format!("{} + 256 * ({})", b.atom_lean(), s);
                    }
                }
                s
            }
        }
    }
    /// Lean rendering as a function argument (parenthesised when not already atomic).
    fn atom_lean(&self) -> String {
        match self {
            Expr::Raw(s) => format!("({})", s),
            Expr::InitReg(_) | Expr::InitMem(_) => self.to_lean(),
            // Negative constants need parens: `toU64 -1` parses as subtraction otherwise.
            Expr::Const(n) if *n < 0 => format!("({})", n),
            Expr::Const(_) => self.to_lean(),
            _ => format!("({})", self.to_lean()),
        }
    }
}

/// Load/store width — determines Lean memory notation (↦ₘ byte, ↦U16/32/64 wider).
#[derive(Clone, Copy, Debug)]
enum Width { Byte, Halfword, Word, Dword }

impl Width {
    fn lean_arrow(&self) -> &'static str {
        match self {
            Width::Byte     => "↦ₘ",
            Width::Halfword => "↦U16",
            Width::Word     => "↦U32",
            Width::Dword    => "↦U64",
        }
    }
}

/// Render a memory offset for `effectiveAddr base off`. Negative offsets MUST be parenthesised: `effectiveAddr b -8` parses as `(effectiveAddr b) - 8` (HSub type error, partial application).
fn lean_off(off: i64) -> String {
    if off < 0 { format!("({})", off) } else { format!("{}", off) }
}

/// Render `arsh{32,64}`'s post as a parenthesised Lean term matching `arsh{32,64}_{imm,reg}_spec` (used as `Expr::Raw`). Parens required: `↦ᵣ` can't take a bare `let`.
fn arsh_render(vold: &str, shift_src: &str, bits: u32) -> String {
    let m = if bits == 64 { "U64_MODULUS" } else { "U32_MODULUS" };
    if bits == 64 {
        format!("(let shift := {s} % 64; if {v} < {m} / 2 then {v} >>> shift \
                 else (let shifted := {v} >>> shift; \
                 let highBits := ({m} - 1) - ({m} / (2 ^ shift) - 1); \
                 (shifted ||| highBits) % {m}))",
                s = shift_src, v = vold, m = m)
    } else {
        format!("(let shift := {s} % 32; let a := {v} % {m}; \
                 if a < {m} / 2 then a >>> shift \
                 else (let shifted := a >>> shift; \
                 let highBits := ({m} - 1) - ({m} / (2 ^ shift) - 1); \
                 (shifted ||| highBits) % {m}))",
                s = shift_src, v = vold, m = m)
    }
}

/// Variable-length byte blob (`↦Bytes`). Pre-state is a fresh symbolic `ByteArray`; a memset rewrites it to a `Replicate` payload.
#[derive(Clone, Debug)]
enum BytesVal {
    /// Fresh symbolic byte-array name; `.size = <r3>` bound surfaced as a hypothesis via `memset_blobs`, not stored here.
    Sym(String),
    /// `replicateByte (fill % 256).toUInt8 count` — post-state of `sol_memset_(dst, fill, count)`.
    Replicate { fill: Expr, count: Expr },
}

impl BytesVal {
    fn to_lean(&self) -> String {
        match self {
            BytesVal::Sym(name) => name.clone(),
            BytesVal::Replicate { fill, count } => format!(
                "replicateByte ({} % 256).toUInt8 {}",
                fill.atom_lean(), count.atom_lean(),
            ),
        }
    }
}

/// One precondition atom: register binding, fixed-width memory cell, or `↦Bytes` blob (from `sol_memset_` etc.).
#[derive(Clone, Debug)]
enum Atom {
    Reg(u8, Expr),
    Mem { addr_base: Expr, addr_off: i64, width: Width, value: Expr, delta: i64 },
    /// `addr ↦Bytes <bytes>`. Address is the raw syscall `r1` value (no `effectiveAddr` — `memBytesIs` takes a bare Nat), matching `call_sol_memset_spec`.
    Bytes { addr: Expr, value: BytesVal },
    /// `↦Bytes32` referencing a named Lean `ByteArray` constant (e.g. `SysvarData.rentId` for `sol_get_sysvar`'s id read). Read-only: identical pre and post.
    Bytes32 { addr: Expr, name: String },
}


fn reg_lit(n: u8) -> &'static str {
    match n {
        0 => "r0", 1 => "r1", 2 => "r2", 3 => "r3", 4 => "r4",
        5 => "r5", 6 => "r6", 7 => "r7", 8 => "r8", 9 => "r9", 10 => "r10",
        _ => "r0",
    }
}

fn reg_initial_name(n: u8) -> String {
    match n {
        1 => "baseAddr".to_string(),    // r1 = input ptr by Solana ABI
        _ => format!("vR{}Old", n),
    }
}

/// One memory cell in the symbolic walk. Address is the SYMBOLIC value of `base_reg` at access time — `[r1+0]` at two different PCs is two distinct cells if `r1` changed.
#[derive(Clone, Debug)]
struct MemCell {
    addr_base: Expr,
    addr_off:  i64,
    width:     Width,
    value:     Expr,
    /// Byte offset within a hot (byte-demoted) region relative to `(addr_base, addr_off)`. 0 for ordinary cells. Renders as `effectiveAddr base off + delta`, matching `ldxdw_bytes_spec`'s atom shape (H8 Phase B).
    delta:     i64,
}

impl MemCell {
    /// Stable key over (rendered address, width) — same rendering = same physical cell.
    fn key(&self) -> (String, i64, i64, u8) {
        (self.addr_base.to_lean(), self.addr_off, self.delta, self.width as u8)
    }
}

/// Fold a constant out of an `Expr` (through `toU64`).
fn const_of_expr(e: &Expr) -> Option<i64> {
    match e {
        Expr::Const(k) => Some(*k),
        Expr::ToU64(inner) => const_of_expr(inner),
        _ => None,
    }
}

/// Fold constant `wrapAdd`/`wrapSub`/`NatAdd` layers of an address into a canonical `(root, displacement)` pair. Opaque bases become their own root. Soundness: without canonicalization the walker keys by RENDERED address, so aliased footprints generate two overlapping atoms in one sepConj — UNSATISFIABLE, making the theorem vacuous. Audit H8: InitializeMint2 was vacuous via `stw [r10-4]; stw [r10-7]`.
fn canon_addr(base: &Expr, off: i64) -> (String, i64) {
    fn go(e: &Expr, acc: i64) -> Option<(String, i64)> {
        match e {
            Expr::InitReg(_) | Expr::InitMem(_) => Some((e.to_lean(), acc)),
            Expr::Const(k) => Some(("«absolute»".to_string(), acc.wrapping_add(*k))),
            Expr::ToU64(inner) => go(inner, acc),
            Expr::WrapAdd(a, b) | Expr::NatAdd(a, b) => {
                if let Some(k) = const_of_expr(b) {
                    go(a, acc.wrapping_add(k))
                } else if let Some(k) = const_of_expr(a) {
                    go(b, acc.wrapping_add(k))
                } else {
                    None
                }
            }
            Expr::WrapSub(a, b) => {
                if let Some(k) = const_of_expr(b) {
                    go(a, acc.wrapping_sub(k))
                } else {
                    None
                }
            }
            _ => None,
        }
    }
    go(base, off).unwrap_or_else(|| (base.to_lean(), off))
}

/// Like `canon_addr` but returns the root sub-`Expr` instead of its rendering — the satisfiability-witness builder needs the tree to solve/evaluate.
fn canon_root_expr<'a>(e: &'a Expr, acc: i64) -> (Option<&'a Expr>, i64) {
    match e {
        Expr::InitReg(_) | Expr::InitMem(_) => (Some(e), acc),
        Expr::Const(k) => (None, acc.wrapping_add(*k)),
        Expr::ToU64(inner) => canon_root_expr(inner, acc),
        Expr::WrapAdd(a, b) | Expr::NatAdd(a, b) => {
            if let Some(k) = const_of_expr(b) {
                canon_root_expr(a, acc.wrapping_add(k))
            } else if let Some(k) = const_of_expr(a) {
                canon_root_expr(b, acc.wrapping_add(k))
            } else {
                (Some(e), acc)
            }
        }
        Expr::WrapSub(a, b) => {
            if let Some(k) = const_of_expr(b) {
                canon_root_expr(a, acc.wrapping_sub(k))
            } else {
                (Some(e), acc)
            }
        }
        _ => (Some(e), acc),
    }
}

/// Evaluate an `Expr` to `u64` under a variable assignment, mirroring Lean semantics. `None` for unassigned variables or `Raw`. Used by the satisfiability-witness builder; every result is re-checked kernel-side by `native_decide`, so a divergence fails `lake build` rather than weakening the witness.
fn eval_expr(e: &Expr, env: &std::collections::BTreeMap<String, u64>) -> Option<u64> {
    match e {
        Expr::InitReg(n) | Expr::InitMem(n) => env.get(n).copied(),
        Expr::Const(k) => if *k >= 0 { Some(*k as u64) } else { None },
        Expr::ToU64(inner) => match inner.as_ref() {
            Expr::Const(k) => Some(*k as u64),
            other => eval_expr(other, env),
        },
        Expr::Mod(a, m) => eval_expr(a, env).map(|v| if *m == 0 { v } else { v % *m }),
        Expr::WrapAdd(a, b) => Some(eval_expr(a, env)?.wrapping_add(eval_expr(b, env)?)),
        Expr::WrapSub(a, b) => Some(eval_expr(a, env)?.wrapping_sub(eval_expr(b, env)?)),
        Expr::WrapMul(a, b) => Some(eval_expr(a, env)?.wrapping_mul(eval_expr(b, env)?)),
        // Nat add: overflow would diverge from Lean's Nat (where addition is unbounded), so fail closed.
        Expr::NatAdd(a, b) => eval_expr(a, env)?.checked_add(eval_expr(b, env)?),
        Expr::AndU64Imm(a, imm) => Some(eval_expr(a, env)? & (*imm as u64)),
        Expr::LshU64Imm(a, imm) =>
            Some(eval_expr(a, env)?.wrapping_shl((*imm as u64 % 64) as u32)),
        Expr::RshU64Imm(a, imm) =>
            Some(eval_expr(a, env)? >> (*imm as u64 % 64)),
        Expr::StHalfImm(imm) => Some((*imm as u64) % (1 << 16)),
        Expr::StWordImm(imm) => Some((*imm as u64) % (1 << 32)),
        Expr::StDwordImm(imm) => Some(*imm as u64),
        Expr::CleanSub(a, b) => eval_expr(a, env)?.checked_sub(eval_expr(b, env)?),
        Expr::ByteCombo(bs) => {
            let mut acc: u64 = 0;
            for b in bs.iter().rev() {
                acc = acc.wrapping_mul(256).wrapping_add(eval_expr(b, env)?);
            }
            Some(acc)
        }
        Expr::Raw(_) => None,
    }
}

/// Assign the single unassigned variable in an invertible address expression so it evaluates to `target`. Handles `wrapAdd`/`wrapSub`, `toU64`, `%`, and `&&& imm` mask. Fail-closed on shapes it can't invert.
fn solve_expr(
    e: &Expr,
    target: u64,
    env: &mut std::collections::BTreeMap<String, u64>,
) -> bool {
    // Fully evaluable under current env: can only check, not steer.
    if let Some(v) = eval_expr(e, env) {
        return v == target;
    }
    match e {
        Expr::InitReg(n) | Expr::InitMem(n) => {
            env.insert(n.clone(), target);
            true
        }
        Expr::ToU64(inner) => solve_expr(inner, target, env),
        Expr::Mod(a, m) => {
            if *m != 0 && target >= *m { return false; }
            solve_expr(a, target, env)
        }
        Expr::WrapAdd(a, b) => {
            if let Some(va) = eval_expr(a, env) {
                solve_expr(b, target.wrapping_sub(va), env)
            } else if let Some(vb) = eval_expr(b, env) {
                solve_expr(a, target.wrapping_sub(vb), env)
            } else {
                false
            }
        }
        Expr::WrapSub(a, b) => {
            if let Some(vb) = eval_expr(b, env) {
                solve_expr(a, target.wrapping_add(vb), env)
            } else if let Some(va) = eval_expr(a, env) {
                solve_expr(b, va.wrapping_sub(target), env)
            } else {
                false
            }
        }
        Expr::NatAdd(a, b) => {
            if let Some(va) = eval_expr(a, env) {
                target.checked_sub(va).map_or(false, |t| solve_expr(b, t, env))
            } else if let Some(vb) = eval_expr(b, env) {
                target.checked_sub(vb).map_or(false, |t| solve_expr(a, t, env))
            } else {
                false
            }
        }
        Expr::AndU64Imm(a, imm) => {
            // target must be a fixed point of the mask; then target itself is a valid pre-image.
            if target & (*imm as u64) != target { return false; }
            solve_expr(a, target, env)
        }
        Expr::ByteCombo(bs) => {
            // LE: element i carries byte i of target (elements past 8 must be 0). Re-evaluate to confirm (a conflicting constant fails).
            for (i, b) in bs.iter().enumerate() {
                let byte = if i < 8 { (target >> (8 * i)) & 0xff } else { 0 };
                if !solve_expr(b, byte, env) { return false; }
            }
            eval_expr(e, env) == Some(target)
        }
        _ => false,
    }
}

#[derive(Default)]
struct SymState {
    /// Symbolic register values; absent entries are treated as `InitReg(reg_initial_name(r))`.
    regs: std::collections::BTreeMap<u8, Expr>,
    /// Pre-condition atoms collected in *first-touched* order.
    pre: Vec<Atom>,
    /// Memory cells the slice touched; `base` is the SYMBOLIC register value at access time (so `[r1+0]` after `add64 r1,8` is a distinct cell). Linear search; small N.
    mem: Vec<MemCell>,
    /// Fresh-variable counter for memory initials.
    fresh: u32,
    /// `(var, k)` pairs for memory loads with a `< 2^k` side condition (k=16/32/64 for ldxh/ldxw/ldxdw). Emitted as `h<var>_lt` hypotheses in the theorem signature.
    u64_load_vars: Vec<(String, u32)>,
    /// Conditional jumps on the happy-path walk; each adds a path hypothesis to the theorem signature.
    branch_hyps: Vec<BranchHyp>,
    /// `(resume_pc, [r6..r10] at call time)` pushed by `call_local`, popped by `exit`. Full r6..r10 saved because a callee may clobber r6..r9 — `exit_pops` needs the frame from call time, not exit time.
    call_stack: Vec<(usize, [Expr; 5])>,
    /// Set on first `call_local`; emission then adds `r6..r10` and `callStackIs []` to the pre-condition.
    saw_call: bool,
    /// rr clauses in walk order (load → `containsRange`, store → `containsWritable`), matching `slBlockIter`'s left-fold. `memset_override = Some((dst, count))` is a variable-length `containsWritable` clause (H6: `MemOps.execSet.guardWrite`); fixed fields ignored, address rendered raw without `effectiveAddr`.
    rr_walk: Vec<(Expr, i64, Width, bool, Option<(Expr, Expr)>)>,
    /// Post-state of `↦Bytes` blobs written by `sol_memset_`, keyed by rendered address. Read by `post_atoms` to transform pre `Sym` → post `Replicate`.
    byte_blob_post: std::collections::BTreeMap<String, BytesVal>,
    /// PC → Lean `Syscall` constructor for identified host syscalls; CodeReq renders as `.call <ctor>` instead of `.call_local`.
    syscall_pcs: std::collections::BTreeMap<usize, &'static str>,
    /// `(nCu_var, hCu_hyp, syscall_ctor)` per syscall with surfaced CU cost. `syscallCu` is data-dependent (∝ r3 for mem ops), so the upper bound is an assumption the lift can't discharge.
    syscall_cu_vars: Vec<(String, String, &'static str)>,
    /// `(bytes_sym, size_rendered)` per memset blob; emitted as a `ByteArray` param + `.size = <count>` hypothesis (spec's `hbs` obligation).
    memset_blobs: Vec<(String, String)>,
    /// `(hyp_name, prop)` side-condition hypotheses emitted verbatim (e.g. divisor `v ≠ 0` for `div/mod` reg-form — symbolic divisor, so caller's obligation).
    side_hyps: Vec<(String, String)>,
    /// Canonical `(root, lo, hi_exclusive, key_render)` footprint of every materialized atom. Consulted on each new materialization to detect overlaps — an overlapping sepConj is unsatisfiable (vacuous theorem, soundness audit H8).
    atom_spans: Vec<(String, i64, i64, String)>,
    /// Footprint-overlap errors from `note_access`; reported as a hard error after the walk (fail-closed: never emit a vacuous theorem; full inventory aids Phase B planning).
    overlap_errors: Vec<String>,
    /// `(lhs, rhs)` set when an access resolved to an existing cell under a DIFFERENT rendering (Phase A aliasing). Walk loop drains it into `h_alias_<pc> : lhs = rhs` (discharged by `decide`); the spec-call `rw`s it so the chain composes on one atom.
    pending_alias: Option<(String, String)>,
    /// Per-root byte-granular ("hot") regions for mixed-width accesses; kept as per-byte atoms so the sepConj stays satisfiable (H8 Phase B). Computed by the retry loop in `lift_one`.
    hot_regions: std::collections::BTreeMap<String, Vec<(i64, i64)>>,
    /// Demotion requests from this pass (wide access over cells outside the current hot set). Merged into `hot_regions` by the retry loop; this pass's output is discarded.
    new_hot: Vec<(String, i64, i64)>,
    /// `(root, lo, len, fill)` for constant-count memset blobs; registered by `emit_sol_memset` so later reads can plan a tail split (H8 Phase C).
    blobs: Vec<(String, i64, i64, Option<u8>)>,
    /// `(root, lo)` → split offset `n` plan: blob's last 8 bytes (`[n, n+8)`) become a `↦U64` cell. Input to the walk; grown by `new_blob_splits` + retry.
    blob_splits: std::collections::BTreeMap<(String, i64), i64>,
    /// Tail-split requests from this pass (dword read at a blob's 8-byte tail); merged by the retry loop.
    new_blob_splits: Vec<(String, i64, i64)>,
    /// Per-slot alias equations for the current instruction (a hot wide access whose byte slots live under foreign renderings). Each `(lhs, rhs)` becomes `h_alias_<pc>_<i> : lhs = rhs`, rewritten into the spec hypothesis.
    pending_slot_aliases: Vec<(String, String)>,
}

impl SymState {
    /// Record the byte footprint of a new atom and flag overlap with any DIFFERENT existing atom on the same root. Overlapping atoms in a sepConj → unsatisfiable precondition → vacuous theorem (soundness audit H8).
    fn note_access(&mut self, base: &Expr, off: i64, len: i64, key_render: String) {
        let (root, lo) = canon_addr(base, off);
        let hi = lo.wrapping_add(len);
        for (eroot, elo, ehi, ekey) in &self.atom_spans {
            if *eroot == root && *ekey != key_render && lo < *ehi && *elo < hi {
                self.overlap_errors.push(format!(
                    "atom `{key_render}` (root `{root}`, bytes [{lo}, {hi})) \
                     overlaps existing atom `{ekey}` (bytes [{elo}, {ehi}))"));
                return;
            }
        }
        self.atom_spans.push((root, lo, hi, key_render));
    }
    fn read_reg(&mut self, r: u8) -> Expr {
        if let Some(v) = self.regs.get(&r) { return v.clone(); }
        let v = Expr::InitReg(reg_initial_name(r));
        self.regs.insert(r, v.clone());
        self.pre.push(Atom::Reg(r, v.clone()));
        v
    }
    fn write_reg(&mut self, r: u8, v: Expr) {
        // Record pre-atom before first write so the initial value is captured.
        if !self.regs.contains_key(&r) {
            let init = Expr::InitReg(reg_initial_name(r));
            self.regs.insert(r, init.clone());
            self.pre.push(Atom::Reg(r, init));
        }
        self.regs.insert(r, v);
    }
    /// Is `[lo, hi)` on `root` fully inside a hot (byte-demoted) region?
    fn hot_covers(&self, root: &str, lo: i64, hi: i64) -> bool {
        self.hot_regions.get(root)
            .map_or(false, |v| v.iter().any(|(l, h)| *l <= lo && hi <= *h))
    }
    /// Does `[lo, hi)` on `root` intersect any hot region?
    fn hot_intersects(&self, root: &str, lo: i64, hi: i64) -> bool {
        self.hot_regions.get(root)
            .map_or(false, |v| v.iter().any(|(l, h)| lo < *h && *l < hi))
    }
    /// The `effectiveAddr …` rendering of a cell (hot byte cells carry
    /// a `+ delta` suffix, matching `ldxdw_bytes_spec`'s atom shape).
    fn cell_render(c: &MemCell) -> String {
        if c.delta != 0 {
            format!("effectiveAddr ({}) ({}) + {}",
                c.addr_base.to_lean(), c.addr_off, c.delta)
        } else {
            format!("effectiveAddr ({}) ({})", c.addr_base.to_lean(), c.addr_off)
        }
    }
    /// Push a `new_hot` request covering the UNION of `[lo, lo+wlen)` and every conflicting cell's span when footprints conflict or straddle a hot edge (but NOT for same span+width, which is the aliased lookup's job).
    fn request_demotion_on_conflict(&mut self, root: &str, lo: i64, wlen: i64,
        width: Width) {
        let (mut nlo, mut nhi) = (lo, lo + wlen);
        let mut conflict = false;
        for c in &self.mem {
            let (cr, cd) = canon_addr(&c.addr_base, c.addr_off);
            if cr != root { continue; }
            let cl = cd + c.delta;
            let ch = cl + match c.width {
                Width::Byte => 1, Width::Halfword => 2,
                Width::Word => 4, Width::Dword => 8,
            };
            let same_cell = cl == lo && ch == lo + wlen
                && c.width as u8 == width as u8;
            if !same_cell && lo < ch && cl < lo + wlen {
                conflict = true;
                nlo = nlo.min(cl);
                nhi = nhi.max(ch);
            }
        }
        if conflict || self.hot_intersects(root, lo, lo + wlen) {
            self.new_hot.push((root.to_string(), nlo, nhi));
        }
    }
    /// Address rendering `*_bytes_spec` uses for slot `k` of access at `(base, off)`.
    fn slot_expected_render(base: &Expr, off: i64, k: i64) -> String {
        if k == 0 {
            format!("effectiveAddr ({}) ({})", base.to_lean(), off)
        } else {
            format!("effectiveAddr ({}) ({}) + {}", base.to_lean(), off, k)
        }
    }
    /// Resolve or materialize the byte cell for slot `k` of a hot wide access. Foreign-rendered slots get a per-slot alias equation in `pending_slot_aliases`.
    fn hot_slot(&mut self, base_expr: &Expr, off: i64, k: i64) -> usize {
        let (root, lo) = canon_addr(base_expr, off);
        let base_lean = base_expr.to_lean();
        if let Some(i) = self.mem.iter().position(|c| {
            matches!(c.width, Width::Byte) && {
                let (cr, cd) = canon_addr(&c.addr_base, c.addr_off);
                cr == root && cd + c.delta == lo + k
            }
        }) {
            let render_ok = self.mem[i].addr_base.to_lean() == base_lean
                && self.mem[i].addr_off == off
                && ((k == 0 && self.mem[i].delta == 0)
                    || self.mem[i].delta == k);
            if !render_ok {
                self.pending_slot_aliases.push((
                    Self::cell_render(&self.mem[i]),
                    Self::slot_expected_render(base_expr, off, k),
                ));
            }
            // Bare vars in wide-access byte slots need a `< 256` bound.
            if let Expr::InitMem(name) = &self.mem[i].value {
                let name = name.clone();
                if !self.u64_load_vars.iter().any(|(n, _)| *n == name) {
                    self.u64_load_vars.push((name, 8));
                }
            }
            return i;
        }
        let idx = self.fresh; self.fresh += 1;
        let name = format!("oldMemB_{}", idx);
        self.u64_load_vars.push((name.clone(), 8));
        let v = Expr::InitMem(name);
        self.mem.push(MemCell {
            addr_base: base_expr.clone(), addr_off: off,
            width: Width::Byte, value: v.clone(), delta: k,
        });
        self.pre.push(Atom::Mem {
            addr_base: base_expr.clone(), addr_off: off,
            width: Width::Byte, value: v, delta: k,
        });
        self.note_access(base_expr, off + k, 1,
            format!("{}@{}+{}:HotByte", base_lean, off, k));
        self.mem.len() - 1
    }
    /// Hot `st .word imm`: realize 4 byte cells (pre = spec's `b0..b3`) and overwrite with LE bytes of `imm` (`stw_bytes_spec`'s `c0..c3`).
    fn write_hot_word_imm(&mut self, base_expr: Expr, off: i64, imm: i64) {
        let w = (imm as i64) as u32; // toU64 imm % 2^32
        let bytes = w.to_le_bytes();
        for k in 0..4i64 {
            let i = self.hot_slot(&base_expr, off, k);
            self.mem[i].value = Expr::Const(bytes[k as usize] as i64);
        }
        self.rr_walk.push((base_expr, off, Width::Word, true, None));
    }
    /// Serve a hot wide LOAD: reuse/materialize 8 byte cells and return their Horner combination (matches `ldxdw_bytes_spec`). Fail-closed for non-dword widths.
    fn read_hot_wide(&mut self, base_expr: Expr, off: i64, width: Width) -> Expr {
        if !matches!(width, Width::Dword) {
            self.overlap_errors.push(format!(
                "hot-region {:?} access at ({})+{} — only dword LOADS are \
                 byte-demoted so far (H8 Phase B-1)",
                width, base_expr.to_lean(), off));
            return Expr::Raw("hotUnsupported".into());
        }
        let mut vals: Vec<Expr> = Vec::with_capacity(8);
        for k in 0..8i64 {
            let i = self.hot_slot(&base_expr, off, k);
            vals.push(self.mem[i].value.clone());
        }
        self.rr_walk.push((base_expr, off, Width::Dword, false, None));
        Expr::ByteCombo(vals)
    }
    /// Exact-rendering lookup first, then canonical `(root, disp, width)` — a canonical hit is the SAME cell under a different rendering (Phase A aliasing). Returns `(index, is_alias)`.
    fn lookup_cell_aliased(&self, base: &Expr, off: i64, width: Width)
        -> Option<(usize, bool)> {
        let key = (base.to_lean(), off, 0i64, width as u8);
        if let Some(i) = self.mem.iter().position(|c| c.key() == key) {
            return Some((i, false));
        }
        let (root, disp) = canon_addr(base, off);
        self.mem.iter().position(|c| {
            if c.width as u8 != width as u8 { return false; }
            let (cr, cd) = canon_addr(&c.addr_base, c.addr_off);
            cr == root && cd + c.delta == disp
        }).map(|i| (i, true))
    }
    fn read_mem(&mut self, base: u8, off: i64, width: Width) -> Expr {
        let base_expr = self.read_reg(base);
        let wlen = match width {
            Width::Byte => 1i64, Width::Halfword => 2, Width::Word => 4, Width::Dword => 8,
        };
        if wlen > 1 {
            let (root, lo) = canon_addr(&base_expr, off);
            // Dword read at blob's 8-byte tail → plan a tail split (`↦U64` cell, H8 Phase C). New: request + retry; already planned: aliased lookup hits below.
            if matches!(width, Width::Dword) {
                if let Some((broot, blo, blen, _)) = self.blobs.iter()
                    .find(|(br, bl, bn, _)| *br == root && *bl <= lo
                          && lo + 8 <= *bl + *bn)
                    .cloned() {
                    let rel = lo - blo;
                    if rel + 8 == blen
                        && !self.blob_splits.contains_key(&(broot.clone(), blo)) {
                        self.new_blob_splits.push((broot, blo, rel));
                    }
                    // Non-tail reads fall through to the overlap detector (middle split not implemented).
                }
            }
            if self.hot_covers(&root, lo, lo + wlen) {
                return self.read_hot_wide(base_expr, off, width);
            }
            // Footprint conflict or hot-edge straddle: request demotion and retry (this pass's output is discarded).
            self.request_demotion_on_conflict(&root, lo, wlen, width);
        }
        if let Some((i, aliased)) = self.lookup_cell_aliased(&base_expr, off, width) {
            let cell_base = self.mem[i].addr_base.clone();
            let cell_off  = self.mem[i].addr_off;
            let v = self.mem[i].value.clone();
            // Every load instruction, even a re-read, contributes `containsRange` to keep the goal rr 1:1 with walked instructions.
            if aliased {
                // Aliased: rr clause and (via `rw [h_alias_<pc>]`) the spec hypothesis use the CANONICAL rendering — one atom per physical cell.
                let rhs = Self::cell_render(&self.mem[i]);
                self.pending_alias = Some((
                    format!("effectiveAddr ({}) ({})", base_expr.to_lean(), off),
                    rhs,
                ));
                self.rr_walk.push((cell_base, cell_off, width, false, None));
            } else {
                self.rr_walk.push((base_expr, off, width, false, None));
            }
            return v;
        }
        // Name fresh cells by width+index; the address expression itself may be ill-suited as a Lean identifier.
        let idx = self.fresh; self.fresh += 1;
        let name = format!("oldMem{}_{}", w_short(width), idx);
        match width {
            Width::Dword    => self.u64_load_vars.push((name.clone(), 64)),
            Width::Word     => self.u64_load_vars.push((name.clone(), 32)),
            Width::Halfword => self.u64_load_vars.push((name.clone(), 16)),
            Width::Byte     => {} // bytes always fit; no bound needed
        }
        let v = Expr::InitMem(name);
        let cell = MemCell {
            addr_base: base_expr.clone(), addr_off: off, width, value: v.clone(),
            delta: 0,
        };
        let width_len = match width {
            Width::Byte => 1, Width::Halfword => 2, Width::Word => 4, Width::Dword => 8,
        };
        self.note_access(&base_expr, off, width_len,
            format!("{}@{}:{:?}", base_expr.to_lean(), off, width));
        self.mem.push(cell);
        self.pre.push(Atom::Mem {
            addr_base: base_expr.clone(), addr_off: off, width, value: v.clone(),
            delta: 0,
        });
        self.rr_walk.push((base_expr, off, width, false, None));
        v
    }
    fn write_mem(&mut self, base: u8, off: i64, width: Width, value: Expr) {
        let base_expr = self.read_reg(base);
        let wlen = match width {
            Width::Byte => 1i64, Width::Halfword => 2, Width::Word => 4, Width::Dword => 8,
        };
        if wlen > 1 {
            let (root, lo) = canon_addr(&base_expr, off);
            if self.hot_covers(&root, lo, lo + wlen) {
                // Only word-immediate stores are byte-demotable (`stw_bytes_spec`); other wide hot stores fail closed.
                if matches!(width, Width::Word) {
                    if let Expr::StWordImm(imm) = &value {
                        let imm = *imm;
                        self.write_hot_word_imm(base_expr, off, imm);
                        return;
                    }
                }
                self.overlap_errors.push(format!(
                    "wide {:?} STORE at ({})+{} into a hot (byte-demoted) \
                     region — only word-immediate stores and dword loads \
                     are supported so far (H8 Phase B)",
                    width, base_expr.to_lean(), off));
                return;
            }
            self.request_demotion_on_conflict(&root, lo, wlen, width);
            if self.hot_intersects(&root, lo, lo + wlen) {
                // Straddles a hot edge without full coverage — the
                // demotion request above will widen the region; this
                // pass is discarded.
                return;
            }
        }
        // Materialize the pre-atom if missing (store without preceding load). Canon-aware: avoids creating an overlapping twin (Phase A aliasing).
        if self.lookup_cell_aliased(&base_expr, off, width).is_none() {
            let _ = self.read_mem(base, off, width);
            // `read_mem` pushed a `containsRange` entry, but this is a STORE: drop it so the goal rr stays 1:1 with memory instructions (containsWritable below implies readability).
            self.rr_walk.pop();
        }
        if let Some((i, aliased)) = self.lookup_cell_aliased(&base_expr, off, width) {
            let cell_base = self.mem[i].addr_base.clone();
            let cell_off  = self.mem[i].addr_off;
            self.mem[i].value = value;
            if aliased {
                let rhs = Self::cell_render(&self.mem[i]);
                self.pending_alias = Some((
                    format!("effectiveAddr ({}) ({})", base_expr.to_lean(), off),
                    rhs,
                ));
                self.rr_walk.push((cell_base, cell_off, width, true, None));
            } else {
                self.rr_walk.push((base_expr, off, width, true, None));
            }
        }
    }
}

fn w_short(w: Width) -> &'static str {
    match w { Width::Byte => "B", Width::Halfword => "H", Width::Word => "W", Width::Dword => "D" }
}

/// Conditional jump kind for a happy-path branch hypothesis; `sl_block_auto` doesn't collapse these, so they surface in the theorem signature.
#[derive(Clone, Debug)]
enum BranchKind {
    JeqImm, JneImm, JgtImm, JsgtImm, JsleImm, JltImm, JleImm, JsltImm,
    JgeImm, JsgeImm, JsetImm,
    JeqReg, JneReg, JltReg, JsleReg, JgtReg, JleReg, JsgeReg,
    JgeReg, JsgtReg, JsltReg, JsetReg,
}

#[derive(Clone, Debug)]
struct BranchHyp {
    kind: BranchKind,
    dst_value: Expr,
    /// Src register's symbolic value for reg-form jumps; `None` for imm-form.
    src_value: Option<Expr>,
    imm: i64,
    /// `true` if branch taken; `false` for fall-through. Determines hypothesis form:
    /// jeq-taken → `vDst = toU64 imm`, jeq-not-taken → `vDst ≠ toU64 imm`; jne symmetric.
    taken: bool,
}

impl BranchHyp {
    fn lean_hyp(&self) -> String {
        let v = self.dst_value.to_lean();
        let s = self.src_value.as_ref().map(|e| e.to_lean()).unwrap_or_default();
        // atom_lean() parenthesises compound exprs for use under `toSigned64` (prefix application
        // that grabs only the head: `toSigned64 wrapAdd a b` misparses as `(toSigned64 wrapAdd) a b`).
        let va = self.dst_value.atom_lean();
        let sa = self.src_value.as_ref().map(|e| e.atom_lean()).unwrap_or_default();
        // Parenthesise negative imm: `toU64 -5` parses as `(toU64) - 5` (Int→Nat type error).
        let im = if self.imm < 0 { format!("({})", self.imm) } else { format!("{}", self.imm) };
        match (self.kind.clone(), self.taken) {
            (BranchKind::JeqImm, false) => format!("{} ≠ toU64 {}", v, im),
            (BranchKind::JeqImm, true)  => format!("{} = toU64 {}", v, im),
            (BranchKind::JneImm, false) => format!("{} = toU64 {}", v, im),
            (BranchKind::JneImm, true)  => format!("{} ≠ toU64 {}", v, im),
            // `jgt` unsigned >; taken/not-taken accepted by Lean helpers via if_pos/if_neg.
            (BranchKind::JgtImm, false) => format!("¬ {} > toU64 {}", v, im),
            (BranchKind::JgtImm, true)  => format!("{} > toU64 {}", v, im),
            // `jsgt` signed >: compares `toSigned64 vDst > toSigned64 (toU64 imm)`.
            (BranchKind::JsgtImm, false) => format!("¬ toSigned64 {} > toSigned64 (toU64 {})", va, im),
            (BranchKind::JsgtImm, true)  => format!("toSigned64 {} > toSigned64 (toU64 {})", va, im),
            (BranchKind::JsleImm, false) => format!("¬ toSigned64 {} ≤ toSigned64 (toU64 {})", va, im),
            (BranchKind::JsleImm, true)  => format!("toSigned64 {} ≤ toSigned64 (toU64 {})", va, im),
            (BranchKind::JltImm, false) => format!("¬ {} < toU64 {}", v, im),
            (BranchKind::JltImm, true)  => format!("{} < toU64 {}", v, im),
            (BranchKind::JleImm, false) => format!("¬ {} ≤ toU64 {}", v, im),
            (BranchKind::JleImm, true)  => format!("{} ≤ toU64 {}", v, im),
            (BranchKind::JsltImm, false) => format!("¬ toSigned64 {} < toSigned64 (toU64 {})", va, im),
            (BranchKind::JsltImm, true)  => format!("toSigned64 {} < toSigned64 (toU64 {})", va, im),
            (BranchKind::JgeImm, false) => format!("¬ {} ≥ toU64 {}", v, im),
            (BranchKind::JgeImm, true)  => format!("{} ≥ toU64 {}", v, im),
            (BranchKind::JsgeImm, false) => format!("¬ toSigned64 {} ≥ toSigned64 (toU64 {})", va, im),
            (BranchKind::JsgeImm, true)  => format!("toSigned64 {} ≥ toSigned64 (toU64 {})", va, im),
            (BranchKind::JsetImm, false) => format!("¬ {} &&& toU64 {} ≠ 0", v, im),
            (BranchKind::JsetImm, true)  => format!("{} &&& toU64 {} ≠ 0", v, im),
            (BranchKind::JeqReg, false) => format!("{} ≠ {}", v, s),
            (BranchKind::JeqReg, true)  => format!("{} = {}", v, s),
            (BranchKind::JneReg, false) => format!("{} = {}", v, s),
            (BranchKind::JneReg, true)  => format!("{} ≠ {}", v, s),
            (BranchKind::JltReg, false) => format!("¬ {} < {}", v, s),
            (BranchKind::JltReg, true)  => format!("{} < {}", v, s),
            (BranchKind::JgtReg, false) => format!("¬ {} > {}", v, s),
            (BranchKind::JgtReg, true)  => format!("{} > {}", v, s),
            (BranchKind::JleReg, false) => format!("¬ {} ≤ {}", v, s),
            (BranchKind::JleReg, true)  => format!("{} ≤ {}", v, s),
            (BranchKind::JsgeReg, false) => format!("¬ toSigned64 {} ≥ toSigned64 {}", va, sa),
            (BranchKind::JsgeReg, true)  => format!("toSigned64 {} ≥ toSigned64 {}", va, sa),
            (BranchKind::JgeReg, false) => format!("¬ {} ≥ {}", v, s),
            (BranchKind::JgeReg, true)  => format!("{} ≥ {}", v, s),
            (BranchKind::JsgtReg, false) => format!("¬ toSigned64 {} > toSigned64 {}", va, sa),
            (BranchKind::JsgtReg, true)  => format!("toSigned64 {} > toSigned64 {}", va, sa),
            (BranchKind::JsltReg, false) => format!("¬ toSigned64 {} < toSigned64 {}", va, sa),
            (BranchKind::JsltReg, true)  => format!("toSigned64 {} < toSigned64 {}", va, sa),
            (BranchKind::JsetReg, false) => format!("¬ {} &&& {} ≠ 0", v, s),
            (BranchKind::JsetReg, true)  => format!("{} &&& {} ≠ 0", v, s),
            (BranchKind::JsleReg, false) => format!("¬ toSigned64 {} ≤ toSigned64 {}", va, sa),
            (BranchKind::JsleReg, true)  => format!("toSigned64 {} ≤ toSigned64 {}", va, sa),
        }
    }
    fn name(&self, idx: usize) -> String { format!("h_branch{}", idx) }
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

/// Concatenate atoms into a Lean `**`-separated SL expression (`emp` for empty list).
/// `subst` replaces rendered address-base expressions with their abstracted parameter name.
fn atoms_to_lean(
    atoms: &[Atom],
    subst: &std::collections::BTreeMap<String, String>,
) -> String {
    if atoms.is_empty() { return "emp".to_string(); }
    let parts: Vec<String> = atoms.iter().map(|a| atom_to_lean_with_subst(a, subst)).collect();
    parts.join(" **\n      ")
}

/// Fold abstraction RHSes to parameter names inside a rendered string, including sub-expressions
/// (longest-first so parents fold before sub-terms). Mirrors `sl_rw_abs` so goal and chain atoms match.
fn fold_abstractions(
    s: String,
    subst: &std::collections::BTreeMap<String, String>,
) -> String {
    let mut out = s;
    let mut keys: Vec<&String> = subst.keys().collect();
    keys.sort_by_key(|k| std::cmp::Reverse(k.len()));
    for k in keys {
        if let Some(p) = subst.get(k) {
            out = replace_token(&out, k, p);
        }
    }
    out
}

/// Word-boundary-aware replace: substitutes `needle` only where surrounding bytes aren't
/// alphanumeric/underscore — without this, `toU64 3` would corrupt `toU64 32` into `addr02`.
fn replace_token(haystack: &str, needle: &str, repl: &str) -> String {
    if needle.is_empty() { return haystack.to_string(); }
    let is_word = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
    let hb = haystack.as_bytes();
    let nb = needle.as_bytes();
    let mut out = String::with_capacity(haystack.len());
    let mut i = 0usize;
    while i < hb.len() {
        if hb[i..].starts_with(nb) {
            let before_ok = i == 0 || !is_word(hb[i - 1]);
            let after = i + nb.len();
            let after_ok = after >= hb.len() || !is_word(hb[after]);
            if before_ok && after_ok {
                out.push_str(repl);
                i = after;
                continue;
            }
        }
        // Advance one UTF-8 char (handles the `↦`/`%`/`<<<` etc.).
        let ch = haystack[i..].chars().next().unwrap();
        out.push(ch);
        i += ch.len_utf8();
    }
    out
}

fn atom_to_lean_with_subst(
    atom: &Atom,
    subst: &std::collections::BTreeMap<String, String>,
) -> String {
    // Fold whole OR sub-expression abstractions to param names, matching the sl_rw_abs-rewritten goal.
    let sub = |e: &Expr| -> String {
        fold_abstractions(e.to_lean(), subst)
    };
    match atom {
        Atom::Reg(r, v) => {
            format!("(.{} ↦ᵣ {})", reg_lit(*r), sub(v))
        }
        Atom::Mem { addr_base, addr_off, width, value, delta } => {
            let rendered = addr_base.to_lean();
            let addr_str = subst.get(&rendered)
                .map(|p| p.clone())
                .unwrap_or_else(|| addr_base.atom_lean());
            if *delta != 0 {
                // Hot byte cell: `effectiveAddr base off + delta ↦ₘ v` — plain Nat add, the form `ldxdw_bytes_spec` uses.
                return format!(
                    "(effectiveAddr {} {} + {} {} {})",
                    addr_str,
                    if *addr_off < 0 { format!("({})", addr_off) } else { format!("{}", addr_off) },
                    delta, width.lean_arrow(), sub(value),
                );
            }
            format!(
                "(effectiveAddr {} {} {} {})",
                addr_str, lean_off(*addr_off), width.lean_arrow(), sub(value),
            )
        }
        Atom::Bytes { addr, value } => {
            // `memBytesIs` uses a bare Nat address (no effectiveAddr). Use `fold_abstractions` not
            // `subst.get` — the blob address may contain sub-expressions like `wrapAdd baseAddr 8`
            // that `subst.get` (whole-key lookup) misses; `fold_abstractions` matches inner `addrK`.
            format!("({} ↦Bytes {})", sub(addr), value.to_lean())
        }
        Atom::Bytes32 { addr, name } => {
            format!("({} ↦Bytes32 {})", sub(addr), name)
        }
    }
}

/// Build the H8 satisfiability-witness: a concrete variable assignment proving the precondition
/// is satisfiable, kernel-checked by `native_decide`. One guard pins each `addrK` literal to its
/// `h_addrK` equation; the `∃ s, pre s` example uses `SatWitness.sat_witness` with reflected
/// atoms tied to the real pre by defeq. An unsatisfiable pre fails here (fail closed) or fails
/// `lake build` — vacuity is structurally unshippable. Scope: heap/footprint overlap; value-level
/// `h_branch*` path hypotheses are outside the overlap-vacuity class. Address strategy: each
/// canonical root gets a far-apart 0x10000000-spaced base (0x400000000+); remaining vars = 0.
fn build_sat_witness(
    pre: &[Atom],
    state: &SymState,
    abstractions: &[(String, String, String)],
    abs_subst: &std::collections::BTreeMap<String, String>,
    folded_rhs: &[String],
    vars: &[String],
) -> Result<String, String> {
    use std::collections::BTreeMap;

    // Abstraction param → the pre-atom addr_base whose rendering it captured.
    let mut param_expr: BTreeMap<String, Expr> = BTreeMap::new();
    for atom in pre {
        if let Atom::Mem { addr_base, .. } = atom {
            if let Some(p) = abs_subst.get(&addr_base.to_lean()) {
                param_expr.entry(p.clone()).or_insert_with(|| addr_base.clone());
            }
        }
    }

    let mut env: BTreeMap<String, u64> = BTreeMap::new();
    let mut next_base: u64 = 0x4_0000_0000;
    let mut alloc_base = || { let t = next_base; next_base += 0x1000_0000; t };

    let addr_exprs: Vec<&Expr> = pre.iter().filter_map(|a| match a {
        Atom::Mem { addr_base, .. } => Some(addr_base),
        Atom::Bytes { addr, .. } => Some(addr),
        Atom::Bytes32 { addr, .. } => Some(addr),
        Atom::Reg(..) => None,
    }).collect();

    // Pass 1: variable roots get bases directly.
    for e in &addr_exprs {
        if let (Some(Expr::InitReg(n)), _) | (Some(Expr::InitMem(n)), _) =
            canon_root_expr(e, 0)
        {
            if !env.contains_key(n) {
                let b = alloc_base();
                env.insert(n.clone(), b);
            }
        }
    }
    // Pass 2: opaque (derived) roots, steered via their free variable (atom order = creation order).
    let mut solved_roots: std::collections::BTreeSet<String> = Default::default();
    for e in &addr_exprs {
        if let (Some(root), _) = canon_root_expr(e, 0) {
            if matches!(root, Expr::InitReg(_) | Expr::InitMem(_)) { continue; }
            let key = root.to_lean();
            if !solved_roots.insert(key.clone()) { continue; }
            let target = alloc_base();
            if !solve_expr(root, target, &mut env) {
                return Err(format!(
                    "cannot steer derived address root `{}` to a witness \
                     base (unsupported expression shape)", key));
            }
        }
    }
    // Pass 3: every remaining theorem variable is 0.
    for v in vars {
        env.entry(v.clone()).or_insert(0);
    }

    let mut param_vals: BTreeMap<String, u64> = BTreeMap::new();
    for (param, _, _) in abstractions {
        let e = param_expr.get(param).ok_or_else(|| format!(
            "no defining expression recorded for abstraction `{}`", param))?;
        let v = eval_expr(e, &env).ok_or_else(|| format!(
            "cannot evaluate abstraction `{}` under the witness assignment", param))?;
        param_vals.insert(param.clone(), v);
    }

    // `effectiveAddr base off (+ delta)` over u64/i64, mirroring
    // `Int.toNat (base + off)` (clamp at 0, no 2^64 wrap).
    let eff = |base: u64, off: i64, delta: i64| -> u64 {
        let a = (base as i128) + (off as i128);
        let a = if a < 0 { 0 } else { a as u128 };
        (a + delta as u128) as u64
    };

    struct Foot { mem: Option<(u64, u64)>, reg: Option<u8>, cs: bool, desc: String }
    let mut sat_atoms: Vec<String> = Vec::new();
    let mut feet: Vec<Foot> = Vec::new();
    let mut blob_subst: Vec<(String, String)> = Vec::new();
    for atom in pre {
        match atom {
            Atom::Reg(r, v) => {
                let vv = eval_expr(v, &env).ok_or_else(|| format!(
                    "cannot evaluate register r{} initial value", r))?;
                sat_atoms.push(format!(".reg .{} {}", reg_lit(*r), vv));
                feet.push(Foot { mem: None, reg: Some(*r), cs: false,
                                 desc: format!("r{}", r) });
            }
            Atom::Mem { addr_base, addr_off, width, value, delta } => {
                let base = eval_expr(addr_base, &env).ok_or_else(|| format!(
                    "cannot evaluate address base `{}`", addr_base.to_lean()))?;
                let a = eff(base, *addr_off, *delta);
                let vv = eval_expr(value, &env).ok_or_else(|| format!(
                    "cannot evaluate cell value `{}`", value.to_lean()))?;
                let (ctor, sz) = match width {
                    Width::Byte => (".byte", 1u64),
                    Width::Halfword => (".u16", 2),
                    Width::Word => (".u32", 4),
                    Width::Dword => (".u64", 8),
                };
                sat_atoms.push(format!("{} {} {}", ctor, a, vv));
                feet.push(Foot { mem: Some((a, sz)), reg: None, cs: false,
                                 desc: format!("{} cell at {}", ctor, a) });
            }
            Atom::Bytes { addr, value } => {
                let a = eval_expr(addr, &env).ok_or_else(|| format!(
                    "cannot evaluate blob address `{}`", addr.to_lean()))?;
                let name = match value {
                    BytesVal::Sym(n) => n,
                    BytesVal::Replicate { .. } => return Err(
                        "unexpected Replicate blob in a precondition".into()),
                };
                let size_s = state.memset_blobs.iter()
                    .find(|(n, _)| n == name).map(|(_, s)| s.clone())
                    .ok_or_else(|| format!("no size recorded for blob `{}`", name))?;
                let sz: u64 = size_s.parse().map_err(|_| format!(
                    "blob `{}` has a non-constant size `{}`", name, size_s))?;
                let repl = format!("(replicateByte 0 {})", sz);
                sat_atoms.push(format!(".bytes {} {}", a, repl));
                blob_subst.push((name.clone(), repl));
                feet.push(Foot { mem: Some((a, sz)), reg: None, cs: false,
                                 desc: format!("blob `{}` at {}", name, a) });
            }
            Atom::Bytes32 { addr, name } => {
                let a = eval_expr(addr, &env).ok_or_else(|| format!(
                    "cannot evaluate Bytes32 address `{}`", addr.to_lean()))?;
                sat_atoms.push(format!(".bytes32 {} {}", a, name));
                feet.push(Foot { mem: Some((a, 32)), reg: None, cs: false,
                                 desc: format!("`{}` at {}", name, a) });
            }
        }
    }
    if state.saw_call {
        sat_atoms.push(".callStack []".to_string());
        feet.push(Foot { mem: None, reg: None, cs: true,
                         desc: "callStack".to_string() });
    }

    // Rust-side pairwise disjointness (mirrored kernel-side by `satCheck`). Overlap = H8 vacuity; fail.
    for i in 0..feet.len() {
        for j in (i + 1)..feet.len() {
            let (x, y) = (&feet[i], &feet[j]);
            let mem_clash = match (x.mem, y.mem) {
                (Some((s1, n1)), Some((s2, n2))) =>
                    n1 > 0 && n2 > 0 && s1 + n1 > s2 && s2 + n2 > s1,
                _ => false,
            };
            let reg_clash = matches!((x.reg, y.reg), (Some(a), Some(b)) if a == b);
            if mem_clash || reg_clash || (x.cs && y.cs) {
                return Err(format!(
                    "precondition atoms overlap under the witness assignment \
                     ({} vs {}) — the theorem would be vacuous",
                    x.desc, y.desc));
            }
        }
    }

    let mut tokens: Vec<(String, String)> = Vec::new();
    for v in vars {
        tokens.push((v.clone(), env.get(v).copied().unwrap_or(0).to_string()));
    }
    for (p, val) in &param_vals {
        tokens.push((p.clone(), val.to_string()));
    }
    for (n, repl) in &blob_subst {
        tokens.push((n.clone(), repl.clone()));
    }
    let subst = |s: &str| -> String {
        let mut out = s.to_string();
        for (k, v) in &tokens {
            out = replace_token(&out, k, v);
        }
        out
    };

    let mut w = String::new();
    w.push_str(
        "/-! ## Satisfiability witness (soundness-audit H8)\n\n\
         The triple's precondition is SATISFIABLE at the concrete\n\
         assignment below — an overlapping (vacuous) sepConj would fail\n\
         `native_decide` here, so vacuity cannot ship. The guards pin\n\
         each `addrK` literal to its `h_addrK` defining equation at the\n\
         assignment; the witness goal is the theorem's precondition with\n\
         the variables instantiated, so the reflected `SatWitness` atoms\n\
         are tied to the real pre by the elaborator's defeq check.\n\
         Value-level path hypotheses (`h_branch*`) are not certified\n\
         consistent — they are outside the overlap-vacuity class this\n\
         guards against. -/\n\n");
    for (i, (param, _, _)) in abstractions.iter().enumerate() {
        w.push_str(&format!(
            "example : {} = {} := by native_decide\n",
            param_vals[param], subst(&folded_rhs[i])));
    }
    if !abstractions.is_empty() { w.push('\n'); }
    let cs = if state.saw_call { " ** callStackIs []" } else { "" };
    // `have` before `exact`: with an expected `∃ s, interp [..] s` type the unifier postpones
    // list metavariables and gets stuck; `have` elaborates the list closed, then `exact` unifies.
    w.push_str(&format!(
        "open Memory in\nexample : ∃ s,\n    ({}{}) s := by\n  \
         have w := SatWitness.sat_witness\n    [{}]\n    (by native_decide)\n  \
         exact w\n\n",
        subst(&atoms_to_lean(pre, abs_subst)), cs,
        sat_atoms.join(",\n     "),
    ));
    Ok(w)
}

/// Evaluate a branch hypothesis under a concrete assignment, mirroring EXACTLY `BranchHyp::lean_hyp`
/// semantics so `Some(true)` guarantees `native_decide` accepts the substituted hypothesis.
/// `None` = unmodeled kind (signed compares) — those lifts are skipped, never failed.
fn eval_branch(bh: &BranchHyp, env: &std::collections::BTreeMap<String, u64>)
    -> Option<bool> {
    use BranchKind::*;
    let dv = eval_expr(&bh.dst_value, env)?;
    let immu = bh.imm as u64;
    let sv = match &bh.src_value {
        Some(s) => Some(eval_expr(s, env)?),
        None => None,
    };
    let r = match (&bh.kind, bh.taken) {
        (JeqImm, true) | (JneImm, false) => dv == immu,
        (JeqImm, false) | (JneImm, true) => dv != immu,
        (JgtImm, true)  => dv > immu,
        (JgtImm, false) => !(dv > immu),
        (JltImm, true)  => dv < immu,
        (JltImm, false) => !(dv < immu),
        (JleImm, true)  => dv <= immu,
        (JleImm, false) => !(dv <= immu),
        (JgeImm, true)  => dv >= immu,
        (JgeImm, false) => !(dv >= immu),
        (JsetImm, true)  => (dv & immu) != 0,
        (JsetImm, false) => (dv & immu) == 0,
        (JeqReg, true) | (JneReg, false) => dv == sv?,
        (JeqReg, false) | (JneReg, true) => dv != sv?,
        (JltReg, true)  => dv < sv?,
        (JltReg, false) => !(dv < sv?),
        (JgtReg, true)  => dv > sv?,
        (JgtReg, false) => !(dv > sv?),
        (JleReg, true)  => dv <= sv?,
        (JleReg, false) => !(dv <= sv?),
        (JgeReg, true)  => dv >= sv?,
        (JgeReg, false) => !(dv >= sv?),
        (JsetReg, true)  => (dv & sv?) != 0,
        (JsetReg, false) => (dv & sv?) == 0,
        // Signed compares: `toSigned64 v` is two's-complement reinterpretation
        // = `v as i64`, so each Lean `toSigned64 a (op) toSigned64 b` matches
        // the Rust `(a as i64) (op) (b as i64)`.
        (JsgtImm, true)  => (dv as i64) > (immu as i64),
        (JsgtImm, false) => !((dv as i64) > (immu as i64)),
        (JsltImm, true)  => (dv as i64) < (immu as i64),
        (JsltImm, false) => !((dv as i64) < (immu as i64)),
        (JsleImm, true)  => (dv as i64) <= (immu as i64),
        (JsleImm, false) => !((dv as i64) <= (immu as i64)),
        (JsgeImm, true)  => (dv as i64) >= (immu as i64),
        (JsgeImm, false) => !((dv as i64) >= (immu as i64)),
        (JsgtReg, true)  => (dv as i64) > (sv? as i64),
        (JsgtReg, false) => !((dv as i64) > (sv? as i64)),
        (JsltReg, true)  => (dv as i64) < (sv? as i64),
        (JsltReg, false) => !((dv as i64) < (sv? as i64)),
        (JsleReg, true)  => (dv as i64) <= (sv? as i64),
        (JsleReg, false) => !((dv as i64) <= (sv? as i64)),
        (JsgeReg, true)  => (dv as i64) >= (sv? as i64),
        (JsgeReg, false) => !((dv as i64) >= (sv? as i64)),
    };
    Some(r)
}

/// Candidate `(dst_target, src_target?)` pairs that would satisfy the branch under the current
/// partial assignment. Driver tries in order, `solve_expr`-ing free variables, keeps first that
/// `eval_branch`-verifies. Empty = unmodeled kind (signed) => lift is skipped.
fn branch_candidates(bh: &BranchHyp, env: &std::collections::BTreeMap<String, u64>)
    -> Vec<(u64, Option<u64>)> {
    use BranchKind::*;
    let immu = bh.imm as u64;
    let sv = bh.src_value.as_ref().and_then(|s| eval_expr(s, env));
    let dv = eval_expr(&bh.dst_value, env);
    let ne_imm: Vec<(u64, Option<u64>)> =
        [immu.wrapping_add(1), immu.wrapping_sub(1), 0, 1, 2, 3]
            .into_iter().filter(|t| *t != immu).map(|t| (t, None)).collect();
    match (&bh.kind, bh.taken) {
        (JeqImm, true) | (JneImm, false) => vec![(immu, None)],
        (JeqImm, false) | (JneImm, true) => ne_imm,
        (JgtImm, true)  => vec![(immu.wrapping_add(1), None)],
        (JgtImm, false) => vec![(0, None), (immu, None)],
        (JltImm, true)  => if immu > 0 { vec![(0, None), (immu - 1, None)] } else { vec![] },
        (JltImm, false) => vec![(immu, None), (immu.wrapping_add(1), None)],
        (JleImm, true)  => vec![(0, None), (immu, None)],
        (JleImm, false) => vec![(immu.wrapping_add(1), None)],
        (JgeImm, true)  => vec![(immu, None), (immu.wrapping_add(1), None)],
        (JgeImm, false) => if immu > 0 { vec![(0, None), (immu - 1, None)] } else { vec![] },
        (JsetImm, true)  => if immu != 0 { vec![(immu, None)] } else { vec![] },
        (JsetImm, false) => vec![(0, None)],
        // reg-form: couple the two sides.
        (JeqReg, true) | (JneReg, false) => match sv {
            Some(v) => vec![(v, None)],
            None => match dv { Some(v) => vec![(v, Some(v))], None => vec![(0, Some(0))] },
        },
        (JeqReg, false) | (JneReg, true) => match sv {
            Some(v) => vec![(v.wrapping_add(1), None), (v.wrapping_sub(1), None)],
            None => vec![(1, Some(0)), (0, Some(1))],
        },
        (JltReg, true) => match sv {
            Some(v) if v > 0 => vec![(v - 1, None), (0, None)],
            _ => vec![(0, Some(1))],
        },
        (JltReg, false) => match sv {           // dst ≥ src
            Some(v) => vec![(v, None), (v.wrapping_add(1), None)],
            None => vec![(1, Some(0)), (0, Some(0))],
        },
        (JgtReg, true) => match sv {
            Some(v) => vec![(v.wrapping_add(1), None)],
            None => vec![(1, Some(0))],
        },
        (JgtReg, false) => match sv {           // dst ≤ src
            Some(v) => vec![(v, None), (0, None)],
            None => vec![(0, Some(1)), (0, Some(0))],
        },
        (JleReg, true) => match sv {
            Some(v) => vec![(v, None), (0, None)],
            None => vec![(0, Some(0)), (0, Some(1))],
        },
        (JleReg, false) => match sv {           // dst > src
            Some(v) => vec![(v.wrapping_add(1), None)],
            None => vec![(1, Some(0))],
        },
        (JgeReg, true) => match sv {
            Some(v) => vec![(v, None), (v.wrapping_add(1), None)],
            None => vec![(0, Some(0)), (1, Some(0))],
        },
        (JgeReg, false) => match sv {           // dst < src
            Some(v) if v > 0 => vec![(v - 1, None), (0, None)],
            _ => vec![(0, Some(1))],
        },
        (JsetReg, true) => match sv {
            Some(v) if v != 0 => vec![(v, None)],
            _ => vec![(1, Some(1))],
        },
        (JsetReg, false) => vec![(0, None)],
        // Signed compares. For the small non-negative immediates these lifts
        // use (2/6/11/17), the witness values stay in the positive i64 range
        // where signed = unsigned, so the candidate VALUES match the unsigned
        // counterpart; the `256`/`65536` magnitudes let a byte-combo dst be
        // steered into a higher byte when its low byte is already pinned.
        (JsgtImm, true)  => vec![(immu.wrapping_add(1), None), (256, None), (65536, None)],
        (JsgtImm, false) => vec![(0, None), (immu, None)],
        (JsleImm, true)  => vec![(0, None), (immu, None)],
        (JsleImm, false) => vec![(immu.wrapping_add(1), None), (256, None), (65536, None)],
        (JsltImm, true)  => if immu > 0 { vec![(0, None), (immu - 1, None)] } else { vec![] },
        (JsltImm, false) => vec![(immu, None), (immu.wrapping_add(1), None)],
        (JsgeImm, true)  => vec![(immu, None), (immu.wrapping_add(1), None), (256, None)],
        (JsgeImm, false) => if immu > 0 { vec![(0, None), (immu - 1, None)] } else { vec![] },
        (JsgtReg, true) => match sv {
            Some(v) => vec![(v.wrapping_add(1), None)],
            None => vec![(1, Some(0))],
        },
        (JsgtReg, false) => match sv {
            Some(v) => vec![(v, None), (0, None)],
            None => vec![(0, Some(1)), (0, Some(0))],
        },
        (JsltReg, true) => match sv {
            Some(v) if v > 0 => vec![(v - 1, None), (0, None)],
            _ => vec![(0, Some(1))],
        },
        (JsltReg, false) => match sv {
            Some(v) => vec![(v, None), (v.wrapping_add(1), None)],
            None => vec![(1, Some(0)), (0, Some(0))],
        },
        (JsleReg, true) => match sv {
            Some(v) => vec![(v, None), (0, None)],
            None => vec![(0, Some(0)), (0, Some(1))],
        },
        (JsleReg, false) => match sv {
            Some(v) => vec![(v.wrapping_add(1), None)],
            None => vec![(1, Some(0))],
        },
        (JsgeReg, true) => match sv {
            Some(v) => vec![(v, None), (v.wrapping_add(1), None)],
            None => vec![(0, Some(0)), (1, Some(0))],
        },
        (JsgeReg, false) => match sv {
            Some(v) if v > 0 => vec![(v - 1, None), (0, None)],
            _ => vec![(0, Some(1))],
        },
    }
}

fn uf_find(parent: &mut std::collections::BTreeMap<String, String>, x: &str) -> String {
    let mut root = x.to_string();
    while let Some(p) = parent.get(&root) { if *p == root { break; } root = p.clone(); }
    let mut cur = x.to_string();
    while cur != root {
        let next = parent.get(&cur).cloned().unwrap_or_else(|| root.clone());
        parent.insert(cur, root.clone());
        cur = next;
    }
    root
}

fn expr_vars(e: &Expr, out: &mut Vec<String>) {
    match e {
        Expr::InitReg(n) | Expr::InitMem(n) => out.push(n.clone()),
        Expr::ToU64(a) | Expr::Mod(a, _) | Expr::AndU64Imm(a, _)
        | Expr::LshU64Imm(a, _) | Expr::RshU64Imm(a, _) => expr_vars(a, out),
        Expr::WrapAdd(a, b) | Expr::WrapSub(a, b) | Expr::WrapMul(a, b)
        | Expr::NatAdd(a, b) | Expr::CleanSub(a, b) => { expr_vars(a, out); expr_vars(b, out); }
        Expr::ByteCombo(bs) => for b in bs { expr_vars(b, out); },
        Expr::Const(_) | Expr::StHalfImm(_) | Expr::StWordImm(_)
        | Expr::StDwordImm(_) | Expr::Raw(_) => {}
    }
}

/// Steerer priority (0 = most constraining): 0=byte-combo-eq (pins several cells), 1=scalar-eq,
/// 2=inequality (commits a value in range before a disequality can block it), 3=disequality.
fn branch_priority(bh: &BranchHyp) -> u8 {
    use BranchKind::*;
    let combo = matches!(&bh.dst_value, Expr::ByteCombo(_));
    match (&bh.kind, bh.taken) {
        (JeqImm, true) | (JneImm, false) | (JeqReg, true) | (JneReg, false) =>
            if combo { 0 } else { 1 },
        (JeqImm, false) | (JneImm, true) | (JeqReg, false) | (JneReg, true) => 3,
        _ => 2,
    }
}

/// Phase 7 sub-item 1: branch-satisfiability witness (complements the H8 footprint witness).
/// `h_branch*` and `h*_lt` are uncertified parameters — an unsatisfiable conjunction makes the
/// triple vacuously true. Emits a concrete assignment satisfying every modeled hypothesis
/// simultaneously, kernel-checked by `native_decide`. Conservative: returns `None` (non-breaking)
/// when the steerer cannot satisfy every branch — never emits an unverified witness.
fn build_branch_witness(state: &SymState, vars: &[String]) -> Option<String> {
    use std::collections::BTreeMap;
    if state.branch_hyps.is_empty() { return None; }

    let mut env: BTreeMap<String, u64> = BTreeMap::new();
    let mut order: Vec<usize> = (0..state.branch_hyps.len()).collect();
    order.sort_by_key(|&i| branch_priority(&state.branch_hyps[i]));

    for &i in &order {
        let bh = &state.branch_hyps[i];
        // Already satisfied by the partial assignment (e.g. pinned by an earlier branch).
        if eval_branch(bh, &env) == Some(true) { continue; }
        // Non-committing zero-fill probe (disequalities only): if the `≠` holds with free cells=0,
        // leave them free — committing 0 here would block a later `bN ≠ 0` on the same cell.
        // Inequalities are NOT probed: they define a range and must commit a value in range.
        if branch_priority(bh) == 3 {
            let mut bvars = Vec::new();
            expr_vars(&bh.dst_value, &mut bvars);
            if let Some(s) = &bh.src_value { expr_vars(s, &mut bvars); }
            let mut probe = env.clone();
            for v in &bvars { probe.entry(v.clone()).or_insert(0); }
            if eval_branch(bh, &probe) == Some(true) { continue; }
        }
        // Try both solve orders: src-first unlocks compound dst whose free sub-cell = src.
        let cands = branch_candidates(bh, &env);
        'cand: for (dt, st) in cands {
            for src_first in [false, true] {
                let mut trial = env.clone();
                let solve_src = |tr: &mut std::collections::BTreeMap<String, u64>| {
                    match (&bh.src_value, st) {
                        (Some(s), Some(t)) => solve_expr(s, t, tr),
                        _ => true,
                    }
                };
                let ok = if src_first {
                    solve_src(&mut trial) && solve_expr(&bh.dst_value, dt, &mut trial)
                } else {
                    solve_expr(&bh.dst_value, dt, &mut trial) && solve_src(&mut trial)
                };
                if ok && eval_branch(bh, &trial) == Some(true) {
                    env = trial;
                    break 'cand;
                }
            }
        }
        // If not steered (pinned by an earlier shared constraint), the repair pass handles it.
    }

    for v in vars { env.entry(v.clone()).or_insert(0); }

    // Repair pass: the greedy pass mis-handles multi-constraint cells (e.g. `≤2 ∧ ≠2 ∧ ≠0` => must be 1)
    // and reg-equality classes. Union equalities into UF classes, brute-force one shared value per class.
    {
        use std::collections::{BTreeMap, BTreeSet};
        let mut allvars: Vec<String> = Vec::new();
        for bh in &state.branch_hyps {
            expr_vars(&bh.dst_value, &mut allvars);
            if let Some(s) = &bh.src_value { expr_vars(s, &mut allvars); }
        }
        allvars.sort(); allvars.dedup();
        let mut parent: BTreeMap<String, String> = BTreeMap::new();
        for v in &allvars { parent.insert(v.clone(), v.clone()); }
        for bh in &state.branch_hyps {
            let is_eq = matches!((&bh.kind, bh.taken),
                (BranchKind::JeqReg, true) | (BranchKind::JneReg, false));
            if !is_eq { continue; }
            let mut dv = Vec::new(); expr_vars(&bh.dst_value, &mut dv);
            let mut sv = Vec::new();
            if let Some(s) = &bh.src_value { expr_vars(s, &mut sv); }
            if dv.len() == 1 && sv.len() == 1 {
                let ra = uf_find(&mut parent, &dv[0]);
                let rb = uf_find(&mut parent, &sv[0]);
                if ra != rb { parent.insert(ra, rb); }
            }
        }
        let mut classes: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for v in &allvars { let r = uf_find(&mut parent, v); classes.entry(r).or_default().push(v.clone()); }
        let mut pool: Vec<u64> = (0u64..=256).collect();
        for bh in &state.branch_hyps {
            let im = bh.imm as u64;
            pool.push(im); pool.push(im.wrapping_add(1)); pool.push(im.wrapping_sub(1));
        }
        for members in classes.values() {
            let mset: BTreeSet<&String> = members.iter().collect();
            let internal: Vec<usize> = state.branch_hyps.iter().enumerate().filter_map(|(i, bh)| {
                let mut vs = Vec::new();
                expr_vars(&bh.dst_value, &mut vs);
                if let Some(s) = &bh.src_value { expr_vars(s, &mut vs); }
                if !vs.is_empty() && vs.iter().all(|v| mset.contains(v)) { Some(i) } else { None }
            }).collect();
            if internal.is_empty() { continue; }
            let holds = |e: &BTreeMap<String, u64>| internal.iter().all(|&i|
                eval_branch(&state.branch_hyps[i], e) == Some(true));
            if holds(&env) { continue; }
            for &cand in &pool {
                let mut trial = env.clone();
                for m in members { trial.insert(m.clone(), cand); }
                if holds(&trial) { env = trial; break; }
            }
        }
    }

    for (i, bh) in state.branch_hyps.iter().enumerate() {
        if eval_branch(bh, &env) != Some(true) {
            if std::env::var("QEDLIFT_DEBUG_BRANCH").is_ok() {
                eprintln!("BRANCH-WITNESS skip: final verify failed h_branch{} : {}",
                    i, bh.lean_hyp());
            }
            return None;
        }
    }

    let sub = |s: &str| -> String {
        let mut out = s.to_string();
        for (k, val) in &env {
            out = replace_token(&out, k, &val.to_string());
        }
        out
    };
    let mut conjuncts: Vec<String> = Vec::new();
    for bh in &state.branch_hyps {
        conjuncts.push(format!("({})", sub(&bh.lean_hyp())));
    }
    for (v, k) in &state.u64_load_vars {
        let lit = env.get(v).copied().unwrap_or(0);
        conjuncts.push(format!("({} < 2 ^ {})", lit, k));
    }
    let mut w = String::new();
    w.push_str(
        "/-! ## Branch-satisfiability witness (Phase 7 sub-item 1)\n\n\
         The triple's value-level path hypotheses (`h_branch*`) and load\n\
         bounds (`h*_lt`) are uncertified parameters — an UNSATISFIABLE\n\
         conjunction of them would make the triple vacuously true. The\n\
         assignment below satisfies every (modeled) path hypothesis\n\
         SIMULTANEOUSLY; `native_decide` machine-checks it, so a\n\
         contradictory path-constraint set cannot ship silently. This\n\
         complements the H8 footprint witness above (disjoint variable\n\
         sets: address roots vs. discriminant/flag cells). -/\n\n");
    // Split via `refine ⟨?_,…⟩` so each conjunct is decided individually —
    // a single `native_decide` over deeply-nested `And` fails Decidable-synth past ~60 conjuncts.
    let body = conjuncts.join(" ∧\n      ");
    if conjuncts.len() == 1 {
        w.push_str(&format!("example :\n      {} := by native_decide\n\n", body));
    } else {
        let holes = vec!["?_"; conjuncts.len()].join(", ");
        w.push_str(&format!(
            "example :\n      {} := by\n  refine ⟨{}⟩ <;> native_decide\n\n",
            body, holes));
    }
    Some(w)
}

/// The BPF program heap: `[MM_HEAP_START, MM_HEAP_START + 0x8000)`.
const HEAP_START_I: i64 = 0x300000000;
const HEAP_END_I:   i64 = 0x300000000 + 0x8000;

/// If `addr_base` is an `lddw`-loaded constant in `[MM_HEAP_START, MM_HEAP_END)`, return its
/// absolute address — used to fold heap cells into `heapBumpPtr`/`heapBlockU64` predicates.
fn heap_cell_addr(addr_base: &Expr, off: i64) -> Option<i64> {
    let k = match addr_base {
        Expr::Const(k) => *k,
        Expr::ToU64(inner) => match inner.as_ref() {
            Expr::Const(k) => *k,
            _ => return None,
        },
        _ => return None,
    };
    let abs = k.checked_add(off)?;
    if (HEAP_START_I..HEAP_END_I).contains(&abs) { Some(abs) } else { None }
}

/// Render an atom for the heap corollary: the `u64` cell at `MM_HEAP_START` -> `heapBumpPtr v`;
/// any other heap cell -> `heapBlockU64 addr v`; everything else renders normally.
fn atom_to_lean_heap(
    atom: &Atom,
    subst: &std::collections::BTreeMap<String, String>,
) -> String {
    if let Atom::Mem { addr_base, addr_off, width, value, .. } = atom {
        if matches!(width, Width::Dword) {
            if let Some(abs) = heap_cell_addr(addr_base, *addr_off) {
                let v = fold_abstractions(value.to_lean(), subst);
                return if abs == HEAP_START_I {
                    format!("(heapBumpPtr ({}))", v)
                } else {
                    format!("(heapBlockU64 ({}) ({}))", addr_base.atom_lean(), v)
                };
            }
        }
    }
    atom_to_lean_with_subst(atom, subst)
}

fn atoms_to_lean_heap(
    atoms: &[Atom],
    subst: &std::collections::BTreeMap<String, String>,
) -> String {
    atoms.iter()
        .map(|a| atom_to_lean_heap(a, subst))
        .collect::<Vec<_>>()
        .join(" **\n      ")
}

/// Emit lift artifacts for `sol_memset_(r1, r2, r3)` at logical PC `pc`, shaped to
/// `call_sol_memset_spec`. Adds a `↦Bytes` pre-atom at r1 (fresh ByteArray, size r3),
/// records post (region filled with r2%256) and `r0 := 0`. CU is data-dependent (∝r3)
/// so `nCu`/`hCu` are surfaced as hypotheses rather than discharged here.
fn emit_sol_memset(
    state: &mut SymState,
    spec_calls: &mut Vec<SpecCall>,
    block_pcs: &mut Vec<usize>,
    pc: usize,
) {
    let r0v = state.read_reg(0);
    let r1v = state.read_reg(1);
    let r2v = state.read_reg(2);
    let r3v = state.read_reg(3);

    // H6: record writable rr for [r1V, r1V+r3V) so the goal rr matches the `containsWritable`
    // clause that `sl_block_iter` folds in from `call_sol_memset_*_spec`.
    state.rr_walk.push((r1v.clone(), 0, Width::Byte, true,
        Some((r1v.clone(), r3v.clone()))));

    let idx = state.fresh; state.fresh += 1;
    let bs_name  = format!("memsetBs_{}", idx);
    let bs_sz    = format!("hmemsetBs_{}_sz", idx);
    let ncu_name = format!("nCuMemset{}", idx);
    let hcu_name = format!("hCuMemset{}", idx);

    // Pre atom: `r1V ↦Bytes memsetBs_idx`; size = r3V, or prefix length under a pre-split.
    let mut size_rendered = r3v.atom_lean();
    let blob_len = const_of_expr(&r3v).unwrap_or(1).max(1);
    let (root, lo) = canon_addr(&r1v, 0);
    // Register blob for H8 Phase C split planning (a later dword read at the tail triggers a split).
    let fill_const = const_of_expr(&r2v).map(|f| f as u8);
    if const_of_expr(&r3v).is_some() {
        state.blobs.push((root.clone(), lo, blob_len, fill_const));
    }
    let split_n = state.blob_splits.get(&(root.clone(), lo)).copied();
    // PRE-SPLIT: lift already owns a dword at the blob tail (CloseAccount reads lamports BEFORE
    // zeroing). Collect trailing owned dwords at [len-8k, len-8(k-1)) for k=1,2;
    // `tail_cells[0]` = last 8 bytes. Pre-split specs own prefix-blob + those cells.
    let mut tail_cells: Vec<usize> = Vec::new();
    if const_of_expr(&r3v).is_some() && fill_const.is_some() {
        for k in 1..=2i64 {
            if blob_len < 8 * k + 1 { break; }
            let want = lo + blob_len - 8 * k;
            match state.mem.iter().position(|c| {
                matches!(c.width, Width::Dword) && {
                    let (cr, cd) = canon_addr(&c.addr_base, c.addr_off);
                    cr == root && cd + c.delta == want
                }
            }) {
                Some(i) => tail_cells.push(i),
                None => break,
            }
        }
    }
    if !tail_cells.is_empty() {
        size_rendered = format!("{}", blob_len - 8 * tail_cells.len() as i64);
    }
    state.pre.push(Atom::Bytes {
        addr: r1v.clone(),
        value: BytesVal::Sym(bs_name.clone()),
    });
    state.memset_blobs.push((bs_name.clone(), size_rendered));
    state.syscall_cu_vars.push((ncu_name.clone(), hcu_name.clone(), ".sol_memset"));
    state.syscall_pcs.insert(pc, ".sol_memset");

    // Post: r0=0; blob -> `replicateByte (r2V%256) r3V`, or under tail-split: prefix blob +
    // a `↦U64` cell with fill across all 8 lanes (`call_sol_memset_split_u64_spec`).
    state.write_reg(0, Expr::Const(0));
    let have_line = match (tail_cells.len(), split_n, fill_const) {
        (1, _, Some(fill)) => {
            let ci = tail_cells[0];
            let n = blob_len - 8;
            let w: u64 = u64::from_le_bytes([fill; 8]);
            let a_render = SymState::cell_render(&state.mem[ci]);
            let old_v = state.mem[ci].value.atom_lean();
            // Post: cell holds fill across all 8 lanes; blob shrinks to prefix.
            state.mem[ci].value = Expr::Const(w as i64);
            state.note_access(&r1v, 0, n, format!("blob:{}", r1v.to_lean()));
            state.byte_blob_post.insert(
                r1v.to_lean(),
                BytesVal::Replicate { fill: r2v.clone(), count: Expr::Const(n) },
            );
            let ha_name = format!("h_msplit_{}", pc);
            state.side_hyps.push((ha_name.clone(), format!(
                "{} = {} + {}", a_render, r1v.atom_lean(), n)));
            // call_sol_memset_presplit_u64_spec r0Old r1V r2V r3V n w a
            //   oldV pc nCu bsOld hbs hn ha hw0..hw7 hCu
            format!(
                "have h_{pc} := call_sol_memset_presplit_u64_spec {r0} {r1} {r2} {r3} \
{n} {w} ({a}) {oldv} {pc} {ncu} {bs} {hbs} (by decide) {ha} \
(by decide) (by decide) (by decide) (by decide) (by decide) (by decide) \
(by decide) (by decide) {hcu}",
                pc = pc,
                r0 = r0v.atom_lean(), r1 = r1v.atom_lean(),
                r2 = r2v.atom_lean(), r3 = r3v.atom_lean(),
                n = n, w = w, a = a_render, oldv = old_v, ha = ha_name,
                ncu = ncu_name, bs = bs_name, hbs = bs_sz, hcu = hcu_name,
            )
        }
        (2, _, Some(fill)) => {
            // tail_cells[0] = last 8 bytes (a2), [1] = the 8 before (a1).
            let (c2, c1) = (tail_cells[0], tail_cells[1]);
            let n = blob_len - 16;
            let w: u64 = u64::from_le_bytes([fill; 8]);
            let a1_render = SymState::cell_render(&state.mem[c1]);
            let a2_render = SymState::cell_render(&state.mem[c2]);
            let old1 = state.mem[c1].value.atom_lean();
            let old2 = state.mem[c2].value.atom_lean();
            state.mem[c1].value = Expr::Const(w as i64);
            state.mem[c2].value = Expr::Const(w as i64);
            state.note_access(&r1v, 0, n, format!("blob:{}", r1v.to_lean()));
            state.byte_blob_post.insert(
                r1v.to_lean(),
                BytesVal::Replicate { fill: r2v.clone(), count: Expr::Const(n) },
            );
            let ha1_name = format!("h_msplit_{}_a1", pc);
            let ha2_name = format!("h_msplit_{}_a2", pc);
            state.side_hyps.push((ha1_name.clone(), format!(
                "{} = {} + {}", a1_render, r1v.atom_lean(), n)));
            state.side_hyps.push((ha2_name.clone(), format!(
                "{} = {} + {} + 8", a2_render, r1v.atom_lean(), n)));
            // call_sol_memset_presplit_2u64_spec r0Old r1V r2V r3V n w
            //   a1 a2 oldV1 oldV2 pc nCu bsOld hbs hn ha1 ha2 hw0..hw7 hCu
            format!(
                "have h_{pc} := call_sol_memset_presplit_2u64_spec {r0} {r1} {r2} {r3} \
{n} {w} ({a1}) ({a2}) {old1} {old2} {pc} {ncu} {bs} {hbs} (by decide) {ha1} {ha2} \
(by decide) (by decide) (by decide) (by decide) (by decide) (by decide) \
(by decide) (by decide) {hcu}",
                pc = pc,
                r0 = r0v.atom_lean(), r1 = r1v.atom_lean(),
                r2 = r2v.atom_lean(), r3 = r3v.atom_lean(),
                n = n, w = w, a1 = a1_render, a2 = a2_render,
                old1 = old1, old2 = old2, ha1 = ha1_name, ha2 = ha2_name,
                ncu = ncu_name, bs = bs_name, hbs = bs_sz, hcu = hcu_name,
            )
        }
        (0, Some(n), Some(fill)) => {
            // Footprints: shrunk blob + the split cell.
            state.note_access(&r1v, 0, n, format!("blob:{}", r1v.to_lean()));
            state.note_access(&r1v, n, 8, format!("blobtail:{}", r1v.to_lean()));
            state.byte_blob_post.insert(
                r1v.to_lean(),
                BytesVal::Replicate { fill: r2v.clone(), count: Expr::Const(n) },
            );
            // Split `↦U64` cell registered at blob-base; later aliased reads reach it via `h_alias`.
            let w: u64 = u64::from_le_bytes([fill; 8]);
            state.mem.push(MemCell {
                addr_base: r1v.clone(), addr_off: n,
                width: Width::Dword, value: Expr::Const(w as i64), delta: 0,
            });
            // Split-cell address equation, consumer-discharged like h_addr* abstractions.
            let ha_name = format!("h_msplit_{}", pc);
            state.side_hyps.push((ha_name.clone(), format!(
                "effectiveAddr ({}) ({}) = {} + {}",
                r1v.to_lean(), n, r1v.atom_lean(), n)));
            // call_sol_memset_split_u64_spec r0Old r1V r2V r3V n w a pc
            //   nCu bsOld hbs hn ha hw0..hw7 hCu
            format!(
                "have h_{pc} := call_sol_memset_split_u64_spec {r0} {r1} {r2} {r3} \
{n} {w} (effectiveAddr ({r1raw}) ({n})) {pc} {ncu} {bs} {hbs} (by decide) {ha} \
(by decide) (by decide) (by decide) (by decide) (by decide) (by decide) \
(by decide) (by decide) {hcu}",
                pc = pc,
                r0 = r0v.atom_lean(), r1 = r1v.atom_lean(),
                r2 = r2v.atom_lean(), r3 = r3v.atom_lean(),
                n = n, w = w, r1raw = r1v.to_lean(), ha = ha_name,
                ncu = ncu_name, bs = bs_name, hbs = bs_sz, hcu = hcu_name,
            )
        }
        _ => {
            // Blob overlap accounting (symbolic count => 1-byte footprint at base, no split).
            // Catches exact-base collisions; full symbolic-length support is part of H8 byte-aliasing.
            state.note_access(&r1v, 0, blob_len, format!("blob:{}", r1v.to_lean()));
            state.byte_blob_post.insert(
                r1v.to_lean(),
                BytesVal::Replicate { fill: r2v.clone(), count: r3v.clone() },
            );
            // call_sol_memset_spec r0Old r1V r2V r3V pc nCu bsOld hbs hCu
            format!(
                "have h_{pc} := call_sol_memset_spec {r0} {r1} {r2} {r3} {pc} {ncu} {bs} {hbs} {hcu}",
                pc = pc,
                r0 = r0v.atom_lean(), r1 = r1v.atom_lean(),
                r2 = r2v.atom_lean(), r3 = r3v.atom_lean(),
                ncu = ncu_name, bs = bs_name, hbs = bs_sz, hcu = hcu_name,
            )
        }
    };
    spec_calls.push(SpecCall { hyp_name: format!("h_{}", pc), have_line });
    block_pcs.push(pc);
}

/// The 32-byte rent sysvar id (`SysvarRent111…`), mirroring
/// `SysvarData.rentId`.
const RENT_ID_BYTES: [u8; 32] = [
    0x06, 0xa7, 0xd5, 0x17, 0x19, 0x2c, 0x5c, 0x51,
    0x21, 0x8c, 0xc9, 0x4c, 0x3d, 0x4a, 0xf1, 0x7f,
    0x58, 0xda, 0xee, 0x08, 0x9b, 0xa1, 0xfd, 0x44,
    0xe3, 0xdb, 0xd9, 0x8a, 0x00, 0x00, 0x00, 0x00,
];

/// Emit `sol_get_sysvar` (H8 Phase C-2). Only the RENT id at offset 0, length 17 (pinocchio
/// `Rent::get()`) is modeled, shaped to `call_sol_get_sysvar_cells17_spec`. Out region owned as
/// two `↦U64` cells + one `↦ₘ` byte (post: mollusk-default rent 3480/2.0-bits/50); address-bound
/// and disjointness side conditions surfaced as hypotheses.
fn emit_sol_get_sysvar(
    state: &mut SymState,
    spec_calls: &mut Vec<SpecCall>,
    block_pcs: &mut Vec<usize>,
    pc: usize,
    ctx: &BinaryCtx,
) -> Result<(), Box<dyn std::error::Error>> {
    let r0v = state.read_reg(0);
    let r1v = state.read_reg(1);
    let r2v = state.read_reg(2);
    let r3v = state.read_reg(3);
    let r4v = state.read_reg(4);
    let id_addr = const_of_expr(&r1v).ok_or_else(|| format!(
        "get_sysvar at pc {pc}: symbolic sysvar-id address"))? as u64;
    let off = const_of_expr(&r3v).ok_or_else(|| format!(
        "get_sysvar at pc {pc}: symbolic offset"))?;
    let len = const_of_expr(&r4v).ok_or_else(|| format!(
        "get_sysvar at pc {pc}: symbolic length"))?;
    let region = ctx.executable.get_ro_region();
    let rel = id_addr.checked_sub(region.vm_addr)
        .filter(|r| r + 32 <= region.len)
        .ok_or_else(|| format!(
            "get_sysvar at pc {pc}: id address {id_addr:#x} outside the \
             RO region"))?;
    let id_bytes: &[u8] = unsafe {
        std::slice::from_raw_parts((region.host_addr + rel) as *const u8, 32)
    };
    if id_bytes != RENT_ID_BYTES || off != 0 || len != 17 {
        return Err(format!(
            "get_sysvar at pc {pc}: only the RENT id with offset 0 / \
             length 17 is modelled (cells17 shape); got id {:02x?}…, \
             offset {off}, length {len}", &id_bytes[..8]).into());
    }

    let idx = state.fresh; state.fresh += 1;
    let ncu_name = format!("nCuGetSysvar{}", idx);
    let hcu_name = format!("hCuGetSysvar{}", idx);
    state.syscall_cu_vars.push((ncu_name.clone(), hcu_name.clone(), ".sol_get_sysvar"));
    state.syscall_pcs.insert(pc, ".sol_get_sysvar");

    state.pre.push(Atom::Bytes32 {
        addr: r1v.clone(), name: "SysvarData.rentId".to_string(),
    });
    state.note_access(&r1v, 0, 32, format!("sysvarId:{}", r1v.to_lean()));

    let mut cells: Vec<(i64, Width, u32, i64)> = vec![
        (0, Width::Dword, 64, 3480),
        (8, Width::Dword, 64, 4611686018427387904),
        (16, Width::Byte, 8, 50),
    ];
    let mut old_names: Vec<String> = Vec::new();
    for (coff, w, bits, post) in cells.drain(..) {
        let i = state.fresh; state.fresh += 1;
        let name = format!("{}_{}",
            if matches!(w, Width::Dword) { "oldMemD" } else { "oldMemB" }, i);
        state.u64_load_vars.push((name.clone(), bits));
        let v = Expr::InitMem(name.clone());
        state.mem.push(MemCell {
            addr_base: r2v.clone(), addr_off: coff, width: w,
            value: v.clone(), delta: 0,
        });
        state.pre.push(Atom::Mem {
            addr_base: r2v.clone(), addr_off: coff, width: w,
            value: v, delta: 0,
        });
        let wl = if matches!(w, Width::Dword) { 8 } else { 1 };
        state.note_access(&r2v, coff, wl,
            format!("sysvarOut:{}@{}", r2v.to_lean(), coff));
        old_names.push(name);
        let ci = state.mem.len() - 1;
        state.mem[ci].value = Expr::Const(post);
    }
    state.write_reg(0, Expr::Const(0));

    // Side conditions (symbolic out address; consumer discharges by `decide`).
    let out = r2v.to_lean();
    let out_atom = r2v.atom_lean();
    let id_atom = r1v.atom_lean();
    let h_out = format!("h_sysvar_out_{}", pc);
    let h_outlen = format!("h_sysvar_outlen_{}", pc);
    let h_disj = format!("h_sysvar_disj_{}", pc);
    let ha1 = format!("h_sysvar_a1_{}", pc);
    let ha2 = format!("h_sysvar_a2_{}", pc);
    state.side_hyps.push((h_out.clone(),
        format!("{} < Memory.INPUT_START", out_atom)));
    state.side_hyps.push((h_outlen.clone(),
        format!("{} + 17 < U64_MODULUS", out_atom)));
    state.side_hyps.push((h_disj.clone(),
        format!("{} + 32 ≤ {} ∨ {} + 17 ≤ {}",
            id_atom, out_atom, out_atom, id_atom)));
    state.side_hyps.push((ha1.clone(),
        format!("effectiveAddr ({}) (8) = {} + 8", out, out_atom)));
    state.side_hyps.push((ha2.clone(),
        format!("effectiveAddr ({}) (16) = {} + 8 + 8", out, out_atom)));

    // call_sol_get_sysvar_cells17_spec r0Old idA outA offV lenV a1 a2
    //   oldD0 oldD1 oldB w0 w1 wb idBytes buf slice pc nCu
    //   hIdSize hBuf hInRange hOutAddr hOffLen hOutLen hLen hSliceSize
    //   hSlice hsl hwb hob ha1 ha2 h_disj hCu
    let have_line = format!(
        "have h_{pc} := call_sol_get_sysvar_cells17_spec {r0} ({id}) ({out}) 0 17 \
(effectiveAddr ({outraw}) (8)) (effectiveAddr ({outraw}) (16)) \
{o0} {o1} {o2} 3480 4611686018427387904 50 \
SysvarData.rentId SysvarData.rentBuf SysvarData.rentBuf {pc} {ncu} \
rfl SysvarData.sysvarBuffer_rent (by decide) {hout} (by decide) {houtlen} \
rfl rfl (by intro i _; rw [Nat.zero_add]) rfl (by decide) h{o2}_lt \
{ha1} {ha2} {hdisj} {hcu}",
        pc = pc, r0 = r0v.atom_lean(), id = r1v.to_lean(),
        out = out, outraw = out,
        o0 = old_names[0], o1 = old_names[1], o2 = old_names[2],
        ncu = ncu_name, hout = h_out, houtlen = h_outlen,
        ha1 = ha1, ha2 = ha2, hdisj = h_disj, hcu = hcu_name,
    );
    spec_calls.push(SpecCall { hyp_name: format!("h_{}", pc), have_line });
    block_pcs.push(pc);
    Ok(())
}

/// Emit the lift artifacts for an "r0-only" host syscall — one whose
/// model effect is just `r0 := 0` (no memory, no output buffer): e.g.
/// `sol_get_sysvar` (`Misc.execGetSysvar`) and `sol_log_`
/// (`Logging.execLog`). The simplest syscall shape: a single `r0` atom,
/// with the `nCu`/`hCu` CU assumption surfaced as a hypothesis (as for
/// memset). `spec` is the proven `call_<name>_spec` (takes r0Old pc nCu
/// hCu); `ctor` is the `Syscall` constructor; `tag` names the fresh vars.
fn emit_r0_syscall(
    state: &mut SymState,
    spec_calls: &mut Vec<SpecCall>,
    block_pcs: &mut Vec<usize>,
    pc: usize,
    spec: &str,
    ctor: &'static str,
    tag: &str,
) {
    let r0v = state.read_reg(0);
    let idx = state.fresh; state.fresh += 1;
    let ncu_name = format!("nCu{}{}", tag, idx);
    let hcu_name = format!("hCu{}{}", tag, idx);
    state.syscall_cu_vars.push((ncu_name.clone(), hcu_name.clone(), ctor));
    state.syscall_pcs.insert(pc, ctor);
    state.write_reg(0, Expr::Const(0));
    // call_<name>_spec r0Old pc nCu hCu
    let have_line = format!(
        "have h_{pc} := {spec} {r0} {pc} {ncu} {hcu}",
        pc = pc, spec = spec, r0 = r0v.atom_lean(), ncu = ncu_name, hcu = hcu_name,
    );
    spec_calls.push(SpecCall { hyp_name: format!("h_{}", pc), have_line });
    block_pcs.push(pc);
}

/// Emit `sol_log_(r1, r2)` (H6). Unlike `emit_r0_syscall`, `call_sol_log_spec` pins r1/r2 and
/// carries `rr = containsRange r1 r2`, so we read those registers and record the rr clause.
fn emit_sol_log(
    state: &mut SymState,
    spec_calls: &mut Vec<SpecCall>,
    block_pcs: &mut Vec<usize>,
    pc: usize,
) {
    let r0v = state.read_reg(0);
    let r1v = state.read_reg(1);
    let r2v = state.read_reg(2);
    // The logged slice `[r1, r1+r2)` must be in a readable region.
    state.rr_walk.push((r1v.clone(), 0, Width::Byte, false,
        Some((r1v.clone(), r2v.clone()))));
    let idx = state.fresh; state.fresh += 1;
    let ncu_name = format!("nCuLog{}", idx);
    let hcu_name = format!("hCuLog{}", idx);
    state.syscall_cu_vars.push((ncu_name.clone(), hcu_name.clone(), ".sol_log_"));
    state.syscall_pcs.insert(pc, ".sol_log_");
    state.write_reg(0, Expr::Const(0));
    let have_line = format!(
        "have h_{pc} := call_sol_log_spec {r0} {r1} {r2} {pc} {ncu} {hcu}",
        pc = pc, r0 = r0v.atom_lean(), r1 = r1v.atom_lean(), r2 = r2v.atom_lean(),
        ncu = ncu_name, hcu = hcu_name,
    );
    spec_calls.push(SpecCall { hyp_name: format!("h_{}", pc), have_line });
    block_pcs.push(pc);
}

fn post_atoms(initial_pre: &[Atom], state: &SymState) -> Vec<Atom> {
    let mut out = Vec::with_capacity(initial_pre.len());
    for atom in initial_pre {
        match atom {
            Atom::Reg(r, _) => {
                let v = state.regs.get(r).cloned()
                    .unwrap_or_else(|| Expr::InitReg(reg_initial_name(*r)));
                out.push(Atom::Reg(*r, v));
            }
            Atom::Mem { addr_base, addr_off, width, delta, .. } => {
                let key = (addr_base.to_lean(), *addr_off, *delta, *width as u8);
                let v = state.mem.iter()
                    .find(|c| c.key() == key)
                    .map(|c| c.value.clone())
                    .unwrap_or_else(|| Expr::InitMem("?".to_string()));
                out.push(Atom::Mem {
                    addr_base: addr_base.clone(),
                    addr_off:  *addr_off,
                    width:     *width,
                    value:     v,
                    delta:     *delta,
                });
            }
            Atom::Bytes { addr, value } => {
                // Look up post blob contents by rendered address (set by memory syscall emitters).
                let post_val = state.byte_blob_post.get(&addr.to_lean())
                    .cloned()
                    .unwrap_or_else(|| value.clone());
                out.push(Atom::Bytes { addr: addr.clone(), value: post_val });
            }
            Atom::Bytes32 { addr, name } => {
                // Read-only named constant (sysvar id) — unchanged.
                out.push(Atom::Bytes32 { addr: addr.clone(), name: name.clone() });
            }
        }
    }
    out
}

/// Build the `rr` clause: `rt.containsRange`/`containsWritable` per walk-order atom.
fn region_req(
    _pre: &[Atom],
    state: &SymState,
    subst: &std::collections::BTreeMap<String, String>,
) -> String {
    let mut clauses = Vec::new();
    // Walk-order: load -> containsRange, store -> containsWritable; left-fold order matches slBlockIter.
    for (addr_base, addr_off, width, writable, raw) in &state.rr_walk {
        // H6 variable-length: `contains{Writable,Range} addr count` with raw (subst-folded, no
        // `effectiveAddr`) address — matches the rr from `call_sol_{memset,log}_*_spec` after sl_rw_abs.
        if let Some((addr, count)) = raw {
            let addr_str = fold_abstractions(addr.to_lean(), subst);
            let kind = if *writable { "containsWritable" } else { "containsRange" };
            clauses.push(format!(
                "rt.{} ({}) ({}) = true", kind, addr_str, count.to_lean()));
            continue;
        }
        let width_bytes = match width {
            Width::Byte => 1, Width::Halfword => 2, Width::Word => 4, Width::Dword => 8,
        };
        let addr_str = subst.get(&addr_base.to_lean())
            .map(|p| p.clone())
            .unwrap_or_else(|| addr_base.atom_lean());
        let addr = format!("effectiveAddr {} {}", addr_str, lean_off(*addr_off));
        let kind = if *writable { "containsWritable" } else { "containsRange" };
        clauses.push(format!("rt.{} ({}) {} = true", kind, addr, width_bytes));
    }
    if clauses.is_empty() {
        "True".to_string()
    } else {
        // Left-associative `((A ∧ B) ∧ C) ∧ D` — matches sl_block_iter's left-fold shape so the
        // goal is isDefEq to the chain without extra rewrites.
        let mut out = clauses[0].clone();
        for c in clauses.iter().skip(1) {
            out = format!("({}) ∧\n                  {}", out, c);
        }
        out
    }
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

// Per-binary context shared across arms in batch mode: building `Executable` for a large program
// (~80KB p_token) is ~10s, so sharing it keeps batch cost O(arms) not O(arms × binary).
struct BinaryCtx {
    executable:  Executable<NoopCtx>,
    text_offset: u64,
    text_bytes:  Vec<u8>,
    insns:       Vec<ebpf::Insn>,
    /// Slot<->logical PC converter (shared with qedrecover). Jump `off` fields are slot-relative;
    /// our `insns`/CodeReq PCs are logical indices. Mirrors `SVM/SBPF/Decode.lean` pass 1.
    pc_map:      PcMap,
}

/// Resolve a slot-relative jump to its logical target PC, mirroring `Decode.decodeProgram` so the
/// rendered `.jXX target` matches what `native_decide` proves. Falls back to `logical_pc+1+off`
/// for synthetic fixtures (no lddw => slot == logical).
fn resolve_jump_target(ctx: &BinaryCtx, logical_pc: usize, off: i64) -> i64 {
    ctx.pc_map.resolve_jump_target(logical_pc, off)
}

/// The V0 function registry (murmur3 key -> target SLOT) built at load — ground truth that Lean's
/// `Elf.buildFnRegistry` mirrors (audit H2). Sorted by key for deterministic output; slot units
/// match `Decode.decodeInsn`; `entrypoint` (slot 0) included as the Lean side carries it.
fn function_registry(ctx: &BinaryCtx) -> Vec<(u32, usize)> {
    let mut v: Vec<(u32, usize)> = ctx.executable
        .get_function_registry()
        .iter()
        .map(|(key, (_name, slot))| (key, slot))
        .collect();
    v.sort_by_key(|(k, _)| *k);
    v
}

fn function_registry_lean(reg: &[(u32, usize)]) -> String {
    let mut s = String::from("[");
    for (i, (k, slot)) in reg.iter().enumerate() {
        if i > 0 { s.push_str(", "); }
        if i > 0 && i % 4 == 0 { s.push_str("\n  "); }
        s.push_str(&format!("({}, {})", k, slot));
    }
    s.push(']');
    s
}

/// Parse an execution-trace file: one decimal logical PC per line, in
/// execution order. Blank lines and `#`-prefixed comments are skipped.
/// Captured from the Lean runner's `TRACE_STEPS` output (the `STEP
/// pc=<hex>` lines, converted to decimal).
fn load_trace(path: &Path) -> Result<Vec<usize>, Box<dyn std::error::Error>> {
    let text = std::fs::read_to_string(path)?;
    let mut pcs = Vec::new();
    for (lineno, raw) in text.lines().enumerate() {
        let line = raw.trim();
        if line.is_empty() || line.starts_with('#') { continue; }
        let pc: usize = line.parse().map_err(|e| {
            format!("--trace {}: line {}: not a decimal PC ({:?}): {}",
                    path.display(), lineno + 1, line, e)
        })?;
        pcs.push(pc);
    }
    if pcs.is_empty() {
        return Err(format!("--trace {}: no PCs found", path.display()).into());
    }
    Ok(pcs)
}

fn load_binary(so_path: &Path) -> Result<BinaryCtx, Box<dyn std::error::Error>> {
    let bytes = std::fs::read(so_path)?;
    let loader = Arc::new(BuiltinProgram::new_mock());
    let executable: Executable<NoopCtx> = Executable::load(&bytes, loader)?;
    let (text_offset, text_bytes) = {
        let (o, b) = executable.get_text_bytes();
        (o, b.to_vec())
    };
    let mut insns = Vec::new();
    let mut pc = 0;
    while pc * ebpf::INSN_SIZE < text_bytes.len() {
        let mut insn = ebpf::get_insn(&text_bytes, pc);
        let opc  = insn.opc;
        // lddw spans 2 slots; merge the high-half immediate from the next slot to match decodeProgram.
        if opc == ebpf::LD_DW_IMM {
            ebpf::augment_lddw_unchecked(&text_bytes, &mut insn);
        }
        let span = if opc == ebpf::LD_DW_IMM { 2 } else { 1 };
        insns.push(insn);
        pc += span;
    }
    // Shared slot<->logical converter (see `qed_analysis::PcMap`).
    let pc_map = PcMap::from_insns(&insns);
    Ok(BinaryCtx { executable, text_offset, text_bytes, insns, pc_map })
}

// ════════════════════════════════════════════════════════════════
// Refinement codegen — mechanically emit the per-arm `AsmRefines…` obligation theorem.
// Detects mutated cells, classifies codec (token/mint/counter/vault), picks aggregation lemma.
// Returns `(module_name, lean)` or `None` for unregistered arms / unrecognized layouts.
// ════════════════════════════════════════════════════════════════

#[derive(Clone, Copy, PartialEq, Eq)]
enum CodecKind { Token, Mint, Counter, Vault }

struct RefineSpec {
    asm_pred: &'static str,
    /// account roles in `AsmRefines…` argument order.
    accounts: &'static [(&'static str, CodecKind)],
}

fn refine_registry(arm: &str) -> Option<RefineSpec> {
    match arm {
        "Transfer" | "TransferChecked" => Some(RefineSpec {
            asm_pred: "AsmRefinesTokenTransfer",
            accounts: &[("src", CodecKind::Token), ("dst", CodecKind::Token)],
        }),
        "MintTo" => Some(RefineSpec {
            asm_pred: "AsmRefinesTokenMintTo",
            accounts: &[("mint", CodecKind::Mint), ("dest", CodecKind::Token)],
        }),
        "Burn" => Some(RefineSpec {
            asm_pred: "AsmRefinesTokenBurn",
            accounts: &[("account", CodecKind::Token), ("mint", CodecKind::Mint)],
        }),
        // Non-token single-field counter: codec is one u64 (coarse=fine, no aggregation).
        // Constant +1 delta handled by `counterIncrement` clean-up + `emit_counter_refinement`.
        "counterIncrement" => Some(RefineSpec {
            asm_pred: "AsmRefinesCounterIncrement",
            accounts: &[("counter", CodecKind::Counter)],
        }),
        // Multi-field non-token account (IDL-driven). `AsmRefinesFieldUpdate` proved by reshaping
        // via `account_agg` and framing untouched fields — `emit_vault_refinement`.
        "VaultIncrement" => Some(RefineSpec {
            asm_pred: "AsmRefinesFieldUpdate",
            accounts: &[("vault", CodecKind::Vault)],
        }),
        _ => None,
    }
}

/// True for arms with a constant `+1` delta (counter/vault). Gates the delta-cleaning so arms
/// like `two_op`'s `+1` are not mistakenly cleaned.
fn is_const_delta_arm(arm: Option<&str>) -> bool {
    arm.and_then(refine_registry).map_or(false, |s| {
        s.accounts.iter().all(|(_, c)| matches!(c, CodecKind::Counter | CodecKind::Vault))
    })
}

/// Value of a memory cell at `(base_raw, off)` with the given byte-ness,
/// if the lift owns it.
fn cell_val<'a>(atoms: &'a [Atom], base_raw: &str, off: i64, byte: bool) -> Option<&'a Expr> {
    for a in atoms {
        if let Atom::Mem { addr_base, addr_off, width, value, .. } = a {
            if *addr_off == off && matches!(width, Width::Byte) == byte
               && addr_base.to_lean() == base_raw {
                return Some(value);
            }
        }
    }
    None
}

/// A balance/supply cell mutated in the post (`a ± b`, both loaded).
struct MutCell { base: Expr, base_raw: String, off: i64, a: Expr, b: Expr, is_sub: bool }

struct AcctBuild {
    base_arg: String,                  // "(addr5 + 88)" — lemma base argument
    record: String,                    // the codec record literal
    rw_pre: String,                    // aggregation rw call at the pre value
    rw_post: String,                   // aggregation rw call at the post value
    frame: Vec<String>,                // frame atoms
    owned: Vec<(String, i64, bool)>,   // lift cells consumed (excluded from setup)
    params: Vec<String>,               // new Nat params (framed owner o…)
    barrays: Vec<String>,              // new ByteArray params
    hyps: Vec<String>,                 // size + byte-bound hypotheses
    // Token aggregation: (lemma_name, owner_owned, rest_pattern). `None` for mint (hand-written).
    agg: Option<(String, bool, Vec<i64>)>,
    // `codecCoarse base (tokenFields/mintFields …)` atoms for pre and post. The keystone
    // (`tokenAcctBalance_codec`/`mintSupply_codec`) equates the bespoke atom to these, reshaping
    // the `AsmRefinesToken*` obligation to the layout-general `refines_field` corollary.
    field_pre: String,
    field_post: String,
}

fn emit_refinement(
    arm_name:     &str,
    lift_module:  &str,
    pre:          &[Atom],
    post_clean:   &[Atom],
    abs_subst:    &std::collections::BTreeMap<String, String>,
    vars:         &[String],
    n_cu:         usize,
    start_pc:     usize,
    exit_pc:      usize,
    idl:          Option<&serde_json::Value>,
    // qedrecover-emitted layouts; preferred over `idl` for account-codec offsets (#41 loop closure).
    sidecar_layouts: Option<&[AccountLayout]>,
    // Returns `(refine_module, refine_lean, optional (agg_module, agg_lean))`.
) -> Option<(String, String, Option<(String, String)>)> {
    let spec = refine_registry(arm_name)?;

    // Counter codec (single u64, coarse=fine): dedicated path keeps token/mint codegen byte-identical.
    if spec.accounts.iter().all(|(_, c)| matches!(c, CodecKind::Counter)) {
        return emit_counter_refinement(&spec, lift_module, pre, post_clean,
            abs_subst, vars, n_cu, start_pc, exit_pc);
    }

    // Vault codec (IDL layout, multi-field): owns updated u64, frames the rest, reshapes via `account_agg`.
    if spec.accounts.iter().all(|(_, c)| matches!(c, CodecKind::Vault)) {
        return emit_vault_refinement(&spec, lift_module, pre, post_clean,
            abs_subst, vars, n_cu, start_pc, exit_pc, idl, sidecar_layouts);
    }

    let fold = |e: &Expr| fold_abstractions(e.to_lean(), abs_subst);

    // ── Detect mutated account cells (a ± b, both InitMem) ──────────
    let is_initmem = |e: &Expr| matches!(e, Expr::InitMem(_));
    let mut muts: Vec<MutCell> = Vec::new();
    for atom in post_clean {
        if let Atom::Mem { addr_base, addr_off, value, .. } = atom {
            let (a, b, is_sub) = match value {
                Expr::CleanSub(a, b) => ((**a).clone(), (**b).clone(), true),
                Expr::NatAdd(a, b)   => ((**a).clone(), (**b).clone(), false),
                _ => continue,
            };
            if is_initmem(&a) && is_initmem(&b) {
                muts.push(MutCell { base: addr_base.clone(), base_raw: addr_base.to_lean(),
                    off: *addr_off, a, b, is_sub });
            }
        }
    }
    if muts.is_empty() { return None; }
    // The transferred amount `b` is shared across all mutated cells.
    let amount = fold(&muts[0].b);

    // ── Assign each registry account to a mutated cell ─────────────────────────────────────────
    // Token amount cells have a mint dword at off-64; mint supply cells have is_initialized at off+9.
    let is_mint_mut = |m: &MutCell| cell_val(pre, &m.base_raw, m.off + 9, true).is_some();
    let is_tok_mut  = |m: &MutCell| cell_val(pre, &m.base_raw, m.off - 64, false).is_some();
    let mut used = vec![false; muts.len()];
    let mut builds: Vec<AcctBuild> = Vec::new();
    let mut barray_ctr = 0u32;
    let mut framed_owner = false;
    for (role, codec) in spec.accounts {
        // Pick unused mutated cell for this codec; for two token accounts (Transfer), src=sub, dst=add.
        let want_sub = *role == "src" || *role == "account";
        let idx = (0..muts.len()).find(|&i| {
            !used[i] && match codec {
                CodecKind::Token => is_tok_mut(&muts[i])
                    && (spec.accounts.iter().filter(|(_, c)| *c == CodecKind::Token).count() < 2
                        || muts[i].is_sub == want_sub),
                CodecKind::Mint => is_mint_mut(&muts[i]),
                // All-counter / all-vault specs take their early
                // `emit_*_refinement` paths; this loop only runs for
                // token/mint codecs.
                CodecKind::Counter | CodecKind::Vault =>
                    unreachable!("counter/vault codec handled by its own emitter"),
            }
        })?;
        used[idx] = true;
        let m = &muts[idx];
        let field_off = if *codec == CodecKind::Token { 64 } else { 36 };
        let base_off = m.off - field_off;
        let base_expr = fold(&m.base);
        let base_arg = format!("({} + {})", base_expr, base_off);
        let build = match codec {
            CodecKind::Token => build_token(pre, m, &base_expr, base_off, &amount,
                &fold, &mut barray_ctr, &mut framed_owner)?,
            CodecKind::Mint  => build_mint(pre, m, &base_expr, base_off, &amount,
                &fold, &mut barray_ctr)?,
            CodecKind::Counter | CodecKind::Vault =>
                unreachable!("counter/vault codec handled by its own emitter"),
        };
        let _ = base_arg;
        builds.push(build);
    }

    // ── Assemble setup atoms (lift cells not owned by any account) ──
    let owned: std::collections::HashSet<(String, i64, bool)> =
        builds.iter().flat_map(|b| b.owned.iter().cloned()).collect();
    let is_owned = |a: &Atom| match a {
        Atom::Mem { addr_base, addr_off, width, .. } =>
            owned.contains(&(addr_base.to_lean(), *addr_off, matches!(width, Width::Byte))),
        _ => false,
    };
    let setup_pre: Vec<Atom> = pre.iter().filter(|a| !is_owned(a)).cloned().collect();
    let setup_post: Vec<Atom> = post_clean.iter().filter(|a| !is_owned(a)).cloned().collect();

    // ── Render ──────────────────────────────────────────────────────
    let module = format!("{}Refinement", lift_module);
    let lean = render_refinement(&spec, &module, &builds, pre, post_clean,
        &setup_pre, &setup_post, abs_subst, vars, &amount, n_cu, start_pc, exit_pc);

    // Emit aggregation module from detected owned-byte patterns. Token -> `PToken.TransferAggregation`;
    // mint -> `PToken.MintAggregation`. Rest-region start/size from IDL; fallback = SPL token 72/165.
    let (tok_rest_start, tok_size) = resolve_layout(sidecar_layouts, idl, "token")
        .and_then(|l| {
            let amount = l.fields.iter().find(|f| f.name == "amount")?;
            Some((amount.offset as i64 + 8, l.size as i64))
        })
        .unwrap_or((72, 165));

    let uses_mint = spec.accounts.iter().any(|(_, c)| matches!(c, CodecKind::Mint));
    let aggregation = if uses_mint {
        // Mint codec: supply/rest offsets from the IDL mint layout; fallback = SPL defaults.
        let (supply_off, rest_off, mint_size) = resolve_layout(sidecar_layouts, idl, "mint")
            .and_then(|l| {
                let s = l.fields.iter().find(|f| f.name == "supply")?;
                Some((s.offset as i64, s.offset as i64 + 8, l.size as i64))
            })
            .unwrap_or((36, 44, 82));
        let agg_lean = render_mint_agg_module(
            "Examples.PTokenMintAggregation", supply_off, rest_off, mint_size,
            tok_rest_start, tok_size);
        Some(("PToken.MintAggregation".to_string(), agg_lean))
    } else {
        let token_aggs: Vec<(&str, bool, Vec<i64>)> = builds.iter()
            .filter_map(|b| b.agg.as_ref().map(|(n, oo, p)| (n.as_str(), *oo, p.clone())))
            .collect();
        if token_aggs.is_empty() {
            None
        } else {
            let agg_lean = render_token_agg_module(
                "Examples.PTokenTransferAggregation", &token_aggs, tok_rest_start, tok_size);
            Some(("PToken.TransferAggregation".to_string(), agg_lean))
        }
    };
    Some((module, lean, aggregation))
}

/// Build a token-account aggregation (src/dst/dest patterns).
fn build_token(
    pre: &[Atom], m: &MutCell, base_expr: &str, base_off: i64, amount: &str,
    fold: &dyn Fn(&Expr) -> String, barray_ctr: &mut u32, framed_owner: &mut bool,
) -> Option<AcctBuild> {
    let base_arg = format!("({} + {})", base_expr, base_off);
    let mut owned = Vec::new();
    let mut params = Vec::new();
    let mut barrays = Vec::new();
    let mut hyps = Vec::new();
    let mut frame = Vec::new();

    let mut mint = Vec::new();
    for i in 0..4 {
        let off = base_off + 8 * i;
        let v = fold(cell_val(pre, &m.base_raw, off, false)?);
        mint.push(v);
        owned.push((m.base_raw.clone(), off, false));
    }
    let owner_owned = cell_val(pre, &m.base_raw, base_off + 32, false).is_some();
    let owner: Vec<String> = if owner_owned {
        (0..4).map(|i| {
            let off = base_off + 32 + 8 * i;
            owned.push((m.base_raw.clone(), off, false));
            fold(cell_val(pre, &m.base_raw, off, false).unwrap())
        }).collect()
    } else {
        if *framed_owner { return None; } // only one framed-owner account supported
        *framed_owner = true;
        for i in 0..4 {
            params.push(format!("o{}", i));
            frame.push(format!("(effectiveAddr {} {} ↦U64 o{})", base_expr, base_off + 32 + 8 * i, i));
        }
        (0..4).map(|i| format!("o{}", i)).collect()
    };
    let amt_field = fold(&m.a);
    owned.push((m.base_raw.clone(), base_off + 64, false));

    // rest bytes owned in [base+72, base+165).
    let mut rest_bytes: Vec<i64> = Vec::new();
    for a in pre {
        if let Atom::Mem { addr_base, addr_off, width, .. } = a {
            if addr_base.to_lean() == m.base_raw && matches!(width, Width::Byte)
               && *addr_off >= base_off + 72 && *addr_off < base_off + 165 {
                rest_bytes.push(*addr_off - base_off);
            }
        }
    }
    rest_bytes.sort();
    let byte_val = |off: i64| fold(cell_val(pre, &m.base_raw, base_off + off, true).unwrap());
    let g1 = { *barray_ctr += 1; format!("g{}", *barray_ctr) };
    let g2 = { *barray_ctr += 1; format!("g{}", *barray_ctr) };
    barrays.push(g1.clone()); barrays.push(g2.clone());

    let hb = |v: &str| format!("h_{}", v);
    let g1sz = format!("{}sz", g1);
    // (lemma, rest-record, rw_args_tail) — tail is lemma args after base/mint/owner/amount.
    let (lemma, rest, rest_args): (&str, String, String) = match rest_bytes.as_slice() {
        [72, 108, 109] => {
            let (b72, b108, b109) = (byte_val(72), byte_val(108), byte_val(109));
            for o in [72, 108, 109] { owned.push((m.base_raw.clone(), base_off + o, true)); }
            hyps.push(format!("({} : {}.size = 35)", g1sz, g1));
            hyps.push(format!("({} : {} < 256)", hb(&b72), b72));
            hyps.push(format!("({} : {} < 256)", hb(&b108), b108));
            hyps.push(format!("({} : {} < 256)", hb(&b109), b109));
            frame.push(format!("memBytesIs ({} + {}) {}", base_expr, base_off + 73, g1));
            frame.push(format!("memBytesIs ({} + {}) {}", base_expr, base_off + 110, g2));
            ("src_account_eq",
             format!("PartialState.byteBA {} ++ ({} ++ (PartialState.byteBA {} ++ (PartialState.byteBA {} ++ {})))", b72, g1, b108, b109, g2),
             format!("{} {} {} {} {} {} {} {} {}", b72, b108, b109, g1, g2, g1sz, hb(&b72), hb(&b108), hb(&b109)))
        }
        [108] => {
            let b108 = byte_val(108);
            owned.push((m.base_raw.clone(), base_off + 108, true));
            hyps.push(format!("({} : {}.size = 36)", g1sz, g1));
            hyps.push(format!("({} : {} < 256)", hb(&b108), b108));
            frame.push(format!("memBytesIs ({} + {}) {}", base_expr, base_off + 72, g1));
            frame.push(format!("memBytesIs ({} + {}) {}", base_expr, base_off + 109, g2));
            ("dst_account_eq",
             format!("{} ++ (PartialState.byteBA {} ++ {})", g1, b108, g2),
             format!("{} {} {} {} {}", b108, g1, g2, g1sz, hb(&b108)))
        }
        [108, 109] => {
            let (b108, b109) = (byte_val(108), byte_val(109));
            for o in [108, 109] { owned.push((m.base_raw.clone(), base_off + o, true)); }
            hyps.push(format!("({} : {}.size = 36)", g1sz, g1));
            hyps.push(format!("({} : {} < 256)", hb(&b108), b108));
            hyps.push(format!("({} : {} < 256)", hb(&b109), b109));
            frame.push(format!("memBytesIs ({} + {}) {}", base_expr, base_off + 72, g1));
            frame.push(format!("memBytesIs ({} + {}) {}", base_expr, base_off + 110, g2));
            ("dest_account_eq",
             format!("{} ++ (PartialState.byteBA {} ++ (PartialState.byteBA {} ++ {}))", g1, b108, b109, g2),
             format!("{} {} {} {} {} {} {}", b108, b109, g1, g2, g1sz, hb(&b108), hb(&b109)))
        }
        _ => return None,
    };

    let owner_args = owner.join(" ");
    let mint_args = mint.join(" ");
    let record = format!(
        "{{ mint := ⟨{}⟩,\n        owner := ⟨{}⟩, amount := {},\n        rest := {} }}",
        mint.join(", "), owner.join(", "), amt_field, rest);
    let post_amt = if m.is_sub { format!("({} - {})", amt_field, amount) } else { format!("({} + {})", amt_field, amount) };
    let rw_pre = format!("{} {} {} {} {} {}", lemma, base_arg, mint_args, owner_args, amt_field, rest_args);
    let rw_post = format!("{} {} {} {} {} {}", lemma, base_arg, mint_args, owner_args, post_amt, rest_args);
    let agg = Some((lemma.to_string(), owner_owned, rest_bytes.clone()));
    // codecCoarse field list (SPL token layout) — `tokenAcctBalance_codec` keystone target.
    let field_pre = format!(
        "codecCoarse {} (SVM.Solana.tokenFields ⟨{}⟩ ⟨{}⟩ {} ({}))",
        base_arg, mint.join(", "), owner.join(", "), amt_field, rest);
    let field_post = format!(
        "codecCoarse {} (SVM.Solana.tokenFields ⟨{}⟩ ⟨{}⟩ {} ({}))",
        base_arg, mint.join(", "), owner.join(", "), post_amt, rest);
    Some(AcctBuild { base_arg, record, rw_pre, rw_post, frame, owned, params, barrays, hyps, agg,
        field_pre, field_post })
}

// -----------------------------------------------------------------------------
// Account-aggregation codegen: emits `*_account_eq` lemmas from the IDL layout
// + owned-byte pattern via `rest_segments` (generic, not lift-var-specific).
// -----------------------------------------------------------------------------

enum RestSeg { Byte(i64), Gap { off: i64, len: i64 } }

/// Segment `[start, end)` by sorted owned byte offsets: owned → `Byte`, spans → `Gap`.
fn rest_segments(owned: &[i64], start: i64, end: i64) -> Vec<RestSeg> {
    let mut segs = Vec::new();
    let mut cur = start;
    for &b in owned {
        if b > cur { segs.push(RestSeg::Gap { off: cur, len: b - cur }); }
        segs.push(RestSeg::Byte(b));
        cur = b + 1;
    }
    if cur < end { segs.push(RestSeg::Gap { off: cur, len: end - cur }); }
    segs
}

/// Emit one `tokenAcctBalanceOf` aggregation lemma for an account owning `owned` rest-bytes.
/// `owner_owned`: lift read the owner (else framed via `o0..o3`). `gap_ctr`: cross-lemma numbering.
fn render_token_agg_lemma(
    name: &str, owner_owned: bool, owned: &[i64], rest_start: i64, size: i64,
    gap_ctr: &mut u32,
) -> String {
    let segs = rest_segments(owned, rest_start, size);
    let mut gap_name: Vec<(usize, String)> = Vec::new(); // (seg idx, gN)
    for (i, s) in segs.iter().enumerate() {
        if let RestSeg::Gap { .. } = s {
            *gap_ctr += 1;
            gap_name.push((i, format!("g{}", gap_ctr)));
        }
    }
    let gname = |idx: usize| gap_name.iter().find(|(i, _)| *i == idx).unwrap().1.clone();
    let byte_offs: Vec<i64> = segs.iter().filter_map(|s|
        if let RestSeg::Byte(o) = s { Some(*o) } else { None }).collect();

    let byte_vars: Vec<String> = byte_offs.iter().map(|o| format!("b{}", o)).collect();
    let gap_vars: Vec<String> = gap_name.iter().map(|(_, g)| g.clone()).collect();
    let nat_params = {
        let mut p = vec!["base".to_string(), "c0".into(), "c1".into(), "c2".into(), "c3".into(),
            "o0".into(), "o1".into(), "o2".into(), "o3".into(), "amount".into()];
        p.extend(byte_vars.clone());
        p.join(" ")
    };
    // Hyps: non-last gaps need a size hyp; each owned byte needs `< 256`.
    let last = segs.len().saturating_sub(1);
    let mut hyps: Vec<String> = Vec::new();
    let mut size_hyps: Vec<String> = Vec::new();
    for (i, s) in segs.iter().enumerate() {
        if let RestSeg::Gap { len, .. } = s {
            if i != last {
                let g = gname(i);
                hyps.push(format!("(h{} : {}.size = {})", g, g, len));
                size_hyps.push(format!("h{}", g));
            }
        }
    }
    for o in &byte_offs { hyps.push(format!("(h{} : b{} < 256)", o, o)); }

    let term = |s: &RestSeg, i: usize| match s {
        RestSeg::Byte(o)  => format!("PartialState.byteBA b{}", o),
        RestSeg::Gap { .. } => gname(i),
    };
    let chain = {
        let parts: Vec<String> = segs.iter().enumerate().map(|(i, s)| term(s, i)).collect();
        let mut acc = parts.last().cloned().unwrap_or_else(|| "ByteArray.empty".into());
        for p in parts.iter().rev().skip(1) {
            // Parenthesise only a compound tail; an atomic tail stays bare.
            acc = if acc.contains(" ++ ") { format!("{} ++ ({})", p, acc) }
                  else { format!("{} ++ {}", p, acc) };
        }
        acc
    };
    let fine: Vec<String> = segs.iter().enumerate().map(|(i, s)| match s {
        RestSeg::Byte(o)        => format!("memByteIs (base + {}) b{}", o, o),
        RestSeg::Gap { off, .. } => format!("memBytesIs (base + {}) {}", off, gname(i)),
    }).collect();
    let seg_list: Vec<String> = segs.iter().enumerate().map(|(i, s)| match s {
        RestSeg::Byte(o)  => format!(".byte b{}", o),
        RestSeg::Gap { .. } => format!(".gap {}", gname(i)),
    }).collect();
    let mut bounds: Vec<String> = segs.iter().map(|s| match s {
        RestSeg::Byte(o)  => format!("h{}", o),
        RestSeg::Gap { .. } => "trivial".to_string(),
    }).collect();
    bounds.push("trivial".to_string()); // nil case
    let simp_sizes = if size_hyps.is_empty() { String::new() }
        else { format!("{}, ", size_hyps.join(", ")) };

    let _ = owner_owned; // owner is always spelled via o0..o3 params either way
    format!(
"theorem {name}
    ({nat_params} : Nat)
    ({gaps} : ByteArray){hyps} :
    tokenAcctBalanceOf base
      {{ mint := ⟨c0, c1, c2, c3⟩, owner := ⟨o0, o1, o2, o3⟩, amount := amount,
        rest := {chain} }}
      = ( pubkeyIs base ⟨c0, c1, c2, c3⟩ **
          pubkeyIs (base + 32) ⟨o0, o1, o2, o3⟩ **
          memU64Is (base + 64) amount **
          ( {fine} ) ) := by
  funext h
  apply propext
  simp only [tokenAcctBalanceOf, tokenAcctBalance, MINT_OFF, OWNER_OFF, AMOUNT_OFF,
    REST_OFF, Nat.add_zero]
  refine sepConj_iff_congr_right _ ?_ h; intro h
  refine sepConj_iff_congr_right _ ?_ h; intro h
  refine sepConj_iff_congr_right _ ?_ h; intro h
  have key := memBytesIs_segs (base + {rest_start})
    [{seg_list}]
    ⟨{bounds}⟩ h
  simp only [segsBytes, segsSL, FieldSeg.bytes, FieldSeg.sl, FieldSeg.size,
    {simp_sizes}ba_append_empty, sepConj_emp_right_eq, Nat.add_assoc, Nat.reduceAdd] at key
  exact key",
        name = name, nat_params = nat_params, gaps = gap_vars.join(" "),
        hyps = if hyps.is_empty() { String::new() } else { format!(" {}", hyps.join(" ")) },
        chain = chain, fine = fine.join(" **\n            "),
        rest_start = rest_start, seg_list = seg_list.join(", "),
        bounds = bounds.join(", "), simp_sizes = simp_sizes,
    )
}

/// Emit the token-aggregation module. `accounts` = `(lemma_name, owner_owned, owned_bytes)`.
fn render_token_agg_module(
    ns: &str, accounts: &[(&str, bool, Vec<i64>)], rest_start: i64, size: i64,
) -> String {
    let mut gap_ctr = 0u32;
    let lemmas: Vec<String> = accounts.iter()
        .map(|(name, owner_owned, owned)|
            render_token_agg_lemma(name, *owner_owned, owned, rest_start, size, &mut gap_ctr))
        .collect();
    format!(
"/-
  Account-codec aggregation for token-account lifts.
  MECHANICALLY EMITTED by qedlift from the IDL account layout + the lift's
  owned-byte pattern (general `rest_segments`; the proof is a fixed
  `memBytesIs_segs` instance). Do not edit by hand.
-/

import SVM.SBPF.SegAggregation
import SVM.SBPF.PubkeySL
import SVM.Solana.TokenAccountCodec

namespace {ns}

open SVM.SBPF SVM.Solana

{lemmas}

end {ns}
",
        ns = ns, lemmas = lemmas.join("\n\n"))
}

/// Emit the mint-aggregation module (`mint_account_eq` full preAuth, `mint_supply_eq` opaque
/// preAuth, `dest_account_eq` token). SPL `COption<Pubkey>` at [0,36), supply at `supply_off`.
fn render_mint_agg_module(
    ns: &str, supply_off: i64, rest_off: i64, mint_size: i64,
    tok_rest_start: i64, tok_size: i64,
) -> String {
    let b1 = rest_off + 1;          // is_initialized byte offset
    let b2 = rest_off + 2;          // freeze-authority gap start
    let _ = mint_size;
    let rest_proof = format!(
"  have key := memBytesIs_segs (base + {rest_off})
    [.gap gD, .byte b45, .gap gF] ⟨trivial, hb45, trivial, trivial⟩ h
  simp only [segsBytes, segsSL, FieldSeg.bytes, FieldSeg.sl, FieldSeg.size,
    hgD, ba_append_empty, sepConj_emp_right_eq, Nat.add_assoc, Nat.reduceAdd] at key
  exact key", rest_off = rest_off);

    let mint_account_eq = format!(
"theorem mint_account_eq
    (base b0 p0 p1 p2 p3 supply b45 : Nat) (gA gD gF : ByteArray)
    (hgA : gA.size = 3) (hgD : gD.size = 1) (hb0 : b0 < 256) (hb45 : b45 < 256) :
    mintSupplyOf base
      {{ preAuth := PartialState.byteBA b0 ++ (gA ++
          (PartialState.u64LE p0 ++ (PartialState.u64LE p1 ++
            (PartialState.u64LE p2 ++ PartialState.u64LE p3)))),
        supply := supply,
        rest := gD ++ (PartialState.byteBA b45 ++ gF) }}
      = ( ( memByteIs base b0 ** memBytesIs (base + 1) gA **
            memU64Is (base + 4) p0 ** memU64Is (base + 12) p1 **
            memU64Is (base + 20) p2 ** memU64Is (base + 28) p3 ) **
          memU64Is (base + {supply_off}) supply **
          ( memBytesIs (base + {rest_off}) gD ** memByteIs (base + {b1}) b45 **
            memBytesIs (base + {b2}) gF ) ) := by
  funext h
  apply propext
  simp only [mintSupplyOf, mintAcctSupply, MINT_AUTH_OFF, SUPPLY_OFF,
    MINT_REST_OFF, Nat.add_zero]
  have keyP : ∀ h, memBytesIs base
      (PartialState.byteBA b0 ++ (gA ++ (PartialState.u64LE p0 ++
        (PartialState.u64LE p1 ++ (PartialState.u64LE p2 ++ PartialState.u64LE p3))))) h ↔
      ( memByteIs base b0 ** memBytesIs (base + 1) gA ** memU64Is (base + 4) p0 **
        memU64Is (base + 12) p1 ** memU64Is (base + 20) p2 ** memU64Is (base + 28) p3 ) h := by
    intro h
    have key := memBytesIs_segs base
      [.byte b0, .gap gA, .u64 p0, .u64 p1, .u64 p2, .u64 p3]
      ⟨hb0, trivial, trivial, trivial, trivial, trivial, trivial⟩ h
    simp only [segsBytes, segsSL, FieldSeg.bytes, FieldSeg.sl, FieldSeg.size,
      hgA, ba_append_empty, sepConj_emp_right_eq, Nat.add_assoc, Nat.reduceAdd] at key
    exact key
  refine Iff.trans (sepConj_iff_congr_left _ keyP h) ?_
  refine sepConj_iff_congr_right _ ?_ h; intro h
  refine sepConj_iff_congr_right _ ?_ h; intro h
{rest_proof}",
        supply_off = supply_off, rest_off = rest_off, b1 = b1, b2 = b2,
        rest_proof = rest_proof);

    let mint_supply_eq = format!(
"theorem mint_supply_eq
    (base supply b45 : Nat) (preAuth gD gF : ByteArray)
    (hgD : gD.size = 1) (hb45 : b45 < 256) :
    mintSupplyOf base
      {{ preAuth := preAuth, supply := supply,
        rest := gD ++ (PartialState.byteBA b45 ++ gF) }}
      = ( memBytesIs base preAuth **
          memU64Is (base + {supply_off}) supply **
          ( memBytesIs (base + {rest_off}) gD ** memByteIs (base + {b1}) b45 **
            memBytesIs (base + {b2}) gF ) ) := by
  funext h
  apply propext
  simp only [mintSupplyOf, mintAcctSupply, MINT_AUTH_OFF, SUPPLY_OFF,
    MINT_REST_OFF, Nat.add_zero]
  refine sepConj_iff_congr_right _ ?_ h; intro h
  refine sepConj_iff_congr_right _ ?_ h; intro h
{rest_proof}",
        supply_off = supply_off, rest_off = rest_off, b1 = b1, b2 = b2,
        rest_proof = rest_proof);

    let mut gap_ctr = 0u32;
    let dest = render_token_agg_lemma(
        "dest_account_eq", false, &[108, 109], tok_rest_start, tok_size, &mut gap_ctr);
    format!(
"/-
  Account-codec aggregation for mint-account lifts (MintTo / Burn).
  MECHANICALLY EMITTED by qedlift from the IDL mint+token layouts + the
  lift's owned-byte pattern. Do not edit by hand.
-/

import SVM.SBPF.SegAggregation
import SVM.SBPF.PubkeySL
import SVM.Solana.MintAccountCodec
import SVM.Solana.TokenAccountCodec

namespace {ns}

open SVM.SBPF SVM.Solana

{mint_account_eq}

{mint_supply_eq}

{dest}

end {ns}
",
        ns = ns, mint_account_eq = mint_account_eq, mint_supply_eq = mint_supply_eq, dest = dest)
}

/// Write the emitted aggregation module to `examples/lean/<module>.lean`. Returns a log label.
fn write_aggregation(agg: &Option<(String, String)>) -> std::io::Result<&'static str> {
    if let Some((module, lean)) = agg {
        let path = format!("examples/lean/{}.lean", module.replace('.', "/"));
        if let Some(parent) = std::path::Path::new(&path).parent() {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::write(&path, lean)?;
        Ok(" (+agg)")
    } else {
        Ok("")
    }
}

/// Build a mint-account aggregation (full preAuth or supply-only).
fn build_mint(
    pre: &[Atom], m: &MutCell, base_expr: &str, base_off: i64, amount: &str,
    fold: &dyn Fn(&Expr) -> String, barray_ctr: &mut u32,
) -> Option<AcctBuild> {
    let base_arg = format!("({} + {})", base_expr, base_off);
    let mut owned = Vec::new();
    let mut barrays = Vec::new();
    let mut hyps = Vec::new();
    let mut frame = Vec::new();

    let supply = fold(&m.a);
    owned.push((m.base_raw.clone(), base_off + 36, false));
    let b45 = fold(cell_val(pre, &m.base_raw, base_off + 45, true)?);
    owned.push((m.base_raw.clone(), base_off + 45, true));
    hyps.push(format!("(h_{} : {} < 256)", b45, b45));

    let g_rest = { *barray_ctr += 1; format!("g{}", *barray_ctr) }; // gD (1B)
    let g_free = { *barray_ctr += 1; format!("g{}", *barray_ctr) }; // gF (36B)
    barrays.push(g_rest.clone()); barrays.push(g_free.clone());
    hyps.push(format!("({}sz : {}.size = 1)", g_rest, g_rest));
    frame.push(format!("memBytesIs ({} + {}) {}", base_expr, base_off + 44, g_rest));
    frame.push(format!("memBytesIs ({} + {}) {}", base_expr, base_off + 46, g_free));
    let rest = format!("{} ++ (PartialState.byteBA {} ++ {})", g_rest, b45, g_free);

    let preauth_owned = cell_val(pre, &m.base_raw, base_off + 4, false).is_some();
    let (lemma, preauth, pre_args): (&str, String, String) = if preauth_owned {
        let b0 = fold(cell_val(pre, &m.base_raw, base_off, true)?);
        owned.push((m.base_raw.clone(), base_off, true));
        hyps.insert(0, format!("(h_{} : {} < 256)", b0, b0));
        let mut ps = Vec::new();
        for i in 0..4 {
            let off = base_off + 4 + 8 * i;
            ps.push(fold(cell_val(pre, &m.base_raw, off, false)?));
            owned.push((m.base_raw.clone(), off, false));
        }
        let g_a = { *barray_ctr += 1; format!("g{}", *barray_ctr) }; // gA (3B)
        barrays.insert(0, g_a.clone());
        hyps.insert(0, format!("({}sz : {}.size = 3)", g_a, g_a));
        frame.insert(0, format!("memBytesIs ({} + {}) {}", base_expr, base_off + 1, g_a));
        ("mint_account_eq",
         format!("PartialState.byteBA {} ++ ({} ++ (PartialState.u64LE {} ++ (PartialState.u64LE {} ++ (PartialState.u64LE {} ++ PartialState.u64LE {}))))",
            b0, g_a, ps[0], ps[1], ps[2], ps[3]),
         format!("{} {} {} {} {} {}", b0, ps[0], ps[1], ps[2], ps[3], format!("{}", b45)))
    } else {
        let pa = { *barray_ctr += 1; format!("preAuth{}", *barray_ctr) };
        barrays.insert(0, pa.clone());
        frame.insert(0, format!("memBytesIs ({} + {}) {}", base_expr, base_off, pa));
        ("mint_supply_eq", pa.clone(), format!("{}", b45))
    };

    let record = format!(
        "{{ preAuth := {},\n        supply := {},\n        rest := {} }}",
        preauth, supply, rest);
    let post_sup = if m.is_sub { format!("({} - {})", supply, amount) } else { format!("({} + {})", supply, amount) };
    let rw_pre = mint_rw(lemma, &base_arg, &preauth, &pre_args, &supply, &b45, &barrays, preauth_owned);
    let rw_post = mint_rw(lemma, &base_arg, &preauth, &pre_args, &post_sup, &b45, &barrays, preauth_owned);
    // Discharge-route field list (SPL mint: mint_authority@0, supply@36,
    // tail@44) — the `mintSupply_codec` keystone target.
    let field_pre = format!(
        "codecCoarse {} (SVM.Solana.mintFields ({}) {} ({}))",
        base_arg, preauth, supply, rest);
    let field_post = format!(
        "codecCoarse {} (SVM.Solana.mintFields ({}) {} ({}))",
        base_arg, preauth, post_sup, rest);
    Some(AcctBuild { base_arg, record, rw_pre, rw_post, frame, owned, params: Vec::new(), barrays, hyps, agg: None,
        field_pre, field_post })
}

fn mint_rw(lemma: &str, base_arg: &str, preauth: &str, pre_args: &str,
           supply: &str, b45: &str, barrays: &[String], preauth_owned: bool) -> String {
    if preauth_owned {
        // mint_account_eq base b0 p0 p1 p2 p3 supply b45 gA gD gF gAsz gDsz h_b0 h_b45
        let g_a = &barrays[0]; let g_d = &barrays[1]; let g_f = &barrays[2];
        let parts: Vec<&str> = pre_args.split_whitespace().collect(); // [b0, p0, p1, p2, p3, b45]
        format!("{} {} {} {} {} {} {} {} {} {} {} {} {} {} h_{} h_{}",
            lemma, base_arg, parts[0], parts[1], parts[2], parts[3], parts[4],
            supply, b45, g_a, g_d, g_f,
            format!("{}sz", g_a), format!("{}sz", g_d), parts[0], b45)
    } else {
        // mint_supply_eq base supply b45 preAuth gD gF gDsz h_b45
        let g_d = &barrays[1]; let g_f = &barrays[2];
        format!("{} {} {} {} {} {} {} {} h_{}",
            lemma, base_arg, supply, b45, preauth, g_d, g_f,
            format!("{}sz", g_d), b45)
    }
}

#[allow(clippy::too_many_arguments)]
fn render_refinement(
    spec: &RefineSpec, module: &str, builds: &[AcctBuild],
    pre: &[Atom], post_clean: &[Atom], setup_pre: &[Atom], setup_post: &[Atom],
    abs_subst: &std::collections::BTreeMap<String, String>, vars: &[String], amount: &str,
    n_cu: usize, start_pc: usize, exit_pc: usize,
) -> String {
    let mut nat_params = vars.join(" ");
    for b in builds { for p in &b.params { nat_params.push(' '); nat_params.push_str(p); } }
    let mut barrays: Vec<String> = Vec::new();
    let mut hyps: Vec<String> = Vec::new();
    for b in builds { barrays.extend(b.barrays.iter().cloned()); hyps.extend(b.hyps.iter().cloned()); }

    // AsmRefines arg order: pred cr nCu 0 entry exit rr <addrs> <records> amount setupPre setupPost
    let addr_args: Vec<String> = builds.iter().map(|b| b.base_arg.clone()).collect();
    let record_args: Vec<String> = builds.iter().map(|b| format!("\n      {}", b.record)).collect();

    let mut rw: Vec<String> = Vec::new();
    for b in builds { rw.push(b.rw_pre.clone()); }
    for b in builds { rw.push(b.rw_post.clone()); }

    let frame_atoms: Vec<String> = builds.iter().flat_map(|b| b.frame.iter().cloned()).collect();
    let frame = frame_atoms.join(" **\n      ");

    let uses_mint_codec = builds.iter().any(|b| b.field_pre.contains("mintFields"));
    let mut imports = vec![
        "import SVM.SBPF.Tactic.SL".to_string(),
        "import SVM.Solana.Abstract.Refinement".to_string(),
        "import SVM.Solana.TokenFieldCodec".to_string(),
        format!("import Generated.{}TracedLifted", strip_refinement(module)),
    ];
    if uses_mint_codec { imports.push("import SVM.Solana.MintFieldCodec".to_string()); }
    let uses_transfer_agg = builds.iter().any(|b|
        b.rw_pre.starts_with("src_account_eq") || b.rw_pre.starts_with("dst_account_eq"));
    let uses_mint_agg = builds.iter().any(|b|
        b.rw_pre.starts_with("mint_account_eq") || b.rw_pre.starts_with("mint_supply_eq")
        || b.rw_pre.starts_with("dest_account_eq"));
    if uses_transfer_agg { imports.push("import PToken.TransferAggregation".to_string()); }
    if uses_mint_agg { imports.push("import PToken.MintAggregation".to_string()); }

    // Field-list atoms for the `refines_field` corollary; order matches obligation's account order.
    let field_pre_join = builds.iter().map(|b| b.field_pre.clone())
        .collect::<Vec<_>>().join(" **\n      ");
    let field_post_join = builds.iter().map(|b| b.field_post.clone())
        .collect::<Vec<_>>().join(" **\n      ");
    // Simp set: token keystone always; mint keystone only when a mint account is present (#MintFieldCodec guard).
    let mut reshape_simp = vec![
        "SVM.Solana.tokenAcctBalanceOf_eq", "SVM.Solana.tokenAcctBalanceOf_withAmount",
        "SVM.Solana.tokenAcctBalance_codec",
    ];
    if uses_mint_codec {
        reshape_simp.extend([
            "SVM.Solana.mintSupplyOf_eq", "SVM.Solana.mintSupplyOf_withSupply",
            "SVM.Solana.mintSupply_codec",
        ]);
    }
    let reshape_simp = reshape_simp.join(", ");

    let mut opens = Vec::new();
    if uses_transfer_agg { opens.push("Examples.PTokenTransferAggregation"); }
    if uses_mint_agg { opens.push("Examples.PTokenMintAggregation"); }

    let barray_sig = if barrays.is_empty() { String::new() }
        else { format!("\n    ({} : ByteArray)", barrays.join(" ")) };
    let hyp_sig = if hyps.is_empty() { String::new() }
        else { format!("\n    {}", hyps.join("\n    ")) };

    let lift_pre = atoms_to_lean(pre, abs_subst);
    let lift_post = atoms_to_lean(post_clean, abs_subst);
    let setup_pre_s = atoms_to_lean(setup_pre, abs_subst);
    let setup_post_s = atoms_to_lean(setup_post, abs_subst);

    format!(
"/-
  {arm} asm-refines-intrinsic theorem. MECHANICALLY EMITTED by qedlift's
  refinement codegen from the lift's atoms + the IDL arm name. Wires the
  trace-guided lift to `{pred}` via the codec-aggregation lemmas +
  `cuTripleWithinMem_frame_right` + `sl_exact`.
-/

{imports}

namespace Examples.{module}
open SVM SVM.SBPF SVM.SBPF.Memory
{opens}

set_option maxHeartbeats 800000 in
theorem refines_asm
    (cr : CodeReq) (rr : Memory.RegionTable → Prop)
    ({nat_params} : Nat){barray_sig}{hyp_sig}
    (lift : cuTripleWithinMem {n} 0 {entry} {exit} cr
      ({lift_pre})
      ({lift_post}) rr) :
    SVM.Solana.Abstract.{pred} cr {n} 0 {entry} {exit} rr {addrs}{records}
      {amount}
      ({setup_pre})
      ({setup_post}) := by
  unfold SVM.Solana.Abstract.{pred}
  simp only [SVM.Solana.Abstract.Mint.withSupply, SVM.Solana.Abstract.TokenAccount.withAmount]
  rw [{rw}]
  simp only [pubkeyIs]
  have framed := cuTripleWithinMem_frame_right
    ( {frame} )
    (by sl_pcfree) lift
  simp only [Nat.add_assoc, Nat.reduceAdd]
  sl_exact framed

/-- Discharge-route reshape: the `{pred}` obligation is a layout-general
    field-list (`codecCoarse`/`tokenFields`/`mintFields`) obligation. The
    convergence keystones (`tokenAcctBalance_codec` / `mintSupply_codec`)
    rewrite the bespoke `tokenAcctBalanceOf` / `mintSupplyOf` atoms to the
    field-list codec, so qedgen reads the mutated field off the decoded list
    via the library `*_ensures_*` facts (`qedsvm_discharge`). Pairs with
    `refines_asm` (the lift realises the obligation). -/
theorem refines_field
    (cr : CodeReq) (rr : Memory.RegionTable → Prop)
    ({nat_params} : Nat){barray_sig}
    (h : SVM.Solana.Abstract.{pred} cr {n} 0 {entry} {exit} rr {addrs}{records}
      {amount}
      ({setup_pre})
      ({setup_post})) :
    cuTripleWithinMem {n} 0 {entry} {exit} cr
      (({setup_pre}) **
      {field_pre})
      (({setup_post}) **
      {field_post})
      rr := by
  unfold SVM.Solana.Abstract.{pred} at h
  simpa only [{reshape_simp}] using h

end Examples.{module}
",
        arm = spec.asm_pred, pred = spec.asm_pred, module = module,
        imports = imports.join("\n"),
        opens = if opens.is_empty() { String::new() } else { format!("open {}", opens.join(" ")) },
        nat_params = nat_params, barray_sig = barray_sig, hyp_sig = hyp_sig,
        n = n_cu, entry = start_pc, exit = exit_pc,
        lift_pre = lift_pre, lift_post = lift_post,
        addrs = addr_args.join(" "), records = record_args.join(""),
        amount = amount,
        setup_pre = setup_pre_s, setup_post = setup_post_s,
        rw = rw.join(",\n      "), frame = frame,
        field_pre = field_pre_join, field_post = field_post_join,
        reshape_simp = reshape_simp,
    )
}

/// Emit a counter-codec refinement: single owned `u64` cell, constant +1 delta.
/// No aggregation (coarse = fine for `u64`), no frame, no `amount` arg.
fn emit_counter_refinement(
    spec: &RefineSpec, lift_module: &str,
    pre: &[Atom], post_clean: &[Atom],
    abs_subst: &std::collections::BTreeMap<String, String>, vars: &[String],
    n_cu: usize, start_pc: usize, exit_pc: usize,
) -> Option<(String, String, Option<(String, String)>)> {
    let fold = |e: &Expr| fold_abstractions(e.to_lean(), abs_subst);

    // Find the post-state incremented `u64` cell (NatAdd(InitMem, Const) form).
    let mut found: Option<(Expr, i64, Expr, i64)> = None;
    for atom in post_clean {
        if let Atom::Mem { addr_base, addr_off, width, value, .. } = atom {
            if matches!(width, Width::Dword) {
                if let Expr::NatAdd(a, b) = value {
                    if let (Expr::InitMem(_), Expr::Const(k)) = (a.as_ref(), b.as_ref()) {
                        found = Some(((*addr_base).clone(), *addr_off, (**a).clone(), *k));
                        break;
                    }
                }
            }
        }
    }
    let (base, off, pre_val, delta) = found?;
    let base_l = fold(&base);
    let addr_arg = if off == 0 { base_l.clone() } else { format!("({} + {})", base_l, off) };
    let counter_pre = fold(&pre_val);
    let record = format!("{{ counter := {} }}", counter_pre);

    // Owned `u64` cell flows through the codec's fine form; everything else stays in setup.
    let owned_base = base.to_lean();
    let is_owned = |a: &Atom| match a {
        Atom::Mem { addr_base, addr_off, width, .. } =>
            addr_base.to_lean() == owned_base && *addr_off == off
                && matches!(width, Width::Dword),
        _ => false,
    };
    let setup_pre: Vec<Atom> = pre.iter().filter(|a| !is_owned(a)).cloned().collect();
    let setup_post: Vec<Atom> = post_clean.iter().filter(|a| !is_owned(a)).cloned().collect();

    let module = format!("{}Refinement", lift_module);
    let lean = render_counter_refinement(spec, &module, &addr_arg, &record,
        pre, post_clean, &setup_pre, &setup_post, abs_subst, vars, n_cu, start_pc, exit_pc,
        &counter_pre, delta);
    Some((module, lean, None))
}

/// Render the counter refinement theorem. Proof: `unfold` + `simp [counterValOf]` + `sl_exact`.
fn render_counter_refinement(
    spec: &RefineSpec, module: &str, addr_arg: &str, record: &str,
    pre: &[Atom], post_clean: &[Atom], setup_pre: &[Atom], setup_post: &[Atom],
    abs_subst: &std::collections::BTreeMap<String, String>, vars: &[String],
    n_cu: usize, start_pc: usize, exit_pc: usize,
    counter_pre: &str, delta: i64,
) -> String {
    let nat_params = vars.join(" ");
    let lift_pre = atoms_to_lean(pre, abs_subst);
    let lift_post = atoms_to_lean(post_clean, abs_subst);
    let setup_pre_s = atoms_to_lean(setup_pre, abs_subst);
    let setup_post_s = atoms_to_lean(setup_post, abs_subst);

    format!(
"/-
  {pred} asm-refines-intrinsic theorem. MECHANICALLY EMITTED by qedlift's
  refinement codegen — the first NON-token refinement. The counter
  account is a single `u64` field (coarse = fine, no codec aggregation),
  so the proof is `unfold` + `simp [counterValOf]` + `sl_exact` with no
  aggregation rewrite and no frame.
-/

import SVM.SBPF.Tactic.SL
import SVM.SBPF.Tactic.Discharge
import SVM.Solana.Abstract.Refinement
import Generated.{lift}TracedLifted

namespace Examples.{module}
open SVM SVM.SBPF SVM.SBPF.Memory

set_option maxHeartbeats 800000 in
theorem refines_asm
    (cr : CodeReq) (rr : Memory.RegionTable → Prop)
    ({nat_params} : Nat)
    (lift : cuTripleWithinMem {n} 0 {entry} {exit} cr
      ({lift_pre})
      ({lift_post}) rr) :
    SVM.Solana.Abstract.{pred} cr {n} 0 {entry} {exit} rr {addr}
      {record}
      ({setup_pre})
      ({setup_post}) := by
  unfold SVM.Solana.Abstract.{pred}
  simp only [SVM.Solana.counterValOf_eq]
  sl_exact lift

/-- qedgen `ensures`-shape, mechanically discharged: the counter field
    shifts by {delta}. Pairs with `refines_asm`; the counter account is a
    single-`u64` field list, so the accessor projection is `u64FieldAt 0`. -/
theorem ensures ({counter_pre} : Nat) :
    u64FieldAt 0 [(0, .u64 ({counter_pre} + {delta}))]
      = u64FieldAt 0 [(0, .u64 {counter_pre})] + {delta} := by
  qedsvm_discharge

end Examples.{module}
",
        pred = spec.asm_pred,
        lift = strip_refinement(module),
        module = module,
        nat_params = nat_params,
        counter_pre = counter_pre, delta = delta,
        n = n_cu, entry = start_pc, exit = exit_pc,
        lift_pre = lift_pre, lift_post = lift_post,
        addr = addr_arg, record = record,
        setup_pre = setup_pre_s, setup_post = setup_post_s,
    )
}

/// Emit a vault (`AsmRefinesFieldUpdate`) refinement: owns the updated `u64`, frames the rest,
/// reshapes via `codecCoarse_eq_fine`. IDL-driven — new programs cost only a qedspec.
fn emit_vault_refinement(
    spec: &RefineSpec, lift_module: &str,
    pre: &[Atom], post_clean: &[Atom],
    abs_subst: &std::collections::BTreeMap<String, String>, vars: &[String],
    n_cu: usize, start_pc: usize, exit_pc: usize,
    idl: Option<&serde_json::Value>,
    sidecar_layouts: Option<&[AccountLayout]>,
) -> Option<(String, String, Option<(String, String)>)> {
    let fold = |e: &Expr| fold_abstractions(e.to_lean(), abs_subst);
    let layout = resolve_layout(sidecar_layouts, idl, "vault")?;

    let mut updated: Option<(Expr, i64, Expr, i64)> = None; // base, off, pre_val, delta (NatAdd(InitMem, Const))
    for atom in post_clean {
        if let Atom::Mem { addr_base, addr_off, width, value, .. } = atom {
            if matches!(width, Width::Dword) {
                if let Expr::NatAdd(a, b) = value {
                    if let (Expr::InitMem(_), Expr::Const(k)) = (a.as_ref(), b.as_ref()) {
                        updated = Some(((*addr_base).clone(), *addr_off, (**a).clone(), *k));
                        break;
                    }
                }
            }
        }
    }
    let (base, upd_off, upd_pre, delta) = updated?;
    let base_l = fold(&base);
    let upd_pre_l = fold(&upd_pre);

    // Walk IDL layout: own the updated `u64`, frame every other field.
    let mut fresh = 0u32;
    let mut params: Vec<String> = Vec::new();
    let mut ba_params: Vec<String> = Vec::new();
    let mut pre_fields: Vec<String> = Vec::new();
    let mut post_fields: Vec<String> = Vec::new();
    let mut frame: Vec<String> = Vec::new();
    // Owned blob bytes (SPLIT blob): excluded from `setup`, need `< 256` hyps for codecValid.
    let mut owned_blob_offs: Vec<i64> = Vec::new();
    // `< 256` hyps for split blob's owned bytes; `omega` discharges after codecValid simp.
    let mut byte_hyps: Vec<String> = Vec::new();
    // Gap-size hyps `(name, "g.size = len")`: pin offsets so fine atoms land at lift's addresses.
    let mut gap_size_hyps: Vec<(String, String)> = Vec::new();
    let base_raw_blob = base.to_lean();
    let mut updated_seen = false;
    for f in &layout.fields {
        let off = f.offset as i64;
        match &f.kind {
            FieldKind::U64 if off == upd_off => {
                updated_seen = true;
                pre_fields.push(format!("({}, .u64 {})", off, upd_pre_l));
                post_fields.push(format!("({}, .u64 ({} + {}))", off, upd_pre_l, delta));
            }
            FieldKind::Pubkey => {
                let limbs: Vec<String> = (0..4).map(|_| {
                    let p = format!("o{}", fresh); fresh += 1; params.push(p.clone()); p
                }).collect();
                let rec = format!("⟨{}⟩", limbs.join(", "));
                pre_fields.push(format!("({}, .pubkey {})", off, rec));
                post_fields.push(format!("({}, .pubkey {})", off, rec));
                for (i, limb) in limbs.iter().enumerate() {
                    frame.push(format!("(effectiveAddr {} {} ↦U64 {})", base_l, off + 8 * i as i64, limb));
                }
            }
            FieldKind::U64 => {
                let p = format!("fu{}", fresh); fresh += 1; params.push(p.clone());
                pre_fields.push(format!("({}, .u64 {})", off, p));
                post_fields.push(format!("({}, .u64 {})", off, p));
                frame.push(format!("(effectiveAddr {} {} ↦U64 {})", base_l, off, p));
            }
            FieldKind::Byte => {
                let p = format!("fb{}", fresh); fresh += 1; params.push(p.clone());
                pre_fields.push(format!("({}, .byte {})", off, p));
                post_fields.push(format!("({}, .byte {})", off, p));
                frame.push(format!("(effectiveAddr {} {} ↦ₘ {})", base_l, off, p));
            }
            // Blob field: frame as opaque `↦Bytes` gap unless the lift owns bytes inside it (SPLIT path below).
            FieldKind::Bytes(len) => {
                let len = *len as i64;
                // SPLIT if the lift owns bytes inside [off, off+len); else whole field is one opaque gap.
                let owned: Vec<(i64, String)> = (0..len).filter_map(|rel| {
                    cell_val(pre, &base_raw_blob, off + rel, true)
                        .map(|v| (rel, fold(v)))
                }).collect();
                if owned.is_empty() {
                    let g = format!("fg{}", fresh); fresh += 1; ba_params.push(g.clone());
                    pre_fields.push(format!("({}, .blob [.gap {}])", off, g));
                    post_fields.push(format!("({}, .blob [.gap {}])", off, g));
                    frame.push(format!("(effectiveAddr {} {} ↦Bytes {})", base_l, off, g));
                } else {
                    let mut segs: Vec<String> = Vec::new();
                    let mut cursor = 0i64;
                    for (rel, val) in &owned {
                        if *rel > cursor {
                            // Gap before owned byte: pin size (`fg.size = len`) so segsSL places the byte at `base + rel`.
                            let g = format!("fg{}", fresh); fresh += 1; ba_params.push(g.clone());
                            gap_size_hyps.push((format!("h{}_sz", g), format!("{}.size = {}", g, rel - cursor)));
                            segs.push(format!(".gap {}", g));
                            frame.push(format!("(effectiveAddr {} {} ↦Bytes {})", base_l, off + cursor, g));
                        }
                        // Owned byte: NOT framed; fine `.byte` atom matches directly. Needs `< 256` hyp.
                        segs.push(format!(".byte ({})", val));
                        owned_blob_offs.push(off + rel);
                        byte_hyps.push(format!("(h_blob{} : {} < 256)", off + rel, val));
                        cursor = rel + 1;
                    }
                    if cursor < len {
                        // Trailing gap (last seg): no size hyp needed — free ByteArray.
                        let g = format!("fg{}", fresh); fresh += 1; ba_params.push(g.clone());
                        segs.push(format!(".gap {}", g));
                        frame.push(format!("(effectiveAddr {} {} ↦Bytes {})", base_l, off + cursor, g));
                    }
                    let seglist = format!("[{}]", segs.join(", "));
                    pre_fields.push(format!("({}, .blob {})", off, seglist));
                    post_fields.push(format!("({}, .blob {})", off, seglist));
                }
            }
        }
    }
    if !updated_seen { return None; }

    // setup: lift atoms that don't own codec cells (updated u64 + split blob bytes flow through fine form).
    let owned_base = base.to_lean();
    let is_owned = |a: &Atom| match a {
        Atom::Mem { addr_base, addr_off, width, .. } =>
            addr_base.to_lean() == owned_base
                && ((*addr_off == upd_off && matches!(width, Width::Dword))
                    || (matches!(width, Width::Byte) && owned_blob_offs.contains(addr_off))),
        _ => false,
    };
    let setup_pre: Vec<Atom> = pre.iter().filter(|a| !is_owned(a)).cloned().collect();
    let setup_post: Vec<Atom> = post_clean.iter().filter(|a| !is_owned(a)).cloned().collect();

    let module = format!("{}Refinement", lift_module);
    let lean = render_vault_refinement(spec, &module, &base_l, &pre_fields, &post_fields,
        &frame, &params, &ba_params, pre, post_clean, &setup_pre, &setup_post,
        abs_subst, vars, n_cu, start_pc, exit_pc, upd_off, delta, &upd_pre_l,
        &byte_hyps, &gap_size_hyps);
    Some((module, lean, None))
}

/// Render the vault refinement. Proof: `codecCoarse_eq_fine` reshape → simp fine atoms → `sl_exact`.
fn render_vault_refinement(
    spec: &RefineSpec, module: &str, base_l: &str,
    pre_fields: &[String], post_fields: &[String], frame: &[String], params: &[String],
    ba_params: &[String],
    pre: &[Atom], post_clean: &[Atom], setup_pre: &[Atom], setup_post: &[Atom],
    abs_subst: &std::collections::BTreeMap<String, String>, vars: &[String],
    n_cu: usize, start_pc: usize, exit_pc: usize,
    upd_off: i64, delta: i64, upd_pre_l: &str, byte_hyps: &[String],
    gap_size_hyps: &[(String, String)],
) -> String {
    let mut nat_params = vars.join(" ");
    for p in params { nat_params.push(' '); nat_params.push_str(p); }
    // `ensures` corollary binders: only params that appear in the field lists (no unused binders).
    let mut ens_nat = upd_pre_l.to_string();
    for p in params { ens_nat.push(' '); ens_nat.push_str(p); }
    let mut ensures_binders = format!("({ens_nat} : Nat)");
    if !ba_params.is_empty() {
        ensures_binders.push_str(&format!("\n    ({} : ByteArray)", ba_params.join(" ")));
    }
    // ByteArray group only when a blob field is present; keeps non-blob output byte-identical.
    let mut binders = format!("({nat_params} : Nat)");
    if !ba_params.is_empty() {
        binders.push_str(&format!("\n    ({} : ByteArray)", ba_params.join(" ")));
    }
    for h in byte_hyps { binders.push_str(&format!("\n    {}", h)); }
    for (name, prop) in gap_size_hyps { binders.push_str(&format!("\n    ({} : {})", name, prop)); }
    // Simp sets: conditioned on field kinds present to avoid `unusedSimpArgs` and keep non-blob output stable.
    let has_pubkey = pre_fields.iter().any(|f| f.contains(".pubkey"));
    let has_blob = !ba_params.is_empty();
    let mut fine: Vec<String> = vec!["codecFine".into(), "FieldVal.fine".into()];
    if has_pubkey { fine.push("pubkeyIs".into()); }
    if has_blob { fine.push("segsSL".into()); fine.push("FieldSeg.sl".into()); }
    // SPLIT blob: add `FieldSeg.size` + gap-size hyps so running offsets reduce to concrete addresses.
    if !gap_size_hyps.is_empty() {
        fine.push("FieldSeg.size".into());
        for (name, _) in gap_size_hyps { fine.push(name.clone()); }
    }
    fine.push("sepConj_emp_right_eq".into());
    fine.push("Nat.add_zero".into());
    let fine_simp = fine.join(", ");
    let mut valid = vec!["codecValid", "FieldVal.fineValid"];
    if has_blob { valid.push("segsValid"); valid.push("FieldSeg.valid"); }
    let valid_simp = valid.join(", ");
    // SPLIT blob: `(v % 256) < 256` residual after codecValid simp → `omega`; whole-gap closes in simp alone.
    let valid_tac = if byte_hyps.is_empty() {
        format!("by simp [{valid_simp}]")
    } else {
        format!("by simp [{valid_simp}] <;> omega")
    };
    let pre_list = pre_fields.join(", ");
    let post_list = post_fields.join(", ");
    let frame_s = frame.join(" **\n      ");
    let lift_pre = atoms_to_lean(pre, abs_subst);
    let lift_post = atoms_to_lean(post_clean, abs_subst);
    let setup_pre_s = atoms_to_lean(setup_pre, abs_subst);
    let setup_post_s = atoms_to_lean(setup_post, abs_subst);

    format!(
"/-
  {pred} asm-refines theorem for a multi-field NON-token account.
  MECHANICALLY EMITTED by qedlift from the Codama IDL account layout +
  the lift's atoms. The lift owns the updated `u64` field; the account
  codec is reshaped coarse→fine via the layout-general `account_agg`
  (`codecCoarse_eq_fine`) and the untouched fields are framed.
-/

import SVM.SBPF.Tactic.SL
import SVM.SBPF.Tactic.Discharge
import SVM.Solana.Abstract.Refinement
import Generated.{lift}TracedLifted

namespace Examples.{module}
open SVM SVM.SBPF SVM.SBPF.Memory

set_option maxHeartbeats 800000 in
theorem refines_asm
    (cr : CodeReq) (rr : Memory.RegionTable → Prop)
    {binders}
    (lift : cuTripleWithinMem {n} 0 {entry} {exit} cr
      ({lift_pre})
      ({lift_post}) rr) :
    SVM.Solana.Abstract.{pred} cr {n} 0 {entry} {exit} rr {base}
      [{pre_list}]
      [{post_list}]
      ({setup_pre})
      ({setup_post}) := by
  unfold SVM.Solana.Abstract.{pred}
  rw [codecCoarse_eq_fine {base}
        [{pre_list}]
        ({valid_tac}),
      codecCoarse_eq_fine {base}
        [{post_list}]
        ({valid_tac})]
  simp only [{fine_simp}]
  have framed := cuTripleWithinMem_frame_right
    ( {frame} )
    (by sl_pcfree) lift
  sl_exact framed

/-- qedgen `ensures`-shape, mechanically discharged: the mutated `u64`
    field (offset {upd_off}) shifts by {delta}. Pairs with `refines_asm`
    (which says the bytecode realises this field-list transition); together
    they discharge qedgen's `accessor post = accessor pre ± k` over the
    decoded field list via the layout-general accessor projection. -/
theorem ensures
    {ensures_binders} :
    u64FieldAt {upd_off} [{post_list}]
      = u64FieldAt {upd_off} [{pre_list}] + {delta} := by
  qedsvm_discharge

end Examples.{module}
",
        pred = spec.asm_pred,
        lift = strip_refinement(module),
        module = module,
        binders = binders,
        ensures_binders = ensures_binders,
        upd_off = upd_off, delta = delta,
        valid_tac = valid_tac,
        fine_simp = fine_simp,
        n = n_cu, entry = start_pc, exit = exit_pc,
        lift_pre = lift_pre, lift_post = lift_post,
        base = base_l,
        pre_list = pre_list, post_list = post_list,
        setup_pre = setup_pre_s, setup_post = setup_post_s,
        frame = frame_s,
    )
}

/// "PTokenMintToRefinement" → "PTokenMintTo".
fn strip_refinement(module: &str) -> String {
    module.strip_suffix("Refinement").unwrap_or(module).to_string()
}

/// Lift without a qedrecover layout sidecar (tests, batch, single-arm `--idl`): refinement
/// codegen resolves account layouts from the IDL only. `--qedmeta` runs call
/// `lift_one_with_layouts` directly so the sidecar's `[[account_layout]]` is the layout source.
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
        trace, arm_name, idl, arm_entry, None)
}

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
    const DECODE_BRIDGE_MAX_BYTES: usize = 4096;
    let emit_decode_bridge = text_bytes.len() <= DECODE_BRIDGE_MAX_BYTES;

    let mut out = String::new();
    let decode_claim = if emit_decode_bridge {
        "1. The .text bytes are embedded verbatim as a `ByteArray`.\n\
         2. `Decode.decodeProgram` recovers the instruction sequence;\n\
            `native_decide` proves the decode is correct.\n"
    } else {
        "1. The .text bytes are embedded as a hex string\n\
            (`Decode.bytesOfHex`; a `ByteArray` literal this large\n\
            blows `maxRecDepth`).\n\
         2. The full `decodeProgram` bridge is omitted; instead the\n\
            `_decode_pins` theorem pins the decode of every walked\n\
            PC's bytes by `native_decide`, threading the V0 function\n\
            registry so internal `call_local` PCs resolve (audit H2).\n"
    };
    out.push_str(&format!(
        "/-\n  Generated by `qedlift` from `{}`.\n\
         \n\
         End-to-end lift demonstration:\n\
         {}\
         3. A `cuTripleWithinMem` Hoare triple is stated over the\n\
            decoded sequence. The pre/post atom synthesis is the next\n\
            iteration's work (the \"symbolic executor\" piece); for the\n\
            demo, see the worked example in\n\
            `SVM/SBPF/Macros.lean` (`{}_macro_spec_auto`) where the\n\
            theorem is proved by `sl_block_auto` against the same\n\
            instruction sequence.\n\
         -/\n\n",
        so_path.display(), decode_claim, so_stem,
    ));
    out.push_str("import SVM.SBPF.Decode\n");
    out.push_str("import SVM.SBPF.RunnerBridge\n");
    out.push_str("import SVM.SBPF.Macros\n");
    // The satisfiability-witness section (H8) applies `SatWitness.sat_witness`.
    out.push_str("import SVM.SBPF.SatWitness\n\n");
    // call_local + exit_pops chains blow past default heartbeats during slBlockIter isDefEq.
    out.push_str("set_option maxRecDepth 65536\n");
    // Hot regions leave Horner byte-combos; their defeq needs a larger budget — patched post-walk via @@HEARTBEATS@@.
    out.push_str("set_option maxHeartbeats @@HEARTBEATS@@\n\n");
    out.push_str(&format!("namespace Examples.Lifted.{}\n\n", module_name));

    out.push_str("open SVM.SBPF\n\n");

    if emit_decode_bridge {
        out.push_str("/-- `.text` bytes extracted from the .so by qedlift. -/\n");
        out.push_str(&format!("def {}Bytes : ByteArray := ⟨#[\n", module_name));
        for (i, byte) in text_bytes.iter().enumerate() {
            if i % 8 == 0 { out.push_str("  "); }
            out.push_str(&format!("0x{:02x}", byte));
            if i + 1 < text_bytes.len() { out.push_str(", "); }
            if i % 8 == 7 || i + 1 == text_bytes.len() { out.push('\n'); }
        }
        out.push_str("]⟩\n\n");
        out.push_str(&format!("/-- Text section file-offset: 0x{:x}. -/\n", text_offset));
        out.push_str(&format!("def {}TextOffset : Nat := 0x{:x}\n\n", module_name, text_offset));
    } else {
        out.push_str(&format!(
            "-- NOTE: `{}Bytes` + `{}Insns` + `{}_decodes` omitted — the .text\n\
             -- is {} bytes, which blows `maxRecDepth` as a ByteArray literal.\n\
             -- The byte→insn link is pinned instead by `{}_decode_pins` below:\n\
             -- the `.text` is embedded as a hex string (`{}Text`) and every\n\
             -- walked PC's decode is checked by `native_decide` against the\n\
             -- exact instruction the Hoare triple's `CodeReq` claims there\n\
             -- (soundness-audit H8).\n\n",
            module_name, module_name, module_name, text_bytes.len(),
            module_name, module_name,
        ));
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
        out.push_str(&format!(
            "-- NOTE: `{}Insns` + `{}_decodes` omitted — `.text` contains an\n\
             -- opcode the renderer doesn't model yet ({}). The Hoare\n\
             -- triple below is unaffected: its `CodeReq` references only\n\
             -- the walked-arm PCs, not the full `.text`.\n\n",
            module_name, module_name, reason,
        ));
    } else {
        out.push_str("/-- Decoded form of the .text bytes. -/\n");
        out.push_str(&format!("def {}Insns : Array Insn := #[\n", module_name));
        for (i, lean) in rendered_insns.iter().enumerate() {
            let sep = if i + 1 < rendered_insns.len() { "," } else { "" };
            out.push_str(&format!("  {}{}\n", lean, sep));
        }
        out.push_str("]\n\n");
        // H2: registry resolves call murmur3 imm → .call_local; empty registry fail-closes to .unknown.
        let reg = function_registry(ctx);
        out.push_str(&format!(
            "/-- The V0 function registry (murmur3 key → target slot) \
             solana-sbpf built\n    at load, mirroring `Elf.buildFnRegistry` \
             (audit H2). Resolves internal\n    `call` immediates to \
             `.call_local` targets. -/\n"));
        out.push_str(&format!(
            "def {}FnRegistry : List (Nat × Nat) := {}\n\n",
            module_name, function_registry_lean(&reg)));
        out.push_str("/-- The bytes decode exactly to the expected instruction array. -/\n");
        out.push_str(&format!(
            "theorem {}_decodes :\n    \
             Decode.decodeProgram {}Bytes {}FnRegistry = some {}Insns := by\n  \
             native_decide\n\n",
            module_name, module_name, module_name, module_name,
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
                             sol_memset_ / sol_get_sysvar / sol_log_ / \
                             sol_invoke_signed{{,_c}} are modelled so far. This arm \
                             needs a syscall-effect spec for that hash.",
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

        out.push_str(&format!(
            "/-- The `.text` bytes of the binary, embedded as hex \
             (whitespace-insensitive;\n    see `Decode.bytesOfHex`). \
             {} bytes. -/\n",
            text_bytes.len()));
        out.push_str(&format!(
            "def {}Text : ByteArray := Decode.bytesOfHex \"\n", module_name));
        for chunk in text_bytes.chunks(64) {
            let line: String = chunk.iter().map(|b| format!("{:02x}", b)).collect();
            out.push_str(&format!("  {}\n", line));
        }
        out.push_str("  \"\n\n");
        out.push_str(&format!(
            "/-- Byte-slot → logical-PC map for `{}Text` (pass 1 of the \
             decoder),\n    computed in-kernel — jump-target resolution \
             in the pins below depends on\n    the `lddw` positions of \
             the WHOLE text, not just the pinned windows. -/\n",
            module_name));
        out.push_str(&format!(
            "def {}SlotMap : Array Nat := Decode.buildSlotMap {}Text\n\n",
            module_name, module_name));

        // H2: registry resolves call imms to .call_local targets in the pins below.
        let reg = function_registry(ctx);
        out.push_str(&format!(
            "/-- The V0 function registry (murmur3 key → target slot) \
             solana-sbpf built\n    at load, mirroring `Elf.buildFnRegistry` \
             (audit H2). Resolves internal\n    `call` immediates in the \
             pins below to `.call_local` targets. -/\n"));
        out.push_str(&format!(
            "def {}FnRegistry : List (Nat × Nat) := {}\n\n",
            module_name, function_registry_lean(&reg)));
        out.push_str(&format!(
            "/-- Walked-PC decode pins (soundness-audit H8 + H2): every \
             instruction the\n    Hoare triple's `CodeReq` claims at a \
             walked PC is the decode of the\n    `.text` bytes at that \
             PC's byte offset, checked end-to-end in-kernel\n    \
             (`bytesOfHex` → `buildSlotMap` → `decodeInsn` with the \
             function registry) by\n    `native_decide`. Internal \
             `call_local` PCs are included — their murmur3\n    imm \
             resolves through `{}FnRegistry`. -/\n",
            module_name));
        out.push_str(&format!("theorem {}_decode_pins :\n    ([", module_name));
        for (i, off) in pin_offs.iter().enumerate() {
            if i > 0 {
                out.push_str(", ");
                if i % 16 == 0 { out.push_str("\n      "); }
            }
            out.push_str(off);
        }
        out.push_str(&format!(
            "].map fun off =>\n      Decode.decodeInsn {}Text {}SlotMap off \
             {}FnRegistry) = [\n",
            module_name, module_name, module_name));
        for (i, exp) in pin_exps.iter().enumerate() {
            let sep = if i + 1 < pin_exps.len() { "," } else { "" };
            out.push_str(&format!("      {}{}\n", exp, sep));
        }
        out.push_str("    ] := by\n  native_decide\n\n");
    }

    // Phase 2: Hoare-triple emission. Symbolic execution already done inline above; `state` is ready.
    out.push_str("/-! ## Symbolically lifted Hoare triple\n\n");
    out.push_str("Synthesised by qedlift's symbolic executor walking the\n");
    out.push_str("decoded insns left-to-right. Closed by `sl_block_auto`. -/\n\n");
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
    for (bs, size) in &state.memset_blobs {
        syscall_sig.push_str(&format!("({} : ByteArray)\n    ", bs));
        syscall_sig.push_str(&format!("(h{}_sz : {}.size = {})\n    ", bs, bs, size));
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
    // or any cond-jump taken (SpecGen.mkSpec only has _not_taken; taken arms need explicit spec calls).
    let any_taken = state.branch_hyps.iter().any(|b| b.taken);
    let use_block_iter = state.saw_call || any_taken;

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
                Atom::Bytes { .. } | Atom::Bytes32 { .. } => continue,
            };
            if is_complex(v) {
                // Fold sub-expr abstractions first so generalize target matches the sl_rw_abs-folded proof term.
                let r = fold_abstractions(v.to_lean(), &abs_subst);
                // Skip address abstractions: generalizing an address rewrites it everywhere, breaking post/rr matching.
                let is_addr_abs = abs_subst.contains_key(&r)
                    || abs_subst.values().any(|p| *p == r);
                if !is_addr_abs && seen.insert(r.clone()) {
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

    out.push_str(&format!(
        "open Memory in\n\
         theorem {}_lifted_spec\n    {}{}{}{}{}{}: \
         cuTripleWithinMem {} {} {} {}\n      \
         ({})\n      \
         ({}{})\n      \
         ({}{})\n      \
         (fun rt => {}) := by\n\
         {}\n\n",
        module_name,
        vars_sig,
        abs_sig,
        u64_hyps,
        branch_hyps_sig,
        side_hyps_sig,
        syscall_sig,
        n, m_bound, start_pc, exit_pc,
        cr_lean,
        atoms_to_lean(&pre,  &abs_subst),  cs_atom,
        atoms_to_lean(&post, &abs_subst),  cs_atom,
        rr,
        tactic,
    ));

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
        for (bs, _) in &state.memset_blobs {
            names.push(bs.clone());
            names.push(format!("h{}_sz", bs));
        }
        for (ncu, hcu, _) in &state.syscall_cu_vars {
            names.push(ncu.clone());
            names.push(hcu.clone());
        }
        out = out.replacen("import SVM.SBPF.Macros\n",
            "import SVM.SBPF.Macros\nimport SVM.SBPF.HeapSL\n", 1);
        out.push_str(&format!(
            "open Memory in\n\
             theorem {}_allocates\n    {}{}{}{}{}{}: \
             cuTripleWithinMem {} {} {} {}\n      \
             ({})\n      \
             ({}{})\n      \
             ({}{})\n      \
             (fun rt => {}) := by\n  \
             simp only [heapBumpPtr, heapBlockU64]\n  \
             exact {}_lifted_spec {}\n\n",
            module_name,
            vars_sig, abs_sig, u64_hyps, branch_hyps_sig, side_hyps_sig, syscall_sig,
            n, m_bound, start_pc, exit_pc,
            cr_lean,
            atoms_to_lean_heap(&pre,  &abs_subst), cs_atom,
            atoms_to_lean_heap(&post, &abs_subst), cs_atom,
            rr,
            module_name, names.join(" "),
        ));
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
    // Only counter/vault arms (is_const_delta_arm) get the constant +k cleaning; others stay wrapAdd.
    let counter_arm = is_const_delta_arm(arm_name);
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
        for (bs, _) in &state.memset_blobs {
            names.push(bs.clone());
            names.push(format!("h{}_sz", bs));
        }
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
                    // wrapAdd_one_of_lt cleans wrapAdd a (toU64 1) → a+1; only +1 delta wired.
                    debug_assert_eq!(*c, 1, "only a +1 constant delta is supported");
                    let al = fold_abstractions(a.to_lean(), &abs_subst);
                    extra_hyps.push_str(&format!("(h_noovf{} : {} + {} < 2 ^ 64)\n    ", k, al, c));
                    rw_terms.push(format!("← wrapAdd_one_of_lt h_noovf{}", k));
                }
            }
        }

        out.push_str(&format!(
            "open Memory in\n\
             theorem {}_balance_correct\n    {}{}{}{}{}{}{}: \
             cuTripleWithinMem {} {} {} {}\n      \
             ({})\n      \
             ({}{})\n      \
             ({}{})\n      \
             (fun rt => {}) := by\n  \
             have h := {}_lifted_spec {}\n  \
             rw [{}]\n  \
             exact h\n\n",
            module_name,
            vars_sig, abs_sig, u64_hyps, branch_hyps_sig, side_hyps_sig, syscall_sig, extra_hyps,
            n, m_bound, start_pc, exit_pc,
            cr_lean,
            atoms_to_lean(&pre, &abs_subst), cs_atom,
            atoms_to_lean(&post_clean, &abs_subst), cs_atom,
            rr,
            module_name, names.join(" "),
            rw_terms.join(", "),
        ));
    }

    out.push_str(&format!("end Examples.Lifted.{}\n", module_name));

    // ── Asm-refines-intrinsic theorem (mechanized recipe) ───────────
    let refine_emit = arm_name.and_then(|arm| emit_refinement(
        arm, &module_name, &pre, &post_clean, &abs_subst, &vars, n, start_pc, exit_pc, idl,
        sidecar_layouts));
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

// PascalCase: "transfer_checked" → "TransferChecked".
fn pascal_case(s: &str) -> String {
    let mut out = String::new();
    let mut up = true;
    for c in s.chars() {
        if c == '_' || c == '-' || c == ' ' { up = true; continue; }
        if up { out.extend(c.to_uppercase()); up = false; }
        else  { out.push(c); }
    }
    out
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

    // --qedmeta mode: targeting from qedrecover sidecar (disc + name), CU cross-check, optional --target-name filter.
    if let Some(meta_path) = args.qedmeta.as_ref() {
        let meta = load_qedmeta(meta_path)?;
        // #41 loop closure: consume qedrecover's emitted + validated account layouts as the
        // refinement-codegen layout source (falls back to `--idl` per-name when a layout is absent).
        let sidecar_layouts = sidecar_account_layouts(&meta);
        let so_stem = args.so.file_stem()
            .map(|s| pascal_case(&s.to_string_lossy()))
            .unwrap_or_else(|| "Lifted".to_string());

        let selected: Vec<&QedMetaIx> = match args.target_name.as_ref() {
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
                Some(&sidecar_layouts))?;

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

    let result = lift_one(&args.so, &ctx, &analysis, args.target_disc, args.module.clone(),
                          trace.as_deref(), args.arm_name.as_deref(), idl_value.as_ref(), None)?;
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
