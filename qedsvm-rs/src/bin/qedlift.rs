//! qedlift — end-to-end lift demo for a simple Solana program.
//!
//! Takes a `.so` whose `.text` is short and straight-line, and emits a
//! Lean module that:
//!   1. embeds the `.text` bytes verbatim as a `ByteArray`,
//!   2. decodes them via `SVM.SBPF.Decode.decodeProgram` and proves the
//!      decoded form via `native_decide`,
//!   3. states a `cuTripleWithinMem` Hoare triple over the decoded
//!      sequence with mvars (`?_`) for the pre/post atoms, and
//!   4. discharges the proof via `sl_block_auto`.
//!
//! For byte_increment.so this reproduces the same theorem
//! `byte_increment_macro_spec_auto` already proves in `SVM/SBPF/Macros.lean`
//! — but the *theorem statement* is now generated mechanically from the
//! `.so`, not hand-typed. That's the load-bearing demonstration: given
//! the binary, we can produce the Lean proof obligation automatically;
//! `sl_block_auto` then closes it.
//!
//! Phase 2 (this iteration): a symbolic executor walks the decoded
//! insns left-to-right, maintaining a `SymState` (symbolic regs +
//! memory atoms), and synthesises the pre/post-condition assertions
//! that `sl_block_auto` then closes. Supports the byte_increment +
//! counter instruction set today: ldxb/ldxdw/stxb/stxdw, add64.imm,
//! sub64.imm, mov64.imm. Extending to more opcodes is mechanical —
//! one match arm per `ebpf::OPCODE`.
//!
//! Usage:
//!   cargo run --features qedrecover --bin qedlift -- \
//!     --so tests/fixtures/byte_increment.so \
//!     --output examples/lean/Generated/ByteIncrementLifted.lean

use std::path::{Path, PathBuf};
use std::sync::Arc;

use solana_sbpf::{
    ebpf,
    elf::Executable,
    program::BuiltinProgram,
    static_analysis::Analysis,
    vm::ContextObject,
};

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

// -----------------------------------------------------------------------------
// qedmeta sidecar (subset). Only the fields qedlift needs for targeting;
// serde ignores the rest (target/idl/account/recovered/blocks).
// -----------------------------------------------------------------------------

#[derive(Debug, serde::Deserialize)]
struct QedMeta {
    #[serde(rename = "instruction")]
    instructions: Vec<QedMetaIx>,
}

#[derive(Debug, serde::Deserialize)]
struct QedMetaIx {
    name:          String,
    #[allow(dead_code)] refines: Option<String>,
    cu_budget:     Option<u64>,
    discriminator: QedMetaDisc,
}

#[derive(Debug, serde::Deserialize)]
struct QedMetaDisc {
    value: i64,
}

fn load_qedmeta(path: &Path) -> Result<QedMeta, Box<dyn std::error::Error>> {
    let text = std::fs::read_to_string(path)?;
    Ok(toml::from_str(&text)?)
}

// -----------------------------------------------------------------------------
// IDL parsing. Two formats are supported, dispatched on file extension:
//   • .toml  — minimal in-tree schema for fixtures (see two_op.qedidl.toml)
//   • .json  — Codama IDL (the de-facto format Solana programs ship with;
//              same JSON qedrecover already consumes)
// Both flatten to a `Vec<IdlInstruction>` for the batch loop.
// -----------------------------------------------------------------------------

#[derive(Debug)]
struct IdlInstruction {
    name:          String,
    discriminator: i64,
}

#[derive(Debug, serde::Deserialize)]
struct IdlToml {
    #[allow(dead_code)] schema_version: u32,
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

// Codama is a tree of typed nodes. For the batch lift, we only need
// `(name, discriminator)` per instructionNode. The discriminator value
// lives in the `arguments[]` entry whose `name` matches the
// `discriminators[0].name`, under `defaultValue.number`. Only the
// "u8 at offset 0" shape is handled today — that covers SPL Token,
// p-token, and our in-tree fixtures. Anchor's 8-byte sighashes need
// a wider executor and aren't supported yet.
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
        // Only field-style single-byte discriminators at offset 0.
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

/// Load a Codama (`.json`) IDL as a raw `serde_json::Value` for layout
/// extraction. Returns `None` for the minimal `.toml` IDL format (which
/// carries no account layout) or on read/parse error.
fn load_idl_value(path: &Path) -> Option<serde_json::Value> {
    if path.extension().and_then(|e| e.to_str()) != Some("json") { return None; }
    let text = std::fs::read_to_string(path).ok()?;
    serde_json::from_str(&text).ok()
}

// -----------------------------------------------------------------------------
// Codama account-data-struct → byte layout.
//
// Walks a Codama account's field list, computing each field's byte offset
// and size from its type node, so the refinement codegen can derive the
// account layout (which `account_agg` instantiates) from the IDL instead
// of hardcoding offsets like `+64`/`+36`. The field KIND maps onto the
// `FieldVal` codec: pubkey → `.pubkey`, u64 → `.u64`, u8/bool → `.byte`,
// everything else (options, enums, arrays, wide scalars) → opaque `.blob`
// bytes folded into the account's `rest` region.
// -----------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq)]
enum FieldKind {
    Pubkey,      // 32-byte ↦Pubkey (four u64 limbs)
    U64,         // 8-byte ↦U64
    Byte,        // 1-byte ↦ₘ  (u8 / bool / single-byte enum tag)
    Bytes(usize),// opaque region of N bytes (options, arrays, wide scalars)
}

#[derive(Debug, Clone)]
struct AccountField {
    name:   String,
    offset: usize,
    kind:   FieldKind, // FieldVal classification, consumed by the vault codegen
}

#[derive(Debug, Clone)]
struct AccountLayout {
    #[allow(dead_code)] name: String,    // metadata; offsets/size are what's consumed
    fields: Vec<AccountField>,
    size:   usize,
}

/// Byte width of a Codama `numberTypeNode` format.
fn codama_number_size(fmt: &str) -> Option<usize> {
    match fmt {
        "u8" | "i8"     => Some(1),
        "u16" | "i16"   => Some(2),
        "u32" | "i32"   => Some(4),
        "u64" | "i64"   => Some(8),
        "u128" | "i128" => Some(16),
        _ => None,
    }
}

/// Byte size of a Codama type node. `defined` resolves
/// `definedTypeLinkNode`s (e.g. the `accountState` enum). Returns `None`
/// for variable-size or unsupported nodes.
fn codama_type_size(
    ty: &serde_json::Value,
    defined: &std::collections::HashMap<String, serde_json::Value>,
) -> Option<usize> {
    match ty.get("kind")?.as_str()? {
        "publicKeyTypeNode" => Some(32),
        "numberTypeNode"    => codama_number_size(ty.get("format")?.as_str()?),
        // Solana COption: a fixed prefix (u32 here) + the item bytes.
        "optionTypeNode" => {
            let prefix = ty.get("prefix")
                .and_then(|p| codama_type_size(p, defined)).unwrap_or(4);
            Some(prefix + codama_type_size(ty.get("item")?, defined)?)
        }
        "booleanTypeNode" => ty.get("size")
            .and_then(|s| codama_type_size(s, defined)).or(Some(1)),
        "enumTypeNode" => ty.get("size")
            .and_then(|s| codama_type_size(s, defined)).or(Some(1)),
        "arrayTypeNode" => {
            let item = codama_type_size(ty.get("item")?, defined)?;
            // fixedCountNode { value: N } (older codama uses `count`).
            let count = ty.get("count")?;
            let n = count.get("value").or_else(|| count.get("count"))?.as_u64()? as usize;
            Some(item * n)
        }
        "fixedSizeTypeNode" => ty.get("size")?.as_u64().map(|n| n as usize),
        "definedTypeLinkNode" => {
            let name = ty.get("name")?.as_str()?;
            codama_type_size(defined.get(name)?.get("type")?, defined)
        }
        _ => None,
    }
}

/// Classify a field's type node into a codec `FieldKind`.
fn codama_field_kind(
    ty: &serde_json::Value,
    defined: &std::collections::HashMap<String, serde_json::Value>,
) -> Option<FieldKind> {
    let size = codama_type_size(ty, defined)?;
    Some(match ty.get("kind").and_then(|k| k.as_str()) {
        Some("publicKeyTypeNode")              => FieldKind::Pubkey,
        Some("numberTypeNode") if size == 8    => FieldKind::U64,
        Some("numberTypeNode") if size == 1    => FieldKind::Byte,
        Some("booleanTypeNode") if size == 1   => FieldKind::Byte,
        _                                      => FieldKind::Bytes(size),
    })
}

/// Parse a Codama account-data struct into a byte layout. `name` is the
/// account node name (e.g. "token", "mint").
fn parse_account_layout(
    root: &serde_json::Value,
    name: &str,
) -> Result<AccountLayout, Box<dyn std::error::Error>> {
    let prog = root.get("program").unwrap_or(root);
    let defined: std::collections::HashMap<String, serde_json::Value> = prog
        .get("definedTypes").and_then(|v| v.as_array())
        .map(|arr| arr.iter()
            .filter_map(|t| Some((t.get("name")?.as_str()?.to_string(), t.clone())))
            .collect())
        .unwrap_or_default();
    let accts = prog.get("accounts").and_then(|v| v.as_array())
        .ok_or("codama: /program/accounts missing")?;
    let acct = accts.iter()
        .find(|a| a.get("name").and_then(|n| n.as_str()) == Some(name))
        .ok_or_else(|| format!("codama: account {:?} not found", name))?;
    let fields_json = acct.pointer("/data/fields").and_then(|v| v.as_array())
        .ok_or_else(|| format!("codama: account {:?} has no data.fields", name))?;

    let mut offset = 0usize;
    let mut fields = Vec::new();
    for f in fields_json {
        let fname = f.get("name").and_then(|n| n.as_str()).unwrap_or("?").to_string();
        let ty = f.get("type").ok_or("codama: field has no type")?;
        let size = codama_type_size(ty, &defined)
            .ok_or_else(|| format!("codama: field {:?}: unsupported type node", fname))?;
        let kind = codama_field_kind(ty, &defined)
            .ok_or_else(|| format!("codama: field {:?}: unclassifiable", fname))?;
        fields.push(AccountField { name: fname, offset, kind });
        offset += size;
    }
    Ok(AccountLayout { name: name.to_string(), fields, size: offset })
}

#[cfg(test)]
mod layout_tests {
    use super::*;

    fn idl() -> serde_json::Value {
        let text = std::fs::read_to_string("tests/fixtures/spl_token.codama.json")
            .expect("read spl_token.codama.json");
        serde_json::from_str(&text).expect("parse IDL")
    }

    #[test]
    fn token_account_layout() {
        let l = parse_account_layout(&idl(), "token").unwrap();
        assert_eq!(l.size, 165, "SPL token account is 165 bytes");
        let by = |n: &str| l.fields.iter().find(|f| f.name == n).unwrap();
        assert_eq!((by("mint").offset,   by("mint").kind.clone()),   (0,  FieldKind::Pubkey));
        assert_eq!((by("owner").offset,  by("owner").kind.clone()),  (32, FieldKind::Pubkey));
        assert_eq!((by("amount").offset, by("amount").kind.clone()), (64, FieldKind::U64));
        // delegate (option<pubkey>) begins the opaque rest region at 72.
        assert_eq!(by("delegate").offset, 72);
    }

    #[test]
    fn mint_account_layout() {
        let l = parse_account_layout(&idl(), "mint").unwrap();
        assert_eq!(l.size, 82, "SPL mint account is 82 bytes");
        let supply = l.fields.iter().find(|f| f.name == "supply").unwrap();
        assert_eq!((supply.offset, supply.kind.clone()), (36, FieldKind::U64));
    }

    #[test]
    fn transfer_aggregation_is_mechanically_emitted() {
        // src reads owner + rest bytes 72/108/109; dst frames owner, reads 108.
        let m = render_token_agg_module(
            "Examples.PTokenTransferAggregation",
            &[("src_account_eq", true,  vec![72, 108, 109]),
              ("dst_account_eq", false, vec![108])],
            72, 165);
        let on_disk = std::fs::read_to_string("../examples/lean/PToken/TransferAggregation.lean")
            .expect("read TransferAggregation.lean");
        assert_eq!(m, on_disk,
            "TransferAggregation.lean is out of sync with the qedlift emitter — \
             regenerate it (the file is mechanically emitted, do not hand-edit)");
    }

    #[test]
    fn mint_aggregation_is_mechanically_emitted() {
        // SPL mint: supply@36, rest@44, size 82; dest token 72/165.
        let m = render_mint_agg_module(
            "Examples.PTokenMintAggregation", 36, 44, 82, 72, 165);
        let on_disk = std::fs::read_to_string("../examples/lean/PToken/MintAggregation.lean")
            .expect("read MintAggregation.lean");
        assert_eq!(m, on_disk,
            "MintAggregation.lean is out of sync with the qedlift emitter \
             (mechanically emitted, do not hand-edit)");
    }

    /// The counter lift + the first NON-token refinement
    /// (`AsmRefinesCounterIncrement`) are mechanically emitted. Re-runs
    /// the whole emitter (detection + constant-`+1` cleaning + render) on
    /// `counter.so` and diffs both files, guarding the counter-codec path.
    #[test]
    fn counter_refinement_is_mechanically_emitted() {
        let so = std::path::Path::new("tests/fixtures/counter.so");
        let ctx = load_binary(so).expect("load counter.so");
        let analysis = Analysis::from_executable(&ctx.executable).expect("analyse counter.so");
        let result = lift_one(so, &ctx, &analysis, None, Some("Counter".to_string()),
            None, Some("counterIncrement"), None).expect("lift counter.so");

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

    /// The multi-field NON-token vault refinement (`AsmRefinesFieldUpdate`)
    /// is mechanically emitted from the Codama IDL account layout. Re-runs
    /// the emitter on `vault.so` + `vault.codama.json` and diffs both
    /// files, guarding the layout-general account-codec path.
    #[test]
    fn vault_refinement_is_mechanically_emitted() {
        let so = std::path::Path::new("tests/fixtures/vault.so");
        let idl: serde_json::Value = serde_json::from_str(
            &std::fs::read_to_string("tests/fixtures/vault.codama.json")
                .expect("read vault.codama.json")).expect("parse vault IDL");
        let ctx = load_binary(so).expect("load vault.so");
        let analysis = Analysis::from_executable(&ctx.executable).expect("analyse vault.so");
        let result = lift_one(so, &ctx, &analysis, None, Some("Vault".to_string()),
            None, Some("VaultIncrement"), Some(&idl)).expect("lift vault.so");

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

    /// The blob/`account_agg` codegen path: the SAME `vault.so`, but the
    /// untouched `owner` field is described as a `[u8; 32]` array in the
    /// IDL, so it is framed as an opaque `.blob [.gap g]` (`↦Bytes`) rather
    /// than four pubkey dwords. Guards the layout-general blob aggregation
    /// (`memBytesIs_segs`) the vault codegen now emits. Both files are
    /// `lake build`-verified (sorry-free) under `Generated.VaultBlob*`.
    #[test]
    fn vault_blob_refinement_is_mechanically_emitted() {
        let so = std::path::Path::new("tests/fixtures/vault.so");
        let idl: serde_json::Value = serde_json::from_str(
            &std::fs::read_to_string("tests/fixtures/vault_blob.codama.json")
                .expect("read vault_blob.codama.json")).expect("parse vault_blob IDL");
        let ctx = load_binary(so).expect("load vault.so");
        let analysis = Analysis::from_executable(&ctx.executable).expect("analyse vault.so");
        let result = lift_one(so, &ctx, &analysis, None, Some("VaultBlob".to_string()),
            None, Some("VaultIncrement"), Some(&idl)).expect("lift vault.so (blob)");

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

    /// The heap-allocating lift, including the mechanically-emitted
    /// `HeapAlloc_allocates` corollary (heap cells folded into
    /// `heapBumpPtr`/`heapBlockU64`) and the conditional `HeapSL` import,
    /// is mechanically emitted. Guards the heap-corollary codegen.
    #[test]
    fn heap_alloc_lift_is_mechanically_emitted() {
        let so = std::path::Path::new("tests/fixtures/heap_alloc.so");
        let ctx = load_binary(so).expect("load heap_alloc.so");
        let analysis = Analysis::from_executable(&ctx.executable).expect("analyse heap_alloc.so");
        let result = lift_one(so, &ctx, &analysis, None, Some("HeapAlloc".to_string()),
            None, None, None).expect("lift heap_alloc.so");

        let on_disk =
            std::fs::read_to_string("../examples/lean/Generated/HeapAllocLifted.lean")
                .expect("read HeapAllocLifted.lean");
        assert_eq!(result.lean, on_disk,
            "HeapAllocLifted.lean is out of sync with the qedlift emitter \
             (mechanically emitted, do not hand-edit)");
    }

    /// Pins the halfword path on real cargo-build-sbf bytecode: ldxh /
    /// stxh and the ST_H_IMM dispatch (`sth_spec`) in one straight line.
    #[test]
    fn halfword_store_lift_is_mechanically_emitted() {
        let so = std::path::Path::new("tests/fixtures/halfword_store.so");
        let ctx = load_binary(so).expect("load halfword_store.so");
        let analysis = Analysis::from_executable(&ctx.executable).expect("analyse halfword_store.so");
        let result = lift_one(so, &ctx, &analysis, None, Some("HalfwordStore".to_string()),
            None, None, None).expect("lift halfword_store.so");

        let on_disk =
            std::fs::read_to_string("../examples/lean/Generated/HalfwordStoreLifted.lean")
                .expect("read HalfwordStoreLifted.lean");
        assert_eq!(result.lean, on_disk,
            "HalfwordStoreLifted.lean is out of sync with the qedlift emitter \
             (mechanically emitted, do not hand-edit)");
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

/// Convert a `solana_sbpf::ebpf::Insn` at analysis PC `pc` to the
/// Lean `Insn` constructor syntax. The cases here cover the
/// byte_increment / counter / guarded-counter / counter_with_helper
/// instruction sets; extending it is mechanical (each new opcode
/// adds one match arm). For conditional jumps `pc` is used to
/// resolve the target PC; for `call_local`, `call_target` (when
/// provided) is substituted as the resolved callee PC (because the
/// raw immediate is a Murmur3 hash, not an offset).
fn insn_to_lean_full(insn: &ebpf::Insn, pc: usize, call_target: Option<usize>,
                     jump_target: Option<i64>) -> Result<String, String> {
    use ebpf::*;
    let (dst, src, off, imm) = (insn.dst, insn.src, insn.off as i64, insn.imm);
    // Logical jump target (slot→logical resolved by the caller). Falls
    // back to the raw slot-relative sum for callers that don't resolve.
    let jt = || jump_target.unwrap_or((pc as i64) + 1 + off);
    let reg = |n: u8| match n {
        0 => ".r0", 1 => ".r1", 2 => ".r2", 3 => ".r3",
        4 => ".r4", 5 => ".r5", 6 => ".r6", 7 => ".r7",
        8 => ".r8", 9 => ".r9", 10 => ".r10",
        _ => "?reg",
    };
    // Offset rendered for Lean Insn syntax: negative offsets need
    // parens (`.stx .dword .r10 -2072 .r0` would parse as
    // `.r10 - 2072`). Same rationale as `lean_off`.
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
        // Conditional jumps with immediate operand. Lean syntax is
        // `.jXX dst (.imm K) target_pc`. We resolve `target_pc` to the
        // absolute PC the jump lands at (caller-supplied).
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
        // 32-bit ALU family.
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
        // call_local: the immediate is the Solana ABI Murmur3 hash
        // of the symbol, NOT a relative offset. Resolving the actual
        // target PC requires `solana_sbpf::Analysis::cfg_nodes`; the
        // caller pre-resolves it via `?TARGET` substitution before
        // emitting Lean. Render with a placeholder so any caller that
        // forgets to substitute fails loudly rather than emitting a
        // garbage target.
        CALL_IMM    => match call_target {
            Some(t) => format!(".call_local {}", t),
            None    => ".call_local TARGET_PC_NOT_RESOLVED".to_string(),
        },
        opc         => return Err(format!("opcode 0x{:02x} not yet lifted to Lean", opc)),
    })
}

/// Thin wrapper for callers that don't know the resolved call target
/// (e.g. the raw "decoded insns" listing in the diagnostic dump).
/// Renders call_local with a placeholder.
fn insn_to_lean(insn: &ebpf::Insn, pc: usize) -> Result<String, String> {
    insn_to_lean_full(insn, pc, None, None)
}

/// Resolve a CALL_IMM at `pc` to its callee PC. solana-sbpf encodes
/// the call's immediate field as the Murmur3 hash of the symbol name
/// (not a relative offset). The function registry — exposed as
/// `analysis.functions: BTreeMap<usize, (u32, String)>` mapping
/// function-start-pc → (hash, name) — lets us reverse the lookup.
fn resolve_call_target(analysis: &Analysis, insn: &ebpf::Insn) -> Option<usize> {
    if insn.opc != ebpf::CALL_IMM { return None; }
    let target_hash = insn.imm as u32;
    analysis.functions.iter()
        .find_map(|(&pc, (h, _name))| if *h == target_hash { Some(pc) } else { None })
}

/// `resolve_call_target` but mapped from the function registry's
/// SLOT-based PC to a LOGICAL instruction index. The registry (and the
/// VM) count `lddw` as two slots, while the lift's PCs / CodeReq /
/// `call_local_spec` target are all logical indices — so a callee past
/// any `lddw` would otherwise be off by the lddw count (e.g. p_token's
/// `call_local` to logical 10836 resolves to slot 11537). Mirrors
/// `resolve_jump_target`'s slot→logical handling. For lddw-free programs
/// slot == logical, so this is a no-op (keeps those lifts byte-identical).
fn resolve_call_target_logical(
    ctx: &BinaryCtx, analysis: &Analysis, insn: &ebpf::Insn,
) -> Option<usize> {
    let slot = resolve_call_target(analysis, insn)?;
    match ctx.slot_to_logical.get(slot) {
        Some(Some(logical)) => Some(*logical),
        _ => Some(slot), // out of range / mid-lddw: fall back (fail loudly downstream)
    }
}

/// Render a symbolic call stack as a Lean `List CallFrame` literal,
/// newest-frame first (matching `call_local_spec`'s `frame :: cs` post).
/// Each frame is `⟨<callpc> + 1, r6, r7, r8, r9, r10⟩` (retPc kept as the
/// unreduced `pc + 1` the spec pushes, + the call-time saved registers).
/// Used to thread the rest-of-stack `cs` through nested call/return.
fn render_callstack(frames: &[(usize, [Expr; 5])]) -> String {
    if frames.is_empty() { return "[]".to_string(); }
    let items: Vec<String> = frames.iter().rev().map(|(cp, regs)| {
        format!("⟨{} + 1, {}, {}, {}, {}, {}⟩", cp,
            regs[0].atom_lean(), regs[1].atom_lean(), regs[2].atom_lean(),
            regs[3].atom_lean(), regs[4].atom_lean())
    }).collect();
    format!("[{}]", items.join(", "))
}

// -----------------------------------------------------------------------------
// Symbolic executor — phase 2 of the lift
// -----------------------------------------------------------------------------
//
// Walks a straight-line slice of decoded eBPF insns, maintaining a
// SymState (symbolic register values + ordered list of pre-condition
// atoms touched). Emits the Lean SL expressions for the precondition
// and postcondition. The triple type is `cuTripleWithinMem n 0 0 n cr
// PRE POST RR` where `n` is the number of insns covered (excluding
// the trailing exit, if any) — exactly the shape `sl_block_auto`
// accepts.

/// Symbolic-algebra expression representing a Nat value during
/// symbolic execution. Stringified to Lean source via `to_lean`.
#[derive(Clone, Debug)]
enum Expr {
    /// Initial value of a register at entry (e.g., "initR2", "baseAddr").
    InitReg(String),
    /// Initial value of a memory cell loaded during execution (e.g., "oldCounter").
    InitMem(String),
    /// Integer literal.
    Const(i64),
    /// `toU64 n` — Solana ABI helper for sign-extended Nat literals.
    ToU64(Box<Expr>),
    /// `e % m` — narrowing modulus from a byte/half/word load.
    Mod(Box<Expr>, u64),
    /// `wrapAdd a b` — 64-bit wrapping add.
    WrapAdd(Box<Expr>, Box<Expr>),
    /// `wrapSub a b` — 64-bit wrapping sub.
    WrapSub(Box<Expr>, Box<Expr>),
    /// `wrapMul a b` — 64-bit wrapping multiply.
    WrapMul(Box<Expr>, Box<Expr>),
    /// Plain `Nat.add a b`. Used for `call_local_spec`'s `r10 +
    /// 0x1000` which uses Nat addition rather than `wrapAdd`.
    NatAdd(Box<Expr>, Box<Expr>),
    /// `(a &&& toU64 imm) % U64_MODULUS` — output of `and64_imm_spec`.
    /// The `imm` arg is the raw immediate; we render `toU64 imm`
    /// inside `to_lean`.
    AndU64Imm(Box<Expr>, i64),
    /// `(a <<< (toU64 imm % 64)) % U64_MODULUS` — output of
    /// `lsh64_imm_spec` (logical left shift by immediate, modulo 64,
    /// truncated to 64 bits).
    LshU64Imm(Box<Expr>, i64),
    /// `toU64 imm % 2 ^ (2 * 8)` — the halfword value `st .half`
    /// writes. Matches `sth_spec`'s post.
    StHalfImm(i64),
    /// `toU64 imm % 2 ^ (4 * 8)` — the word value `st .word` writes.
    /// Rendered to match `stw_spec`'s post exactly (the machine's
    /// `writeByWidth` truncates to 32 bits).
    StWordImm(i64),
    /// `toU64 imm % 2 ^ (8 * 8)` — the dword value `st .dword` writes.
    /// Matches `stdw_spec`'s post.
    StDwordImm(i64),
    /// `a >>> (toU64 imm % 64)` — output of `rsh64_imm_spec`. No
    /// `% U64_MODULUS` wrapper (a right shift never grows the value).
    RshU64Imm(Box<Expr>, i64),
    /// Render-only: ordinary Nat subtraction `a - b`. Used by the
    /// balance-correctness corollary to expose a `wrapSub a b` debit in
    /// clean form (justified by `wrapSub_of_le` under a funds guard).
    CleanSub(Box<Expr>, Box<Expr>),
    /// Pre-rendered Lean term for an ALU result whose shape doesn't
    /// warrant a bespoke variant (the long tail: or/xor/div/mod/neg,
    /// reg-form shifts, 32-bit ops). The string is exactly what the
    /// corresponding `*_spec` writes in its post. Opaque to the
    /// balance-corollary pattern match (which only tracks wrapAdd /
    /// wrapSub), and always parenthesised as a function argument.
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
                // Render exactly as `and64_imm_spec` writes its post.
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
        }
    }
    /// Lean rendering suitable for use as a function argument
    /// (parenthesised when the head isn't already atomic).
    fn atom_lean(&self) -> String {
        match self {
            Expr::Raw(s) => format!("({})", s),
            Expr::InitReg(_) | Expr::InitMem(_) => self.to_lean(),
            // Negative constants need parens (`-1` would otherwise
            // parse as subtraction in `toU64 -1`).
            Expr::Const(n) if *n < 0 => format!("({})", n),
            Expr::Const(_) => self.to_lean(),
            _ => format!("({})", self.to_lean()),
        }
    }
}

/// Load/store width — used to pick the right Lean memory binding
/// notation (↦ₘ for byte, ↦U16/32/64 for wider).
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

/// Render a memory offset for `effectiveAddr base off`. Negative
/// offsets MUST be parenthesised: `effectiveAddr b -8` parses as
/// `(effectiveAddr b) - 8` (an `HSub (Int → Nat) Nat` type error,
/// since `effectiveAddr b` is partially applied).
fn lean_off(off: i64) -> String {
    if off < 0 { format!("({})", off) } else { format!("{}", off) }
}

/// Render `arsh{32,64}`'s post — the arithmetic-shift-right
/// `let shift … if sign-bit then logical-shift else fill-high-bits`
/// expression — as a parenthesised Lean term, matching
/// `arsh{32,64}_{imm,reg}_spec` exactly (used as an `Expr::Raw`). `vold`
/// is the dst's prior value (already atom-rendered); `shift_src` is the
/// shift amount (`toU64 <imm>` or the src reg value). Parens are
/// included because `↦ᵣ` can't take a bare `let`.
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

/// Contents of a variable-length byte blob (`↦Bytes`). Pre-state is a
/// fresh symbolic `ByteArray` (`Sym`); a memory syscall rewrites it to
/// a closed-form payload (`Replicate`, for `sol_memset_`).
#[derive(Clone, Debug)]
enum BytesVal {
    /// Fresh symbolic byte-array variable name (the unknown pre-state of
    /// a memset'd region). Its `.size = <r3>` bound is surfaced as a
    /// theorem hypothesis via `SymState.memset_blobs`, not stored here.
    Sym(String),
    /// `replicateByte (fill % 256).toUInt8 count` — the post-state a
    /// `sol_memset_(dst, fill, count)` leaves at `dst`.
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

/// One precondition atom: a register binding, a fixed-width memory
/// cell, or a variable-length byte blob (`↦Bytes`, from a memory
/// syscall such as `sol_memset_`).
#[derive(Clone, Debug)]
enum Atom {
    Reg(u8, Expr),
    Mem { addr_base: Expr, addr_off: i64, width: Width, value: Expr },
    /// A `↦Bytes` atom: `addr ↦Bytes <bytes>`. The address is the raw
    /// symbolic value of the syscall's `r1` (no `effectiveAddr`
    /// wrapper — `memBytesIs` takes a bare Nat), matching
    /// `call_sol_memset_spec`'s precondition shape.
    Bytes { addr: Expr, value: BytesVal },
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

/// One memory cell in the symbolic walk. The address is the SYMBOLIC
/// value of `base_reg` at the access — necessary because the same
/// `[r1+0]` access at two different walk PCs can refer to different
/// physical cells if `r1` was modified in between.
#[derive(Clone, Debug)]
struct MemCell {
    addr_base: Expr,
    addr_off:  i64,
    width:     Width,
    value:     Expr,
}

impl MemCell {
    /// Stable key over (rendered address, width) — two cells whose
    /// addresses render identically refer to the same physical cell.
    fn key(&self) -> (String, i64, u8) {
        (self.addr_base.to_lean(), self.addr_off, self.width as u8)
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

/// Decompose an effective address `base_expr + off` into a canonical
/// `(root, displacement)` pair by folding constant `wrapAdd`/`wrapSub`/
/// `Nat.add` layers (e.g. `r2 = r10 - 24` and a later `[r10 - 16]`
/// access both canonicalize to root `vR10Old` with displacements −24
/// and −16). A base the folding can't see through (multiplies, masks,
/// loads) becomes its own opaque root — same non-aliasing assumption
/// the cell map already makes for distinct rendered bases.
///
/// Soundness role: the walker keys cells by RENDERED address, so two
/// accesses whose byte footprints overlap under different renderings
/// produce two separate (overlapping) atoms — and an overlapping
/// sepConj is UNSATISFIABLE, making the emitted theorem vacuous. The
/// canonical form lets `note_access` detect that and fail the lift
/// closed instead. (Soundness audit H8: the shipped InitializeMint2
/// lift was vacuous via the 7-byte tail-zeroing idiom
/// `stw [r10-4]; stw [r10-7]`.)
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

/// Symbolic state threaded through one walk of the slice.
#[derive(Default)]
struct SymState {
    /// Current symbolic value of each register, if read or written.
    /// Registers not present are treated as their initial value
    /// (`InitReg(reg_initial_name(r))`).
    regs: std::collections::BTreeMap<u8, Expr>,
    /// Pre-condition atoms collected in *first-touched* order.
    pre: Vec<Atom>,
    /// Memory cells the slice touched. Keyed by the rendered Lean
    /// representation of the effective address `(base, off, width)`,
    /// where `base` is the SYMBOLIC value of the base register at
    /// access time — so two reads at `[r1+0]` separated by an
    /// `add64 r1, 8` correctly resolve to two distinct cells.
    /// Implementation: linear search over a Vec (small N).
    mem: Vec<MemCell>,
    /// Fresh-variable counter for memory initials.
    fresh: u32,
    /// Names of symbolic variables that come from u64-width loads
    /// (`ldxdw`). The corresponding per-instruction spec carries a
    /// `< 2^64` side condition that the theorem signature must
    /// hypothesise so `sl_block_auto <;> assumption` discharges it.
    /// Loaded mem-cell vars that carry a `< 2^k` bound the spec needs
    /// surfaced as a hypothesis: `(var, k)` with k ∈ {16,32,64} for
    /// half/word/dword loads (`ldxh`/`ldxw`/`ldxdw`). `h<var>_lt`.
    u64_load_vars: Vec<(String, u32)>,
    /// Conditional jumps encountered on the happy-path walk. Each one
    /// adds a path hypothesis to the theorem signature.
    branch_hyps: Vec<BranchHyp>,
    /// Symbolic call stack — `(resume_pc, [r6,r7,r8,r9,r10] at call time)`
    /// pushed by `call_local`, popped by the corresponding `exit`. The
    /// full call-time r6..r10 are saved (not just r10) because the
    /// `exit_pops` spec's `frame` must equal the frame the `call_local`
    /// pushed — and a callee may clobber r6..r9, so their *current*
    /// (exit-time) values would mismatch the pushed frame. Empty at the
    /// start of the walk and empty when it terminates at the top exit.
    call_stack: Vec<(usize, [Expr; 5])>,
    /// True once the walk has seen at least one `call_local`. When
    /// set, the emission adds `r6..r10` and `callStackIs []` to the
    /// pre-condition (the atoms `call_local_spec` needs to compose).
    saw_call: bool,
    /// rr clauses in walk order. Each memory load contributes
    /// `containsRange`; each store contributes `containsWritable`.
    /// Order matches the chain's left-fold ordering, so the emitted
    /// goal rr structurally equals what `slBlockIter` produces.
    /// Entries: (addr_base, off, width, is_writable).
    rr_walk: Vec<(Expr, i64, Width, bool)>,
    /// Post-state contents of `↦Bytes` blobs written by memory
    /// syscalls (`sol_memset_`), keyed by the rendered destination
    /// address. `post_atoms` reads this to transform the pre `↦Bytes`
    /// (a fresh `Sym`) into its post form (`Replicate`).
    byte_blob_post: std::collections::BTreeMap<String, BytesVal>,
    /// PCs the walk identified as host syscalls, mapped to the Lean
    /// `Syscall` constructor (e.g. `.sol_memset`). The CodeReq builder
    /// renders these as `.call <ctor>` rather than `.call_local`.
    syscall_pcs: std::collections::BTreeMap<usize, &'static str>,
    /// One entry per syscall whose CU cost is surfaced as a theorem
    /// hypothesis: `(nCu_var, hCu_hyp, syscall_ctor)`. The model's
    /// `syscallCu` is data-dependent (∝ r3 for mem ops), so an honest
    /// upper bound is an assumption, not something the lift can
    /// discharge. `syscall_ctor` (e.g. `.sol_memset`) names the
    /// syscall in the `hCu` hypothesis's `step (.call …)` term.
    syscall_cu_vars: Vec<(String, String, &'static str)>,
    /// One entry per memset byte-blob: `(bytes_sym, size_rendered)`.
    /// Surfaced as a `ByteArray` param + a `.size = <count>` hypothesis
    /// in the theorem signature (the spec's `hbs` obligation).
    memset_blobs: Vec<(String, String)>,
    /// Generic surfaced side-condition hypotheses `(hyp_name, prop)` —
    /// e.g. a divisor's `v ≠ 0` for `div/mod` reg-form (the divisor is
    /// symbolic, so its non-zeroness is the caller's obligation, like a
    /// branch hypothesis). Emitted into the theorem signature verbatim.
    side_hyps: Vec<(String, String)>,
    /// Byte footprints of every materialized atom, in canonical
    /// `(root, lo, hi_exclusive, cell_key_rendering)` form (see
    /// `canon_addr`). Consulted on each NEW materialization to detect
    /// footprint overlap between DISTINCT atoms — which would make the
    /// emitted sepConj unsatisfiable (a vacuous theorem). Blob entries
    /// (memset) use the blob's rendered address as the key component.
    atom_spans: Vec<(String, i64, i64, String)>,
    /// Set when `note_access` detects an overlap; the walk loop
    /// surfaces it as a hard error (fail closed — never emit a
    /// vacuous theorem).
    overlap_error: Option<String>,
}

impl SymState {
    /// Record the byte footprint `[base+off, base+off+len)` of a newly
    /// materialized atom (cell or blob) and flag any overlap with a
    /// DIFFERENT existing atom on the same canonical root. Two atoms
    /// with overlapping byte footprints in one sepConj make the
    /// precondition unsatisfiable — the emitted theorem would be
    /// vacuously true, which is worse than no theorem (soundness
    /// audit H8 / the InitializeMint2 finding). Distinct opaque roots
    /// keep the walker's existing assumed-disjoint treatment.
    fn note_access(&mut self, base: &Expr, off: i64, len: i64, key_render: String) {
        let (root, lo) = canon_addr(base, off);
        let hi = lo.wrapping_add(len);
        for (eroot, elo, ehi, ekey) in &self.atom_spans {
            if *eroot == root && *ekey != key_render && lo < *ehi && *elo < hi {
                self.overlap_error = Some(format!(
                    "aliasing: atom `{key_render}` (root `{root}`, bytes \
                     [{lo}, {hi})) overlaps existing atom `{ekey}` (bytes \
                     [{elo}, {ehi})). Emitting both would make the \
                     precondition's sepConj unsatisfiable — a VACUOUS \
                     theorem. The walker does not yet alias overlapping \
                     accesses at byte granularity (tracked under the \
                     soundness-audit H8 emitter follow-ups), so this \
                     lift fails closed."));
                return;
            }
        }
        self.atom_spans.push((root, lo, hi, key_render));
    }
    fn read_reg(&mut self, r: u8) -> Expr {
        if let Some(v) = self.regs.get(&r) { return v.clone(); }
        let v = Expr::InitReg(reg_initial_name(r));
        self.regs.insert(r, v.clone());
        // Register reads from r0/r2..r9 add a pre-atom (we need to
        // know its initial value); r1 (input ptr) and r10 (frame top)
        // are conventional and also recorded.
        self.pre.push(Atom::Reg(r, v.clone()));
        v
    }
    fn write_reg(&mut self, r: u8, v: Expr) {
        // Ensure r has a pre-atom: if it was never read, its initial
        // value is still "free" — record it before overwriting.
        if !self.regs.contains_key(&r) {
            let init = Expr::InitReg(reg_initial_name(r));
            self.regs.insert(r, init.clone());
            self.pre.push(Atom::Reg(r, init));
        }
        self.regs.insert(r, v);
    }
    fn read_mem(&mut self, base: u8, off: i64, width: Width) -> Expr {
        // Compute the effective-address key from the base register's
        // *current* symbolic value (not just its register number).
        let base_expr = self.read_reg(base);
        let key = (base_expr.to_lean(), off, width as u8);
        if let Some(cell) = self.mem.iter().find(|c| c.key() == key) {
            let v = cell.value.clone();
            // A re-read of an already-cached cell is still a load
            // instruction: its spec contributes a `containsRange` to the
            // sl_block_iter chain. Record it here too so the goal rr stays
            // 1:1 with the walked load instructions (the fresh path below
            // pushes the same clause). Without this, a cell read twice
            // makes the chain rr out-count the goal rr.
            self.rr_walk.push((base_expr, off, width, false));
            return v;
        }
        // Fresh cell: name by (width, sequence index) since the
        // address expression itself may be complex (`wrapAdd baseAddr
        // (toU64 8)`) and ill-suited as a Lean identifier.
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
        };
        let width_len = match width {
            Width::Byte => 1, Width::Halfword => 2, Width::Word => 4, Width::Dword => 8,
        };
        self.note_access(&base_expr, off, width_len,
            format!("{}@{}:{:?}", base_expr.to_lean(), off, width));
        self.mem.push(cell);
        self.pre.push(Atom::Mem {
            addr_base: base_expr.clone(), addr_off: off, width, value: v.clone(),
        });
        // rr contribution: every load needs containsRange at the
        // accessed cell.
        self.rr_walk.push((base_expr, off, width, false));
        v
    }
    fn write_mem(&mut self, base: u8, off: i64, width: Width, value: Expr) {
        let base_expr = self.read_reg(base);
        let key = (base_expr.to_lean(), off, width as u8);
        // Make sure the pre-atom exists (a store after no preceding
        // load still needs the cell to be present in the pre-state).
        if !self.mem.iter().any(|c| c.key() == key) {
            let _ = self.read_mem(base, off, width);
            // `read_mem` materialised the cell AND pushed a
            // `containsRange` rr_walk entry — but this access is a
            // STORE. Its region requirement is the `containsWritable`
            // pushed below (which implies readability), and the chain's
            // rr has exactly one clause per memory instruction. Drop the
            // read's spurious entry so the goal rr stays 1:1 with the
            // walked memory instructions (matching sl_block_iter).
            self.rr_walk.pop();
        }
        if let Some(cell) = self.mem.iter_mut().find(|c| c.key() == key) {
            cell.value = value;
        }
        // rr contribution: every store needs containsWritable.
        self.rr_walk.push((base_expr, off, width, true));
    }
}

fn w_short(w: Width) -> &'static str {
    match w { Width::Byte => "B", Width::Halfword => "H", Width::Word => "W", Width::Dword => "D" }
}

/// A conditional jump the symbolic executor walked past on its
/// happy-path traversal. The theorem signature surfaces this as a
/// hypothesis the user (or a downstream tactic) must invoke when
/// closing the proof — `sl_block_auto` doesn't currently collapse
/// these on its own.
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
    /// For reg-form jumps, this is the src register's symbolic value.
    /// `None` for imm-form jumps (the imm is in `self.imm`).
    src_value: Option<Expr>,
    imm: i64,
    /// `true` if the branch was taken on the walked path; `false`
    /// if it was the fall-through. Determines the form of the path
    /// hypothesis: jeq-taken means `vDst = toU64 imm`; jeq-not-taken
    /// means `vDst ≠ toU64 imm`. jne is symmetric.
    taken: bool,
    #[allow(dead_code)] target_pc: usize,
}

impl BranchHyp {
    fn lean_hyp(&self) -> String {
        let v = self.dst_value.to_lean();
        let s = self.src_value.as_ref().map(|e| e.to_lean()).unwrap_or_default();
        // Parenthesised forms for use under `toSigned64`, which is a
        // prefix application and would otherwise grab only the head of
        // a compound expr (e.g. `toSigned64 wrapAdd a b` misparses as
        // `(toSigned64 wrapAdd) a b`). Unsigned comparisons don't need
        // this — infix `<`/`>`/`≤`/`=` bind looser than application.
        let va = self.dst_value.atom_lean();
        let sa = self.src_value.as_ref().map(|e| e.atom_lean()).unwrap_or_default();
        // Immediate, parenthesised when negative: `toU64 -5` would parse
        // as `(toU64) - 5` (an `Int → Nat` minus `Nat` type error).
        let im = if self.imm < 0 { format!("({})", self.imm) } else { format!("{}", self.imm) };
        match (self.kind.clone(), self.taken) {
            (BranchKind::JeqImm, false) => format!("{} ≠ toU64 {}", v, im),
            (BranchKind::JeqImm, true)  => format!("{} = toU64 {}", v, im),
            (BranchKind::JneImm, false) => format!("{} = toU64 {}", v, im),
            (BranchKind::JneImm, true)  => format!("{} ≠ toU64 {}", v, im),
            // `jgt` is unsigned >. Taken => vDst > toU64 imm; not-taken
            // is the strict negation (¬ >). The Lean helper accepts
            // exactly these via if_pos/if_neg.
            (BranchKind::JgtImm, false) => format!("¬ {} > toU64 {}", v, im),
            (BranchKind::JgtImm, true)  => format!("{} > toU64 {}", v, im),
            // `jsgt` is signed >. Lean spec compares
            // `toSigned64 vDst > toSigned64 (toU64 imm)`.
            (BranchKind::JsgtImm, false) => format!("¬ toSigned64 {} > toSigned64 (toU64 {})", va, im),
            (BranchKind::JsgtImm, true)  => format!("toSigned64 {} > toSigned64 (toU64 {})", va, im),
            // `jsle` is signed ≤ (imm form).
            (BranchKind::JsleImm, false) => format!("¬ toSigned64 {} ≤ toSigned64 (toU64 {})", va, im),
            (BranchKind::JsleImm, true)  => format!("toSigned64 {} ≤ toSigned64 (toU64 {})", va, im),
            // `jlt`/`jle` are unsigned < / ≤ (imm form).
            (BranchKind::JltImm, false) => format!("¬ {} < toU64 {}", v, im),
            (BranchKind::JltImm, true)  => format!("{} < toU64 {}", v, im),
            (BranchKind::JleImm, false) => format!("¬ {} ≤ toU64 {}", v, im),
            (BranchKind::JleImm, true)  => format!("{} ≤ toU64 {}", v, im),
            // `jslt` is signed < (imm form).
            (BranchKind::JsltImm, false) => format!("¬ toSigned64 {} < toSigned64 (toU64 {})", va, im),
            (BranchKind::JsltImm, true)  => format!("toSigned64 {} < toSigned64 (toU64 {})", va, im),
            // `jge` unsigned ≥, `jsge` signed ≥, `jset` bit-test (imm form).
            (BranchKind::JgeImm, false) => format!("¬ {} ≥ toU64 {}", v, im),
            (BranchKind::JgeImm, true)  => format!("{} ≥ toU64 {}", v, im),
            (BranchKind::JsgeImm, false) => format!("¬ toSigned64 {} ≥ toSigned64 (toU64 {})", va, im),
            (BranchKind::JsgeImm, true)  => format!("toSigned64 {} ≥ toSigned64 (toU64 {})", va, im),
            (BranchKind::JsetImm, false) => format!("¬ {} &&& toU64 {} ≠ 0", v, im),
            (BranchKind::JsetImm, true)  => format!("{} &&& toU64 {} ≠ 0", v, im),
            // Register-form jumps compare two registers directly.
            (BranchKind::JeqReg, false) => format!("{} ≠ {}", v, s),
            (BranchKind::JeqReg, true)  => format!("{} = {}", v, s),
            (BranchKind::JneReg, false) => format!("{} = {}", v, s),
            (BranchKind::JneReg, true)  => format!("{} ≠ {}", v, s),
            (BranchKind::JltReg, false) => format!("¬ {} < {}", v, s),
            (BranchKind::JltReg, true)  => format!("{} < {}", v, s),
            // `jgt`/`jle` are unsigned > / ≤ (reg form).
            (BranchKind::JgtReg, false) => format!("¬ {} > {}", v, s),
            (BranchKind::JgtReg, true)  => format!("{} > {}", v, s),
            (BranchKind::JleReg, false) => format!("¬ {} ≤ {}", v, s),
            (BranchKind::JleReg, true)  => format!("{} ≤ {}", v, s),
            // `jsge` is signed ≥ (reg form).
            (BranchKind::JsgeReg, false) => format!("¬ toSigned64 {} ≥ toSigned64 {}", va, sa),
            (BranchKind::JsgeReg, true)  => format!("toSigned64 {} ≥ toSigned64 {}", va, sa),
            // `jge` unsigned ≥, `jsgt`/`jslt` signed, `jset` bit-test (reg form).
            (BranchKind::JgeReg, false) => format!("¬ {} ≥ {}", v, s),
            (BranchKind::JgeReg, true)  => format!("{} ≥ {}", v, s),
            (BranchKind::JsgtReg, false) => format!("¬ toSigned64 {} > toSigned64 {}", va, sa),
            (BranchKind::JsgtReg, true)  => format!("toSigned64 {} > toSigned64 {}", va, sa),
            (BranchKind::JsltReg, false) => format!("¬ toSigned64 {} < toSigned64 {}", va, sa),
            (BranchKind::JsltReg, true)  => format!("toSigned64 {} < toSigned64 {}", va, sa),
            (BranchKind::JsetReg, false) => format!("¬ {} &&& {} ≠ 0", v, s),
            (BranchKind::JsetReg, true)  => format!("{} &&& {} ≠ 0", v, s),
            // `jsle` is signed ≤. Lean spec compares
            // `toSigned64 vDst ≤ toSigned64 vSrc`.
            (BranchKind::JsleReg, false) => format!("¬ toSigned64 {} ≤ toSigned64 {}", va, sa),
            (BranchKind::JsleReg, true)  => format!("toSigned64 {} ≤ toSigned64 {}", va, sa),
        }
    }
    fn name(&self, idx: usize) -> String { format!("h_branch{}", idx) }
}

/// A single emitted `have h_<pc> := <spec_name> <args>` line plus the
/// hypothesis name. Used to build the `sl_block_iter` proof body for
/// programs containing call_local (where `sl_block_auto` diverges).
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
    // Offset as a spec argument: parenthesise negatives so
    // `ldxb_same_spec .r10 -8 …` doesn't parse as `.r10 - 8`.
    let offl = lean_off(off);
    // Logical jump target (slot→logical resolved by the caller).
    let jt = jump_target.unwrap_or((pc as i64) + 1 + off);
    // `imm` is only ever a spec argument here (never arithmetic), so
    // render it parenthesised-when-negative: `and64_imm_spec .r1 -8`
    // would otherwise parse as `(and64_imm_spec .r1) - 8`.
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
    // Look up a register's current symbolic value as a Lean string.
    // If the register hasn't been read yet, fall back to its initial-
    // name convention (`baseAddr` for r1, `vR<N>Old` otherwise).
    let reg_val_lean = |r: u8| -> String {
        match state.regs.get(&r) {
            Some(e) => e.to_lean(),
            None    => reg_initial_name(r),
        }
    };
    let have_line = match insn.opc {
        LD_B_REG => {
            // ldxb_spec dst src off vOldDst baseAddr v pc hne
            // (no `< 2^64` bound — bytes always fit). On a first access
            // the loaded byte name is `oldMemB_<fresh>`; on a re-read of
            // an already-accessed cell, reuse its existing value var
            // (read_mem returns the same cell). Mirrors SymState::read_mem.
            let base_addr = reg_val_lean(src);
            let v_name = state.mem.iter()
                .find(|c| c.addr_base.to_lean() == base_addr
                       && c.addr_off == off
                       && c.width as u8 == Width::Byte as u8)
                .map(|c| c.value.atom_lean())
                .unwrap_or_else(|| format!("oldMemB_{}", state.fresh));
            if dst == src {
                // `ldxb r, [r]`: dst == src. The generic ldxb_spec would
                // emit two `r ↦ᵣ` atoms (unsatisfiable). The same-register
                // spec owns one register atom; baseAddr IS the dst's old value.
                format!(
                    "have {} := ldxb_same_spec {} {} ({}) {} {} (by decide)",
                    hyp_name, reg(dst), offl, base_addr, v_name, pc,
                )
            } else {
                let v_old_dst = state.regs.get(&dst)
                    .map(|e| e.to_lean())
                    .unwrap_or_else(|| reg_initial_name(dst));
                format!(
                    "have {} := ldxb_spec {} {} {} ({}) ({}) {} {} (by decide)",
                    hyp_name, reg(dst), reg(src), offl,
                    v_old_dst, base_addr, v_name, pc,
                )
            }
        }
        LD_DW_REG => {
            // ldxdw_spec dst src off vOldDst baseAddr v pc hne hv
            // Spec_call_for runs BEFORE step()'s read_mem; predict
            // the freshly-created mem variable name as `oldMemD_{N}`
            // where N is the current `state.fresh` (the next index
            // read_mem will allocate). The matching `< 2^64`
            // hypothesis the theorem signature surfaces is named
            // `h<var>_lt` (i.e., `holdMemD_<N>_lt`).
            let base_addr = reg_val_lean(src);
            // Re-read of an already-accessed cell reuses its existing
            // value (read_mem returns the same cell); only a first access
            // allocates oldMemD_<fresh>. A fresh / `InitMem`-valued cell
            // renders bare with its surfaced `h<name>_lt` bound (the
            // common case — kept byte-identical). A *reloaded compound*
            // value (a register spilled to the stack then loaded back) is
            // parenthesised and its `< 2^64` bound surfaced as the side
            // hyp `hReloadLt_<pc>` that `step` registers.
            let cell_val = state.mem.iter()
                .find(|c| c.addr_base.to_lean() == base_addr
                       && c.addr_off == off
                       && c.width as u8 == Width::Dword as u8)
                .map(|c| c.value.clone());
            let (v_arg, hv) = match &cell_val {
                Some(Expr::InitMem(name)) => (name.clone(), format!("h{}_lt", name)),
                Some(v) => (v.atom_lean(), format!("hReloadLt_{}", pc)),
                None => { let n = format!("oldMemD_{}", state.fresh); (n.clone(), format!("h{}_lt", n)) }
            };
            if dst == src {
                // `ldxdw r, [r]`: same-register variant (ldxdw_same_spec).
                format!(
                    "have {} := ldxdw_same_spec {} {} ({}) {} {} (by decide) {}",
                    hyp_name, reg(dst), offl, base_addr, v_arg, pc, hv,
                )
            } else {
                let v_old_dst = state.regs.get(&dst)
                    .map(|e| e.to_lean())
                    .unwrap_or_else(|| reg_initial_name(dst));
                format!(
                    "have {} := ldxdw_spec {} {} {} ({}) ({}) {} {} (by decide) {}",
                    hyp_name, reg(dst), reg(src), offl,
                    v_old_dst, base_addr, v_arg, pc, hv,
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
            let cell_val = state.mem.iter()
                .find(|c| c.addr_base.to_lean() == base_addr
                       && c.addr_off == off
                       && c.width as u8 == w as u8)
                .map(|c| c.value.clone());
            let (v_arg, hv) = match &cell_val {
                Some(Expr::InitMem(name)) => (name.clone(), format!("h{}_lt", name)),
                Some(v) => (v.atom_lean(), format!("hReloadLt_{}", pc)),
                None => { let n = format!("{}_{}", pfx, state.fresh); (n.clone(), format!("h{}_lt", n)) }
            };
            let v_old_dst = state.regs.get(&dst)
                .map(|e| e.to_lean())
                .unwrap_or_else(|| reg_initial_name(dst));
            format!(
                "have {} := {} {} {} {} ({}) ({}) {} {} (by decide) {}",
                hyp_name, spec, reg(dst), reg(src), offl,
                v_old_dst, base_addr, v_arg, pc, hv,
            )
        }
        ST_B_REG | ST_H_REG | ST_W_REG | ST_DW_REG => {
            // stx{b,h,w,dw}_spec baseReg valReg off baseAddr vSrc oldV pc
            // (all four share this arg shape; only the width and old-cell
            // var prefix differ).
            let (spec, w, pfx) = match insn.opc {
                ST_B_REG  => ("stxb_spec",  Width::Byte,     "oldMemB"),
                ST_H_REG  => ("stxh_spec",  Width::Halfword, "oldMemH"),
                ST_W_REG  => ("stxw_spec",  Width::Word,     "oldMemW"),
                ST_DW_REG => ("stxdw_spec", Width::Dword,    "oldMemD"),
                _ => unreachable!(),
            };
            let base_addr = reg_val_lean(dst);
            let v_src = reg_val_lean(src);
            let key_addr = base_addr.clone();
            // `atom_lean` parenthesises a compound prior value (e.g. a
            // `toU64 0` left by an earlier imm store) while leaving a
            // bare `oldMem*_N` / fresh name unparenthesised (so the common
            // case stays byte-identical).
            let old_v = state.mem.iter()
                .find(|c| c.addr_base.to_lean() == key_addr
                       && c.addr_off == off
                       && c.width as u8 == w as u8)
                .map(|c| c.value.atom_lean())
                // Cell not yet in state.mem → this store is the FIRST
                // access to it. step()'s write_mem will call read_mem,
                // allocating `oldMem*_{fresh}`. Predict that name (same
                // as the load specs) instead of an unresolved `?oldV`.
                .unwrap_or_else(|| format!("{}_{}", pfx, state.fresh));
            format!(
                "have {} := {} {} {} {} ({}) ({}) {} {}",
                hyp_name, spec, reg(dst), reg(src), offl,
                base_addr, v_src, old_v, pc,
            )
        }
        ADD64_IMM => {
            // add64_imm_spec dst imm vOld pc hne
            let v_old = reg_val_lean(dst);
            format!(
                "have {} := add64_imm_spec {} {} ({}) {} (by decide)",
                hyp_name, reg(dst), imm, v_old, pc,
            )
        }
        AND64_IMM => {
            // and64_imm_spec dst imm vOld pc hne — same shape as add64_imm.
            let v_old = reg_val_lean(dst);
            format!(
                "have {} := and64_imm_spec {} {} ({}) {} (by decide)",
                hyp_name, reg(dst), imm, v_old, pc,
            )
        }
        LSH64_IMM => {
            // lsh64_imm_spec dst imm vOld pc hne
            let v_old = reg_val_lean(dst);
            format!(
                "have {} := lsh64_imm_spec {} {} ({}) {} (by decide)",
                hyp_name, reg(dst), imm, v_old, pc,
            )
        }
        RSH64_IMM => {
            // rsh64_imm_spec dst imm vOld pc hne
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
        // Div/mod imm-form: extra `hnz : toU64 imm ≠ 0` — the immediate is
        // a concrete literal, so `(by decide)` discharges it (and fails
        // loudly on a literal `div r, 0`).
        DIV64_IMM | MOD64_IMM => {
            let v_old = reg_val_lean(dst);
            let spec = if insn.opc == DIV64_IMM { "div64_imm_spec" } else { "mod64_imm_spec" };
            format!(
                "have {} := {} {} {} ({}) {} (by decide) (by decide)",
                hyp_name, spec, reg(dst), imm, v_old, pc,
            )
        }
        NEG64 => {
            // neg64_spec dst vOld pc hne (no operand).
            let v_old = reg_val_lean(dst);
            format!(
                "have {} := neg64_spec {} ({}) {} (by decide)",
                hyp_name, reg(dst), v_old, pc,
            )
        }
        // div/mod reg-form: the divisor `v` is symbolic, so the spec's
        // `hnz : v ≠ 0` (64) / `v % U32_MODULUS ≠ 0` (32) is surfaced as
        // a theorem hypothesis named `hnz_<pc>` (registered by `step`).
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
            // The old byte value lives in state.mem keyed by the
            // base-address expression + offset + byte width. Same
            // pattern as ST_DW_REG.
            let key_addr = base_addr.clone();
            let old_v = state.mem.iter()
                .find(|c| c.addr_base.to_lean() == key_addr
                       && c.addr_off == off
                       && c.width as u8 == Width::Byte as u8)
                .map(|c| c.value.atom_lean())
                .unwrap_or_else(|| format!("oldMemB_{}", state.fresh));
            format!(
                "have {} := stb_spec {} {} {} ({}) ({}) {}",
                hyp_name, reg(dst), offl, imm, base_addr, old_v, pc,
            )
        }
        ST_H_IMM => {
            // sth_spec baseReg off imm baseAddr oldHalfVal pc
            let base_addr = reg_val_lean(dst);
            let key_addr = base_addr.clone();
            let old_v = state.mem.iter()
                .find(|c| c.addr_base.to_lean() == key_addr
                       && c.addr_off == off
                       && c.width as u8 == Width::Halfword as u8)
                .map(|c| c.value.atom_lean())
                .unwrap_or_else(|| format!("oldMemH_{}", state.fresh));
            format!(
                "have {} := sth_spec {} {} {} ({}) ({}) {}",
                hyp_name, reg(dst), offl, imm, base_addr, old_v, pc,
            )
        }
        ST_W_IMM => {
            // stw_spec baseReg off imm baseAddr oldWordVal pc
            let base_addr = reg_val_lean(dst);
            let key_addr = base_addr.clone();
            let old_v = state.mem.iter()
                .find(|c| c.addr_base.to_lean() == key_addr
                       && c.addr_off == off
                       && c.width as u8 == Width::Word as u8)
                .map(|c| c.value.atom_lean())
                .unwrap_or_else(|| format!("oldMemW_{}", state.fresh));
            format!(
                "have {} := stw_spec {} {} {} ({}) ({}) {}",
                hyp_name, reg(dst), offl, imm, base_addr, old_v, pc,
            )
        }
        ST_DW_IMM => {
            // stdw_spec baseReg off imm baseAddr oldDwordVal pc
            let base_addr = reg_val_lean(dst);
            let key_addr = base_addr.clone();
            let old_v = state.mem.iter()
                .find(|c| c.addr_base.to_lean() == key_addr
                       && c.addr_off == off
                       && c.width as u8 == Width::Dword as u8)
                .map(|c| c.value.atom_lean())
                .unwrap_or_else(|| format!("oldMemD_{}", state.fresh));
            format!(
                "have {} := stdw_spec {} {} {} ({}) ({}) {}",
                hyp_name, reg(dst), offl, imm, base_addr, old_v, pc,
            )
        }
        ADD64_REG => {
            // add64_reg_spec dst src vOld v pc hne
            let v_old = reg_val_lean(dst);
            let v_src = reg_val_lean(src);
            format!(
                "have {} := add64_reg_spec {} {} ({}) ({}) {} (by decide)",
                hyp_name, reg(dst), reg(src), v_old, v_src, pc,
            )
        }
        SUB64_REG => {
            // sub64_reg_spec dst src vOld v pc hne — same shape as add.
            let v_old = reg_val_lean(dst);
            let v_src = reg_val_lean(src);
            format!(
                "have {} := sub64_reg_spec {} {} ({}) ({}) {} (by decide)",
                hyp_name, reg(dst), reg(src), v_old, v_src, pc,
            )
        }
        // Wrapping/bitwise reg-form ALU ops. All share the spec shape
        // `<op>_reg_spec dst src vOld v pc hne` (hne : dst ≠ .r10).
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
            // mov64_reg_spec dst src vOld v pc hne — register copy.
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
            // `cs` is the CURRENT call stack (the frames already pushed) —
            // empty for a top-level call, [outer…] for a nested one. The
            // push of this frame happens in step(), so `state.call_stack`
            // here is exactly the pre-call stack = `cs`.
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
            // The explicit `r6Old..r10Old` args are the CURRENT (exit-time)
            // register values — what the `r ↦ᵣ` atoms hold in the
            // exit_pops PRE, before it restores them.
            let r6 = reg_val_lean(6); let r7 = reg_val_lean(7);
            let r8 = reg_val_lean(8); let r9 = reg_val_lean(9);
            let r10 = reg_val_lean(10);
            // `frame` = the top of the call stack (the frame this exit
            // pops): retPc = `<callpc> + 1` and savedR6..savedR10 = the
            // CALL-TIME snapshot (NOT current — a callee may clobber
            // r6..r9). `cs` = the REST of the stack below it (empty for a
            // top-level call, [outer…] for a nested one).
            let n = state.call_stack.len();
            let (call_pc, saved) = state.call_stack.last()
                .map(|(p, s)| (*p, s.clone()))
                .unwrap_or((0, std::array::from_fn(|_| Expr::InitReg("?".into()))));
            let (sv6, sv7, sv8, sv9, sv10) = (
                saved[0].atom_lean(), saved[1].atom_lean(), saved[2].atom_lean(),
                saved[3].atom_lean(), saved[4].atom_lean());
            let cs = render_callstack(&state.call_stack[..n.saturating_sub(1)]);
            // exit_pops' post projects `frame.savedR6..savedR10`, which
            // reduce by iota to the `⟨…⟩` fields — but sl_block_iter's
            // structural match doesn't run iota, so `dsimp` forces it.
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
        branch_taken: Option<bool>, jump_target: Option<i64>) -> Result<bool, String> {
    use ebpf::*;
    let (dst, src, off, imm) = (insn.dst, insn.src, insn.off as i64, insn.imm);
    // Logical jump target for path-hypothesis bookkeeping.
    let jt = || jump_target.unwrap_or((pc.unwrap_or(0) as i64) + 1 + off) as usize;
    match insn.opc {
        LD_B_REG => {
            let raw = state.read_mem(src, off, Width::Byte);
            // Byte load narrows: r := raw % 256.
            state.write_reg(dst, Expr::Mod(Box::new(raw), 256));
        }
        LD_H_REG => {
            // `ldxh_spec` post is `dst ↦ᵣ v` (the ↦U16 cell value, raw —
            // bounded < 2^16 by the surfaced hv). Mirrors ldxdw, not ldxb.
            let raw = state.read_mem(src, off, Width::Halfword);
            state.write_reg(dst, raw);
        }
        LD_W_REG => {
            // `ldxw_spec` post is `dst ↦ᵣ v` (the ↦U32 cell value, raw).
            let raw = state.read_mem(src, off, Width::Word);
            state.write_reg(dst, raw);
        }
        LD_DW_REG => {
            let raw = state.read_mem(src, off, Width::Dword);
            // A reloaded *compound* dword (a spilled register read back) is
            // not a fresh `oldMemD_N` var, so `read_mem` surfaced no
            // `< 2^64` bound for it. Register the matching `hReloadLt_<pc>`
            // side hyp that `spec_call_for` references as the spec's `hv`.
            if !matches!(raw, Expr::InitMem(_)) {
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
            // Byte store narrows: mem := r % 256.
            state.write_mem(dst, off, Width::Byte, Expr::Mod(Box::new(cur), 256));
        }
        ST_H_REG => {
            // `stxh_spec` post is `↦U16 vSrc` (the width notation truncates;
            // the cell value is the raw register value, like stxdw's ↦U64).
            let cur = state.read_reg(src);
            state.write_mem(dst, off, Width::Halfword, cur);
        }
        ST_W_REG => {
            // `stxw_spec` post is `↦U32 vSrc` (raw value; ↦U32 truncates).
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
            // Write a constant byte (toU64 imm % 256) at [dst + off].
            state.write_mem(dst, off, Width::Byte,
                Expr::Mod(Box::new(Expr::ToU64(Box::new(Expr::Const(imm)))), 256));
        }
        ST_H_IMM => {
            // Write a constant halfword (toU64 imm % 2^16) at [dst + off].
            state.write_mem(dst, off, Width::Halfword, Expr::StHalfImm(imm));
        }
        ST_W_IMM => {
            // Write a constant word (toU64 imm % 2^32) at [dst + off].
            state.write_mem(dst, off, Width::Word, Expr::StWordImm(imm));
        }
        ST_DW_IMM => {
            // Write a constant dword (toU64 imm % 2^64) at [dst + off].
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
            // lddw is semantically mov64-from-immediate (the merged
            // 64-bit value is already in `imm`).
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
        // Bitwise / shift reg-form ALU: render the result exactly as the
        // matching `*_reg_spec` writes its post (an `Expr::Raw` blob).
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
        // Bitwise/mul/div/mod/neg imm-form ALU — render as the matching
        // `*_imm_spec` / `neg64_spec` post.
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
        // 32-bit imm ALU — render as the matching `*32_imm_spec` post.
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
        // 32-bit reg ALU — render as the matching `*32_reg_spec` post.
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
        // div/mod reg-form: surface the divisor's non-zeroness as a
        // `hnz_<pc>` hypothesis (the divisor `src` is symbolic, read
        // before the `dst` write so its rendering matches the spec arg).
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
        // Conditional jumps on an immediate. Modelled as "happy path
        // = fall-through" by default (the common shape for guard
        // checks at function start). Records a path hypothesis the
        // theorem signature will surface; doesn't change reg/mem
        // state. Caller invents a path-hypothesis variable name.
        JEQ64_IMM | JEQ32_IMM => {
            let r = state.read_reg(dst);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JeqImm, dst_value: r, src_value: None, imm,
                taken: branch_taken.unwrap_or(false),
                target_pc: jt(),
            });
        }
        JNE64_IMM | JNE32_IMM => {
            let r = state.read_reg(dst);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JneImm, dst_value: r, src_value: None, imm,
                taken: branch_taken.unwrap_or(false),
                target_pc: jt(),
            });
        }
        JGT64_IMM | JGT32_IMM => {
            let r = state.read_reg(dst);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JgtImm, dst_value: r, src_value: None, imm,
                taken: branch_taken.unwrap_or(false),
                target_pc: jt(),
            });
        }
        JSGT64_IMM | JSGT32_IMM => {
            let r = state.read_reg(dst);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JsgtImm, dst_value: r, src_value: None, imm,
                taken: branch_taken.unwrap_or(false),
                target_pc: jt(),
            });
        }
        JSLE64_IMM | JSLE32_IMM => {
            let r = state.read_reg(dst);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JsleImm, dst_value: r, src_value: None, imm,
                taken: branch_taken.unwrap_or(false),
                target_pc: jt(),
            });
        }
        JLT64_IMM | JLT32_IMM => {
            let r = state.read_reg(dst);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JltImm, dst_value: r, src_value: None, imm,
                taken: branch_taken.unwrap_or(false),
                target_pc: jt(),
            });
        }
        JLE64_IMM | JLE32_IMM => {
            let r = state.read_reg(dst);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JleImm, dst_value: r, src_value: None, imm,
                taken: branch_taken.unwrap_or(false),
                target_pc: jt(),
            });
        }
        JSLT64_IMM | JSLT32_IMM => {
            let r = state.read_reg(dst);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JsltImm, dst_value: r, src_value: None, imm,
                taken: branch_taken.unwrap_or(false),
                target_pc: jt(),
            });
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
                taken: branch_taken.unwrap_or(false),
                target_pc: jt(),
            });
        }
        JEQ64_REG | JEQ32_REG => {
            let rd = state.read_reg(dst);
            let rs = state.read_reg(src);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JeqReg, dst_value: rd, src_value: Some(rs), imm: 0,
                taken: branch_taken.unwrap_or(false),
                target_pc: jt(),
            });
        }
        JNE64_REG | JNE32_REG => {
            let rd = state.read_reg(dst);
            let rs = state.read_reg(src);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JneReg, dst_value: rd, src_value: Some(rs), imm: 0,
                taken: branch_taken.unwrap_or(false),
                target_pc: jt(),
            });
        }
        JLT64_REG | JLT32_REG => {
            let rd = state.read_reg(dst);
            let rs = state.read_reg(src);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JltReg, dst_value: rd, src_value: Some(rs), imm: 0,
                taken: branch_taken.unwrap_or(false),
                target_pc: jt(),
            });
        }
        JSLE64_REG | JSLE32_REG => {
            let rd = state.read_reg(dst);
            let rs = state.read_reg(src);
            state.branch_hyps.push(BranchHyp {
                kind: BranchKind::JsleReg, dst_value: rd, src_value: Some(rs), imm: 0,
                taken: branch_taken.unwrap_or(false),
                target_pc: jt(),
            });
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
                taken: branch_taken.unwrap_or(false),
                target_pc: jt(),
            });
        }
        JA => { /* unconditional fall-through reset is handled by the caller's PC walk */ }
        // call_local target: pushes a frame, bumps r10 by 0x1000,
        // redirects PC to target. The PC redirect happens in the
        // walker; here we just update the symbolic state per
        // `call_local_spec` in InstructionSpecs/CallReturn.lean.
        CALL_IMM => {
            state.saw_call = true;
            // r6..r9 must be in scope (they're framed by call_local_spec).
            // Snapshot the call-time r6..r10 — this is the exact frame the
            // `call_local` pushes and the matching `exit_pops` must restore.
            let r6 = state.read_reg(6); let r7 = state.read_reg(7);
            let r8 = state.read_reg(8); let r9 = state.read_reg(9);
            // r10 is bumped by 0x1000 (one Solana V0 stack frame).
            // Use Nat.add (matching call_local_spec's `r10V + 0x1000`)
            // rather than wrapAdd, so the chain composes cleanly.
            let r10_old = state.read_reg(10);
            state.write_reg(10, Expr::NatAdd(
                Box::new(r10_old.clone()),
                Box::new(Expr::Const(0x1000)),
            ));
            // Store the CALL pc (not pc+1): the frame's retPc renders as
            // `<callpc> + 1` to match what `call_local_spec` pushes (Lean
            // keeps it unreduced); the walk's resume PC is callpc + 1.
            let call_pc = pc.unwrap_or(0);
            state.call_stack.push((call_pc, [r6, r7, r8, r9, r10_old]));
        }
        EXIT => {
            if state.call_stack.is_empty() {
                // Top-level termination — caller decides what to do.
                return Ok(false);
            } else {
                // Nested exit: pop the frame. Per exit_pops_spec, r6..r10
                // are restored to their pre-call values. In the symbolic
                // walk, the callee should not have modified r6..r10 (Solana
                // ABI). We undo r10's +0x1000 bump from the matching
                // call_local; if the callee touched r6..r9 in violation
                // of the ABI, the chain won't compose and the user will
                // see the failure as a sl_block_iter residual.
                let _ = state.call_stack.pop();
                let r10_cur = state.read_reg(10);
                state.write_reg(10, Expr::WrapSub(
                    Box::new(r10_cur),
                    Box::new(Expr::Const(0x1000)),
                ));
                // step() returns Ok(true) so the walker continues; the
                // walker resumes at the popped PC.
            }
        }
        opc => return Err(format!("symbolic executor: opcode 0x{:02x} not yet modelled", opc)),
    }
    Ok(true)
}

/// Concatenate the pre-atom list into a Lean `**`-separated SL
/// expression. Empty list renders as `emp`. `subst` substitutes
/// complex address-base expressions (matched on rendered form) with
/// the abstracted parameter name.
fn atoms_to_lean(
    atoms: &[Atom],
    subst: &std::collections::BTreeMap<String, String>,
) -> String {
    if atoms.is_empty() { return "emp".to_string(); }
    let parts: Vec<String> = atoms.iter().map(|a| atom_to_lean_with_subst(a, subst)).collect();
    parts.join(" **\n      ")
}

/// Fold abstraction expressions inside a rendered string, replacing
/// each abstraction's RHS with its parameter name — including when it
/// appears as a SUB-expression (e.g. `addr0` inside a discriminator
/// value `(addr0 <<< …) …`). Longest-first so a parent is folded
/// before its sub-terms. This mirrors what `sl_rw_abs` does to the
/// proof chain, so goal atoms and chain atoms stay in the same form.
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

/// Word-boundary-aware string replace: substitutes `needle` with
/// `repl` only at positions where the surrounding characters aren't
/// alphanumerics/underscore. Without this, an abstraction whose
/// rendered form is `toU64 3` would corrupt `toU64 32` into `addr02`.
/// Lean identifiers and numerals are word-char runs, so a boundary
/// check is enough to keep replacements at real sub-term edges.
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

/// Render one atom, substituting any matching addr_base expression
/// with its abstracted parameter name.
fn atom_to_lean_with_subst(
    atom: &Atom,
    subst: &std::collections::BTreeMap<String, String>,
) -> String {
    // Substitute the rendered form of a value-expression, folding any
    // abstraction (whole OR sub-expression) to its param so the goal
    // matches the sl_rw_abs-folded chain.
    let sub = |e: &Expr| -> String {
        fold_abstractions(e.to_lean(), subst)
    };
    match atom {
        Atom::Reg(r, v) => {
            format!("(.{} ↦ᵣ {})", reg_lit(*r), sub(v))
        }
        Atom::Mem { addr_base, addr_off, width, value } => {
            let rendered = addr_base.to_lean();
            let addr_str = subst.get(&rendered)
                .map(|p| p.clone())
                .unwrap_or_else(|| addr_base.atom_lean());
            format!(
                "(effectiveAddr {} {} {} {})",
                addr_str, lean_off(*addr_off), width.lean_arrow(), sub(value),
            )
        }
        Atom::Bytes { addr, value } => {
            // `memBytesIs` takes a bare Nat address (no effectiveAddr).
            // Fold the address through the abstraction map — including
            // SUB-expressions (e.g. `wrapAdd baseAddr 8` → `addr4`),
            // exactly as register/mem *values* are folded via `sub`. The
            // address isn't itself an abstraction (no fixed-width atom
            // owns it), so a whole-address `subst.get` wouldn't catch the
            // inner `addrK`; `fold_abstractions` does, keeping the goal
            // atom in the same shape the sl_rw_abs-rewritten chain (and
            // the value `generalize`) produces.
            format!("({} ↦Bytes {})", sub(addr), value.to_lean())
        }
    }
}

/// The BPF program heap: `[MM_HEAP_START, MM_HEAP_START + 0x8000)`.
const HEAP_START_I: i64 = 0x300000000;
const HEAP_END_I:   i64 = 0x300000000 + 0x8000;

/// If a memory cell's address is a flat heap constant (an `lddw`-loaded
/// `MM_HEAP_START`-range address with offset `off`), return its absolute
/// heap address. Used to fold heap cells into the `heapBumpPtr` /
/// `heapBlockU64` allocator predicates.
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

/// Render an atom for the heap-allocation corollary: a `u64` heap cell at
/// `MM_HEAP_START` becomes `heapBumpPtr v` (the bump-position slot), any
/// other heap cell becomes `heapBlockU64 addr v` (an allocated block);
/// everything else renders as usual.
fn atom_to_lean_heap(
    atom: &Atom,
    subst: &std::collections::BTreeMap<String, String>,
) -> String {
    if let Atom::Mem { addr_base, addr_off, width, value } = atom {
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

/// Emit the lift artifacts for a `sol_memset_(dst=r1, fill=r2, count=r3)`
/// host syscall at logical PC `pc`. Shaped to `call_sol_memset_spec`:
/// adds a `↦Bytes` precondition atom at `r1`'s current value (a fresh
/// `ByteArray` of size `r3`), records the post (the region filled with
/// `r2`'s low byte) and `r0 := 0`. The model's `syscallCu` for memory
/// ops is data-dependent (∝ r3), so the CU bound (`nCu`) and the blob
/// size are surfaced as theorem hypotheses and threaded into the spec
/// call rather than discharged here.
fn emit_sol_memset(
    state: &mut SymState,
    spec_calls: &mut Vec<SpecCall>,
    block_pcs: &mut Vec<usize>,
    pc: usize,
) {
    // Read the operands at the call (pre-state). `read_reg` records each
    // in `pre` if not already present, so the chain frames them through
    // to this step.
    let r0v = state.read_reg(0);
    let r1v = state.read_reg(1);
    let r2v = state.read_reg(2);
    let r3v = state.read_reg(3);

    let idx = state.fresh; state.fresh += 1;
    let bs_name  = format!("memsetBs_{}", idx);
    let bs_sz    = format!("hmemsetBs_{}_sz", idx);
    let ncu_name = format!("nCuMemset{}", idx);
    let hcu_name = format!("hCuMemset{}", idx);

    // Pre atom: `r1V ↦Bytes memsetBs_idx`, size pinned to `r3V`.
    let size_rendered = r3v.atom_lean();
    // Overlap accounting for the blob's byte footprint. A symbolic
    // count can't be span-checked — record a 1-byte footprint at the
    // base (catches exact-base collisions; full symbolic-length
    // support is part of the H8 byte-aliasing work).
    let blob_len = const_of_expr(&r3v).unwrap_or(1).max(1);
    state.note_access(&r1v, 0, blob_len, format!("blob:{}", r1v.to_lean()));
    state.pre.push(Atom::Bytes {
        addr: r1v.clone(),
        value: BytesVal::Sym(bs_name.clone()),
    });
    state.memset_blobs.push((bs_name.clone(), size_rendered));
    state.syscall_cu_vars.push((ncu_name.clone(), hcu_name.clone(), ".sol_memset"));
    state.syscall_pcs.insert(pc, ".sol_memset");

    // Post effect: `r0 := 0`; the blob becomes `replicateByte (r2V%256) r3V`.
    state.write_reg(0, Expr::Const(0));
    state.byte_blob_post.insert(
        r1v.to_lean(),
        BytesVal::Replicate { fill: r2v.clone(), count: r3v.clone() },
    );

    // The spec call:
    //   call_sol_memset_spec r0Old r1V r2V r3V pc nCu bsOld hbs hCu
    let have_line = format!(
        "have h_{pc} := call_sol_memset_spec {r0} {r1} {r2} {r3} {pc} {ncu} {bs} {hbs} {hcu}",
        pc = pc,
        r0 = r0v.atom_lean(), r1 = r1v.atom_lean(),
        r2 = r2v.atom_lean(), r3 = r3v.atom_lean(),
        ncu = ncu_name, bs = bs_name, hbs = bs_sz, hcu = hcu_name,
    );
    spec_calls.push(SpecCall { hyp_name: format!("h_{}", pc), have_line });
    block_pcs.push(pc);
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

/// Build the postcondition atom list: same shape as pre, but each atom
/// reflects the symbolic value at the end of the walk.
fn post_atoms(initial_pre: &[Atom], state: &SymState) -> Vec<Atom> {
    let mut out = Vec::with_capacity(initial_pre.len());
    for atom in initial_pre {
        match atom {
            Atom::Reg(r, _) => {
                let v = state.regs.get(r).cloned()
                    .unwrap_or_else(|| Expr::InitReg(reg_initial_name(*r)));
                out.push(Atom::Reg(*r, v));
            }
            Atom::Mem { addr_base, addr_off, width, .. } => {
                // Look up the cell by (rendered-addr, off, width) key —
                // the same scheme `read_mem`/`write_mem` use.
                let key = (addr_base.to_lean(), *addr_off, *width as u8);
                let v = state.mem.iter()
                    .find(|c| c.key() == key)
                    .map(|c| c.value.clone())
                    .unwrap_or_else(|| Expr::InitMem("?".to_string()));
                out.push(Atom::Mem {
                    addr_base: addr_base.clone(),
                    addr_off:  *addr_off,
                    width:     *width,
                    value:     v,
                });
            }
            Atom::Bytes { addr, value } => {
                // A memory syscall rewrote this blob: look up its post
                // contents by rendered address (set in `byte_blob_post`).
                let post_val = state.byte_blob_post.get(&addr.to_lean())
                    .cloned()
                    .unwrap_or_else(|| value.clone());
                out.push(Atom::Bytes { addr: addr.clone(), value: post_val });
            }
        }
    }
    out
}

/// Build the region-requirement clause: for each memory atom in pre,
/// emit `rt.containsRange addr width = true` (and `containsWritable`
/// for any atom we mutated).
fn region_req(
    _pre: &[Atom],
    state: &SymState,
    subst: &std::collections::BTreeMap<String, String>,
) -> String {
    let mut clauses = Vec::new();
    // Walk-order rr contributions: each load → containsRange; each
    // store → containsWritable. Order matches what slBlockIter
    // produces by left-folding per chain step.
    for (addr_base, addr_off, width, writable) in &state.rr_walk {
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
        // Left-associative: `((A ∧ B) ∧ C) ∧ D`. `sl_block_iter`'s
        // chain composition produces this shape (each step's rr is
        // ∧-merged on the left); to keep the goal isDefEq to the
        // chain, the emitted goal needs the same parenthesisation.
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

// Per-binary context shared across arms in batch mode. Building
// `Executable` + `Analysis` for a large program (e.g. p_token at
// ~80KB compiled) is ~10s; reusing the same context for every arm
// keeps batch runs proportional to the number of arms, not the
// product of arms × binary size.
struct BinaryCtx {
    executable:  Executable<NoopCtx>,
    text_offset: u64,
    text_bytes:  Vec<u8>,
    insns:       Vec<ebpf::Insn>,
    /// `logical_to_slot[i]` = the 8-byte slot index where logical
    /// instruction `insns[i]` begins. lddw occupies 2 slots, so the
    /// logical index and slot index diverge once any lddw appears.
    logical_to_slot: Vec<usize>,
    /// `slot_to_logical[s]` = the logical index of the instruction
    /// occupying slot `s` (both slots of an lddw map to its logical
    /// index). `None` for slots past the end. Mirror of the slotMap
    /// in `SVM/SBPF/Decode.lean` pass 1 — needed because jump `off`
    /// fields are slot-relative but our `insns`/CodeReq PCs are
    /// logical indices.
    slot_to_logical: Vec<Option<usize>>,
}

/// Resolve a slot-relative jump from logical PC `logical_pc` with raw
/// offset `off` to the *logical* target PC. Mirrors how
/// `Decode.decodeProgram` rewrites jump targets, so the rendered
/// `.jXX ... target` matches what `native_decide` proves. Falls back
/// to `logical_pc + 1 + off` when the maps don't cover the PC (e.g.
/// the synthetic two_op fixture has no lddw, so slot == logical).
fn resolve_jump_target(ctx: &BinaryCtx, logical_pc: usize, off: i64) -> i64 {
    match ctx.logical_to_slot.get(logical_pc) {
        Some(&slot) => {
            let target_slot = slot as i64 + 1 + off;
            if target_slot < 0 {
                return target_slot; // out of range; render as-is to fail loudly
            }
            match ctx.slot_to_logical.get(target_slot as usize) {
                Some(Some(logical)) => *logical as i64,
                // Target slot is past the end (e.g. exit fall-off) or the
                // middle of an lddw (malformed) — fall back to the raw sum.
                _ => target_slot,
            }
        }
        None => logical_pc as i64 + 1 + off,
    }
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
    let mut logical_to_slot = Vec::new();
    let mut slot_to_logical: Vec<Option<usize>> = Vec::new();
    let mut pc = 0;
    while pc * ebpf::INSN_SIZE < text_bytes.len() {
        let mut insn = ebpf::get_insn(&text_bytes, pc);
        let opc  = insn.opc;
        // lddw spans 2 slots; `get_insn` only reads the low 32 bits of
        // the immediate. Merge in the high half from the next slot so
        // the rendered `.lddw dst imm` matches decodeProgram's output.
        if opc == ebpf::LD_DW_IMM {
            ebpf::augment_lddw_unchecked(&text_bytes, &mut insn);
        }
        let logical = insns.len();
        logical_to_slot.push(pc);
        let span = if opc == ebpf::LD_DW_IMM { 2 } else { 1 };
        // Map every slot this instruction occupies back to its logical index.
        for s in pc..pc + span {
            while slot_to_logical.len() <= s { slot_to_logical.push(None); }
            slot_to_logical[s] = Some(logical);
        }
        insns.push(insn);
        pc += span;
    }
    Ok(BinaryCtx { executable, text_offset, text_bytes, insns, logical_to_slot, slot_to_logical })
}

// ════════════════════════════════════════════════════════════════
// Refinement codegen — emit a per-arm asm-refines-intrinsic theorem
// alongside the lift, mechanizing the hand recipe used for
// Transfer / TransferChecked / MintTo / Burn. Given the lift's atoms +
// the IDL arm name, it detects the mutated account cells, classifies
// each account's codec fields (token vs mint), picks the matching
// aggregation lemma, builds the frame, and emits the
// `AsmRefines…`-obligation theorem. Returns `(module_name, lean)` or
// `None` for arms not in the intrinsic registry / with an unrecognised
// account layout.
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
        // First NON-token intrinsic: a single-field counter account whose
        // codec is one `u64` (coarse = fine, no aggregation). The constant
        // `+1` delta is handled by the `counterIncrement` clean-up + the
        // dedicated `emit_counter_refinement` path.
        "counterIncrement" => Some(RefineSpec {
            asm_pred: "AsmRefinesCounterIncrement",
            accounts: &[("counter", CodecKind::Counter)],
        }),
        // Multi-field NON-token account (e.g. {owner:Pubkey, total:u64,
        // bump:u8}). The layout-general `AsmRefinesFieldUpdate` obligation
        // is proved by reshaping the codec via `account_agg` and framing
        // the untouched fields — `emit_vault_refinement`, IDL-driven.
        "VaultIncrement" => Some(RefineSpec {
            asm_pred: "AsmRefinesFieldUpdate",
            accounts: &[("vault", CodecKind::Vault)],
        }),
        _ => None,
    }
}

/// Whether `arm` refines a codec with a constant `+1` delta (counter or
/// vault). Gates the constant-delta balance cleaning so other arms (e.g.
/// `two_op`'s `+1`) stay byte-identical.
fn is_const_delta_arm(arm: Option<&str>) -> bool {
    arm.and_then(refine_registry).map_or(false, |s| {
        s.accounts.iter().all(|(_, c)| matches!(c, CodecKind::Counter | CodecKind::Vault))
    })
}

/// Value of a memory cell at `(base_raw, off)` with the given byte-ness,
/// if the lift owns it.
fn cell_val<'a>(atoms: &'a [Atom], base_raw: &str, off: i64, byte: bool) -> Option<&'a Expr> {
    for a in atoms {
        if let Atom::Mem { addr_base, addr_off, width, value } = a {
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

/// Output of building one account's aggregation + frame.
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
    // Token-codec aggregation: (lemma_name, owner_owned, rest_pattern).
    // `Some` for token accounts (drives mechanically emitting the
    // aggregation module); `None` for mint accounts (hand-written for now).
    agg: Option<(String, bool, Vec<i64>)>,
    // Discharge-route field-list atoms: this account's `codecCoarse base
    // (tokenFields/mintFields …)` in the pre- and post-state. The keystone
    // (`tokenAcctBalance_codec` / `mintSupply_codec`) shows the bespoke
    // `tokenAcctBalanceOf` / `mintSupplyOf` atom equals these, so the kept
    // `AsmRefinesToken*` obligation reshapes to a layout-general field-list
    // obligation — the `refines_field` corollary the codegen emits.
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
    // Returns `(refine_module, refine_lean, optional (agg_module, agg_lean))`.
) -> Option<(String, String, Option<(String, String)>)> {
    let spec = refine_registry(arm_name)?;

    // Counter codec: a single `u64` field with a constant `+1` delta and
    // no aggregation (coarse = fine). A dedicated path keeps the token /
    // mint codegen byte-for-byte unchanged.
    if spec.accounts.iter().all(|(_, c)| matches!(c, CodecKind::Counter)) {
        return emit_counter_refinement(&spec, lift_module, pre, post_clean,
            abs_subst, vars, n_cu, start_pc, exit_pc);
    }

    // Vault codec: a multi-field NON-token account (IDL layout). Owns the
    // updated `u64` field, frames the rest, reshapes via `account_agg`.
    if spec.accounts.iter().all(|(_, c)| matches!(c, CodecKind::Vault)) {
        return emit_vault_refinement(&spec, lift_module, pre, post_clean,
            abs_subst, vars, n_cu, start_pc, exit_pc, idl);
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

    // ── Assign each registry account to a mutated cell ──────────────
    // Token amount cells own a mint dword at off-64; mint supply cells
    // own the is_initialized byte at off+9 (= base+45).
    let is_mint_mut = |m: &MutCell| cell_val(pre, &m.base_raw, m.off + 9, true).is_some();
    let is_tok_mut  = |m: &MutCell| cell_val(pre, &m.base_raw, m.off - 64, false).is_some();
    let mut used = vec![false; muts.len()];
    let mut builds: Vec<AcctBuild> = Vec::new();
    let mut barray_ctr = 0u32;
    let mut framed_owner = false;
    for (role, codec) in spec.accounts {
        // Pick an unused mutated cell matching this codec; for two
        // same-codec token accounts (Transfer), src=sub, dst=add.
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

    // Mechanically emit the token-codec aggregation module (the
    // `*_account_eq` lemmas the refinement imports), from the detected
    // owned-byte patterns. Token codec uses the shared
    // `PToken.TransferAggregation`; mint accounts (agg: None) still rely
    // on the hand-written `PToken.MintAggregation`.
    // Token account rest-region start + size from the IDL layout (step a);
    // fall back to SPL token's 72/165. `rest_start` = the byte after `amount`.
    let (tok_rest_start, tok_size) = idl
        .and_then(|v| parse_account_layout(v, "token").ok())
        .and_then(|l| {
            let amount = l.fields.iter().find(|f| f.name == "amount")?;
            Some((amount.offset as i64 + 8, l.size as i64))
        })
        .unwrap_or((72, 165));

    let uses_mint = spec.accounts.iter().any(|(_, c)| matches!(c, CodecKind::Mint));
    let aggregation = if uses_mint {
        // Mint codec → the shared MintAggregation module (union of
        // mint_account_eq / mint_supply_eq / dest_account_eq). Mint
        // supply offset + rest offset from the IDL mint layout.
        let (supply_off, rest_off, mint_size) = idl
            .and_then(|v| parse_account_layout(v, "mint").ok())
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
        // Token codec → TransferAggregation, from the detected src/dst patterns.
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

    // mint pubkey: 4 dwords at +0/8/16/24 (always owned).
    let mut mint = Vec::new();
    for i in 0..4 {
        let off = base_off + 8 * i;
        let v = fold(cell_val(pre, &m.base_raw, off, false)?);
        mint.push(v);
        owned.push((m.base_raw.clone(), off, false));
    }
    // owner pubkey: owned (read) or framed.
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
    // amount field pre-value (the balance `a`).
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

    // Per-byte hyp name derived from the byte var (unique across accounts).
    let hb = |v: &str| format!("h_{}", v);
    let g1sz = format!("{}sz", g1);
    // (lemma, record_rest, rw_args_tail). The tail is the lemma args after
    // `base mint… owner… amount`: the rest bytes, gaps, and size/bound hyps.
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
    // Discharge-route field list (SPL token: mint@0, owner@32, amount@64,
    // opaque tail@72) — the `tokenAcctBalance_codec` keystone target.
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
// Account-aggregation codegen.
//
// Emits the `*_account_eq` aggregation lemmas (today hand-written in
// PToken/TransferAggregation.lean) from the account layout + the lift's
// owned-byte pattern. The lemmas are GENERIC in the field values
// (`b72`/`h72`/`g1`, not lift vars), so they're a pure function of the
// owned-byte pattern — `rest_segments` generalizes the previously
// hardcoded `match rest_bytes` arms to any pattern.
// -----------------------------------------------------------------------------

/// A segment of an account's `rest` region.
enum RestSeg { Byte(i64), Gap { off: i64, len: i64 } }

/// General segmentation of `[start, end)` given sorted owned byte offsets:
/// owned bytes become `Byte`, the runs between/around them become `Gap`s.
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

/// Emit one `tokenAcctBalanceOf base record = <fine cells>` aggregation
/// lemma for a token account whose `rest` region owns `owned` bytes.
/// `owner_owned` = the lift read the owner (else it's framed via `o0..o3`).
/// `gap_ctr` threads gap numbering across a module's lemmas.
fn render_token_agg_lemma(
    name: &str, owner_owned: bool, owned: &[i64], rest_start: i64, size: i64,
    gap_ctr: &mut u32,
) -> String {
    let segs = rest_segments(owned, rest_start, size);
    // Assign gap names + collect byte offsets, preserving segment order.
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

    // Params.
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

    // LHS record `rest` (right-folded `++` chain) + RHS fine cells.
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
    // memBytesIs_segs args.
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

/// Emit the full token-aggregation module (the lemmas a token-codec
/// refinement imports). `accounts` is `(lemma_name, owner_owned, owned_bytes)`.
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

/// Emit the full mint-aggregation module (the lemmas a mint-codec
/// refinement imports: `mint_account_eq` full preAuth, `mint_supply_eq`
/// opaque preAuth, and the token `dest_account_eq`). Mint structure is the
/// SPL `COption<Pubkey>` preAuth (tag byte + 3-byte gap + 32-byte pubkey
/// as four dwords) at [0,36), `supply` u64 at `supply_off`, rest at
/// `rest_off`. The preAuth/rest splits reuse the `memBytesIs_segs` keystone.
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

/// Write the mechanically-emitted aggregation module to its canonical
/// `examples/lean/<module-path>.lean` location (relative to cwd). The
/// import module name (e.g. `PToken.TransferAggregation`) maps to the
/// path under the Examples lib `srcDir`. Returns a label for the log.
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

/// Render a mint aggregation rw call for a given supply value.
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
    // params: vars (Nat), framed owners, ByteArrays, hyps.
    let mut nat_params = vars.join(" ");
    for b in builds { for p in &b.params { nat_params.push(' '); nat_params.push_str(p); } }
    let mut barrays: Vec<String> = Vec::new();
    let mut hyps: Vec<String> = Vec::new();
    for b in builds { barrays.extend(b.barrays.iter().cloned()); hyps.extend(b.hyps.iter().cloned()); }

    // AsmRefines account argument order (records), interleaved with addrs.
    // Build: pred cr nCu 0 entry exit rr <addr args> <record args> amount setupPre setupPost
    let addr_args: Vec<String> = builds.iter().map(|b| b.base_arg.clone()).collect();
    let record_args: Vec<String> = builds.iter().map(|b| format!("\n      {}", b.record)).collect();

    // rw list: pre-aggregations then post-aggregations.
    let mut rw: Vec<String> = Vec::new();
    for b in builds { rw.push(b.rw_pre.clone()); }
    for b in builds { rw.push(b.rw_post.clone()); }

    // frame F (right-folded sep-conj of all accounts' frame atoms).
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
    // aggregation deps
    let uses_transfer_agg = builds.iter().any(|b|
        b.rw_pre.starts_with("src_account_eq") || b.rw_pre.starts_with("dst_account_eq"));
    let uses_mint_agg = builds.iter().any(|b|
        b.rw_pre.starts_with("mint_account_eq") || b.rw_pre.starts_with("mint_supply_eq")
        || b.rw_pre.starts_with("dest_account_eq"));
    if uses_transfer_agg { imports.push("import PToken.TransferAggregation".to_string()); }
    if uses_mint_agg { imports.push("import PToken.MintAggregation".to_string()); }

    // Discharge-route field-list atoms (builds order matches the obligation's
    // account-atom order), for the `refines_field` reshape corollary.
    let field_pre_join = builds.iter().map(|b| b.field_pre.clone())
        .collect::<Vec<_>>().join(" **\n      ");
    let field_post_join = builds.iter().map(|b| b.field_post.clone())
        .collect::<Vec<_>>().join(" **\n      ");
    // Reshape simp set for `refines_field`: the token keystone always (every
    // arm owns ≥1 token account); the mint keystone only when a mint account
    // is present, so a token-only arm doesn't reference the unimported
    // `MintFieldCodec` lemmas.
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

/// Emit a counter-codec refinement: a single owned `u64` cell at the
/// counter offset, incremented by the constant 1. No aggregation module
/// (coarse = fine for a `u64`), no frame (the cell is fully owned), no
/// `amount` argument (the delta is the constant 1).
fn emit_counter_refinement(
    spec: &RefineSpec, lift_module: &str,
    pre: &[Atom], post_clean: &[Atom],
    abs_subst: &std::collections::BTreeMap<String, String>, vars: &[String],
    n_cu: usize, start_pc: usize, exit_pc: usize,
) -> Option<(String, String, Option<(String, String)>)> {
    let fold = |e: &Expr| fold_abstractions(e.to_lean(), abs_subst);

    // Find the incremented counter cell: a `u64` whose post value is the
    // cleaned `NatAdd(InitMem, Const)` form.
    let mut found: Option<(Expr, i64, Expr, i64)> = None;
    for atom in post_clean {
        if let Atom::Mem { addr_base, addr_off, width, value } = atom {
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

    // The single owned `u64` cell is excluded from the setup frame; every
    // other lift atom (registers, etc.) stays in setup.
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

/// Render the counter refinement theorem. The proof is `unfold` +
/// `simp [counterValOf]` + `sl_exact lift`: no codec aggregation rewrite
/// (a single `u64` is coarse = fine) and no frame (the cell is owned).
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

/// Emit a multi-field NON-token vault refinement (`AsmRefinesFieldUpdate`).
/// Owns the updated `u64` field, frames the untouched fields, and reshapes
/// the account codec via `account_agg`/`codecCoarse_eq_fine`. The field
/// layout is driven by the Codama IDL account struct — the layout-general
/// path that makes a new program's refinement free.
fn emit_vault_refinement(
    spec: &RefineSpec, lift_module: &str,
    pre: &[Atom], post_clean: &[Atom],
    abs_subst: &std::collections::BTreeMap<String, String>, vars: &[String],
    n_cu: usize, start_pc: usize, exit_pc: usize,
    idl: Option<&serde_json::Value>,
) -> Option<(String, String, Option<(String, String)>)> {
    let fold = |e: &Expr| fold_abstractions(e.to_lean(), abs_subst);
    let layout = parse_account_layout(idl?, "vault").ok()?;

    // The updated field: a `u64` cell whose cleaned post value is
    // `NatAdd(InitMem, Const)` (the constant `+k` delta).
    let mut updated: Option<(Expr, i64, Expr, i64)> = None; // base, off, pre_val, delta
    for atom in post_clean {
        if let Atom::Mem { addr_base, addr_off, width, value } = atom {
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

    // Walk the IDL layout: emit a `FieldVal` per field; own the updated
    // `u64`, frame every other field (fresh params + fine atoms).
    let mut fresh = 0u32;
    let mut params: Vec<String> = Vec::new();
    let mut ba_params: Vec<String> = Vec::new();
    let mut pre_fields: Vec<String> = Vec::new();
    let mut post_fields: Vec<String> = Vec::new();
    let mut frame: Vec<String> = Vec::new();
    let mut updated_seen = false;
    for f in &layout.fields {
        let off = f.offset as i64;
        match &f.kind {
            FieldKind::U64 if off == upd_off => {
                updated_seen = true;
                pre_fields.push(format!("({}, .u64 {})", off, upd_pre_l));
                post_fields.push(format!("({}, .u64 ({} + {}))", off, upd_pre_l, delta));
                // owned by the lift — not framed.
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
            // A blob field (option / enum / array / wide scalar) the handler
            // does not touch: frame the whole region as a single opaque `↦Bytes`
            // gap (`.blob [.gap g]`). `account_agg`/`memBytesIs_segs` reshape
            // coarse⟷fine generically; the gap carries no `< 256` side
            // condition. The byte size is not pinned in the obligation (the
            // gap is a free `ByteArray`), so the theorem holds for any
            // contents of that region.
            FieldKind::Bytes(_) => {
                let g = format!("fg{}", fresh); fresh += 1; ba_params.push(g.clone());
                pre_fields.push(format!("({}, .blob [.gap {}])", off, g));
                post_fields.push(format!("({}, .blob [.gap {}])", off, g));
                frame.push(format!("(effectiveAddr {} {} ↦Bytes {})", base_l, off, g));
            }
        }
    }
    if !updated_seen { return None; }

    // setup = lift atoms not owning the updated cell (registers, etc.).
    let owned_base = base.to_lean();
    let is_owned = |a: &Atom| match a {
        Atom::Mem { addr_base, addr_off, width, .. } =>
            addr_base.to_lean() == owned_base && *addr_off == upd_off
                && matches!(width, Width::Dword),
        _ => false,
    };
    let setup_pre: Vec<Atom> = pre.iter().filter(|a| !is_owned(a)).cloned().collect();
    let setup_post: Vec<Atom> = post_clean.iter().filter(|a| !is_owned(a)).cloned().collect();

    let module = format!("{}Refinement", lift_module);
    let lean = render_vault_refinement(spec, &module, &base_l, &pre_fields, &post_fields,
        &frame, &params, &ba_params, pre, post_clean, &setup_pre, &setup_post,
        abs_subst, vars, n_cu, start_pc, exit_pc, upd_off, delta, &upd_pre_l);
    Some((module, lean, None))
}

/// Render the vault refinement. The proof reshapes both coarse codecs to
/// fine via `account_agg` (`codecCoarse_eq_fine`), unfolds the fine atoms,
/// frames the untouched fields, and closes with `sl_exact`.
fn render_vault_refinement(
    spec: &RefineSpec, module: &str, base_l: &str,
    pre_fields: &[String], post_fields: &[String], frame: &[String], params: &[String],
    ba_params: &[String],
    pre: &[Atom], post_clean: &[Atom], setup_pre: &[Atom], setup_post: &[Atom],
    abs_subst: &std::collections::BTreeMap<String, String>, vars: &[String],
    n_cu: usize, start_pc: usize, exit_pc: usize,
    upd_off: i64, delta: i64, upd_pre_l: &str,
) -> String {
    let mut nat_params = vars.join(" ");
    for p in params { nat_params.push(' '); nat_params.push_str(p); }
    // Binder group for the `ensures` corollary: only the params that appear
    // in the field lists (the updated field's pre value + the framed-field
    // params), so the projection theorem has no unused binders.
    let mut ens_nat = upd_pre_l.to_string();
    for p in params { ens_nat.push(' '); ens_nat.push_str(p); }
    let mut ensures_binders = format!("({ens_nat} : Nat)");
    if !ba_params.is_empty() {
        ensures_binders.push_str(&format!("\n    ({} : ByteArray)", ba_params.join(" ")));
    }
    // Nat binder group, plus a `ByteArray` group for blob-field gaps (only
    // emitted when a blob field is present, so non-blob output is unchanged).
    let mut binders = format!("({nat_params} : Nat)");
    if !ba_params.is_empty() {
        binders.push_str(&format!("\n    ({} : ByteArray)", ba_params.join(" ")));
    }
    // Compose the simp sets from the field kinds actually present, so each
    // lemma is used (no `unusedSimpArgs` lint) and a blob-free vault emits
    // byte-identically to before. `pubkeyIs` only when a pubkey field is
    // framed; the segment lemmas (`segsSL`/`FieldSeg.sl`, `segsValid`/
    // `FieldSeg.valid`) only when a blob field is present.
    let has_pubkey = pre_fields.iter().any(|f| f.contains(".pubkey"));
    let has_blob = !ba_params.is_empty();
    let mut fine = vec!["codecFine", "FieldVal.fine"];
    if has_pubkey { fine.push("pubkeyIs"); }
    if has_blob { fine.push("segsSL"); fine.push("FieldSeg.sl"); }
    fine.push("sepConj_emp_right_eq");
    fine.push("Nat.add_zero");
    let fine_simp = fine.join(", ");
    let mut valid = vec!["codecValid", "FieldVal.fineValid"];
    if has_blob { valid.push("segsValid"); valid.push("FieldSeg.valid"); }
    let valid_simp = valid.join(", ");
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
        (by simp [{valid_simp}]),
      codecCoarse_eq_fine {base}
        [{post_list}]
        (by simp [{valid_simp}])]
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
        valid_simp = valid_simp,
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

fn lift_one(
    so_path:         &Path,
    ctx:             &BinaryCtx,
    analysis:        &Analysis<'_>,
    target_disc:     Option<i64>,
    module_override: Option<String>,
    trace:           Option<&[usize]>,
    arm_name:        Option<&str>,
    idl:             Option<&serde_json::Value>,
) -> Result<LiftOutput, Box<dyn std::error::Error>> {
    let executable  = &ctx.executable;
    let text_offset = ctx.text_offset;
    let text_bytes  = ctx.text_bytes.as_slice();
    let insns       = &ctx.insns;

    // Diagnostic dump (stderr) — useful when step() can't model an
    // opcode and we want to see the surrounding shape anyway.
    eprintln!("=== decoded insns ===");
    for (i, ins) in insns.iter().enumerate() {
        let rendered = insn_to_lean(ins, i).unwrap_or_else(|e| format!("?? ({})", e));
        eprintln!("  pc={:3}  opc=0x{:02x}  {}", i, ins.opc, rendered);
    }
    eprintln!();

    // Default module name from the .so filename.
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

    // Emit the Lean module.
    let mut out = String::new();
    out.push_str(&format!(
        "/-\n  Generated by `qedlift` from `{}`.\n\
         \n\
         End-to-end lift demonstration:\n\
         1. The .text bytes are embedded verbatim as a `ByteArray`.\n\
         2. `Decode.decodeProgram` recovers the instruction sequence;\n\
            `native_decide` proves the decode is correct.\n\
         3. A `cuTripleWithinMem` Hoare triple is stated over the\n\
            decoded sequence. The pre/post atom synthesis is the next\n\
            iteration's work (the \"symbolic executor\" piece); for the\n\
            demo, see the worked example in\n\
            `SVM/SBPF/Macros.lean` (`{}_macro_spec_auto`) where the\n\
            theorem is proved by `sl_block_auto` against the same\n\
            instruction sequence.\n\
         -/\n\n",
        so_path.display(), so_stem,
    ));
    out.push_str("import SVM.SBPF.Decode\n");
    out.push_str("import SVM.SBPF.RunnerBridge\n");
    out.push_str("import SVM.SBPF.Macros\n\n");
    // File-level option bumps. Long chains (especially ones with
    // call_local + exit_pops composition) blow past the defaults
    // during `slBlockIter`'s isDefEq work.
    out.push_str("set_option maxRecDepth 65536\n");
    out.push_str("set_option maxHeartbeats 4000000\n\n");
    out.push_str(&format!("namespace Examples.Lifted.{}\n\n", module_name));

    out.push_str("open SVM.SBPF\n\n");

    // The byte embedding + decode bridge (`*Bytes`, `*Insns`,
    // `*_decodes`) is a sanity check that the .so bytes decode to the
    // expected insns. It is NOT load-bearing for the Hoare triple,
    // whose `CodeReq` is built from walked-PC singletons. For large
    // binaries the full `.text` as a ByteArray literal blows
    // `maxRecDepth` during elaboration / `native_decide`, so we skip
    // the whole bridge above a threshold. two_op (40 bytes) keeps it;
    // p_token (~96KB) drops it.
    const DECODE_BRIDGE_MAX_BYTES: usize = 4096;
    let emit_decode_bridge = text_bytes.len() <= DECODE_BRIDGE_MAX_BYTES;

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
             -- The byte→insn decode bridge isn't load-bearing for the Hoare\n\
             -- triple below (its `CodeReq` references walked-PC singletons,\n\
             -- not the full `.text`).\n\n",
            module_name, module_name, module_name, text_bytes.len(),
        ));
    }

    // The decoded insns.
    // Try to render the full decoded `.text` as an `Array Insn`. This
    // doubles as a sanity-check (the `*_decodes` theorem proves
    // byte→insn correspondence by `native_decide`) but it isn't
    // load-bearing for the Hoare triple — the triple's `CodeReq` is
    // built from walked-PC singletons, decoupled from this array.
    //
    // If any opcode in `.text` can't yet be rendered, we skip both
    // the array def and the decode theorem and continue with just
    // the Hoare triple. This lets us lift a known-good arm out of a
    // binary that contains other arms we don't yet model (e.g. lifting
    // SPL Token's `Transfer` arm out of p_token even though some other
    // arm uses `jgt_reg`).
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
        // Bridge already noted above; emit nothing here.
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
        out.push_str("/-- The bytes decode exactly to the expected instruction array. -/\n");
        out.push_str(&format!(
            "theorem {}_decodes :\n    \
             Decode.decodeProgram {}Bytes = some {}Insns := by\n  native_decide\n\n",
            module_name, module_name, module_name,
        ));
    }

    // Spec calls collected during the walk for the
    // `sl_block_iter` proof emission (when needed).
    let mut spec_calls: Vec<SpecCall> = Vec::new();

    // CFG-aware happy-path walk + symbolic execution in one pass.
    // PC progression follows the actual control flow:
    //   * straight-line opcode    → pc + 1
    //   * `ja off`                → pc + 1 + off
    //   * conditional jump (jeq/jne) → pc + 1 (fall-through policy)
    //   * `call_local target`     → push pc+1, jump to target
    //   * `exit` with empty stack → top-level terminator, walk ends
    //   * `exit` with non-empty stack → pop, resume at popped PC
    //
    // Walk starts at the ELF's declared entrypoint (NOT analysis PC 0:
    // the linker may place helper functions before the entrypoint).
    let mut block_pcs: Vec<usize> = Vec::new();
    let exit_pc: usize;
    let entry_pc: usize = executable.get_entrypoint_instruction_offset();
    let mut state = SymState::default();
    {
        // In trace mode the walk follows the recorded PC sequence; `ti`
        // is the cursor into it and `pc_iter` mirrors `trace[ti]`.
        let mut ti: usize = 0;
        let mut pc_iter: usize = match trace {
            Some(t) => t[0], // load_trace guarantees non-empty
            None     => entry_pc,
        };
        // Safety cap on walk length. Without this, an unmodelled
        // back-branch (e.g. a copy loop whose conditional jump we
        // default to "not taken") can spin the walker forever. The
        // cap is high enough to permit deep dispatcher cascades
        // (SPL Token has 28 arms; 16 PCs/arm + 200 PCs/handler ≈ 700)
        // but low enough to fail fast on a runaway. With a trace the
        // bound is exactly the trace length (plus slack).
        let walk_cap: usize = match trace { Some(t) => t.len() + 8, None => 1024 };
        let mut walk_steps: usize = 0;
        loop {
            walk_steps += 1;
            if walk_steps > walk_cap {
                return Err(format!(
                    "walker exceeded {} steps at pc={} (likely back-branch \
                     defaulted to fall-through)", walk_cap, pc_iter).into());
            }
            // Trace mode: the recorded sequence is authoritative for the
            // current PC. When it's exhausted the walk is done.
            if let Some(t) = trace {
                if ti >= t.len() { exit_pc = pc_iter; break; }
                pc_iter = t[ti];
            }
            if pc_iter >= insns.len() { exit_pc = pc_iter; break; }
            let ins = &insns[pc_iter];

            // Handle exit specially — it's either a nested return
            // (pops the call stack + restores r10) or a top-level
            // terminator (ends the walk; not included in the CR).
            if ins.opc == ebpf::EXIT {
                if state.call_stack.is_empty() {
                    exit_pc = pc_iter;
                    break;
                } else {
                    block_pcs.push(pc_iter);
                    // Emit a spec call for the nested exit (before
                    // popping the call stack so r10 etc. are still
                    // at their +0x1000-bumped values).
                    if let Some(sc) = spec_call_for(&state, ins, pc_iter, None, None, None, None) {
                        spec_calls.push(sc);
                    }
                    let (call_pc, saved) = state.call_stack.pop().unwrap();
                    // exit_pops_spec restores r6..r10 to the saved frame
                    // (the pre-call values). Mirror that in the symbolic
                    // state so the post matches — a callee that clobbered
                    // r6..r9 leaves their *current* values stale.
                    for (i, r) in (6u8..=10).enumerate() {
                        state.write_reg(r, saved[i].clone());
                    }
                    // In trace mode the next PC comes from the trace (it
                    // should equal the return PC); otherwise jump to callpc+1.
                    if trace.is_some() { ti += 1; } else { pc_iter = call_pc + 1; }
                    continue;
                }
            }

            // Syscall detection (trace mode): a `call_imm` whose next
            // executed PC is the fall-through (pc+1) is a host syscall
            // (e.g. `sol_memset_`), not an internal `call_local` — the
            // host runs it and returns to pc+1 without pushing a BPF
            // frame. Dispatch on the resolved syscall hash; emit the
            // matching syscall-effect spec, advance, and continue.
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
                            // FAIL CLOSED (soundness audit H7). The model's
                            // `sol_get_sysvar` now WRITES the output buffer
                            // (`buf[r3..r3+r4)` of the cached sysvar to *r2)
                            // and its CU is length-dependent, so the old
                            // r0-only emission would frame memory the real
                            // syscall mutates — a false-on-chain claim.
                            // A faithful emission must thread the new
                            // `call_sol_get_sysvar_spec` (id Bytes32 atom
                            // from rodata, output blob, concrete slice) AND
                            // alias the written region into the walker's
                            // cell map so post-syscall loads read the
                            // sysvar bytes. That cell-aliasing machinery is
                            // the same feature needed to fix the walker's
                            // OVERLAPPING-access vacuity (e.g. the 7-byte
                            // tail-zeroing idiom `stw [r10-4]; stw [r10-7]`
                            // emits overlapping `↦U32` pre-atoms, making
                            // the emitted sepConj unsatisfiable). Until
                            // both land, refuse to lift across this
                            // syscall rather than emit an unsound or
                            // vacuous theorem.
                            return Err(format!(
                                "call_imm at pc {pc_iter} is `sol_get_sysvar`: lifting \
                                 across it is temporarily unsupported — the model now \
                                 fills the output buffer (H7 fix), and emitting the \
                                 pre-H7 r0-only shape would claim memory is unchanged \
                                 where the chain writes it. Needs the buffer-write \
                                 emission for `call_sol_get_sysvar_spec` (planned: \
                                 walker cell-aliasing of syscall-written regions).").into());
                        }
                        if imm == ebpf::hash_symbol_name(b"sol_log_") {
                            emit_r0_syscall(&mut state, &mut spec_calls, &mut block_pcs,
                                pc_iter, "call_sol_log_spec", ".sol_log_", "Log");
                            ti += 1;
                            continue;
                        }
                        // CPI. NOTE: modelled per the SVM's step-level CPI
                        // STUB (`Cpi.exec` = r0:=0) — effect-free on the
                        // invoked accounts. Sound w.r.t. `step`, but the
                        // lifted triple does NOT capture the callee's
                        // account writes (those live in executeFnCpi). See
                        // `call_sol_invoke_signed_spec`'s doc comment.
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
            // Branch hypothesis name (if this is a conditional jump).
            // The index into branch_hyps is the count of branches
            // seen so far.
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
            // Resolve the slot-relative jump offset to a logical PC
            // (handles lddw's 2-slot encoding). Shared by spec emission,
            // step's path-hypothesis target, and the PC walk.
            let jtgt = resolve_jump_target(ctx, pc_iter, ins.off as i64);
            // Decide the branch direction.
            //   * Trace mode: a conditional jump is "taken" iff the next
            //     recorded PC is not the fall-through (pc+1). When taken,
            //     that next PC must equal the resolved jump target — if
            //     it doesn't, the trace and the decoder disagree (a bug),
            //     so fail loudly rather than emit an unsound chain.
            //   * Static mode: discriminator-driven where possible,
            //     else fall-through. (No `--trace` supplied.)
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
                    // JGT-on-discriminator: with `--target-disc td`, the
                    // taken branch fires when the discriminator (the
                    // imm being compared) is strictly less than td. This
                    // matches `jgt dst, imm, target` semantics: "jump if
                    // r3 > imm". For dispatcher cascades that use the
                    // pattern `if (disc > N) goto upper_half`, td <= imm
                    // means we take the upper branch.
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
            step(&mut state, ins, Some(pc_iter), branch_taken, Some(jtgt))?;

            // PC progression. In trace mode the next PC is simply the
            // next recorded entry (the loop top reloads `pc_iter` from
            // it); we only advance the cursor here.
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
                    // Take the branch to the resolved logical target.
                    pc_iter = jtgt as usize;
                }
                ebpf::CALL_IMM => {
                    // The immediate is a Murmur3 hash; look up the
                    // function registry to resolve the callee PC (mapped
                    // slot→logical).
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

    // FAIL CLOSED on atom-footprint overlap (soundness audit H8): a
    // sepConj with overlapping memory atoms is unsatisfiable, so the
    // emitted theorem would be vacuously true — worse than no theorem.
    if let Some(err) = state.overlap_error.take() {
        return Err(format!(
            "qedlift: refusing to emit a vacuous lift — {err}").into());
    }

    // Build the CR as a Lean string. `sl_block_auto` requires the CR
    // to appear as a literal `union`-of-`singleton`s in the theorem
    // statement (it walks the AST), so we capture the string here and
    // inline it below instead of emitting a `def`.
    let cr_lean: String = if block_pcs.is_empty() {
        "CodeReq.empty".to_string()
    } else {
        let mut s = String::new();
        let opens = "(".repeat(block_pcs.len().saturating_sub(1));
        s.push_str(&opens);
        for (i, &pc) in block_pcs.iter().enumerate() {
            // A `call_imm` the walk resolved to a host syscall renders
            // as `.call <ctor>` (matching the syscall spec's CodeReq
            // singleton), not the `.call_local` insn_to_lean_full emits.
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

    // --- Phase 2: symbolic execution + Hoare-triple emission. ---
    out.push_str("/-! ## Symbolically lifted Hoare triple\n\n");
    out.push_str("Synthesised by qedlift's symbolic executor walking the\n");
    out.push_str("decoded insns left-to-right. Closed by `sl_block_auto`. -/\n\n");

    // Note: symbolic execution already happened inline in the walker
    // above; `state` is populated and ready to snapshot.
    let pre  = state.pre.clone();
    let post = post_atoms(&pre, &state);
    // (rr computed after abs_subst is built — see below)

    // Drop surfaced `< 2^k` load-bound hypotheses no spec call consumes.
    // `read_mem` records a bound for every fresh wide cell — including a
    // dword cell that's only STORED to (the old value `stxdw_spec` takes
    // but doesn't bound). Such `h<var>_lt` would be an unused theorem
    // hypothesis; keep only the ones a spec call references as `hv`.
    state.u64_load_vars.retain(|(v, _)| {
        let h = format!("h{}_lt", v);
        spec_calls.iter().any(|sc| sc.have_line.contains(&h))
    });

    // Detect "complex" addresses in mem atoms — anything other than a
    // bare `InitReg` base counts as complex (wrapAdd-shaped, etc.).
    // Each unique complex address gets parameterised as an opaque Nat
    // variable with a bridging equality, so the chain composes over
    // clean atoms (see `pda_n1_stack_macro_spec` in
    // SVM/SBPF/Macros.lean for the worked pattern).
    let mut abstractions: Vec<(String, String, String)> = Vec::new();
    // (param_name, bridge_hyp_name, raw_expression)
    {
        let mut seen: std::collections::BTreeMap<String, usize> =
            std::collections::BTreeMap::new();
        // A flat constant address (e.g. `toU64 0x300000000` from an
        // `lddw` — the program-heap case) is NOT complex: it has no nested
        // `wrapAdd` chain to fold, and `sl_block_auto` re-derives the same
        // concrete value, so abstracting it to `addrK` only creates a
        // mismatch (the opaque param can't unify with the literal).
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
    // Substitution map: rendered raw expression → parameter name.
    let abs_subst: std::collections::BTreeMap<String, String> =
        abstractions.iter()
            .map(|(p, _, e)| (e.clone(), p.clone()))
            .collect();
    let rr = region_req(&pre, &state, &abs_subst);
    // When the walk crossed a call_local, the chain's pre/post must
    // include `callStackIs []` as a framed atom — `call_local_spec`
    // takes a `callStackIs cs` in its pre, and the matching
    // `exit_pops_spec` returns the popped `callStackIs cs` in its
    // post. The empty initial stack pushes the new frame, then pops
    // back to empty on exit_pops, so net change is none — but the
    // atom must be present in pre+post for sl_block_iter to thread
    // it through the chain.
    let cs_atom = if state.saw_call { " ** callStackIs []" } else { "" };

    // Collect the symbolic variables we introduced so the theorem
    // signature can quantify over them.
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
            // The blob's `Sym` name is a `ByteArray` (surfaced via
            // `memset_blobs`, not here); the address's Nat leaves were
            // already collected when the syscall's registers were read.
            Atom::Bytes { addr, .. } => push_var(addr, &mut vars),
        }
    }
    let vars_sig = if vars.is_empty() { String::new() }
                   else { format!("({} : Nat)\n    ", vars.join(" ")) };
    // Side-condition hypotheses for u64-width loads. Per
    // `ldxdw_spec`, each loaded value carries a `< 2^64` constraint
    // that `sl_block_auto` leaves as a residual goal; we surface them
    // as theorem hypotheses and discharge with `<;> assumption`.
    let mut u64_hyps = String::new();
    for (v, k) in &state.u64_load_vars {
        u64_hyps.push_str(&format!("(h{}_lt : {} < 2 ^ {})\n    ", v, v, k));
    }
    // Path-hypothesis surface for any conditional jumps we walked.
    // For a JeqImm whose happy path is fall-through (the common
    // guard-check shape), the hypothesis is `dst ≠ toU64 imm`.
    let mut branch_hyps_sig = String::new();
    for (i, bh) in state.branch_hyps.iter().enumerate() {
        branch_hyps_sig.push_str(&format!("({} : {})\n    ", bh.name(i), bh.lean_hyp()));
    }
    // Memory-syscall surface. Each memset contributes a `ByteArray`
    // param + a `.size = <count>` hypothesis (the spec's `hbs`), and a
    // `nCu` Nat param + a per-step CU-bound hypothesis (the spec's
    // `hCu`). The model's `syscallCu` for memory ops scales with `r3`,
    // so this bound is an honest modeling assumption surfaced in the
    // signature, not a fact the lift can prove.
    // Surfaced side-condition hypotheses (e.g. div/mod divisor ≠ 0).
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
    // The triple's CU bound `M`: 0 for syscall-free arms, else the sum
    // of the memory syscalls' `nCu` vars. `sl_block_iter`'s final
    // `cuTripleWithinMem_cast` reconciles the chain's `0 + nCu + …`
    // against this closed form via `omega`.
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
    // Switch to explicit `sl_block_iter`-style proof when either:
    //   * the walk crossed a `call_local` (sl_block_auto diverges on
    //     wrapAdd-shaped addresses) — the `pda_n1_stack_macro_spec`
    //     workaround pattern, or
    //   * the walk took ANY conditional jump's "taken" branch —
    //     SpecGen.lean's mkSpec only dispatches `_not_taken` for
    //     jeq/jne; for taken arms we need the explicit spec call.
    let any_taken = state.branch_hyps.iter().any(|b| b.taken);
    let use_block_iter = state.saw_call || any_taken;

    // Value abstraction: complex bit-level *value* expressions
    // (wrapAdd / shift / mod / and chains) carry no proof content of
    // their own — the per-opcode spec already proved what each one
    // computes. But `sl_block_iter` re-reduces them (whnf) at every
    // chain step, which is the dominant cost on long arms (the
    // discriminator-extraction value alone took transferChecked from
    // 178ms to a >15min timeout). We `generalize` each such value to
    // an opaque `vgvN` immediately before `sl_block_iter`, so the
    // mechanical composition threads an opaque Nat instead of
    // reducing arithmetic. The `generalize h : e = v` keeps the bridge
    // `h` in scope (for the refinement layer) and leaves the THEOREM
    // STATEMENT concrete — only the proof goal is abstracted.
    //
    // Skip values that are already address abstractions (folded via
    // sl_rw_abs) and bare initials/constants (cheap, nothing to gain).
    let value_gens: Vec<String> = if use_block_iter {
        let is_complex = |e: &Expr| matches!(e,
            Expr::WrapAdd(..) | Expr::WrapSub(..) | Expr::WrapMul(..) | Expr::NatAdd(..) |
            Expr::Mod(..) | Expr::AndU64Imm(..) | Expr::LshU64Imm(..) |
            Expr::RshU64Imm(..) | Expr::StHalfImm(..) | Expr::StWordImm(..) |
            Expr::StDwordImm(..) | Expr::Raw(..));
        let mut seen = std::collections::BTreeSet::new();
        let mut gens = Vec::new();
        for atom in pre.iter().chain(post.iter()) {
            // `↦Bytes` blobs carry a `BytesVal`, not a Nat `Expr` value
            // (the fill/count are constants), so there's nothing to
            // generalize — skip them.
            let v = match atom {
                Atom::Reg(_, v) => v,
                Atom::Mem { value, .. } => value,
                Atom::Bytes { .. } => continue,
            };
            if is_complex(v) {
                // Render with sub-expression abstractions folded, so the
                // generalize target matches the (sl_rw_abs-folded) proof
                // term — e.g. `(addr0 <<< …) …`, not addr0's expansion.
                let r = fold_abstractions(v.to_lean(), &abs_subst);
                // Skip address abstractions (handled by sl_rw_abs): both
                // the expanded form (a map key) and — after folding — the
                // bare param name (a map value, e.g. `addr5`). Generalizing
                // an address base rewrites it everywhere, breaking the
                // address matching in the post/rr.
                let is_addr_abs = abs_subst.contains_key(&r)
                    || abs_subst.values().any(|p| *p == r);
                if !is_addr_abs && seen.insert(r.clone()) {
                    gens.push(r);
                }
            }
        }
        // Outer (longer) expressions first: generalizing a parent
        // before its sub-terms keeps the sub-terms from being
        // clobbered into the parent's fresh var prematurely.
        gens.sort_by_key(|e| std::cmp::Reverse(e.len()));
        gens
    } else {
        Vec::new()
    };

    let tactic: String = if use_block_iter {
        let mut t = String::new();
        // Spec-call have lines (one per insn in walk order).
        for sc in &spec_calls {
            t.push_str("  ");
            t.push_str(&sc.have_line);
            t.push('\n');
        }
        // sl_rw_abs to rewrite each spec's wrapAdd-shaped atoms to
        // use the abstracted parameter, if any abstractions exist.
        if !abstractions.is_empty() {
            // Apply innermost-first (shortest raw expression first).
            // sl_rw_abs is a single forward pass, and an outer
            // abstraction's (folded) bridge RHS references inner
            // params — so the inner folds must land in the term before
            // the outer `rw [← h_addrN]` can match. Sorting by raw expr
            // length ascending gives a valid inner→outer topological
            // order (a sub-term is always strictly shorter).
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
        // Final composition. Value abstraction rides along as the
        // `generalizing [...]` clause on sl_block_iter — the tactic
        // opaque-ifies each complex value (generalize … at *) before
        // composing, so generated proofs are a single tactic call and
        // the abstraction logic lives in the library, not here.
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
        // 2-space indent (matching the sl_block_iter branch): a bare
        // col-0 tactic gets absorbed by a following `open Memory in`
        // (parsed as the tactic combinator) when a `_balance_correct`
        // corollary follows, breaking the parse. Indenting lets the
        // col-0 `open …`/`end` terminate the block.
        "  sl_block_auto <;> assumption".to_string()
    } else {
        "  sl_block_auto".to_string()
    };
    let tactic: &str = Box::leak(tactic.into_boxed_str());

    // Fold nested abstractions inside each bridge RHS. A bridge's RHS
    // may contain another abstraction's full expression as a sub-term
    // (e.g. addr3 = `wrapAdd <all of addr0> (toU64 8)`). `sl_rw_abs`
    // folds inner abstractions first; once addr0's expansion becomes
    // `addr0`, the outer bridge's LHS pattern (written with addr0
    // expanded) no longer matches and the fold gets stuck. Rewriting
    // each RHS to reference the inner *param* keeps folding consistent
    // inner→outer. Longest-expression-first avoids partial overlaps;
    // only strictly-shorter exprs are folded (never self, never a
    // same-length sibling).
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

    // Build the abstraction signature fragment (params + bridge
    // equality hypotheses) for programs using sl_block_iter style.
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
    // The triple's start PC is the first instruction actually walked.
    // In static mode that's the entrypoint; in trace mode it's the
    // trace's first PC. Falls back to `entry_pc` only for an empty walk.
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

    // ── Heap-allocation corollary ──────────────────────────────────
    // If the program touched the runtime heap (the embedded bump
    // allocator keeps its position at MM_HEAP_START and allocates by
    // load/store/ALU on heap memory), re-express those cells via the
    // `heapBumpPtr` / `heapBlockU64` predicates so the spec reads as an
    // allocation claim rather than raw cells at fixed addresses. The
    // predicates unfold to the same `memU64Is` cells, so `exact` closes
    // after `simp`. Gated on heap cells being present, so non-heap lifts
    // (counter / vault / token) regenerate byte-identical.
    let has_heap = pre.iter().chain(post.iter()).any(|a|
        matches!(a, Atom::Mem { addr_base, addr_off, width, .. }
            if matches!(width, Width::Dword) && heap_cell_addr(addr_base, *addr_off).is_some()));
    if has_heap {
        // The lift theorem's parameter list, in declaration order.
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

    // ── Balance-correctness corollary ──────────────────────────────
    // Re-expose `wrapSub`/`wrapAdd` balance shifts in the post as
    // ordinary Nat arithmetic (`a - b` / `a + b`), justified by
    // `wrapSub_of_le` / `wrapAdd_of_lt` under explicit funds /
    // no-overflow guards. This lifts the bit-level triple to the
    // domain-meaningful claim "the handler debits/credits the balance
    // cell by exactly the amount." Only memory cells whose value wraps
    // two LOADED values (`InitMem`) qualify — register/address
    // arithmetic (`r8 ↦ wrapAdd addrN k`) is excluded by that filter.
    enum Shift { Sub(Expr, Expr), Add(Expr, Expr), AddConst(Expr, i64) }
    let is_initmem = |e: &Expr| matches!(e, Expr::InitMem(_));
    // A constant immediate delta `toU64 k` (e.g. `add64 r2, 1`).
    let const_delta = |e: &Expr| -> Option<i64> {
        if let Expr::ToU64(inner) = e {
            if let Expr::Const(k) = inner.as_ref() { return Some(*k); }
        }
        None
    };
    // Only constant-delta codec arms (counter / vault) expose the constant
    // `+k` cleaning; other arms (e.g. `two_op`'s `+1`) keep the raw
    // `wrapAdd` form so they regenerate byte-identically.
    let counter_arm = is_const_delta_arm(arm_name);
    let mut shifts: Vec<Shift> = Vec::new();
    let mut post_clean: Vec<Atom> = Vec::with_capacity(post.len());
    for atom in &post {
        if let Atom::Mem { addr_base, addr_off, width, value } = atom {
            if let Expr::WrapSub(a, b) = value {
                if is_initmem(a) && is_initmem(b) {
                    shifts.push(Shift::Sub((**a).clone(), (**b).clone()));
                    post_clean.push(Atom::Mem { addr_base: addr_base.clone(),
                        addr_off: *addr_off, width: *width,
                        value: Expr::CleanSub(a.clone(), b.clone()) });
                    continue;
                }
            }
            if let Expr::WrapAdd(a, b) = value {
                if is_initmem(a) && is_initmem(b) {
                    shifts.push(Shift::Add((**a).clone(), (**b).clone()));
                    post_clean.push(Atom::Mem { addr_base: addr_base.clone(),
                        addr_off: *addr_off, width: *width,
                        value: Expr::NatAdd(a.clone(), b.clone()) });
                    continue;
                }
                if counter_arm && is_initmem(a) {
                    if let Some(k) = const_delta(b) {
                        shifts.push(Shift::AddConst((**a).clone(), k));
                        post_clean.push(Atom::Mem { addr_base: addr_base.clone(),
                            addr_off: *addr_off, width: *width,
                            value: Expr::NatAdd(a.clone(), Box::new(Expr::Const(k))) });
                        continue;
                    }
                }
            }
        }
        post_clean.push(atom.clone());
    }

    if !shifts.is_empty() {
        // Ordered param-name list to re-apply the main spec, mirroring
        // the signature: vars, then (abstraction params, abstraction
        // hyps), u64 bound hyps, branch hyps.
        let mut names: Vec<String> = vars.clone();
        if use_block_iter && !abstractions.is_empty() {
            for (p, _, _) in &abstractions { names.push(p.clone()); }
            for (_, h, _) in &abstractions { names.push(h.clone()); }
        }
        for (v, _) in &state.u64_load_vars { names.push(format!("h{}_lt", v)); }
        for i in 0..state.branch_hyps.len() { names.push(format!("h_branch{}", i)); }
        for (name, _) in &state.side_hyps { names.push(name.clone()); }
        // Memory-syscall params, in the same order `syscall_sig` binds
        // them: each blob's `ByteArray` + size hyp, then each `nCu` +
        // CU-bound hyp.
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
                    // The counter `+1` credit. `wrapAdd_one_of_lt` cleans
                    // `wrapAdd a (toU64 1)` to `a + 1`; only `+1` is wired
                    // (the sole counter delta).
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
        arm, &module_name, &pre, &post_clean, &abs_subst, &vars, n, start_pc, exit_pc, idl));
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

    // Load the .so + analysis once. For batch runs over a large
    // binary (p_token: ~28 arms, ~10s/arm cold), this hoists the
    // per-arm cost from ~10s to a few ms by amortising the parse
    // + CFG build over the whole batch.
    let ctx = load_binary(&args.so)?;
    let analysis = Analysis::from_executable(&ctx.executable)?;

    // Codama IDL (when a `.json` is given) — used by the refinement
    // codegen to derive account layouts (rest-region start + size).
    let idl_value = args.idl.as_ref().and_then(|p| load_idl_value(p));

    // Optional execution-trace oracle (single-arm mode). One decimal
    // logical PC per line; blank lines and `#` comments are ignored.
    let trace: Option<Vec<usize>> = match args.trace.as_ref() {
        Some(p) => Some(load_trace(p)?),
        None => None,
    };

    // Sidecar-driven mode: --qedmeta <toml>. Drives targeting from the
    // qedrecover sidecar (discriminator + name) instead of the manual
    // --target-disc/--arm-name flags, and cross-checks each lifted
    // triple's CU against the claimed cu_budget. Optionally narrowed to
    // one instruction with --target-name.
    if let Some(meta_path) = args.qedmeta.as_ref() {
        let meta = load_qedmeta(meta_path)?;
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
            let result = lift_one(&args.so, &ctx, &analysis,
                Some(ix.discriminator.value), Some(module_name.clone()),
                trace.as_deref(), Some(&arm), idl_value.as_ref())?;

            // Cross-check the claimed CU budget against the lifted triple.
            // The budget is an upper bound on the verified CU; the lifted
            // `n` is the exact CU of the discharged triple.
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

    // Batch mode: --idl <toml|json> + --output-dir <dir>. With --idl but
    // no --output-dir, fall through to single-arm mode (the IDL is still
    // loaded into `idl_value` above for layout-driven aggregation).
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
            // Convention: namespace `Examples.Lifted.<SoStem><Name>`,
            // file `<SoStem><Name>Lifted.lean`. The "Lifted" suffix
            // lives only on the filename so the namespace stays tidy.
            let module_name = format!("{}{}", so_stem, pascal_case(&ix.name));
            // Per-arm error tolerance: an arm that hits an unmodelled
            // opcode (in either the .text renderer or the symbolic
            // executor) is reported and skipped, not fatal. This makes
            // the batch a coverage probe.
            match lift_one(&args.so, &ctx, &analysis, Some(ix.discriminator), Some(module_name.clone()), None, Some(&ix.name), idl_value.as_ref()) {
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

    // Single-instruction mode (unchanged behaviour).
    let result = lift_one(&args.so, &ctx, &analysis, args.target_disc, args.module.clone(),
                          trace.as_deref(), args.arm_name.as_deref(), idl_value.as_ref())?;
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
