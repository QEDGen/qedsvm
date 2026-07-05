use std::path::{Path, PathBuf};
use std::sync::Arc;

use qed_analysis::{
    layout::{parse_account_layout, AccountField, AccountLayout, FieldKind},
    NoopCtx, PcMap,
};
use solana_sbpf::{ebpf, elf::Executable, program::BuiltinProgram};

pub(super) struct Args {
    pub(super) so: PathBuf,
    pub(super) output: Option<PathBuf>,
    pub(super) module: Option<String>,
    /// Discriminator value to target. When set, the walker resolves
    /// each conditional jump on the discriminator register (the dst
    /// of an `ldxb r?, [r1+0]` load) by taking the direction
    /// consistent with `disc_byte == target_disc`. Each such jump
    /// adds a path hypothesis to the theorem signature.
    pub(super) target_disc: Option<i64>,
    /// IDL file (TOML). When given, qedlift loops over the IDL's
    /// instructions and emits one Lean file per instruction. The
    /// per-instruction module names are derived from the IDL's
    /// instruction names; the output directory is `--output-dir`.
    pub(super) idl: Option<PathBuf>,
    pub(super) output_dir: Option<PathBuf>,
    /// Execution-trace file: one decimal logical PC per line, in the
    /// order the instructions were executed on a concrete run (capture
    /// via the Lean runner's `TRACE_STEPS`). When given, the walker
    /// follows this exact path instead of its static branch policy.
    pub(super) trace: Option<PathBuf>,
    /// IDL instruction name for the refinement codegen (single-arm
    /// mode). When given and recognised by the refinement registry,
    /// qedlift also emits the `<module>Refinement.lean` asm-refines
    /// theorem. Batch mode derives this from the IDL automatically.
    pub(super) arm_name: Option<String>,
    /// qedrecover sidecar (`*.qedmeta.toml`). When given, qedlift reads
    /// `{discriminator.value, name, cu_budget}` for each in-scope
    /// instruction and drives targeting from the sidecar.
    pub(super) qedmeta: Option<PathBuf>,
    /// Restrict a `--qedmeta` run to a single instruction by name.
    pub(super) target_name: Option<String>,
    /// Spec-driven refinement descriptor (`*.descriptor.json`). When given
    /// (single-arm mode), qedlift builds the layout-general
    /// `AsmRefinesFieldUpdate` obligation from the descriptor instead of the
    /// hardcoded `refine_registry` arm match. The seam to qedspec.
    pub(super) descriptor: Option<PathBuf>,
    /// Whole-transition mode (#40): discover one trace per path
    /// (`<stem>_<path>.pcs` beside the .so), lift each with the descriptor,
    /// and emit the per-path modules + the bundle theorem. Needs
    /// `--descriptor` and `--output-dir`.
    pub(super) transition: bool,
    /// Shared-text base name (batch dedup, e.g. `PToken`). When given, the
    /// binary's Text/SlotMap/FnRegistry defs are emitted ONCE into
    /// `Generated/{base}Text.lean` and every arm lift imports that module
    /// instead of re-embedding the ~100KB `.text` blob. Requires the
    /// large-text decode-pins path (fails closed on small inline-bridge
    /// binaries).
    pub(super) shared_text: Option<String>,
}

// qedmeta sidecar (#41 Phase 4): v2 adds [instruction.recovered] arm
// decomposition; serde ignores unknown fields so v0.1 sidecars still parse.

/// Newest sidecar schema qedlift understands; v1 = targeting only, v2 = recovered arm.
const QEDMETA_SCHEMA_MAX: u32 = 2;

#[derive(Debug, serde::Deserialize)]
pub(super) struct QedMeta {
    #[serde(default)]
    schema_version: u32,
    #[serde(rename = "instruction")]
    pub(super) instructions: Vec<QedMetaIx>,
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
    name: String,
    offset: usize,
    kind: String,
    /// Present only for `kind = "bytes"` (opaque region width); mirrors `field_kind_name`.
    #[serde(default)]
    width_bytes: Option<usize>,
}

#[derive(Debug, serde::Deserialize)]
pub(super) struct QedMetaIx {
    pub(super) name: String,
    pub(super) cu_budget: Option<u64>,
    pub(super) discriminator: QedMetaDisc,
    /// `[instruction.recovered]` from qedrecover; consumed (#41 "lossy handoff"). `None` for pre-v2 sidecars.
    #[serde(default)]
    pub(super) recovered: Option<QedMetaRecovered>,
}

#[derive(Debug, serde::Deserialize)]
pub(super) struct QedMetaDisc {
    pub(super) value: i64,
}

/// Sub-table from qedrecover; only `arm_entry_pc` is consumed, other keys silently ignored.
#[derive(Debug, serde::Deserialize)]
pub(super) struct QedMetaRecovered {
    /// Logical (decoded-array) arm-entry PC — same space as walker / `.pcs` traces, NOT a raw slot.
    pub(super) arm_entry_pc: usize,
}

/// Reconstruct the shared `AccountLayout`s from a sidecar's `[[account_layout]]` tables.
/// Inverse of qedrecover's emitter (`field_kind_name` + `width_bytes`); the round-trip is
/// exact for the codecs qedlift consumes (pubkey/u64/byte/bytes).
pub(super) fn sidecar_account_layouts(meta: &QedMeta) -> Vec<AccountLayout> {
    meta.account_layouts
        .iter()
        .map(|l| AccountLayout {
            name: l.name.clone(),
            size: l.size,
            fields: l
                .fields
                .iter()
                .map(|f| AccountField {
                    name: f.name.clone(),
                    offset: f.offset,
                    kind: match f.kind.as_str() {
                        "pubkey" => FieldKind::Pubkey,
                        "u64" => FieldKind::U64,
                        "byte" => FieldKind::Byte,
                        // "bytes" (or any unknown) -> opaque region; width_bytes carries the size.
                        _ => FieldKind::Bytes(f.width_bytes.unwrap_or(0)),
                    },
                })
                .collect(),
        })
        .collect()
}

/// Resolve an account layout by name, preferring qedrecover's sidecar tables over a fresh
/// IDL parse. Sidecar layouts are validated + emitted by qedrecover; the IDL fallback keeps
/// non-qedmeta runs (batch / single-arm `--idl`) byte-identical to the prior behaviour.
pub(super) fn resolve_layout(
    sidecar: Option<&[AccountLayout]>,
    idl: Option<&serde_json::Value>,
    name: &str,
) -> Option<AccountLayout> {
    sidecar
        .and_then(|ls| ls.iter().find(|l| l.name == name).cloned())
        .or_else(|| idl.and_then(|v| parse_account_layout(v, name).ok()))
}

// ════════════════════════════════════════════════════════════════
// Refinement descriptor (spec-driven obligation, prototype) — the seam to qedspec.
//
// A `.descriptor.json` is the shape qedgen *would* emit from a `.qedspec`: the
// account's field layout (its `State` projected to byte offsets), which field a
// handler mutates, and how. When qedlift is given one (`--descriptor`), it builds
// the layout-general `AsmRefinesFieldUpdate` obligation straight from the descriptor
// — NOT from the hardcoded `refine_registry` arm match and NOT by resolving the
// layout off a fixed role string. A new program then costs a descriptor, not a Rust
// edit. See docs/DEVEX_QEDSPEC_GAP.md.
// ════════════════════════════════════════════════════════════════

/// Newest refinement-descriptor schema this qedlift understands. The descriptor is a
/// cross-tool contract (qedgen produces it, qedlift consumes it), so it is versioned and
/// fail-closed exactly like `qedmeta` (`QEDMETA_SCHEMA_MAX`): a newer schema may carry
/// semantics we'd silently mis-consume, so we refuse it rather than guess. See
/// docs/REFINEMENT_DESCRIPTOR.md.
const DESCRIPTOR_SCHEMA_MAX: u32 = 2;

#[derive(Debug, serde::Deserialize)]
pub(super) struct RefinementDescriptor {
    /// Contract version. Absent (0) = pre-versioning, accepted; `> DESCRIPTOR_SCHEMA_MAX`
    /// is refused at load (fail-closed). Bump in lockstep with the producer (qedgen).
    #[serde(default)]
    pub(super) schema_version: u32,
    /// Account name. When `layout` is omitted (the IDL-driven default), this is the IDL
    /// account whose shape is resolved via `resolve_layout` — the same `qed-analysis` path
    /// the registry lift uses, so qedgen never needs its own layout parser. When `layout` is
    /// given inline, this is just a label.
    pub(super) account: String,
    /// qedspec handler this obligation comes from. Provenance only (rendered in the comment).
    #[serde(default)]
    pub(super) handler: Option<String>,
    /// Mutated field NAME. Its offset/kind come from the resolved layout (IDL or inline) —
    /// the seam is name-level; offsets are the IDL's job, not the descriptor's.
    pub(super) mutated: String,
    /// The mutation. `{ "add_const": k }` credits the field by a constant literal
    /// (k >= 1, schema v1); `{ "add_param": "name" }` credits it by a runtime parameter
    /// (schema v2). Subtraction / multi-field writes are a follow-up.
    pub(super) op: DescriptorOp,
    /// OPTIONAL explicit layout. ABSENT (the default) = resolve the shape from the IDL by
    /// `account` (the principled, IDL-driven form). PRESENT = hand-authored fallback for
    /// sBPF specs / fixtures with no IDL (e.g. the degenerate counter.so).
    #[serde(default)]
    pub(super) layout: Vec<DescriptorField>,
}

#[derive(Debug, serde::Deserialize)]
pub(super) struct DescriptorField {
    pub(super) offset: usize,
    /// "pubkey" | "u64" | "byte" | "bytes" (mirrors `qed_analysis::layout::FieldKind`).
    pub(super) kind: String,
    pub(super) name: String,
    /// Region width; required for `kind = "bytes"`, ignored otherwise.
    #[serde(default)]
    pub(super) width_bytes: Option<usize>,
}

/// The field mutation a descriptor claims. Untagged: the JSON object's key picks the
/// variant (`{add_const: k}` vs `{add_param: "name"}`), mirroring the qedgen producer.
#[derive(Debug, serde::Deserialize)]
#[serde(untagged)]
pub(super) enum DescriptorOp {
    /// `{ "add_const": k }`: credit the named field by a constant literal k (k >= 1 wired).
    AddConst { add_const: i64 },
    /// `{ "add_param": "name" }`: credit the named field by a runtime parameter (schema v2).
    /// The param's source cell is matched from the lift's reads (inline first-cut; the
    /// IDL instruction-args resolution that maps `name` to a serialized offset is a follow-on).
    AddParam { add_param: String },
}

fn descriptor_field_kind(kind: &str, width_bytes: Option<usize>) -> FieldKind {
    match kind {
        "pubkey" => FieldKind::Pubkey,
        "u64" => FieldKind::U64,
        "byte" => FieldKind::Byte,
        // "bytes" (or any unknown) -> opaque region; width_bytes carries the size.
        _ => FieldKind::Bytes(width_bytes.unwrap_or(0)),
    }
}

fn descriptor_field_width(kind: &FieldKind) -> usize {
    match kind {
        FieldKind::Pubkey => 32,
        FieldKind::U64 => 8,
        FieldKind::Byte => 1,
        FieldKind::Bytes(n) => *n,
    }
}

impl RefinementDescriptor {
    /// The inline layout, if the descriptor carries one (the no-IDL fallback). `None` means
    /// the shape is resolved from the IDL by `account` instead (see `resolve_layout`).
    pub(super) fn explicit_layout(&self) -> Option<AccountLayout> {
        if self.layout.is_empty() {
            return None;
        }
        let fields: Vec<AccountField> = self
            .layout
            .iter()
            .map(|f| AccountField {
                name: f.name.clone(),
                offset: f.offset,
                kind: descriptor_field_kind(&f.kind, f.width_bytes),
            })
            .collect();
        let size = fields
            .iter()
            .map(|f| f.offset + descriptor_field_width(&f.kind))
            .max()
            .unwrap_or(0);
        Some(AccountLayout {
            name: self.account.clone(),
            size,
            fields,
        })
    }
}

pub(super) fn load_descriptor(
    path: &Path,
) -> Result<RefinementDescriptor, Box<dyn std::error::Error>> {
    let text = std::fs::read_to_string(path)?;
    let desc: RefinementDescriptor = serde_json::from_str(&text)?;
    // Fail closed on a newer schema we might mis-consume (mirrors `load_qedmeta`).
    if desc.schema_version > DESCRIPTOR_SCHEMA_MAX {
        return Err(format!(
            "--descriptor {}: schema_version {} is newer than this qedlift understands \
             (max {})",
            path.display(),
            desc.schema_version,
            DESCRIPTOR_SCHEMA_MAX
        )
        .into());
    }
    // With an inline layout, the mutated field must be in it. Without one, the shape comes
    // from the IDL and the field is checked at emit time (the IDL isn't available here).
    if let Some(layout) = desc.explicit_layout() {
        if !layout.fields.iter().any(|f| f.name == desc.mutated) {
            return Err(format!(
                "--descriptor {}: mutated field {:?} is not in the inline layout",
                path.display(),
                desc.mutated
            )
            .into());
        }
    }
    Ok(desc)
}

pub(super) fn load_qedmeta(path: &Path) -> Result<QedMeta, Box<dyn std::error::Error>> {
    let text = std::fs::read_to_string(path)?;
    let meta: QedMeta = toml::from_str(&text)?;
    // Newer schema may carry semantics we'd silently mis-consume — fail closed.
    if meta.schema_version > QEDMETA_SCHEMA_MAX {
        return Err(format!(
            "--qedmeta {}: schema_version {} is newer than this qedlift \
             understands (max {})",
            path.display(),
            meta.schema_version,
            QEDMETA_SCHEMA_MAX
        )
        .into());
    }
    Ok(meta)
}

// IDL parsing: .toml (minimal in-tree fixture schema) or .json (Codama); both flatten to Vec<IdlInstruction>.

#[derive(Debug)]
pub(super) struct IdlInstruction {
    pub(super) name: String,
    pub(super) discriminator: i64,
}

#[derive(Debug, serde::Deserialize)]
struct IdlToml {
    instruction: Vec<IdlInstructionToml>,
}

#[derive(Debug, serde::Deserialize)]
struct IdlInstructionToml {
    name: String,
    discriminator: i64,
}

pub(super) fn load_idl(path: &Path) -> Result<Vec<IdlInstruction>, Box<dyn std::error::Error>> {
    let text = std::fs::read_to_string(path)?;
    match path.extension().and_then(|e| e.to_str()) {
        Some("toml") => {
            let raw: IdlToml = toml::from_str(&text)?;
            Ok(raw
                .instruction
                .into_iter()
                .map(|i| IdlInstruction {
                    name: i.name,
                    discriminator: i.discriminator,
                })
                .collect())
        }
        Some("json") => load_codama(&text),
        ext => Err(format!("unsupported IDL extension: {:?}", ext).into()),
    }
}

// Only fieldDiscriminatorNode at offset 0 is handled (covers SPL Token / p-token); Anchor 8-byte sighashes unsupported.
fn load_codama(text: &str) -> Result<Vec<IdlInstruction>, Box<dyn std::error::Error>> {
    let root: serde_json::Value = serde_json::from_str(text)?;
    let instructions = root
        .pointer("/program/instructions")
        .and_then(|v| v.as_array())
        .ok_or("codama: /program/instructions missing or not an array")?;
    let mut out = Vec::new();
    let mut skipped = Vec::new();
    for ix in instructions {
        let name = ix
            .get("name")
            .and_then(|v| v.as_str())
            .unwrap_or("?")
            .to_string();
        let discs = match ix.get("discriminators").and_then(|v| v.as_array()) {
            Some(d) if !d.is_empty() => d,
            _ => {
                skipped.push((name, "no discriminators"));
                continue;
            }
        };
        let d0 = &discs[0];
        let d_kind = d0.get("kind").and_then(|v| v.as_str()).unwrap_or("");
        let d_name = d0
            .get("name")
            .and_then(|v| v.as_str())
            .unwrap_or("")
            .to_string();
        let d_offset = d0.get("offset").and_then(|v| v.as_i64()).unwrap_or(-1);
        if d_kind != "fieldDiscriminatorNode" {
            skipped.push((name, "non-field discriminator"));
            continue;
        }
        if d_offset != 0 {
            skipped.push((name, "non-zero discriminator offset"));
            continue;
        }
        let args = ix.get("arguments").and_then(|v| v.as_array());
        let value = args
            .and_then(|a| {
                a.iter()
                    .find(|a| a.get("name").and_then(|v| v.as_str()) == Some(&d_name))
            })
            .and_then(|a| a.get("defaultValue"))
            .and_then(|v| v.get("number"))
            .and_then(|v| v.as_i64());
        match value {
            Some(n) => out.push(IdlInstruction {
                name,
                discriminator: n,
            }),
            None => skipped.push((name, "missing default value")),
        }
    }
    if !skipped.is_empty() {
        eprintln!("codama: skipped {} instruction(s):", skipped.len());
        for (n, why) in &skipped {
            eprintln!("  - {:<24} {}", n, why);
        }
    }
    Ok(out)
}

/// Load a Codama `.json` IDL as a raw `Value` for layout extraction; returns `None` for `.toml` or parse error.
pub(super) fn load_idl_value(path: &Path) -> Option<serde_json::Value> {
    if path.extension().and_then(|e| e.to_str()) != Some("json") {
        return None;
    }
    let text = std::fs::read_to_string(path).ok()?;
    serde_json::from_str(&text).ok()
}

pub(super) fn parse_args() -> Result<Args, String> {
    let mut so: Option<PathBuf> = None;
    let mut output: Option<PathBuf> = None;
    let mut module: Option<String> = None;
    let mut target_disc: Option<i64> = None;
    let mut idl: Option<PathBuf> = None;
    let mut output_dir: Option<PathBuf> = None;
    let mut trace: Option<PathBuf> = None;
    let mut arm_name: Option<String> = None;
    let mut qedmeta: Option<PathBuf> = None;
    let mut target_name: Option<String> = None;
    let mut descriptor: Option<PathBuf> = None;
    let mut transition = false;
    let mut shared_text: Option<String> = None;
    let mut it = std::env::args().skip(1);
    while let Some(a) = it.next() {
        match a.as_str() {
            "--so" => so = Some(it.next().ok_or("--so needs a path")?.into()),
            "--output" => output = Some(it.next().ok_or("--output needs a path")?.into()),
            "--module" => module = Some(it.next().ok_or("--module needs a name")?),
            "--target-disc" => {
                target_disc = Some(
                    it.next()
                        .ok_or("--target-disc needs an integer")?
                        .parse()
                        .map_err(|e| format!("--target-disc: {}", e))?,
                )
            }
            "--idl" => idl = Some(it.next().ok_or("--idl needs a path")?.into()),
            "--output-dir" => {
                output_dir = Some(it.next().ok_or("--output-dir needs a path")?.into())
            }
            "--trace" => trace = Some(it.next().ok_or("--trace needs a path")?.into()),
            "--arm-name" => arm_name = Some(it.next().ok_or("--arm-name needs a name")?),
            "--qedmeta" => qedmeta = Some(it.next().ok_or("--qedmeta needs a path")?.into()),
            "--target-name" => target_name = Some(it.next().ok_or("--target-name needs a name")?),
            "--descriptor" => {
                descriptor = Some(it.next().ok_or("--descriptor needs a path")?.into())
            }
            "--transition" => transition = true,
            "--shared-text" => {
                shared_text = Some(it.next().ok_or("--shared-text needs a base name")?)
            }
            other => return Err(format!("unknown arg: {}", other)),
        }
    }
    Ok(Args {
        so: so.ok_or("missing --so")?,
        output,
        module,
        target_disc,
        idl,
        output_dir,
        trace,
        arm_name,
        qedmeta,
        target_name,
        descriptor,
        transition,
        shared_text,
    })
}

// Per-binary context shared across arms in batch mode: building `Executable` for a large program
// (~80KB p_token) is ~10s, so sharing it keeps batch cost O(arms) not O(arms × binary).
pub(super) struct BinaryCtx {
    pub(super) executable: Executable<NoopCtx>,
    pub(super) text_offset: u64,
    pub(super) text_bytes: Vec<u8>,
    pub(super) insns: Vec<ebpf::Insn>,
    /// Slot<->logical PC converter (shared with qedrecover). Jump `off` fields are slot-relative;
    /// our `insns`/CodeReq PCs are logical indices. Mirrors `SVM/SBPF/Decode.lean` pass 1.
    pub(super) pc_map: PcMap,
}

/// Parse an execution-trace file: one decimal logical PC per line, in
/// execution order. Blank lines and `#`-prefixed comments are skipped.
/// Captured from the Lean runner's `TRACE_STEPS` output.
pub(super) fn load_trace(path: &Path) -> Result<Vec<usize>, Box<dyn std::error::Error>> {
    let text = std::fs::read_to_string(path)?;
    let mut pcs = Vec::new();
    for (lineno, raw) in text.lines().enumerate() {
        let line = raw.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let pc: usize = line.parse().map_err(|e| {
            format!(
                "--trace {}: line {}: not a decimal PC ({:?}): {}",
                path.display(),
                lineno + 1,
                line,
                e
            )
        })?;
        pcs.push(pc);
    }
    if pcs.is_empty() {
        return Err(format!("--trace {}: no PCs found", path.display()).into());
    }
    Ok(pcs)
}

pub(super) fn load_binary(so_path: &Path) -> Result<BinaryCtx, Box<dyn std::error::Error>> {
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
        let opc = insn.opc;
        // lddw spans 2 slots; merge the high-half immediate from the next slot to match decodeProgram.
        if opc == ebpf::LD_DW_IMM {
            ebpf::augment_lddw_unchecked(&text_bytes, &mut insn);
        }
        let span = if opc == ebpf::LD_DW_IMM { 2 } else { 1 };
        insns.push(insn);
        pc += span;
    }
    let pc_map = PcMap::from_insns(&insns);
    Ok(BinaryCtx {
        executable,
        text_offset,
        text_bytes,
        insns,
        pc_map,
    })
}

// PascalCase: "transfer_checked" -> "TransferChecked".
pub(super) fn pascal_case(s: &str) -> String {
    let mut out = String::new();
    let mut up = true;
    for c in s.chars() {
        if c == '_' || c == '-' || c == ' ' {
            up = true;
            continue;
        }
        if up {
            out.extend(c.to_uppercase());
            up = false;
        } else {
            out.push(c);
        }
    }
    out
}
