use std::path::{Path, PathBuf};

use qed_analysis::{
    image::ProgramImage,
    layout::{parse_account_layout, AccountLayout},
};

pub(super) struct Args {
    pub(super) command: Command,
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
    /// Restrict a `--qedmeta` run to a single instruction by name.
    pub(super) target_name: Option<String>,
    /// Spec-driven refinement descriptor (`*.descriptor.json`). When given
    /// (single-arm mode), qedlift builds the layout-general
    /// `AsmRefinesFieldUpdate` obligation from the descriptor instead of the
    /// hardcoded `refine_registry` arm match. The seam to qedspec.
    pub(super) descriptor: Option<PathBuf>,
    /// Shared-text base name (batch dedup, e.g. `PToken`). When given, the
    /// binary's Text/SlotMap/FnRegistry defs are emitted ONCE into
    /// `Generated/{base}Text.lean` and every arm lift imports that module
    /// instead of re-embedding the ~100KB `.text` blob. Requires the
    /// large-text decode-pins path (fails closed on small inline-bridge
    /// binaries).
    pub(super) shared_text: Option<String>,
}

/// Mutually exclusive top-level operation selected by the CLI.
pub(super) enum Command {
    Profile,
    Coverage,
    Transition,
    QedMeta { path: PathBuf },
    Batch { idl: PathBuf, output_dir: PathBuf },
    Single,
}

pub(super) use qed_artifacts::{
    load_descriptor, load_qedmeta, DescriptorOp, QedMeta, RefinementDescriptor,
};

pub(super) fn sidecar_account_layouts(meta: &QedMeta) -> Vec<AccountLayout> {
    meta.account_layouts()
}

/// Resolve an account layout by name, preferring qedrecover's sidecar tables.
pub(super) fn resolve_layout(
    sidecar: Option<&[AccountLayout]>,
    idl: Option<&serde_json::Value>,
    name: &str,
) -> Option<AccountLayout> {
    sidecar
        .and_then(|layouts| layouts.iter().find(|layout| layout.name == name).cloned())
        .or_else(|| idl.and_then(|value| parse_account_layout(value, name).ok()))
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
    parse_args_from(std::env::args().skip(1))
}

fn parse_args_from(args: impl IntoIterator<Item = String>) -> Result<Args, String> {
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
    let mut profile = false;
    let mut coverage = false;
    let mut it = args.into_iter();
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
            "--profile" => profile = true,
            "--coverage" => coverage = true,
            other => return Err(format!("unknown arg: {}", other)),
        }
    }
    let explicit_modes = usize::from(profile)
        + usize::from(coverage)
        + usize::from(transition)
        + usize::from(qedmeta.is_some());
    if explicit_modes > 1 {
        return Err(
            "qedlift modes are mutually exclusive: choose one of --profile, --coverage, \
             --transition, or --qedmeta"
                .to_string(),
        );
    }
    let command = if profile {
        Command::Profile
    } else if coverage {
        Command::Coverage
    } else if transition {
        Command::Transition
    } else if let Some(path) = qedmeta.clone() {
        Command::QedMeta { path }
    } else if let (Some(idl), Some(output_dir)) = (idl.clone(), output_dir.clone()) {
        Command::Batch { idl, output_dir }
    } else {
        Command::Single
    };
    Ok(Args {
        command,
        so: so.ok_or("missing --so")?,
        output,
        module,
        target_disc,
        idl,
        output_dir,
        trace,
        arm_name,
        target_name,
        descriptor,
        shared_text,
    })
}

// Per-binary context shared across arms in batch mode: building `Executable` for a large program
// (~80KB p_token) is ~10s, so sharing it keeps batch cost O(arms) not O(arms × binary).
pub(super) type BinaryCtx = ProgramImage;

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
    ProgramImage::load(so_path)
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

#[cfg(test)]
mod command_tests {
    use super::*;

    fn parse(args: &[&str]) -> Result<Args, String> {
        parse_args_from(args.iter().map(|arg| (*arg).to_string()))
    }

    #[test]
    fn rejects_conflicting_modes() {
        let error = parse(&["--so", "program.so", "--profile", "--coverage"])
            .err()
            .expect("conflicting modes must fail");
        assert!(error.contains("mutually exclusive"));
    }

    #[test]
    fn idl_and_output_dir_select_batch_mode() {
        let args = parse(&[
            "--so",
            "program.so",
            "--idl",
            "program.json",
            "--output-dir",
            "Generated",
        ])
        .expect("batch arguments");
        assert!(matches!(args.command, Command::Batch { .. }));
    }
}
