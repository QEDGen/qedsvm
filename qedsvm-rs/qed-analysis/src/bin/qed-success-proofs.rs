//! Repository-owned regeneration entry point; no Lean runtime or debug sidecar required.
use std::path::PathBuf;

use qed_analysis::{
    discover::bindings::Bindings,
    image::ProgramImage,
    success_proofs::{
        bindings_gen::{generate_from_bindings, ProgramNames},
        generate, BaselineInputs,
    },
};

/// `--bindings <bindings.json> --names <Prefix> <ELF> <output-dir> [--check]` (#450).
fn run_bindings(args: &[std::ffi::OsString]) -> Result<(), Box<dyn std::error::Error>> {
    let check = args.len() == 7 && args[6] == "--check";
    if !(args.len() == 6 || check) || args[2] != "--names" {
        return Err("usage: qed-success-proofs --bindings <bindings.json> --names <Prefix> <program.so> <output-dir> [--check]".into());
    }
    let bindings = Bindings::from_json(&std::fs::read_to_string(&args[1])?)?;
    let prefix = args[3].to_str().ok_or("prefix is not UTF-8")?.to_string();
    let image = ProgramImage::load(&PathBuf::from(&args[4]))?;
    let generated = generate_from_bindings(&image, &bindings, &ProgramNames { prefix })?;
    let coverage = format!("{}\n", serde_json::to_string_pretty(&generated.coverage)?);
    let output = PathBuf::from(&args[5]);
    let files = [
        ("Text.lean", &generated.text),
        ("Success.lean", &generated.success),
        ("coverage.json", &coverage),
    ];
    if check {
        for (name, expected) in files {
            let path = output.join(name);
            let actual =
                std::fs::read(&path).map_err(|error| format!("{}: {error}", path.display()))?;
            if actual != expected.as_bytes() {
                return Err(format!("generated proof drift: {}", path.display()).into());
            }
        }
    } else {
        std::fs::create_dir_all(&output)?;
        for (name, contents) in files {
            std::fs::write(output.join(name), contents)?;
        }
    }
    eprintln!(
        "{} success proofs: {} proven edges, {} pinned guards, {} readable facts",
        if check { "checked" } else { "generated" },
        generated.coverage.proven_edges,
        generated.coverage.pinned_guards,
        generated.coverage.readable_facts
    );
    Ok(())
}

fn run() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = std::env::args_os().skip(1).collect();
    if args.first().is_some_and(|a| a == "--bindings") {
        return run_bindings(&args);
    }
    if !(args.len() == 3 || (args.len() == 4 && args[3] == "--check")) {
        return Err("usage: qed-success-proofs <p_token.so> <success-proof-inputs.json> <output-dir> [--check]".into());
    }
    let image = ProgramImage::load(&PathBuf::from(&args[0]))?;
    let inputs: BaselineInputs = serde_json::from_slice(&std::fs::read(&args[1])?)?;
    // Complete validation and generation before creating directories or touching files.
    let generated = generate(&image, &inputs)?;
    let output = PathBuf::from(&args[2]);
    let files = [
        ("SuccessPaths.lean", &generated.paths),
        ("SuccessInputs.lean", &generated.inputs),
        ("ReadableFields.lean", &generated.readable_fields),
    ];
    if args.len() == 4 {
        for (name, expected) in files {
            let path = output.join(name);
            let actual =
                std::fs::read(&path).map_err(|error| format!("{}: {error}", path.display()))?;
            if actual != expected.as_bytes() {
                return Err(format!("generated proof drift: {}", path.display()).into());
            }
        }
    } else {
        std::fs::create_dir_all(&output)?;
        for (name, contents) in files {
            std::fs::write(output.join(name), contents)?;
        }
    }
    eprintln!(
        "{} success proofs: {} edges, {} guards, {} input pins",
        if args.len() == 4 {
            "checked"
        } else {
            "generated"
        },
        inputs.edges.len(),
        generated.guard_count,
        generated.input_guard_count
    );
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("qed-success-proofs: {error}");
        std::process::exit(1);
    }
}
