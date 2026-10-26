//! Repository-owned regeneration entry point; no Lean runtime or debug sidecar required.
use std::path::PathBuf;

use qed_analysis::{
    image::ProgramImage,
    success_proofs::{generate, BaselineInputs},
};

fn run() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = std::env::args_os().skip(1).collect();
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
