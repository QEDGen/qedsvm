//! Discover untrusted success-proof bindings from a same-build binary pair (#450).
use qed_analysis::{concept_map::ConceptMap, discover::bindings::discover};
use sha2::{Digest, Sha256};

fn run() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = std::env::args_os().skip(1).collect();
    if args.len() != 3 {
        return Err(
            "usage: qed-discover <deployed.so> <debug.so> <concepts.json> (JSON on stdout)".into(),
        );
    }
    let deployed = std::fs::read(&args[0])?;
    let debug = std::fs::read(&args[1])?;
    let map: ConceptMap = serde_json::from_str(&std::fs::read_to_string(&args[2])?)?;
    let debug_sha = format!("{:x}", Sha256::digest(&debug));
    if map.artifact.debug_sha256 != debug_sha {
        return Err(
            format!("concept map was not made from this debug binary ({debug_sha})").into(),
        );
    }
    let bindings = discover(&deployed, &map)?;
    println!("{}", bindings.to_json()?);
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("qed-discover: {error}");
        std::process::exit(1);
    }
}
