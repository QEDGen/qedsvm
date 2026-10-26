//! Emit untrusted, same-build source labels without loading Lean.
use qed_analysis::concept_map::ConceptMap;

fn run() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = std::env::args_os().skip(1).collect();
    if args.len() != 2 {
        return Err(
            "usage: qed-concept-map <deployed.so> <unstripped.debug> (JSON on stdout)".into(),
        );
    }
    let deployed = std::fs::read(&args[0])?;
    let debug = std::fs::read(&args[1])?;
    let map = ConceptMap::from_elf_bytes(&deployed, &debug)?;
    println!("{}", map.to_json()?);
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("qed-concept-map: {error}");
        std::process::exit(1);
    }
}
