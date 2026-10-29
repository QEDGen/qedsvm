use qed_analysis::{concept_map::ConceptMap, discover::bindings::discover};
use std::process::Command;

const SO: &str = "../tests/fixtures/label_vault.so";
const DEBUG: &str = "../tests/fixtures/label_vault.debug.so";

fn map() -> ConceptMap {
    ConceptMap::from_elf_bytes(&std::fs::read(SO).unwrap(), &std::fs::read(DEBUG).unwrap()).unwrap()
}

fn cli(args: &[&str]) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_qed-discover"))
        .args(args)
        .output()
        .unwrap()
}

fn concepts_file(name: &str, map: &ConceptMap) -> String {
    let dir = std::env::temp_dir().join(format!("qed-discover-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(name);
    std::fs::write(&path, map.to_json().unwrap()).unwrap();
    path.to_string_lossy().into_owned()
}

#[test]
fn q5_label_vault_bindings_golden() {
    let b = discover(&std::fs::read(SO).unwrap(), &map()).unwrap();
    let json = b.to_json().unwrap();
    let golden = include_str!("../../tests/fixtures/label_vault.bindings.json");
    assert_eq!(
        format!("{json}\n"),
        golden,
        "regenerate label_vault.bindings.json"
    );
}

#[test]
fn q5_cli_matches_library_and_is_deterministic() {
    let concepts = concepts_file("lv.json", &map());
    let a = cli(&[SO, DEBUG, &concepts]);
    let b = cli(&[SO, DEBUG, &concepts]);
    assert!(a.status.success(), "{}", String::from_utf8_lossy(&a.stderr));
    assert_eq!(a.stdout, b.stdout);
    let lib = discover(&std::fs::read(SO).unwrap(), &map())
        .unwrap()
        .to_json()
        .unwrap();
    assert_eq!(String::from_utf8(a.stdout).unwrap(), format!("{lib}\n"));
}

#[test]
fn q5_stale_concept_map_is_refused() {
    let p = ConceptMap::from_elf_bytes(
        &std::fs::read("../tests/fixtures/debug_concepts.so").unwrap(),
        &std::fs::read("../tests/fixtures/debug_concepts.debug").unwrap(),
    )
    .unwrap();
    let concepts = concepts_file("stale.json", &p);
    let out = cli(&[SO, DEBUG, &concepts]);
    assert!(!out.status.success());
    assert!(out.stdout.is_empty());
    assert!(discover(&std::fs::read(SO).unwrap(), &p).is_err());
}

#[test]
fn q5_mismatched_pair_is_refused() {
    let concepts = concepts_file("lv2.json", &map());
    let out = cli(&[SO, "../tests/fixtures/debug_concepts.debug", &concepts]);
    assert!(!out.status.success());
    assert!(out.stdout.is_empty());
}

#[test]
fn q5_missing_types_gives_diagnostic() {
    let mut m = map();
    m.structures.clear();
    let b = discover(&std::fs::read(SO).unwrap(), &m).unwrap();
    assert!(b
        .edges
        .iter()
        .flat_map(|e| &e.fields)
        .all(|f| f.name.is_none()));
    assert!(b.edges.iter().flat_map(|e| &e.fields).count() > 0);
    assert!(
        b.diagnostics.iter().any(|d| d.contains("struct")),
        "{:?}",
        b.diagnostics
    );
}

#[test]
fn q5_duplicate_marker_guard_is_dominating() {
    let b = discover(&std::fs::read(SO).unwrap(), &map()).unwrap();
    assert_eq!(b.edges.len(), 1);
    assert_eq!(b.edges[0].non_duplicate, vec![0, 1]);
}

#[test]
fn q5_unchecked_length_is_visible() {
    let b = discover(&std::fs::read(SO).unwrap(), &map()).unwrap();
    let w = &b.edges[0].assumed;
    assert_eq!((w[0].value, w[0].checked), (48, true));
    assert_eq!((w[1].value, w[1].checked), (0, false));
}
