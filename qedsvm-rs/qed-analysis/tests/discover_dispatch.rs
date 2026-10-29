use qed_analysis::{
    cfg::Cfg,
    concept_map::ConceptMap,
    discover::dispatch::{discover_instructions, edge_layout, LenStatus, Unsupported},
    image::ProgramImage,
    success_proofs::provenance::Width,
};
use std::path::Path;

fn load(name: &str) -> (ProgramImage, Cfg) {
    let image = ProgramImage::load(Path::new(&format!("../tests/fixtures/{name}"))).unwrap();
    let cfg = Cfg::build(&image).unwrap();
    (image, cfg)
}

fn label_vault_map() -> ConceptMap {
    let deployed = std::fs::read("../tests/fixtures/label_vault.so").unwrap();
    let debug = std::fs::read("../tests/fixtures/label_vault.debug.so").unwrap();
    ConceptMap::from_elf_bytes(&deployed, &debug).unwrap()
}

#[test]
fn q3_label_vault_layout_assumes_checked_and_unchecked_lengths() {
    let (image, cfg) = load("label_vault.so");
    let layout = edge_layout(&image, &cfg, 53).unwrap();
    assert_eq!(layout.accounts, 2);
    assert_eq!(layout.instruction_data, 0x5100);
    assert_eq!(layout.assumed.len(), 2);
    // The vault's length is checked by the program (`data_len == 48`).
    assert_eq!(layout.assumed[0].0, (0x58, Width::Dword, 48));
    assert!(matches!(layout.assumed[0].1, LenStatus::Checked { .. }));
    // The authority's length is not checked; the theorem assumes 0 and says so.
    assert_eq!(layout.assumed[1].0, (0x28e8, Width::Dword, 0));
    assert_eq!(layout.assumed[1].1, LenStatus::Unchecked);
}

#[test]
fn q3_label_vault_has_three_instructions() {
    let (image, cfg) = load("label_vault.so");
    let ix = discover_instructions(&image, &cfg, Some(&label_vault_map()))
        .unwrap()
        .instructions;
    let discs: Vec<u64> = ix.iter().map(|i| i.discriminator).collect();
    assert_eq!(discs, vec![0, 1, 2]);
    for (i, name) in ix.iter().zip(["initialize", "increment", "reset"]) {
        assert_eq!(i.success_edges, vec![53], "{name}");
        assert!(!i.routes.is_empty());
        let handler = i.handler.as_ref().map(|l| l.name.as_str()).unwrap_or("");
        assert!(handler.ends_with(name), "{name}: handler label {handler:?}");
    }
}

#[test]
fn q3_handler_labels_are_optional() {
    let (image, cfg) = load("label_vault.so");
    let ix = discover_instructions(&image, &cfg, None)
        .unwrap()
        .instructions;
    assert_eq!(ix.len(), 3);
    assert!(ix.iter().all(|i| i.handler.is_none()));
}

/// The 19 p_token success edges behind loops (docs/SUCCESS_PROOFS.md).
const PTOKEN_LOOP_EDGES: [usize; 19] = [
    3575, 3584, 4065, 4141, 4177, 4226, 4237, 4310, 4346, 4391, 4401, 4527, 4556, 4672, 4679, 4759,
    4793, 5159, 5426,
];

#[test]
fn q3_ptoken_transfer_edges_found_from_dispatch() {
    let (image, cfg) = load("p_token.so");
    let ix = discover_instructions(&image, &cfg, None)
        .unwrap()
        .instructions;
    let edges = |d: u64| {
        ix.iter()
            .find(|i| i.discriminator == d)
            .map(|i| i.success_edges.clone())
            .unwrap_or_default()
    };
    for e in [4825, 4832, 5250] {
        assert!(edges(3).contains(&e), "transfer edge {e}");
    }
    for e in [5063, 5070, 5473] {
        assert!(edges(12).contains(&e), "transfer_checked edge {e}");
    }
}

#[test]
fn q3_loop_success_path_is_unsupported() {
    let (image, cfg) = load("p_token.so");
    let d = discover_instructions(&image, &cfg, None).unwrap();
    for i in &d.instructions {
        for e in &i.success_edges {
            assert!(
                !PTOKEN_LOOP_EDGES.contains(e),
                "loop edge {e} counted as supported"
            );
        }
    }
    let mut loops: Vec<usize> = d
        .unsupported
        .iter()
        .filter(|(_, u)| *u == Unsupported::Loop)
        .map(|(e, _)| *e)
        .collect();
    loops.sort_unstable();
    assert_eq!(loops, PTOKEN_LOOP_EDGES.to_vec());
}
