use std::path::{Path, PathBuf};

use qed_artifacts::load_qedmeta;

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../qed-artifacts/tests/fixtures")
        .join(name)
}

#[test]
fn canonical_qedmeta_versions_match_the_producer_contract() {
    let legacy = load_qedmeta(&fixture("qedmeta-v1.toml")).expect("load canonical v1");
    assert_eq!(legacy.instructions[0].name, "increment");
    assert!(legacy.instructions[0].recovered.is_none());

    let current = load_qedmeta(&fixture("qedmeta-v2.toml")).expect("load canonical v2");
    let instruction = &current.instructions[0];
    assert_eq!(instruction.accounts[0].layout.as_deref(), Some("counter"));
    assert_eq!(
        instruction
            .recovered
            .as_ref()
            .expect("recovered producer facts")
            .arm_entry_pc,
        4
    );
}
