use std::path::{Path, PathBuf};

use qed_artifacts::{load_descriptor, load_qedmeta, ArtifactError, DescriptorOp};

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../qed-artifacts/tests/fixtures")
        .join(name)
}

#[test]
fn canonical_legacy_and_current_artifacts_match_the_lifter_contract() {
    let legacy_meta = load_qedmeta(&fixture("qedmeta-v1.toml")).expect("load canonical v1 meta");
    assert!(legacy_meta.account_layouts().is_empty());

    let current_meta = load_qedmeta(&fixture("qedmeta-v2.toml")).expect("load canonical v2 meta");
    assert_eq!(current_meta.account_layouts()[0].name, "counter");

    let legacy_descriptor =
        load_descriptor(&fixture("descriptor-v1.json")).expect("load canonical v1 descriptor");
    assert!(matches!(
        legacy_descriptor.op,
        DescriptorOp::AddConst { add_const: 1 }
    ));

    let current_descriptor =
        load_descriptor(&fixture("descriptor-v2.json")).expect("load canonical v2 descriptor");
    assert!(matches!(
        current_descriptor.op,
        DescriptorOp::AddParam { ref add_param } if add_param == "amount"
    ));
}

#[test]
fn canonical_future_artifacts_are_rejected_by_the_lifter_contract() {
    assert!(matches!(
        load_qedmeta(&fixture("qedmeta-future.toml")),
        Err(ArtifactError::UnsupportedSchema { .. })
    ));
    assert!(matches!(
        load_descriptor(&fixture("descriptor-future.json")),
        Err(ArtifactError::UnsupportedSchema { .. })
    ));
}
