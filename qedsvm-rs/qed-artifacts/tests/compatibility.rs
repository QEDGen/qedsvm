use std::path::{Path, PathBuf};

use qed_artifacts::{
    descriptor_schema_compatibility, load_descriptor, load_qedmeta, qedmeta_schema_compatibility,
    ArtifactError, DescriptorOp, SchemaCompatibility,
};

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures")
        .join(name)
}

#[test]
fn compatibility_matrix_is_explicit() {
    assert_eq!(
        qedmeta_schema_compatibility(0),
        SchemaCompatibility::Unversioned
    );
    assert_eq!(qedmeta_schema_compatibility(1), SchemaCompatibility::Legacy);
    assert_eq!(
        qedmeta_schema_compatibility(2),
        SchemaCompatibility::Current
    );
    assert_eq!(qedmeta_schema_compatibility(3), SchemaCompatibility::Future);
    assert_eq!(
        descriptor_schema_compatibility(1),
        SchemaCompatibility::Legacy
    );
    assert_eq!(
        descriptor_schema_compatibility(2),
        SchemaCompatibility::Current
    );
}

#[test]
fn qedmeta_legacy_defaults_and_current_fields_are_compatible() {
    let legacy = load_qedmeta(&fixture("qedmeta-v1.toml")).expect("load v1 qedmeta");
    assert_eq!(legacy.schema_version, 1);
    assert!(legacy.account_layouts.is_empty());
    assert!(legacy.instructions[0].recovered.is_none());

    let current = load_qedmeta(&fixture("qedmeta-v2.toml")).expect("load v2 qedmeta");
    assert_eq!(current.schema_version, 2);
    assert_eq!(current.account_layouts()[0].fields[0].name, "value");
    assert_eq!(
        current.instructions[0]
            .recovered
            .as_ref()
            .expect("v2 recovered facts")
            .arm_entry_pc,
        4
    );
}

#[test]
fn descriptor_legacy_and_current_operations_are_compatible() {
    let legacy = load_descriptor(&fixture("descriptor-v1.json")).expect("load v1 descriptor");
    assert!(matches!(legacy.op, DescriptorOp::AddConst { add_const: 1 }));

    let current = load_descriptor(&fixture("descriptor-v2.json")).expect("load v2 descriptor");
    assert!(matches!(
        current.op,
        DescriptorOp::AddParam { ref add_param } if add_param == "amount"
    ));
}

#[test]
fn future_schemas_fail_closed() {
    assert!(matches!(
        load_qedmeta(&fixture("qedmeta-future.toml")),
        Err(ArtifactError::UnsupportedSchema {
            artifact: "qedmeta",
            found: 999,
            max: 2,
            ..
        })
    ));
    assert!(matches!(
        load_descriptor(&fixture("descriptor-future.json")),
        Err(ArtifactError::UnsupportedSchema {
            artifact: "descriptor",
            found: 999,
            max: 2,
            ..
        })
    ));
}
