use qed_analysis::{
    cfg::Cfg,
    concept_map::ConceptMap,
    discover::{
        authority::{route_authority, KeyCompare},
        dispatch::{discover_instructions, Dispatch},
        fields::{label_fields, LabelStatus},
    },
    image::ProgramImage,
};
use std::path::Path;

fn fixture() -> (ProgramImage, Cfg, ConceptMap, Dispatch) {
    let deployed = std::fs::read("../tests/fixtures/label_vault.so").unwrap();
    let debug = std::fs::read("../tests/fixtures/label_vault.debug.so").unwrap();
    let image = ProgramImage::load(Path::new("../tests/fixtures/label_vault.so")).unwrap();
    let cfg = Cfg::build(&image).unwrap();
    let map = ConceptMap::from_elf_bytes(&deployed, &debug).unwrap();
    let d = discover_instructions(&image, &cfg, Some(&map)).unwrap();
    (image, cfg, map, d)
}

fn route_of(d: &Dispatch, disc: u64) -> usize {
    d.instructions
        .iter()
        .find(|i| i.discriminator == disc)
        .unwrap()
        .routes[0]
}

#[test]
fn q4_increment_route_checks_signer_and_stored_authority() {
    let (image, cfg, _, d) = fixture();
    let a = route_authority(&image, &cfg, &d.layouts[0], route_of(&d, 1)).unwrap();
    assert_eq!(a.signers, vec![1]);
    assert_eq!(
        a.key_compares,
        vec![KeyCompare {
            account: 1,
            against_account: 0,
            against_data_offset: 8
        }]
    );
}

#[test]
fn q4_initialize_route_checks_signer_only() {
    let (image, cfg, _, d) = fixture();
    let a = route_authority(&image, &cfg, &d.layouts[0], route_of(&d, 0)).unwrap();
    assert_eq!(a.signers, vec![1]);
    assert!(a.key_compares.is_empty());
}

#[test]
fn q4_vault_fields_are_labelled() {
    let (_, _, map, _) = fixture();
    let labels = label_fields(&map, 48, &[(0, 1), (8, 8), (16, 8), (24, 8), (32, 8)]);
    let named: Vec<_> = labels
        .iter()
        .map(|l| {
            (
                l.data_offset,
                l.name.clone(),
                matches!(l.status, LabelStatus::Labelled { .. }),
            )
        })
        .collect();
    assert_eq!(named[0], (0, Some("initialized".into()), true));
    assert_eq!(named[1], (8, Some("authority".into()), true));
    assert_eq!(named[4], (32, Some("authority".into()), true));
}

#[test]
fn q4_struct_size_match_without_member_cover_is_refused() {
    let (_, _, mut map, _) = fixture();
    let vault = map
        .structures
        .iter_mut()
        .find(|s| s.name.as_deref() == Some("Vault"))
        .unwrap();
    vault.members.retain(|m| m.byte_offset == Some(0));
    // Offset 8 is now in no member of Vault; no other 48-byte struct may stand in for it.
    let labels = label_fields(&map, 48, &[(0, 1), (8, 8)]);
    assert!(
        labels
            .iter()
            .all(|l| matches!(l.status, LabelStatus::Refused(_))),
        "{labels:?}"
    );
}

#[test]
fn q4_ambiguous_struct_is_refused() {
    let (_, _, mut map, _) = fixture();
    let mut twin = map
        .structures
        .iter()
        .find(|s| s.name.as_deref() == Some("Vault"))
        .unwrap()
        .clone();
    twin.id = "die:twin".into();
    twin.name = Some("VaultTwin".into());
    map.structures.push(twin);
    let labels = label_fields(&map, 48, &[(0, 1)]);
    assert!(matches!(labels[0].status, LabelStatus::Refused(_)));
    assert_eq!(labels[0].name, None);
}

#[test]
fn q4_missing_types_refuse_every_label() {
    let (_, _, mut map, _) = fixture();
    map.structures.clear();
    let labels = label_fields(&map, 48, &[(0, 1)]);
    assert!(matches!(labels[0].status, LabelStatus::Refused(_)));
}
