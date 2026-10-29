use qed_analysis::{
    discover::bindings::Bindings,
    image::ProgramImage,
    success_proofs::bindings_gen::{generate_from_bindings, ProgramNames},
};
use std::path::Path;

fn image() -> ProgramImage {
    ProgramImage::load(Path::new("../tests/fixtures/label_vault.so")).unwrap()
}

fn bindings() -> Bindings {
    Bindings::from_json(include_str!(
        "../../tests/fixtures/label_vault.bindings.json"
    ))
    .unwrap()
}

fn names() -> ProgramNames {
    ProgramNames {
        prefix: "LabelVault".into(),
    }
}

#[test]
fn q6_label_vault_modules_golden() {
    let g = generate_from_bindings(&image(), &bindings(), &names()).unwrap();
    assert_eq!(
        g.success,
        include_str!("../../../examples/lean/LabelVault/Success.lean")
    );
    assert_eq!(
        g.text,
        include_str!("../../../examples/lean/LabelVault/Text.lean")
    );
}

#[test]
fn q6_coverage_counts_label_vault() {
    let c = generate_from_bindings(&image(), &bindings(), &names())
        .unwrap()
        .coverage;
    assert_eq!(
        (c.instructions, c.success_edges, c.proven_edges, c.routes),
        (3, 1, 1, 3)
    );
    assert_eq!(
        (c.unchecked_lengths, c.refused_labels, c.unsupported_edges),
        (1, 0, 0)
    );
    assert_eq!(c.native_decide_uses, 5);
}

#[test]
fn q6_increment_requires_signer_and_stored_authority() {
    let g = generate_from_bindings(&image(), &bindings(), &names()).unwrap();
    let ix1 = g.success.split("def requires53_ix1").nth(1).unwrap();
    let ix1 = ix1.split("theorem").next().unwrap();
    assert!(ix1.contains("ix_data_0 s0 = 1"));
    assert!(ix1.contains("acct1_is_signer s0 ≠ 0"));
    for k in 0..4 {
        let off = 8 + 8 * k;
        assert!(
            ix1.contains(&format!("acct1_key_{k} s0 = acct0_authority_{off} s0")),
            "limb {k}"
        );
    }
}

#[test]
fn q6_refused_label_not_in_conclusion() {
    let mut b = bindings();
    for f in &mut b.edges[0].fields {
        f.name = None;
        f.refused = Some("test".into());
    }
    let g = generate_from_bindings(&image(), &b, &names()).unwrap();
    assert!(!g.success.contains("authority_"));
    assert!(!g.success.contains("initialized"));
    assert!(g.success.contains("acct0_data_8 s0"));
    assert_eq!(g.coverage.refused_labels, 5);
}

#[test]
fn q6_bindings_for_other_elf_refused() {
    let other = ProgramImage::load(Path::new("../tests/fixtures/p_token.so")).unwrap();
    assert!(generate_from_bindings(&other, &bindings(), &names()).is_err());
}

#[test]
fn q6_bad_prefix_refused() {
    let bad = ProgramNames {
        prefix: "Label.Vault".into(),
    };
    assert!(generate_from_bindings(&image(), &bindings(), &bad).is_err());
}

#[test]
fn q6_decode_is_checked_not_assumed() {
    let g = generate_from_bindings(&image(), &bindings(), &names()).unwrap();
    assert!(g
        .success
        .contains("theorem decodes : insns?.isSome = true := by\n  native_decide"));
    let readable = g.success.split("theorem readable53").nth(1).unwrap();
    let signature = readable.split(":= by").next().unwrap();
    assert!(
        !signature.contains("insns? = some"),
        "readable53 still assumes decoding: {signature}"
    );
    assert_eq!(g.coverage.native_decide_uses, 5);
}

#[test]
fn q6_route_facts_come_from_the_conclusion() {
    let c = generate_from_bindings(&image(), &bindings(), &names())
        .unwrap()
        .coverage;
    let route = |d: u64| c.route_facts.iter().find(|r| r.discriminator == d).unwrap();
    assert_eq!(route(1).proven_signers, vec![1]);
    assert_eq!(
        route(1).proven_key_compares,
        vec!["account 1 key == account 0 data[8..40]".to_string()]
    );
    assert_eq!(route(0).proven_signers, vec![1]);
    assert!(route(0).proven_key_compares.is_empty());
    // increment's instruction-length and checked_add guards are not pinned: reported, not hidden.
    let unpinned: Vec<usize> = route(1).unpinned.iter().map(|u| u.pc).collect();
    assert!(!unpinned.is_empty(), "{unpinned:?}");
    assert!(c.route_facts.iter().all(|r| r.opaque_calls.is_empty()));
}

#[test]
fn q6_doc_comments_escape_labels() {
    let mut b = bindings();
    b.instructions[0].handler = Some("evil -/ axiom bad : False /-".into());
    let g = generate_from_bindings(&image(), &b, &names()).unwrap();
    assert!(!g.success.contains("evil -/"));
}
