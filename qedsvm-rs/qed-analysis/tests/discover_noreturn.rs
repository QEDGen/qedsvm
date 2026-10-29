use qed_analysis::{
    cfg::Cfg,
    discover::noreturn::{noreturn_witness, NoRetStep},
    image::ProgramImage,
};
use std::path::Path;

fn load(name: &str) -> (ProgramImage, Cfg) {
    let image = ProgramImage::load(Path::new(&format!("../tests/fixtures/{name}"))).unwrap();
    let cfg = Cfg::build(&image).unwrap();
    (image, cfg)
}

#[test]
fn q1_ptoken_witness_matches_hand_chain() {
    let (image, cfg) = load("p_token.so");
    let w = noreturn_witness(&image, &cfg).unwrap();
    // The entrypoint's two helpers, plus the chain functions they call.
    for head in [10881, 11177, 11618, 10862, 10823] {
        assert!(w.heads.contains(&head), "missing head {head}");
    }
    assert!(w.steps.contains(&NoRetStep::PanicCall { pc: 10829 }));
    assert!(w
        .steps
        .contains(&NoRetStep::Straight { pc: 11618, len: 22 }));
    assert!(w.steps.contains(&NoRetStep::CallLocal {
        pc: 11177,
        target: 11618
    }));
    assert!(w.skipped.is_empty(), "{:?}", w.skipped);
}

#[test]
fn q1_steps_continue_only_at_earlier_steps() {
    let (image, cfg) = load("p_token.so");
    let w = noreturn_witness(&image, &cfg).unwrap();
    let mut done = std::collections::BTreeSet::new();
    for step in &w.steps {
        match *step {
            NoRetStep::Straight { pc, len } => assert!(done.contains(&(pc + len))),
            NoRetStep::CallLocal { target, .. } => assert!(done.contains(&target)),
            NoRetStep::Branch { pc, target } => {
                assert!(done.contains(&target) && done.contains(&(pc + 1)))
            }
            NoRetStep::PanicCall { .. } => {}
        }
        done.insert(step.pc());
    }
    assert!(w.heads.iter().all(|h| done.contains(h)));
}

#[test]
fn q1_lean_literal_shape() {
    let (image, cfg) = load("p_token.so");
    let lean = noreturn_witness(&image, &cfg).unwrap().to_lean();
    assert!(lean.starts_with("{ heads := ["));
    assert!(lean.contains(".panicCall 10829"));
    assert!(lean.contains(".straight 11618 22"));
}

#[test]
fn q1_lean_regression_uses_emitted_witness() {
    let (image, cfg) = load("p_token.so");
    let lean = noreturn_witness(&image, &cfg).unwrap().to_lean();
    let module = include_str!("../../../examples/lean/PToken/NoReturnGeneric.lean");
    assert!(
        module.contains(&lean),
        "regenerate the witness in NoReturnGeneric.lean:\n{lean}"
    );
}

#[test]
fn q1_label_vault_witness_nonempty_and_ends_in_panic() {
    let (image, cfg) = load("label_vault.so");
    let w = noreturn_witness(&image, &cfg).unwrap();
    assert!(!w.heads.is_empty());
    assert!(w.skipped.is_empty(), "{:?}", w.skipped);
    assert!(w
        .steps
        .iter()
        .any(|s| matches!(s, NoRetStep::PanicCall { .. })));
    // `slice_index_fail` branches before `panic_fmt`.
    assert!(w
        .steps
        .iter()
        .any(|s| matches!(s, NoRetStep::Branch { .. })));
}
