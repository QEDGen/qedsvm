//! Isolated reproducer for the `Curve25519.validateEdwards` runtime
//! FFI SIGSEGV. Runs the minimal `curve_validate_probe.so` through
//! `qedsvm::Svm::process_instruction` and reports the outcome
//! (or the SIGSEGV).
//!
//! This test does NOT use `--features diff-mollusk`; it exercises
//! our engine alone so we can isolate the curve25519 FFI without any
//! mollusk noise.

use qedsvm::{ProgramResult, Svm};
use solana_instruction::Instruction;
use solana_pubkey::Pubkey;

const CURVE_VALIDATE_PROBE_SO: &[u8] =
    include_bytes!("fixtures/curve_validate_probe.so");

fn pid(seed: u64) -> Pubkey {
    let mut b = [0u8; 32];
    b[..8].copy_from_slice(&seed.to_le_bytes());
    Pubkey::from(b)
}

#[test]
fn curve_validate_via_runtime() {
    let program_id = pid(60);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };
    eprintln!(">>> Svm::default()");
    let mut svm = Svm::default().with_cu_budget(1_400_000);
    eprintln!(">>> add_program");
    svm.add_program(&program_id, CURVE_VALIDATE_PROBE_SO);
    eprintln!(">>> process_instruction");
    let r = svm
        .process_instruction(&ix, &[])
        .expect("qedsvm runs curve_validate_probe");
    eprintln!(">>> result = {:?}", r.program_result);
    eprintln!(">>> cu     = {}", r.compute_units_consumed);
    // Don't assert specific outcome — we want to see if it crashes
    // or returns. Both are acceptable signals at this stage.
    let _ = r;
}
