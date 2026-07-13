//! Isolated probe for `Curve25519.validateEdwards` FFI (was a SIGSEGV reproducer).
//! Runs `curve_validate_probe.so` through Svm alone (no mollusk) to isolate the curve25519 FFI path.

use qedsvm::Svm;
use solana_instruction::Instruction;

const CURVE_VALIDATE_PROBE_SO: &[u8] = include_bytes!("fixtures/curve_validate_probe.so");

mod common;
use common::pid;

#[test]
fn curve_validate_via_runtime() {
    let program_id = pid(60);
    let ix = Instruction {
        program_id,
        accounts: vec![],
        data: vec![],
    };
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
    let _ = r; // any outcome is acceptable; we just confirm it doesn't crash
}
