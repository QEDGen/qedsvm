//! Operational sanity for `byte_increment.so` (companion to `SVM.SBPF.RunnerSpecDemo`).
//! Lean proves the 5-insn .text satisfies `byte_increment_macro_spec`; this checks end-to-end via Svm.

use qedsvm::{ProgramResult, Svm};
use solana_instruction::Instruction;

const BYTE_INCREMENT_SO: &[u8] = include_bytes!("fixtures/byte_increment.so");

mod common;
use common::pid;

#[test]
fn byte_increment_runs_and_exits_cleanly() {
    let program_id = pid(0xb17e);
    let mut svm = Svm::default();
    svm.add_program(&program_id, BYTE_INCREMENT_SO);

    let ix = Instruction { program_id, accounts: vec![], data: vec![] };
    let result = svm.process_instruction(&ix, &[]).expect("runs");
    println!(
        "byte_increment.so: program_result={:?} cu={}",
        result.program_result, result.compute_units_consumed
    );
    assert!(
        matches!(result.program_result, ProgramResult::Success),
        "expected Success, got {:?}",
        result.program_result
    );
}

#[test]
fn byte_increment_text_matches_lean_literal() {
    // Pins the 40 bytes embedded as `byteIncrementSoText` in RunnerSpecDemo. Drift = Lean theorems unsound.
    const EXPECTED_TEXT: [u8; 40] = [
        0x71, 0x12, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // ldx byte r2, r1, 0
        0x07, 0x02, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, // add64 r2, 1
        0x73, 0x21, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // stx byte r1, 0, r2
        0xb7, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // mov64 r0, 0
        0x95, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // exit
    ];
    const TEXT_OFFSET: usize = 0x120; // ELF header places .text at offset 288
    let text = &BYTE_INCREMENT_SO[TEXT_OFFSET..TEXT_OFFSET + EXPECTED_TEXT.len()];
    assert_eq!(text, &EXPECTED_TEXT[..],
        "byte_increment.so .text bytes drifted from the Lean literal — re-run cargo-build-sbf and update SVM.SBPF.RunnerSpecDemo or revert the toolchain");
}
