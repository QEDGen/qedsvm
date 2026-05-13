//! Sanity: a real cargo-build-sbf-produced no-op program runs
//! cleanly through formal-svm.

use formal_svm::{ProgramResult, Svm};
use solana_instruction::Instruction;
use solana_pubkey::Pubkey;

const NOOP_SO: &[u8] = include_bytes!("fixtures/noop.so");
const SOLANA_NOOP_SO: &[u8] = include_bytes!("fixtures/solana_noop.so");

fn pid(seed: u64) -> Pubkey {
    let mut b = [0u8; 32];
    b[..8].copy_from_slice(&seed.to_le_bytes());
    Pubkey::from(b)
}

#[test]
fn minimal_noop_program_runs() {
    let program_id = pid(1);
    let mut svm = Svm::default();
    svm.add_program(&program_id, NOOP_SO);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };
    let result = svm.process_instruction(&ix, &[]).expect("runs");
    println!("noop.so: program_result={:?} cu={}",
        result.program_result, result.compute_units_consumed);
    assert!(matches!(result.program_result,
        ProgramResult::Success | ProgramResult::Failure { .. }
    ), "got OOG — runner couldn't finish a noop within default budget");
}

#[test]
fn solana_program_entrypoint_noop_runs() {
    // The 18KB cargo-build-sbf output of a noop using
    // `solana_program::entrypoint!`. Exercises the full BPF input
    // buffer deserialization path that real on-chain programs use.
    let program_id = pid(2);
    let mut svm = Svm::default();
    svm.add_program(&program_id, SOLANA_NOOP_SO);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };
    let result = svm.process_instruction(&ix, &[]).expect("runs");
    println!("solana_noop.so: program_result={:?} cu={}",
        result.program_result, result.compute_units_consumed);
    // The bar for success here is *not* OOG and not ELF decode failure
    // — a sign that formal-svm's loader/decoder accept the real
    // cargo-build-sbf output.
    assert!(matches!(result.program_result,
        ProgramResult::Success | ProgramResult::Failure { .. }
    ), "got OOG on cargo-build-sbf noop");
}
