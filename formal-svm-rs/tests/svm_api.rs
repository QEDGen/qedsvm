//! Mollusk-shaped API smoke test. Drives `Svm::process_instruction`
//! against the hand-assembled `helloElf` (mov64 r0, 42; exit) — same
//! fixture as `tests/smoke.rs`, but through the high-level instruction
//! API instead of the raw `run_buffer` entry.
//!
//! The hello program doesn't touch its input buffer, so its resulting
//! state is uninteresting beyond "Failure(exit_code=42), no logs, no
//! return data". The point is to exercise the full plumbing path:
//!   instruction + accounts → serialize → Lean → deserialize → result

use formal_svm::{ProgramResult, SerializeError, Svm, SvmError};
use solana_account::{Account, AccountSharedData};
use solana_instruction::{AccountMeta, Instruction};
use solana_pubkey::Pubkey;

// 289-byte ELF: mov64 r0, 42; exit. Same fixture as
// `Svm.SBPF.RunnerDemo.helloElf` and `tests/smoke.rs`. Generated from
// the Lean fixture (see `tests/fixtures/`).
const HELLO_ELF: &[u8] = include_bytes!("fixtures/hello.elf");

fn pid(seed: u64) -> Pubkey {
    let mut b = [0u8; 32];
    b[..8].copy_from_slice(&seed.to_le_bytes());
    Pubkey::from(b)
}

fn shared(lamports: u64, data: Vec<u8>, owner: Pubkey) -> AccountSharedData {
    AccountSharedData::from(Account {
        lamports,
        data,
        owner,
        executable: false,
        rent_epoch: 0,
    })
}

#[test]
fn process_instruction_with_no_accounts_returns_helloelfs_exit_code() {
    let program_id = pid(1);
    let mut svm = Svm::default();
    svm.add_program(&program_id, HELLO_ELF);

    let ix = Instruction { program_id, accounts: vec![], data: vec![] };
    let result = svm.process_instruction(&ix, &[]).expect("runs");

    assert_eq!(result.program_result, ProgramResult::Failure { exit_code: 42 });
    assert!(result.logs.is_empty());
    assert!(result.return_data.is_empty());
    assert!(result.resulting_accounts.is_empty());
}

#[test]
fn process_instruction_with_accounts_round_trips_unchanged_buffer() {
    // hello ELF doesn't touch the input region, so accounts come back
    // identical to what we put in. This exercises serialize +
    // deserialize on a real (Pubkey, AccountSharedData) shape.
    let program_id = pid(2);
    let key = pid(3);
    let owner = pid(4);
    let pre = shared(7_777, vec![0xAA, 0xBB, 0xCC], owner);

    let mut svm = Svm::default();
    svm.add_program(&program_id, HELLO_ELF);

    let ix = Instruction {
        program_id,
        accounts: vec![AccountMeta::new(key, false)],
        data: vec![0x01, 0x02],
    };
    let result = svm.process_instruction(&ix, &[(key, pre.clone())])
        .expect("runs");

    assert_eq!(result.program_result, ProgramResult::Failure { exit_code: 42 });
    assert_eq!(result.resulting_accounts.len(), 1);
    let (out_key, out_acct) = &result.resulting_accounts[0];
    assert_eq!(out_key, &key);
    use solana_account::ReadableAccount;
    assert_eq!(out_acct.lamports(), 7_777);
    assert_eq!(out_acct.data(), &[0xAA, 0xBB, 0xCC]);
    assert_eq!(out_acct.owner(), &owner);
}

#[test]
fn unknown_program_returns_svm_error() {
    let svm = Svm::default();
    let ix = Instruction { program_id: pid(99), accounts: vec![], data: vec![] };
    match svm.process_instruction(&ix, &[]) {
        Err(SvmError::UnknownProgram(pk)) => assert_eq!(pk, pid(99)),
        other => panic!("expected UnknownProgram, got {other:?}"),
    }
}

#[test]
fn compute_units_consumed_matches_program_length() {
    // The hello ELF is `mov64 r0, 42; exit` — two instructions.
    // Each step under `executeFnCpiWithFuel` consumes 1 fuel unit,
    // so consumed should be exactly 2.
    let program_id = pid(7);
    let mut svm = Svm::default();
    svm.add_program(&program_id, HELLO_ELF);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };
    let result = svm.process_instruction(&ix, &[]).expect("runs");
    assert_eq!(result.compute_units_consumed, 2,
        "hello ELF is 2 instructions; got CU={}", result.compute_units_consumed);
    assert_eq!(result.program_result, ProgramResult::Failure { exit_code: 42 });
}

/// Registering a second program triggers the CPI registry path
/// (`run_buffer_with_registry`) instead of the plain `run_buffer`
/// entry. The "main" program (hello ELF) doesn't actually CPI, so
/// the registry's contents go unused — this is purely an exercise of
/// the FFI plumbing: encode_registry → Lean parseRegistry → runner.
/// Asserts the same observable result as the single-program case,
/// proving the new entry is wire-compatible.
#[test]
fn process_instruction_with_multiple_programs_routes_through_registry() {
    let main_id = pid(20);
    let other_id = pid(21);
    let mut svm = Svm::default();
    svm.add_program(&main_id, HELLO_ELF);
    svm.add_program(&other_id, HELLO_ELF); // second program ⇒ registry path
    let ix = Instruction { program_id: main_id, accounts: vec![], data: vec![] };
    let result = svm.process_instruction(&ix, &[]).expect("runs");
    assert_eq!(result.program_result, ProgramResult::Failure { exit_code: 42 });
    assert_eq!(result.compute_units_consumed, 2);
}

#[test]
fn missing_account_returns_serialize_error() {
    let program_id = pid(9);
    let mut svm = Svm::default();
    svm.add_program(&program_id, HELLO_ELF);
    let missing = pid(100);
    let ix = Instruction {
        program_id,
        accounts: vec![AccountMeta::new(missing, false)],
        data: vec![],
    };
    // Pass an empty accounts list — the `missing` pubkey isn't there.
    match svm.process_instruction(&ix, &[]) {
        Err(SvmError::Serialize(SerializeError::MissingAccount(pk))) => {
            assert_eq!(pk, missing);
        }
        other => panic!("expected Serialize(MissingAccount), got {other:?}"),
    }
}

#[test]
fn too_many_accounts_returns_serialize_error() {
    let program_id = pid(10);
    let mut svm = Svm::default();
    svm.add_program(&program_id, HELLO_ELF);
    // 256 accounts → exceeds the 255 cap (NON_DUP_MARKER = 0xFF).
    let metas: Vec<AccountMeta> =
        (0..256).map(|i| AccountMeta::new(pid(1000 + i), false)).collect();
    let accounts: Vec<(Pubkey, AccountSharedData)> =
        (0..256).map(|i| (pid(1000 + i), shared(0, vec![], pid(0)))).collect();
    let ix = Instruction { program_id, accounts: metas, data: vec![] };
    match svm.process_instruction(&ix, &accounts) {
        Err(SvmError::Serialize(SerializeError::TooManyAccounts(n))) => {
            assert_eq!(n, 256);
        }
        other => panic!("expected Serialize(TooManyAccounts), got {other:?}"),
    }
}

#[test]
fn cu_budget_exhaustion_reports_full_budget_consumed() {
    // Set the budget to 1 — not enough to finish even `mov64 r0, 42;
    // exit`. The runner should run 1 step, then return state with
    // exitCode = none. With v1 fuel accounting consumed = budget - 0
    // = 1 (the remaining fuel was zero at the OOG transition).
    let program_id = pid(8);
    let mut svm = Svm::default().with_cu_budget(1);
    svm.add_program(&program_id, HELLO_ELF);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };
    let result = svm.process_instruction(&ix, &[]).expect("runs");
    assert_eq!(result.program_result, ProgramResult::OutOfBudget);
    assert_eq!(result.compute_units_consumed, 1);
}
