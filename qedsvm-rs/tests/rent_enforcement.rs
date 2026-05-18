//! End-to-end integration test for `Svm::with_rent_state_enforcement`.
//!
//! The math (`rent_minimum_balance`, `get_account_rent_state`,
//! `rent_transition_allowed`) and `validate_post_state`'s direct
//! behavior are covered by unit tests in `src/svm.rs`. This file
//! exercises the wire-up through the full `Svm::process_instruction`
//! pipeline: BPF program execution → resulting accounts →
//! `validate_post_state(..., self.enforce_rent_state)` → final
//! `ProgramResult`.
//!
//! Why it's a separate test file: the rent enforcement flag is off
//! by default, and turning it on is incompatible with the
//! `diff-mollusk` fixtures (mollusk's per-instruction harness skips
//! the transaction-level rent check; our test scenarios deliberately
//! exercise *rejection*, which mollusk wouldn't replicate).

use qedsvm::{ProgramResult, Svm, ERR_INVALID_POSTSTATE};
use solana_account::{Account, AccountSharedData};
use solana_instruction::{AccountMeta, Instruction};
use solana_pubkey::Pubkey;

// BPF program that CPIs `system_instruction::transfer(from, to, lamports_to_send)`.
// Source: `tests/fixtures/system_transfer_caller_src/`.
const SYSTEM_TRANSFER_CALLER_SO: &[u8] =
    include_bytes!("fixtures/system_transfer_caller.so");

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

/// Build the System::Transfer ix + the standard 3-account layout.
/// Returns `(ix, accounts)` ready for `Svm::process_instruction`.
fn build_transfer_scenario(
    caller_id: Pubkey,
    from_pk: Pubkey,
    to_pk: Pubkey,
    lamports_to_send: u64,
    from_pre: AccountSharedData,
    to_pre: AccountSharedData,
) -> (Instruction, Vec<(Pubkey, AccountSharedData)>) {
    let system_program_id = Pubkey::new_from_array([0u8; 32]);
    let ix = Instruction {
        program_id: caller_id,
        accounts: vec![
            AccountMeta::new(from_pk, true),
            AccountMeta::new(to_pk, false),
            AccountMeta::new_readonly(system_program_id, false),
        ],
        data: lamports_to_send.to_le_bytes().to_vec(),
    };
    // Stub for the system program (same shape mollusk uses).
    let system_stub = shared(1, vec![], Pubkey::new_from_array([0u8; 32]));
    let accounts = vec![
        (from_pk, from_pre),
        (to_pk, to_pre),
        (system_program_id, system_stub),
    ];
    (ix, accounts)
}

/// **Smoke**: enforcement off (default) — a transfer that credits a
/// RentPaying recipient succeeds. The post-state has the recipient
/// in an invalid rent state (RentPaying credited), but the gate is
/// disabled. Baseline for the rejection test below.
#[test]
fn rent_enforcement_off_admits_invalid_transition() {
    let caller_id = pid(60);
    let from_pk = pid(61);
    let to_pk = pid(62);
    let system_owner = Pubkey::new_from_array([0u8; 32]);

    let from_pre = shared(5_000_000, vec![], system_owner); // RentExempt for 0-data
    // RentPaying: 100 lamports for 1000 bytes data — well below the
    // rent-exempt minimum of (128 + 1000) * 6960 = 7_850_880.
    let to_pre = shared(100, vec![0u8; 1000], system_owner);

    let (ix, accounts) = build_transfer_scenario(
        caller_id, from_pk, to_pk,
        500, from_pre, to_pre,
    );

    let mut svm = Svm::default().with_cu_budget(1_400_000);
    svm.add_program(&caller_id, SYSTEM_TRANSFER_CALLER_SO);
    // No `with_rent_state_enforcement(true)` — flag stays off.

    let result = svm.process_instruction(&ix, &accounts).expect("runs");
    assert!(
        matches!(result.program_result, ProgramResult::Success),
        "enforcement off + credit-to-RentPaying should succeed, got {:?}",
        result.program_result
    );
}

/// **Rejection**: enforcement on — the *same* transfer that crediit
/// a RentPaying recipient is now rejected with
/// `Failure { exit_code: ERR_INVALID_POSTSTATE }`. Demonstrates the
/// flag flows from `Svm` through `process_instruction` into
/// `validate_post_state`.
#[test]
fn rent_enforcement_on_rejects_credit_to_rent_paying() {
    let caller_id = pid(60);
    let from_pk = pid(61);
    let to_pk = pid(62);
    let system_owner = Pubkey::new_from_array([0u8; 32]);

    let from_pre = shared(5_000_000, vec![], system_owner);
    let to_pre = shared(100, vec![0u8; 1000], system_owner); // RentPaying

    let (ix, accounts) = build_transfer_scenario(
        caller_id, from_pk, to_pk,
        500, from_pre, to_pre,
    );

    let mut svm = Svm::default()
        .with_cu_budget(1_400_000)
        .with_rent_state_enforcement(true);
    svm.add_program(&caller_id, SYSTEM_TRANSFER_CALLER_SO);

    let result = svm.process_instruction(&ix, &accounts).expect("runs");
    match result.program_result {
        ProgramResult::Failure { exit_code } => {
            assert_eq!(
                exit_code, ERR_INVALID_POSTSTATE,
                "expected ERR_INVALID_POSTSTATE ({:#x}), got {:#x}",
                ERR_INVALID_POSTSTATE, exit_code,
            );
        }
        other => panic!(
            "expected Failure {{ exit_code: ERR_INVALID_POSTSTATE }}, got {:?}",
            other
        ),
    }
}

/// **Admission**: enforcement on — a transfer where both source and
/// destination remain in valid rent states (RentExempt throughout)
/// succeeds. Sanity that the gate isn't blanket-rejecting.
#[test]
fn rent_enforcement_on_admits_exempt_to_exempt_transfer() {
    let caller_id = pid(60);
    let from_pk = pid(61);
    let to_pk = pid(62);
    let system_owner = Pubkey::new_from_array([0u8; 32]);

    // Both accounts RentExempt at 0-data (1M > minimum of 891_360).
    let from_pre = shared(5_000_000, vec![], system_owner);
    let to_pre = shared(2_000_000, vec![], system_owner);

    let (ix, accounts) = build_transfer_scenario(
        caller_id, from_pk, to_pk,
        1_000, from_pre, to_pre,
    );

    let mut svm = Svm::default()
        .with_cu_budget(1_400_000)
        .with_rent_state_enforcement(true);
    svm.add_program(&caller_id, SYSTEM_TRANSFER_CALLER_SO);

    let result = svm.process_instruction(&ix, &accounts).expect("runs");
    assert!(
        matches!(result.program_result, ProgramResult::Success),
        "enforcement on + exempt-to-exempt transfer should succeed, got {:?}",
        result.program_result
    );
}
