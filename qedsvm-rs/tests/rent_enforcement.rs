//! Integration test for `Svm::with_rent_state_enforcement`.
//! Unit-level math is in `src/svm.rs`; this exercises the full pipeline wiring.
//! Flag is off by default; these scenarios test rejection that mollusk's harness skips.

use qedsvm::{ProgramResult, Svm, ERR_INVALID_POSTSTATE};
use solana_account::AccountSharedData;
use solana_instruction::{AccountMeta, Instruction};
use solana_pubkey::Pubkey;

// BPF program that CPIs `system_instruction::transfer(from, to, lamports_to_send)`.
// Source: `tests/fixtures/system_transfer_caller_src/`.
const SYSTEM_TRANSFER_CALLER_SO: &[u8] =
    include_bytes!("fixtures/system_transfer_caller.so");

mod common;
use common::{pid, shared};

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

/// Enforcement off: credit-to-RentPaying succeeds; gate disabled.
#[test]
fn rent_enforcement_off_admits_invalid_transition() {
    let caller_id = pid(60);
    let from_pk = pid(61);
    let to_pk = pid(62);
    let system_owner = Pubkey::new_from_array([0u8; 32]);

    let from_pre = shared(5_000_000, vec![], system_owner); // RentExempt for 0-data
    let to_pre = shared(100, vec![0u8; 1000], system_owner); // RentPaying: 100 < (128+1000)*6960

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

/// Enforcement on: same transfer rejected with ERR_INVALID_POSTSTATE; flag flows through validate_post_state.
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

/// Enforcement on: exempt-to-exempt transfer succeeds; sanity that the gate isn't blanket-rejecting.
#[test]
fn rent_enforcement_on_admits_exempt_to_exempt_transfer() {
    let caller_id = pid(60);
    let from_pk = pid(61);
    let to_pk = pid(62);
    let system_owner = Pubkey::new_from_array([0u8; 32]);

    let from_pre = shared(5_000_000, vec![], system_owner); // both RentExempt at 0-data (> 891_360)
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
