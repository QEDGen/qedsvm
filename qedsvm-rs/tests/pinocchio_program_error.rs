//! End-to-end: a real Pinocchio 0.8 program (Janus' pyth-price-resolver,
//! pulled via `solana program dump` from devnet) returns
//! `Err(ProgramError::InvalidAccountData)` from its handler. The BPF
//! entrypoint encodes that as `(4 << 32) = 17_179_869_184` in r0;
//! `ProgramResult::from_bpf_r0` decodes it back into the typed variant.
//!
//! Closes the loop on issue #9: confirms the decode works against a
//! published binary (not just synthetic r0 values), and protects
//! against future regressions where the entrypoint's encoding might
//! drift from `solana-program-error`'s constants.

use qedsvm::{ProgramResult, Svm};
use solana_account::{Account, AccountSharedData};
use solana_instruction::{AccountMeta, Instruction};
use solana_program_error::ProgramError;
use solana_pubkey::Pubkey;

// `solana program dump --url devnet 3WDargKHd1UaP9UKPhJY8pF5bv5zJnaFAYDA9uahs5aL`
// at 2026-05-26. SHA-256:
// 0b891f14ed0945fc2ace325a974be59f0f0d88e695536df5dc3bfbfdd70f0a16
// Pinocchio 0.8. Reporter's `janus-pyth-price-resolver` from issue #2.
const PYTH_RESOLVER_DEVNET_SO: &[u8] =
    include_bytes!("fixtures/janus_pyth_price_resolver_devnet.so");

const PYTH_RESOLVER_PROGRAM_ID: &str = "3WDargKHd1UaP9UKPhJY8pF5bv5zJnaFAYDA9uahs5aL";

fn program_id() -> Pubkey {
    PYTH_RESOLVER_PROGRAM_ID.parse().unwrap()
}

#[test]
fn invalid_account_data_decodes_to_typed_program_error() {
    let pid = program_id(); // feed account has wrong discriminator → Resolve bails with InvalidAccountData
    let seed_key = Pubkey::new_unique();
    let price_feed = Pubkey::new_unique();
    let (state_key, bump) =
        Pubkey::find_program_address(&[b"pyth-resolver", seed_key.as_ref()], &pid);

    let mut state_data = vec![0u8; 136]; // minimal valid state layout — enough to reach feed-validate step
    state_data[0] = bump;
    state_data[1] = 0; // comparison: gte
    state_data[8..40].copy_from_slice(price_feed.as_ref());
    state_data[72..80].copy_from_slice(&100u64.to_le_bytes());
    state_data[80..88].copy_from_slice(&3600u64.to_le_bytes());
    state_data[88..96].copy_from_slice(&100_000_000i64.to_le_bytes());
    state_data[96..100].copy_from_slice(&(-8i32).to_le_bytes());
    state_data[104..136].copy_from_slice(seed_key.as_ref());

    let state_account = AccountSharedData::from(Account {
        lamports: 1_000_000,
        data: state_data,
        owner: pid,
        executable: false,
        rent_epoch: 0,
    });
    let feed_account = AccountSharedData::from(Account {
        lamports: 1_000_000,
        data: vec![0u8; 256], // wrong discriminator triggers InvalidAccountData
        owner: Pubkey::new_unique(),
        executable: false,
        rent_epoch: 0,
    });

    let ix = Instruction {
        program_id: pid,
        accounts: vec![
            AccountMeta::new_readonly(state_key, false),
            AccountMeta::new_readonly(price_feed, false),
        ],
        data: vec![0u8], // Resolve tag
    };

    let mut svm = Svm::default().with_cu_budget(1_400_000);
    svm.add_program(&pid, PYTH_RESOLVER_DEVNET_SO);

    let result = svm
        .process_instruction(
            &ix,
            &[(state_key, state_account), (price_feed, feed_account)],
        )
        .expect("runs");

    assert_eq!(
        result.program_result,
        ProgramResult::ProgramError(ProgramError::InvalidAccountData),
        "Pinocchio's packed (4<<32) r0 must decode to ProgramError::InvalidAccountData; \
         got {:?}",
        result.program_result,
    );
}
