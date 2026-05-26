//! Diff-testing helpers — converters + assertion utilities for
//! running the same fixture through both `qedsvm::Svm` and
//! `mollusk_svm::Mollusk`.
//!
//! Gated by the `diff-mollusk` feature. The motivation is the
//! `solana-account` version mismatch:
//!
//! - `qedsvm::Svm::process_instruction` takes
//!   `&[(Pubkey, AccountSharedData)]` from `solana-account 4.x`.
//! - `mollusk-svm 0.12.1-agave-4.0::process_instruction` takes
//!   `&[(Pubkey, mollusk_account::Account)]` where the latter is
//!   aliased to `solana-account 3.x` (Mollusk's internal interface
//!   hasn't moved to 4.x yet).
//!
//! Every differential-test consumer ends up writing the same
//! field-by-field conversion. This module centralises it. See the
//! `conformance_demo` example for a complete usage walk-through.

use solana_account::{AccountSharedData, ReadableAccount, WritableAccount};
use solana_pubkey::Pubkey;

/// Convert a `(pubkey, mollusk_account::Account)` list into the
/// `(pubkey, AccountSharedData)` shape `qedsvm::Svm::process_instruction`
/// expects.
///
/// Field-by-field copy — both sides agree on the byte semantics of
/// `lamports / data / owner / executable / rent_epoch`; only the
/// owning crate version differs.
///
/// # Example
///
/// ```no_run
/// use qedsvm::{diff::mollusk_to_qedsvm, Svm};
/// use solana_instruction::{AccountMeta, Instruction};
/// use solana_pubkey::Pubkey;
///
/// let program_id = Pubkey::new_unique();
/// let acct_key = Pubkey::new_unique();
/// let mollusk_accounts = vec![
///     (acct_key, mollusk_account::Account {
///         lamports: 1_000_000, data: vec![0; 32], owner: program_id,
///         executable: false, rent_epoch: 0,
///     }),
/// ];
/// # let elf: Vec<u8> = vec![];
/// # let ix = Instruction { program_id, accounts: vec![AccountMeta::new(acct_key, false)], data: vec![] };
///
/// let mut svm = Svm::default();
/// svm.add_program(&program_id, &elf); // add_program(...) elided for brevity
/// let qedsvm_accounts = mollusk_to_qedsvm(&mollusk_accounts);
/// let r = svm.process_instruction(&ix, &qedsvm_accounts);
/// ```
pub fn mollusk_to_qedsvm(
    accounts: &[(Pubkey, mollusk_account::Account)],
) -> Vec<(Pubkey, AccountSharedData)> {
    accounts
        .iter()
        .map(|(k, a)| (*k, mollusk_account_to_shared(a)))
        .collect()
}

/// Convert a single `mollusk_account::Account` into `AccountSharedData`.
///
/// Useful when you're building accounts one at a time rather than
/// constructing a full Vec.
pub fn mollusk_account_to_shared(a: &mollusk_account::Account) -> AccountSharedData {
    // `solana_pubkey::Pubkey` byte layout is stable across 3.x/4.x —
    // both wrap a `[u8; 32]`. Reinterpret the owner directly.
    let owner_bytes: &[u8; 32] = a.owner.as_array();
    let owner = Pubkey::from(*owner_bytes);

    let mut shared = AccountSharedData::new(a.lamports, a.data.len(), &owner);
    shared.set_data_from_slice(&a.data);
    shared.set_executable(a.executable);
    shared.set_rent_epoch(a.rent_epoch);
    shared
}

/// Convert a `(pubkey, AccountSharedData)` list back into the
/// `(pubkey, mollusk_account::Account)` shape `mollusk_svm::Mollusk
/// ::process_instruction` expects.
///
/// Useful when fixtures are generated from qedsvm output first
/// (e.g. a fuzzer or property-test driven from the Lean side) and
/// then fed back through mollusk for comparison.
pub fn qedsvm_to_mollusk(
    accounts: &[(Pubkey, AccountSharedData)],
) -> Vec<(Pubkey, mollusk_account::Account)> {
    accounts
        .iter()
        .map(|(k, a)| (*k, shared_to_mollusk_account(a)))
        .collect()
}

/// Convert a single `AccountSharedData` into `mollusk_account::Account`.
/// Inverse of [`mollusk_account_to_shared`]. Pubkey bytes round-trip
/// via the same `[u8; 32]` reinterpret trick — `mollusk_pubkey` is the
/// solana-pubkey 3.x alias mollusk's account type uses internally.
pub fn shared_to_mollusk_account(a: &AccountSharedData) -> mollusk_account::Account {
    let owner_bytes: [u8; 32] = *a.owner().as_array();
    mollusk_account::Account {
        lamports: a.lamports(),
        data: a.data().to_vec(),
        owner: mollusk_pubkey::Pubkey::from(owner_bytes),
        executable: a.executable(),
        rent_epoch: a.rent_epoch(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mollusk_acct(lamports: u64, data: Vec<u8>, exec: bool, epoch: u64) -> mollusk_account::Account {
        mollusk_account::Account {
            lamports,
            data,
            owner: mollusk_account::Account::default().owner,
            executable: exec,
            rent_epoch: epoch,
        }
    }

    #[test]
    fn round_trip_preserves_fields() {
        let m = mollusk_acct(42, vec![1, 2, 3, 4, 5], true, 99);
        let shared = mollusk_account_to_shared(&m);
        assert_eq!(shared.lamports(), 42);
        assert_eq!(shared.data(), &[1, 2, 3, 4, 5]);
        assert!(shared.executable());
        assert_eq!(shared.rent_epoch(), 99);
    }

    #[test]
    fn owner_byte_layout_preserved() {
        // Pubkey is a `[u8; 32]` wrapper on both sides; bytes
        // round-trip exactly even though the types aren't
        // `Into`-convertible directly.
        let m = mollusk_acct(0, vec![], false, 0);
        let owner_bytes_before = *m.owner.as_array();
        let shared = mollusk_account_to_shared(&m);
        let owner_bytes_after = *shared.owner().as_array();
        assert_eq!(owner_bytes_before, owner_bytes_after);
    }

    #[test]
    fn vec_conversion_preserves_order_and_keys() {
        let k1 = Pubkey::new_unique();
        let k2 = Pubkey::new_unique();
        let m = vec![
            (k1, mollusk_acct(1, vec![10], false, 0)),
            (k2, mollusk_acct(2, vec![20, 21], false, 0)),
        ];
        let q = mollusk_to_qedsvm(&m);
        assert_eq!(q.len(), 2);
        assert_eq!(q[0].0, k1);
        assert_eq!(q[1].0, k2);
        assert_eq!(q[0].1.lamports(), 1);
        assert_eq!(q[0].1.data(), &[10]);
        assert_eq!(q[1].1.lamports(), 2);
        assert_eq!(q[1].1.data(), &[20, 21]);
    }

    /// Round-trip: `mollusk → qedsvm → mollusk` must be the identity
    /// at the byte level. Single assertion that catches any future
    /// divergence in either converter.
    #[test]
    fn round_trip_mollusk_qedsvm_mollusk() {
        let k = Pubkey::new_unique();
        let original = vec![
            (k, mollusk_acct(42, vec![1, 2, 3, 4, 5], true, 99)),
            (
                Pubkey::new_unique(),
                mollusk_acct(0, vec![0xFF; 64], false, 0),
            ),
        ];
        let intermediate = mollusk_to_qedsvm(&original);
        let restored = qedsvm_to_mollusk(&intermediate);

        assert_eq!(restored.len(), original.len());
        for (i, ((ka, a), (kb, b))) in original.iter().zip(restored.iter()).enumerate() {
            assert_eq!(ka, kb, "pubkey mismatch at index {i}");
            assert_eq!(a.lamports, b.lamports, "lamports mismatch at index {i}");
            assert_eq!(a.data, b.data, "data mismatch at index {i}");
            assert_eq!(
                a.owner.as_array(),
                b.owner.as_array(),
                "owner mismatch at index {i}",
            );
            assert_eq!(a.executable, b.executable, "executable mismatch at index {i}");
            assert_eq!(a.rent_epoch, b.rent_epoch, "rent_epoch mismatch at index {i}");
        }
    }
}
