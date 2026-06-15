//! Diff-testing helpers: converters between `solana-account 4.x` (`qedsvm::Svm`) and
//! `solana-account 3.x` (`mollusk_svm`; Mollusk hasn't moved to 4.x yet). Feature: `diff-mollusk`.

use solana_account::{AccountSharedData, ReadableAccount, WritableAccount};
use solana_pubkey::Pubkey;

/// Convert `(pubkey, mollusk_account::Account)` list to `(pubkey, AccountSharedData)`.
/// Field-by-field copy — byte semantics agree; only the owning crate version differs.
pub fn mollusk_to_qedsvm(
    accounts: &[(Pubkey, mollusk_account::Account)],
) -> Vec<(Pubkey, AccountSharedData)> {
    accounts
        .iter()
        .map(|(k, a)| (*k, mollusk_account_to_shared(a)))
        .collect()
}

/// Convert a single `mollusk_account::Account` into `AccountSharedData`.
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

/// Convert `(pubkey, AccountSharedData)` list to `(pubkey, mollusk_account::Account)`.
/// Inverse of [`mollusk_to_qedsvm`].
pub fn qedsvm_to_mollusk(
    accounts: &[(Pubkey, AccountSharedData)],
) -> Vec<(Pubkey, mollusk_account::Account)> {
    accounts
        .iter()
        .map(|(k, a)| (*k, shared_to_mollusk_account(a)))
        .collect()
}

/// Convert a single `AccountSharedData` into `mollusk_account::Account`. Inverse of [`mollusk_account_to_shared`].
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
        // Pubkey is `[u8; 32]` on both sides — not `Into`-convertible, but bytes round-trip exactly.
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

    /// `mollusk → qedsvm → mollusk` round-trip must be the byte-level identity.
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
