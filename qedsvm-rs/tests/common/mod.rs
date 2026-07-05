//! Shared helpers for the integration-test binaries (`mod common;` per test file).
//! Each binary uses a subset, so unused helpers are expected per-binary.
//! NOTE: diff_mollusk.rs deliberately does NOT adopt this module yet (later phase).
#![allow(dead_code)]

use solana_account::{Account, AccountSharedData};
use solana_pubkey::Pubkey;

/// Deterministic pubkey from a u64 seed (first 8 bytes LE, rest zero).
pub fn pid(seed: u64) -> Pubkey {
    let mut b = [0u8; 32];
    b[..8].copy_from_slice(&seed.to_le_bytes());
    Pubkey::from(b)
}

/// Counter-derived unique pubkey (avoids the `rand`-gated `Pubkey::new_unique`).
pub fn unique_pubkey() -> Pubkey {
    use std::sync::atomic::{AtomicU64, Ordering};
    static N: AtomicU64 = AtomicU64::new(1);
    let n = N.fetch_add(1, Ordering::Relaxed);
    let mut bytes = [0u8; 32];
    bytes[..8].copy_from_slice(&n.to_le_bytes());
    Pubkey::from(bytes)
}

/// Non-executable `AccountSharedData` with `rent_epoch: 0`.
pub fn shared(lamports: u64, data: Vec<u8>, owner: Pubkey) -> AccountSharedData {
    shared_executable(lamports, data, owner, false)
}

/// Like [`shared`] but with an explicit `executable` flag.
pub fn shared_executable(
    lamports: u64,
    data: Vec<u8>,
    owner: Pubkey,
    executable: bool,
) -> AccountSharedData {
    AccountSharedData::from(Account {
        lamports,
        data,
        owner,
        executable,
        rent_epoch: 0,
    })
}
