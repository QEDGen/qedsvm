//! L7 (TCB hygiene): Rust-side pins on the crypto size axioms in `SVM/SBPF/CryptoTrust.lean`.
//! Those axioms are trusted at native_decide time — a crate bump that changed an output length
//! would silently invalidate an axiom without any Lean build failure. These tests catch that in Rust.

use sha2::Digest as _; // brings ::digest() into scope for sha2 + sha3

/// `Sha256.hashAgave` axiom hook + `solana-sha256-hasher` shape: 32 B.
#[test]
fn sha256_digest_is_32_bytes() {
    assert_eq!(sha2::Sha256::digest(b"").len(), 32);
    assert_eq!(sha2::Sha256::digest(b"qedsvm").len(), 32);
}

/// `(Sha512.hash d).size = 64` (CryptoTrust). Production path for
/// `SVM.SBPF.Sha512.hash` via `lean_sha512`.
#[test]
fn sha512_digest_is_64_bytes() {
    assert_eq!(sha2::Sha512::digest(b"").len(), 64);
    assert_eq!(sha2::Sha512::digest(b"qedsvm").len(), 64);
}

/// `(Keccak256.hash d).size = 32`. Original Keccak (0x01 padding) via
/// `lean_keccak256`.
#[test]
fn keccak256_digest_is_32_bytes() {
    assert_eq!(sha3::Keccak256::digest(b"").len(), 32);
    assert_eq!(sha3::Keccak256::digest(b"qedsvm").len(), 32);
}

/// `(Blake3.hash d).size = 32`. Default hashing mode via `lean_blake3`.
#[test]
fn blake3_hash_is_32_bytes() {
    assert_eq!(blake3::hash(b"").as_bytes().len(), 32);
    assert_eq!(blake3::hash(b"qedsvm").as_bytes().len(), 32);
}
