//! L7 (TCB hygiene): independent Rust-side pins on the crypto SHAPE
//! invariants that `SVM/SBPF/CryptoTrust.lean` asserts as `axiom`s
//! (e.g. `(Sha512.hash d).size = 64`). Those size axioms are trusted
//! whenever a `native_decide` evaluates the corresponding `@[extern]
//! opaque` function: the kernel believes the size claim without
//! checking the native code. If a crate version bump ever changed an
//! output length, the axiom would become false yet nothing in the Lean
//! build would notice.
//!
//! These tests call the EXACT crates `lean-bridge` wraps (sha2 0.10.8,
//! sha3 0.10.8, blake3 1.8.5 — Cargo unifies the versions across the
//! workspace) and assert the lengths the axioms claim. A divergence
//! fails here, in Rust, instead of silently invalidating a size axiom.
//!
//! Scope: the deterministic-length hash externs. Variable-output and
//! point-parsing externs (secp256k1 recover -> 64, curve25519 point ==
//! 32, bn254/bigmodexp) are size-guarded inline in the bridge itself
//! (`if bytes.len() != N { return error }`); see `lean-bridge/src`.

// `sha2` and `sha3` both re-export the same `digest::Digest` trait;
// one import brings `::digest()` into scope for every hasher below.
use sha2::Digest as _;

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
