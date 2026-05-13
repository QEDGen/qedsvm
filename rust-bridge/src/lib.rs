//! Rust bridge for formal-svm's crypto syscalls.
//!
//! Every export here is the direct target of a Lean `@[extern "name"]`
//! declaration in `Svm/SBPF/*.lean`. Functions take/return Lean's
//! `lean_object` ABI directly (no intermediary C shim layer) — that's
//! why `csrc/` no longer exists. The minimal Rust ↔ Lean ABI surface
//! lives in `lean_ffi.rs`.
//!
//! Crate pins are kept in lockstep with agave's `master/Cargo.toml`
//! (queried 2026-05-13):
//!   - `libsecp256k1 = 0.7.2` (no-default-features, `+std`,
//!     `+static-context`) — agave's `solana-syscalls` runtime dep
//!   - `sha2 = 0.10.8` (no-default-features) — via
//!     `solana-sha256-hasher`
//!   - `sha3 = 0.10.8` — via `solana-keccak-hasher`
//!   - `blake3 = 1.8.5` — agave master pin
//!   - `curve25519-dalek = 4.1.3` (`+digest`, `+rand_core`) — via
//!     `solana-curve25519`
//!
//! When agave bumps a version, bump here in lockstep — that is the
//! whole point of this crate.

#![deny(unsafe_op_in_unsafe_fn)]

mod lean_ffi;
use lean_ffi::{
    alloc_bytearray, b_lean_obj_arg, lean_alloc_ctor, lean_box, lean_ctor_set, lean_obj_arg,
    lean_obj_res, sarray_as_slice,
};
use sha2::Digest as _;

// ───────────────────────────────────────────────────────────────────
// SHA-256 (`sha2 = 0.10.8`) — agave-conformance audit hook for the
// pure-Lean Sha256.hash impl. The production path is the pure-Lean
// version; this exists so `Sha256.hash x = Sha256.hashAgave x` can be
// proved by native_decide across a sweep of inputs.
// ───────────────────────────────────────────────────────────────────

#[no_mangle]
pub extern "C" fn lean_sha256_agave(input: b_lean_obj_arg) -> lean_obj_res {
    let bytes = unsafe { sarray_as_slice(input) };
    let digest = sha2::Sha256::digest(bytes);
    alloc_bytearray(&digest)
}

// ───────────────────────────────────────────────────────────────────
// Keccak-256 (`sha3::Keccak256`, original Keccak with 0x01 padding —
// Solana's variant, NOT FIPS-202 SHA-3 which uses 0x06).
// Production path for `Keccak256.hash`.
// ───────────────────────────────────────────────────────────────────

#[no_mangle]
pub extern "C" fn lean_keccak256(input: b_lean_obj_arg) -> lean_obj_res {
    let bytes = unsafe { sarray_as_slice(input) };
    let digest = sha3::Keccak256::digest(bytes);
    alloc_bytearray(&digest)
}

// ───────────────────────────────────────────────────────────────────
// BLAKE3 (`blake3 = 1.8.5`, default hashing mode, 32-byte output).
// Production path for `Blake3.hash`.
// ───────────────────────────────────────────────────────────────────

#[no_mangle]
pub extern "C" fn lean_blake3(input: b_lean_obj_arg) -> lean_obj_res {
    let bytes = unsafe { sarray_as_slice(input) };
    let digest = blake3::hash(bytes);
    alloc_bytearray(digest.as_bytes())
}

// ───────────────────────────────────────────────────────────────────
// secp256k1 ECDSA recovery (`libsecp256k1 = 0.7.2`, paritytech).
//
// Matches agave's `SyscallSecp256k1Recover` body byte-for-byte:
//   Message::parse_slice(hash) → InvalidHash
//   RecoveryId::parse(rid)     → InvalidRecoveryId
//   Signature::parse_standard_slice(sig) → InvalidSignature
//   libsecp256k1::recover(...) → InvalidSignature on Err
//   serialize() trims leading 0x04 → Solana's 64-byte format.
//
// Returns the Lean inductive `Secp256k1.RecoverResult` directly:
//   tag 0 (`success`, 1 obj field = 64-byte ByteArray)
//   tag 1 (`invalidHash`, nullary → lean_box(1))
//   tag 2 (`invalidRecoveryId`, nullary → lean_box(2))
//   tag 3 (`invalidSignature`, nullary → lean_box(3))
// Inductive tags must stay in lockstep with Svm/SBPF/Secp256k1.lean.
// ───────────────────────────────────────────────────────────────────

#[no_mangle]
pub extern "C" fn lean_secp256k1_recover(
    hash: b_lean_obj_arg,
    recovery_id: u8,
    sig: b_lean_obj_arg,
) -> lean_obj_res {
    let hash_bytes = unsafe { sarray_as_slice(hash) };
    let sig_bytes = unsafe { sarray_as_slice(sig) };

    if hash_bytes.len() != 32 {
        return unsafe { lean_box(1) };
    }
    if sig_bytes.len() != 64 {
        return unsafe { lean_box(3) };
    }
    if recovery_id > 3 {
        return unsafe { lean_box(2) };
    }

    let Ok(message) = libsecp256k1::Message::parse_slice(hash_bytes) else {
        return unsafe { lean_box(1) };
    };
    let Ok(rid) = libsecp256k1::RecoveryId::parse(recovery_id) else {
        return unsafe { lean_box(2) };
    };
    let Ok(signature) = libsecp256k1::Signature::parse_standard_slice(sig_bytes) else {
        return unsafe { lean_box(3) };
    };
    let pubkey = match libsecp256k1::recover(&message, &signature, &rid) {
        Ok(pk) => pk,
        Err(_) => return unsafe { lean_box(3) },
    };
    let serialized = pubkey.serialize(); // 65 bytes, leading 0x04
    let bytes_obj = alloc_bytearray(&serialized[1..65]);

    // .success bytes_obj  →  ctor tag 0, 1 obj field, 0 scalar bytes
    let ctor = unsafe { lean_alloc_ctor(0, 1, 0) };
    unsafe { lean_ctor_set(ctor as lean_obj_arg, 0, bytes_obj as lean_obj_arg) };
    ctor
}

// ───────────────────────────────────────────────────────────────────
// curve25519 — point validation (`curve25519-dalek = 4.1.3`).
//
// Matches `solana_curve25519::{edwards,ristretto}::validate_*`
// byte-for-byte: both reduce to
// `CompressedX::from_slice(b).decompress().is_some()`.
//
// Lean's `Bool` ABI is a primitive `uint8_t` (0 = false, 1 = true),
// NOT a heap object — these functions do not allocate.
// ───────────────────────────────────────────────────────────────────

#[no_mangle]
pub extern "C" fn lean_curve_validate_edwards(point: b_lean_obj_arg) -> u8 {
    let bytes = unsafe { sarray_as_slice(point) };
    if bytes.len() != 32 {
        return 0;
    }
    match curve25519_dalek::edwards::CompressedEdwardsY::from_slice(bytes) {
        Ok(c) if c.decompress().is_some() => 1,
        _ => 0,
    }
}

#[no_mangle]
pub extern "C" fn lean_curve_validate_ristretto(point: b_lean_obj_arg) -> u8 {
    let bytes = unsafe { sarray_as_slice(point) };
    if bytes.len() != 32 {
        return 0;
    }
    match curve25519_dalek::ristretto::CompressedRistretto::from_slice(bytes) {
        Ok(c) if c.decompress().is_some() => 1,
        _ => 0,
    }
}
