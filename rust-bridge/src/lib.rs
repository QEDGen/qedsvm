//! Rust → C bridge for formal-svm.
//!
//! Every symbol here is `extern "C"` with `#[no_mangle]` so Lake's
//! `extern_lib` can pull it into the precompiled Lean dynlibs (which
//! reach these through thin `csrc/*.c` shims that handle the
//! `lean_object` ABI). The point of this crate is to make formal-svm's
//! crypto syscalls byte-for-byte equivalent to agave's runtime by
//! pinning the exact crate versions agave uses on master.
//!
//! Conventions:
//! - All buffer parameters are `*const u8` / `*mut u8` with explicit
//!   length constants from the Solana ABI. The C shim validates lengths
//!   at the Lean ↔ C boundary, so by the time we get here the sizes
//!   are guaranteed.
//! - Return codes mirror the Solana error mapping:
//!   `0` = success, `1` = InvalidHash, `2` = InvalidRecoveryId,
//!   `3` = InvalidSignature, etc. — defined per syscall.

#![deny(unsafe_op_in_unsafe_fn)]

use core::slice;

// ───────────────────────────────────────────────────────────────────
// secp256k1_recover (matches agave/syscalls/src/lib.rs SyscallSecp256k1Recover)
// ───────────────────────────────────────────────────────────────────

/// Recover a 64-byte uncompressed secp256k1 public key (x || y, no
/// `0x04` prefix) from a 32-byte message hash, a recovery_id, and a
/// 64-byte compact ECDSA signature (r || s).
///
/// Returns `0` on success, otherwise one of:
/// - `1` InvalidHash
/// - `2` InvalidRecoveryId (recovery_id > 3 or libsecp256k1 rejects it)
/// - `3` InvalidSignature (parse fails, high-S, or recovery fails)
///
/// `hash_ptr` must be readable for 32 bytes, `sig_ptr` for 64 bytes,
/// `out_ptr` writable for 64 bytes. The caller (C shim) guarantees this.
///
/// Internally uses `libsecp256k1::Signature::parse_standard_slice`
/// which enforces low-S form — matching agave's behavior. Bitcoin
/// Core's `libsecp256k1` C library accepts high-S; formal-svm does
/// not, by design.
#[no_mangle]
pub unsafe extern "C" fn formal_svm_secp256k1_recover(
    hash_ptr: *const u8,
    recovery_id: u8,
    sig_ptr: *const u8,
    out_ptr: *mut u8,
) -> u64 {
    let hash = unsafe { slice::from_raw_parts(hash_ptr, 32) };
    let sig = unsafe { slice::from_raw_parts(sig_ptr, 64) };

    let Ok(message) = libsecp256k1::Message::parse_slice(hash) else {
        return 1;
    };
    let Ok(recovery_id) = libsecp256k1::RecoveryId::parse(recovery_id) else {
        return 2;
    };
    let Ok(signature) = libsecp256k1::Signature::parse_standard_slice(sig) else {
        return 3;
    };
    let public_key = match libsecp256k1::recover(&message, &signature, &recovery_id) {
        Ok(pk) => pk,
        Err(_) => return 3,
    };
    let serialized = public_key.serialize(); // 65 bytes, leading 0x04
    let out = unsafe { slice::from_raw_parts_mut(out_ptr, 64) };
    out.copy_from_slice(&serialized[1..65]);
    0
}
