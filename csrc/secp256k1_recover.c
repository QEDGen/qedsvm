/*
 * Lean ↔ rust-bridge shim for secp256k1 ECDSA recovery.
 *
 * The actual cryptography lives in `rust-bridge/src/lib.rs`, which
 * delegates to paritytech's `libsecp256k1 = "0.7.2"` (no_default_features,
 * +std,+static-context) — the same crate agave's runtime
 * `SyscallSecp256k1Recover` calls. This C file only translates between
 * Lean's `lean_object` ABI (ByteArrays, the four-ctor
 * `Secp256k1.RecoverResult` inductive) and the bridge's raw-pointer C
 * ABI. No crypto happens here.
 *
 * Inductive tags must stay in lockstep with `Svm/SBPF/Secp256k1.lean`:
 *   tag 0 = .success (pubkey)
 *   tag 1 = .invalidHash
 *   tag 2 = .invalidRecoveryId
 *   tag 3 = .invalidSignature
 */

#include <stdint.h>
#include <string.h>
#include <lean/lean.h>

/* Bridge ABI (see rust-bridge/src/lib.rs).
 * Returns 0 success / 1 InvalidHash / 2 InvalidRecoveryId /
 * 3 InvalidSignature; writes the 64-byte pubkey to *out_ptr on success. */
extern uint64_t formal_svm_secp256k1_recover(
    const uint8_t *hash_ptr,
    uint8_t        recovery_id,
    const uint8_t *sig_ptr,
    uint8_t       *out_ptr);

/* Allocate a `.success pubkey` constructor (tag 0, one obj field). */
static lean_obj_res mk_success(const uint8_t bytes[64]) {
    lean_object *arr = lean_alloc_sarray(1, 64, 64);
    memcpy(lean_sarray_cptr(arr), bytes, 64);
    lean_object *ctor = lean_alloc_ctor(0, 1, 0);
    lean_ctor_set(ctor, 0, arr);
    return ctor;
}

/* Allocate a nullary constructor (`.invalidHash` / `.invalidRecoveryId`
 * / `.invalidSignature`). Lean represents nullary ctors as boxed
 * scalar tags via `lean_box`. */
static lean_obj_res mk_error(unsigned tag) {
    return lean_box(tag);
}

LEAN_EXPORT lean_obj_res lean_secp256k1_recover(
    b_lean_obj_arg hash_arr,
    uint8_t        recovery_id,
    b_lean_obj_arg sig_arr) {

    /* ABI-boundary length checks. The Lean side always passes 32-byte
     * hash and 64-byte sig (the syscall arm constructs them via
     * `readBytes _ _ 32` / `_ 64`), but defend against caller error
     * anyway — the inductive distinguishes invalidHash from
     * invalidSignature, and we can map malformed lengths conservatively. */
    if (lean_sarray_size(hash_arr) != 32) return mk_error(1);  /* invalidHash */
    if (lean_sarray_size(sig_arr)  != 64) return mk_error(3);  /* invalidSignature */

    const uint8_t *hash = lean_sarray_cptr(hash_arr);
    const uint8_t *sig  = lean_sarray_cptr(sig_arr);

    uint8_t  out[64];
    uint64_t code = formal_svm_secp256k1_recover(hash, recovery_id, sig, out);

    switch (code) {
        case 0: return mk_success(out);
        case 1: return mk_error(1);
        case 2: return mk_error(2);
        case 3: return mk_error(3);
        default: return mk_error(3);  /* unreachable; safe default */
    }
}
