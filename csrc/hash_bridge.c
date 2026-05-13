/*
 * Lean ↔ rust-bridge shims for the SHA-256 / Keccak-256 / BLAKE3
 * audit primitives.
 *
 * These are *separate* from the production hash paths (the pure-Lean
 * `Svm.SBPF.Sha256.hash` and the vendored-C `Keccak256.hash` /
 * `Blake3.hash`). Their sole purpose is to expose the agave-pinned
 * Rust crate behavior to Lean so we can prove byte-equivalence with
 * the production paths via `native_decide`.
 *
 * If the equivalence demos ever fail, we have a divergence to resolve
 * (probably by switching the production path to the bridge here, or
 * by patching the production path to match). Today (2026-05-13) the
 * production paths pass agave-conformance test vectors, so this audit
 * layer is a safety net, not a current call path.
 */

#include <stdint.h>
#include <stddef.h>
#include <string.h>
#include <lean/lean.h>

extern void formal_svm_sha256   (const uint8_t *in_ptr, size_t in_len, uint8_t *out_ptr);
extern void formal_svm_keccak256(const uint8_t *in_ptr, size_t in_len, uint8_t *out_ptr);
extern void formal_svm_blake3   (const uint8_t *in_ptr, size_t in_len, uint8_t *out_ptr);

static lean_obj_res hash_via_bridge(
    b_lean_obj_arg input,
    void (*fn)(const uint8_t *, size_t, uint8_t *)) {
    size_t          in_len = lean_sarray_size(input);
    const uint8_t  *in_ptr = lean_sarray_cptr(input);
    lean_object    *out    = lean_alloc_sarray(1, 32, 32);
    fn(in_ptr, in_len, lean_sarray_cptr(out));
    return out;
}

LEAN_EXPORT lean_obj_res lean_sha256_agave(b_lean_obj_arg input) {
    return hash_via_bridge(input, formal_svm_sha256);
}

LEAN_EXPORT lean_obj_res lean_keccak256_agave(b_lean_obj_arg input) {
    return hash_via_bridge(input, formal_svm_keccak256);
}

LEAN_EXPORT lean_obj_res lean_blake3_agave(b_lean_obj_arg input) {
    return hash_via_bridge(input, formal_svm_blake3);
}
