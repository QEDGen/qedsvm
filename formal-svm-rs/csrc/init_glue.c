/*
 * Out-of-line wrappers for the static-inline init/teardown helpers in
 * `lean/lean.h`. Mirrors the role of `rust-bridge/lean_glue.c` but for
 * the *reverse* FFI direction (Rust calling into Lean's runtime to
 * initialize a module and consume its results).
 *
 * We can't reuse rust-bridge's glue from this crate because rust-bridge
 * is a staticlib *Lean* links — re-using its symbols would create a
 * circular link dep (formal-svm-rs → libleanbridge.a → ... → Svm's
 * dylibs). Keep the two glue files cleanly separated.
 */

#include <stdint.h>
#include <stddef.h>
#include <lean/lean.h>

/* IO result inspection — used to check whether
 * `initialize_formalSvm_Svm_Ffi(...)` succeeded. */
LEAN_EXPORT uint8_t leanfsvm_io_result_is_ok(b_lean_obj_arg r) {
    return lean_io_result_is_ok(r);
}

LEAN_EXPORT uint8_t leanfsvm_io_result_is_error(b_lean_obj_arg r) {
    return lean_io_result_is_error(r);
}

/* Ref-count helpers. We hold ownership of the ByteArray returned by
 * `formal_svm_run_elf_buffer`; once we've copied its bytes out we must
 * drop the reference so Lean can free it. */
LEAN_EXPORT void leanfsvm_dec_ref(lean_object* o) {
    lean_dec_ref(o);
}

LEAN_EXPORT void leanfsvm_inc_ref(lean_object* o) {
    lean_inc_ref(o);
}

/* ByteArray accessors — needed in *both* directions (we both build
 * input ByteArrays and read out the result ByteArray). Same shape as
 * rust-bridge/lean_glue.c. */
LEAN_EXPORT lean_obj_res leanfsvm_alloc_sarray(
    uint32_t elem_size, size_t size, size_t capacity) {
    return lean_alloc_sarray(elem_size, size, capacity);
}

LEAN_EXPORT size_t leanfsvm_sarray_size(b_lean_obj_arg o) {
    return lean_sarray_size(o);
}

LEAN_EXPORT uint8_t* leanfsvm_sarray_cptr(b_lean_obj_arg o) {
    return lean_sarray_cptr((lean_object*)o);
}
