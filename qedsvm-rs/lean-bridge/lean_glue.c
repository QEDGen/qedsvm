/*
 * Lean runtime glue.
 *
 * Most of the functions we need from `lean/lean.h`
 * (`lean_alloc_sarray`, `lean_box`, `lean_alloc_ctor`,
 * `lean_ctor_set`, `lean_sarray_size`, `lean_sarray_cptr`) are
 * declared `static inline` in the header — they have no exported
 * symbols, only inline definitions in each compilation unit that
 * `#include`s `lean.h`.
 *
 * Rust can't call inline-only functions across the FFI boundary, so
 * we emit thin out-of-line wrappers here under different names
 * (`leanrt_*`). `rust-bridge/build.rs` compiles this file and links
 * the resulting object into `libqedsvm_bridge.a`; Rust calls
 * `leanrt_*` via `extern "C"` declarations in `src/lean_ffi.rs`.
 *
 * This is the only C in qedsvm — and it does no algorithmic work,
 * just ABI translation. The actual crypto and inductive construction
 * live in Rust.
 */

#include <stdint.h>
#include <stddef.h>
#include <lean/lean.h>

LEAN_EXPORT lean_obj_res leanrt_alloc_sarray(
    uint32_t elem_size, size_t size, size_t capacity) {
    return lean_alloc_sarray(elem_size, size, capacity);
}

LEAN_EXPORT size_t leanrt_sarray_size(b_lean_obj_arg o) {
    return lean_sarray_size(o);
}

LEAN_EXPORT uint8_t * leanrt_sarray_cptr(b_lean_obj_arg o) {
    return lean_sarray_cptr((lean_object *)o);
}

LEAN_EXPORT lean_obj_res leanrt_alloc_ctor(
    uint32_t tag, uint32_t num_objs, uint32_t scalar_size) {
    return lean_alloc_ctor(tag, num_objs, scalar_size);
}

LEAN_EXPORT void leanrt_ctor_set(lean_obj_arg o, uint32_t idx, lean_obj_arg v) {
    lean_ctor_set(o, idx, v);
}

LEAN_EXPORT lean_obj_res leanrt_box(size_t v) {
    return lean_box(v);
}
