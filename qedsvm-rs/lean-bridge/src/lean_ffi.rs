//! Minimal hand-written Lean runtime C ABI bindings (~6 symbols, no bindgen, no lean/lean.h dep).
//!
//! Ref-count: `b_lean_obj_arg` = borrowed (no RC change); `lean_obj_res` = owned (RC=1 on return).

#![allow(non_camel_case_types)]

/// Opaque Lean heap object pointer — passed through, never inspected.
#[repr(C)]
pub struct lean_object {
    _private: [u8; 0],
}

/// Borrowed reference (no refcount change).
pub type b_lean_obj_arg = *const lean_object;

/// Owned, refcount=1 return value.
pub type lean_obj_res = *mut lean_object;

/// Owned argument (refcount transferred in, e.g. for `lean_ctor_set`).
pub type lean_obj_arg = *mut lean_object;

// `leanrt_` prefix because `lean/lean.h` symbols are `static inline` (no exports).
// `lean_glue.c` provides out-of-line wrappers; `build.rs` compiles and links them.

extern "C" {
    /// Allocate a ByteArray of `size` bytes (elem_size=1, capacity=size). RC=1.
    fn leanrt_alloc_sarray(elem_size: u32, size: usize, capacity: usize) -> lean_obj_res;
    fn leanrt_sarray_size(arr: b_lean_obj_arg) -> usize;
    fn leanrt_sarray_cptr(arr: b_lean_obj_arg) -> *mut u8;
    /// Allocate a constructor with `num_objs` object fields + `scalar_size` inline bytes. RC=1.
    fn leanrt_alloc_ctor(tag: u32, num_objs: u32, scalar_size: u32) -> lean_obj_res;
    fn leanrt_ctor_set(ctor: lean_obj_arg, idx: u32, v: lean_obj_arg);
    /// Box a usize as a tagged Lean value (used for nullary constructors).
    fn leanrt_box(v: usize) -> lean_obj_res;
}

extern "C" {
    // Real exported Lean runtime symbol — no glue wrapper needed.
    fn lean_apply_1(f: lean_obj_arg, a: lean_obj_arg) -> lean_obj_res;
}

/// Apply a Lean thunk `f : Unit → α` to `()`.
pub unsafe fn lean_apply_unit(f: lean_obj_arg) -> lean_obj_res {
    unsafe { lean_apply_1(f, leanrt_box(0)) }
}

// Re-export under canonical lean_* names.
pub unsafe fn lean_alloc_sarray(elem_size: u32, size: usize, capacity: usize) -> lean_obj_res {
    unsafe { leanrt_alloc_sarray(elem_size, size, capacity) }
}
pub unsafe fn lean_sarray_size(arr: b_lean_obj_arg) -> usize {
    unsafe { leanrt_sarray_size(arr) }
}
pub unsafe fn lean_sarray_cptr(arr: b_lean_obj_arg) -> *mut u8 {
    unsafe { leanrt_sarray_cptr(arr) }
}
pub unsafe fn lean_alloc_ctor(tag: u32, num_objs: u32, scalar_size: u32) -> lean_obj_res {
    unsafe { leanrt_alloc_ctor(tag, num_objs, scalar_size) }
}
pub unsafe fn lean_ctor_set(ctor: lean_obj_arg, idx: u32, v: lean_obj_arg) {
    unsafe { leanrt_ctor_set(ctor, idx, v) }
}
pub unsafe fn lean_box(v: usize) -> lean_obj_res {
    unsafe { leanrt_box(v) }
}

// ── Convenience helpers (pure Rust) ─────────────────────────────────

/// View a Lean ByteArray as `&[u8]`. `arr` must be a valid ByteArray; borrow lasts as long as the Lean caller's borrow.
pub unsafe fn sarray_as_slice<'a>(arr: b_lean_obj_arg) -> &'a [u8] {
    let len = unsafe { lean_sarray_size(arr) };
    let ptr = unsafe { lean_sarray_cptr(arr) };
    unsafe { core::slice::from_raw_parts(ptr, len) }
}

/// Allocate a Lean ByteArray, copy `bytes` into it, and return ownership (RC=1).
pub fn alloc_bytearray(bytes: &[u8]) -> lean_obj_res {
    let n = bytes.len();
    let arr = unsafe { lean_alloc_sarray(1, n, n) };
    let dst = unsafe { lean_sarray_cptr(arr) };
    unsafe { core::ptr::copy_nonoverlapping(bytes.as_ptr(), dst, n) };
    arr
}
