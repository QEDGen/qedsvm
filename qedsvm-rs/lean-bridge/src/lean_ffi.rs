//! Minimal hand-written Rust bindings to the Lean runtime's C ABI.
//!
//! We use the same `lean_alloc_sarray` / `lean_alloc_ctor` / `lean_box`
//! / `lean_ctor_set` / `lean_sarray_*` surface that the (now-deleted)
//! `csrc/` shim files used. Hand-written rather than `bindgen`-generated
//! because we only need ~6 symbols and we want zero build-time
//! dependencies on `lean/lean.h`.
//!
//! Ref-count discipline:
//! - `b_lean_obj_arg` ("borrowed") → no refcount touching from Rust.
//! - `lean_obj_res` ("returned, owned") → returned objects have
//!   refcount 1, transferring ownership to the Lean caller.
//!
//! All functions exposed from this module use Lean's `LEAN_EXPORT`
//! visibility (a Rust `#[no_mangle] pub extern "C"`), matching the
//! shape Lean's `@[extern "<name>"]` declaration expects: the named
//! C function is found at link time in the precompiled module's
//! dynlib, statically pulled in from `libleanbridge.a`.

#![allow(non_camel_case_types)]

/// Opaque pointer to a Lean heap object. We never inspect the layout
/// from Rust — only pass it through to the runtime's API.
#[repr(C)]
pub struct lean_object {
    _private: [u8; 0],
}

/// Borrowed reference (no refcount change). Used for input parameters.
pub type b_lean_obj_arg = *const lean_object;

/// Owned, refcount=1 object. Used for return values transferring
/// ownership to the Lean caller.
pub type lean_obj_res = *mut lean_object;

/// Owned argument (refcount transferred in). Used when passing an
/// object to a Lean runtime function that consumes it (e.g.
/// `lean_ctor_set`).
pub type lean_obj_arg = *mut lean_object;

// The functions below have the prefix `leanrt_` because the upstream
// `lean_*` versions in `lean/lean.h` are `static inline` and produce
// no exported symbols. `lean-bridge/lean_glue.c` emits out-of-line
// wrappers under these names, compiled and linked via `build.rs`.

extern "C" {
    /// Allocate a "scalar array" — what Lean represents `ByteArray`
    /// (and `FloatArray` / `Array UInt8` etc.) as. `elem_size` is the
    /// element width in bytes (1 for ByteArray), `size` is the
    /// initial length, `capacity` is the allocation capacity (we use
    /// `size == capacity`). Resulting object's refcount is 1.
    fn leanrt_alloc_sarray(elem_size: u32, size: usize, capacity: usize) -> lean_obj_res;

    /// Length of a scalar array.
    fn leanrt_sarray_size(arr: b_lean_obj_arg) -> usize;

    /// Pointer to the first byte of a scalar array's data. Valid for
    /// `leanrt_sarray_size(arr)` bytes.
    fn leanrt_sarray_cptr(arr: b_lean_obj_arg) -> *mut u8;

    /// Allocate a constructor with `num_objs` object fields and
    /// `scalar_size` bytes of inline scalar data.
    /// Resulting object's refcount is 1.
    fn leanrt_alloc_ctor(tag: u32, num_objs: u32, scalar_size: u32) -> lean_obj_res;

    /// Install an object into field `idx` of a constructor.
    fn leanrt_ctor_set(ctor: lean_obj_arg, idx: u32, v: lean_obj_arg);

    /// Box a small `usize` as a tagged Lean object. Used to represent
    /// nullary constructors (their tag is boxed as the value).
    fn leanrt_box(v: usize) -> lean_obj_res;
}

// Re-export under Lean's familiar names for the rest of the crate.
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

// ───────────────────────────────────────────────────────────────────
// Convenience helpers (pure Rust, no Lean runtime calls)
// ───────────────────────────────────────────────────────────────────

/// View a `b_lean_obj_arg` ByteArray as a `&[u8]`. Caller asserts that
/// the argument is a ByteArray (validated by Lean's type system at
/// the call site).
///
/// # Safety
/// `arr` must point to a valid Lean ByteArray; the slice borrow lasts
/// only as long as the Lean caller's borrow.
pub unsafe fn sarray_as_slice<'a>(arr: b_lean_obj_arg) -> &'a [u8] {
    let len = unsafe { lean_sarray_size(arr) };
    let ptr = unsafe { lean_sarray_cptr(arr) };
    unsafe { core::slice::from_raw_parts(ptr, len) }
}

/// Allocate a fresh `N`-byte ByteArray, copy `bytes` into it, and
/// return ownership to the caller.
pub fn alloc_bytearray(bytes: &[u8]) -> lean_obj_res {
    let n = bytes.len();
    let arr = unsafe { lean_alloc_sarray(1, n, n) };
    let dst = unsafe { lean_sarray_cptr(arr) };
    unsafe { core::ptr::copy_nonoverlapping(bytes.as_ptr(), dst, n) };
    arr
}
