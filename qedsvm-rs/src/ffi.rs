//! Low-level Lean FFI surface — thread-safe, init-once.
//!
//! We expose three kinds of things:
//! - Lean runtime entry points (`lean_initialize_runtime_module`,
//!   `lean_io_mark_end_initialization`) — direct symbols from
//!   `libleanshared`.
//! - The compiled `Svm.Ffi` module — its init function
//!   (`initialize_qedsvm_Svm_Ffi`) and our `@[export]`'d entry
//!   point `qedsvm_run_elf_buffer`. Both come from
//!   `qedsvm_Svm_Ffi.dylib`.
//! - Helper wrappers (`leanfsvm_*`) compiled from
//!   `csrc/init_glue.c` — they expose the otherwise-static-inline
//!   ByteArray + IO-result accessors as out-of-line symbols.
//!
//! ## Threading model
//!
//! Lean's runtime is **not** thread-safe across simultaneous
//! mutator calls. A single process-wide [`Mutex`] (`LEAN_LOCK`)
//! serializes every entry into the runtime: allocation, the
//! `qedsvm_run_elf_buffer` call, and the post-call ByteArray
//! reads + dec_ref. Acquire it via [`lock`] for the full duration of
//! one logical Lean operation.
//!
//! Lock poisoning is treated as fatal — if a prior holder panicked
//! mid-call, the Lean heap may be in an inconsistent state, and we
//! refuse to proceed.
//!
//! ## Ref-count discipline
//!
//! - `b_lean_obj_arg` ("borrowed") — no refcount change.
//! - `lean_obj_arg` / `lean_obj_res` ("owned") — refcount transferred
//!   on call boundary. Functions in `Svm.Ffi` that take owned
//!   ByteArrays *consume* their refs. The returned ByteArray's ref
//!   is *transferred to us* — we must `dec_ref` it after copying
//!   the bytes out.

#![allow(non_camel_case_types)]

use std::sync::{Mutex, MutexGuard};

#[repr(C)]
pub struct lean_object {
    _private: [u8; 0],
}

pub type b_lean_obj_arg = *const lean_object;
pub type lean_obj_arg = *mut lean_object;
pub type lean_obj_res = *mut lean_object;

extern "C" {
    // ─ Lean runtime (libleanshared). ──────────────────────────────
    fn lean_initialize_runtime_module();
    fn lean_io_mark_end_initialization();

    // ─ Compiled Svm.Ffi module. ───────────────────────────────────
    fn initialize_qedsvm_Svm_Ffi(builtin: u8) -> lean_obj_res;
    /// The Lean `@[export]` entry point. Takes two ByteArrays and a
    /// u64, returns a ByteArray (wire format documented in
    /// `Svm/Ffi.lean`).
    pub fn qedsvm_run_elf_buffer(
        elf: lean_obj_arg,
        input: lean_obj_arg,
        cu_budget: u64,
    ) -> lean_obj_res;

    /// Same as `qedsvm_run_elf_buffer` but also accepts a
    /// `registry` ByteArray that encodes a (Pubkey → ELF) map for
    /// cross-program invocation. Format (all LE):
    ///
    ///   u32 num_entries
    ///   for each entry:
    ///     [32]u8 pubkey
    ///     u32 elf_size
    ///     [u8;elf_size] elf
    ///
    /// Wire format of the result is identical to
    /// `qedsvm_run_elf_buffer`.
    pub fn qedsvm_run_with_registry(
        elf: lean_obj_arg,
        input: lean_obj_arg,
        registry: lean_obj_arg,
        cu_budget: u64,
    ) -> lean_obj_res;

    /// Top-level dispatch for the three sig-verify precompiles
    /// (ed25519 / secp256k1 / secp256r1). agave routes these without
    /// entering the BPF VM; this entrypoint runs
    /// `Svm.Native.Precompiles.dispatch` against the raw ix data.
    ///
    /// Inputs: `pid_bytes` (32-byte program pubkey) + `ix_data`
    /// (the full instruction-data blob).
    /// Output: a 16-byte ByteArray laid out as
    ///   bytes 0..8   u64 LE  r0  (0 = Success; 1 = failure)
    ///   bytes 8..16  u64 LE  cu_consumed
    pub fn qedsvm_precompile_dispatch(
        pid_bytes: lean_obj_arg,
        ix_data: lean_obj_arg,
    ) -> lean_obj_res;

    // ─ Out-of-line wrappers (csrc/init_glue.c). ───────────────────
    fn leanfsvm_io_result_is_error(r: b_lean_obj_arg) -> u8;
    fn leanfsvm_dec_ref(o: lean_obj_arg);
    fn leanfsvm_alloc_sarray(elem_size: u32, size: usize, capacity: usize) -> lean_obj_res;
    fn leanfsvm_sarray_size(o: b_lean_obj_arg) -> usize;
    fn leanfsvm_sarray_cptr(o: b_lean_obj_arg) -> *mut u8;
}

/// `Mutex<bool>` where the bool is the "initialized" flag. First
/// acquirer runs the one-shot Lean init under the lock; subsequent
/// acquirers see `true` and skip.
///
/// `Mutex::new(false)` is a const initializer (Rust ≥ 1.63), so this
/// can live in a `static`.
static LEAN_LOCK: Mutex<bool> = Mutex::new(false);

/// RAII guard granting exclusive access to the Lean runtime. Hold it
/// for the entire duration of a Lean call sequence (alloc → call →
/// read result → dec_ref). Dropping it releases the runtime to other
/// threads.
pub struct LeanGuard<'a>(#[allow(dead_code)] MutexGuard<'a, bool>);

/// Acquire the Lean runtime lock. First call also performs the
/// one-shot runtime + module initialization.
///
/// # Panics
/// - If `LEAN_LOCK` is poisoned by a prior panic-mid-call. We refuse
///   to recover because Lean's heap state could be corrupt.
/// - If the `Svm.Ffi` module init fails (indicates a stale or
///   mismatched `.dylib` — a build-time problem, not a runtime one).
pub fn lock() -> LeanGuard<'static> {
    let mut guard = LEAN_LOCK
        .lock()
        .expect("Lean runtime lock poisoned: a previous call panicked while holding the lock, leaving the Lean heap in an undefined state — this is a fatal harness bug, not a recoverable error");

    if !*guard {
        // SAFETY: we hold the exclusive Lean lock, so no other
        // thread is touching the runtime.
        unsafe {
            lean_initialize_runtime_module();
            let res = initialize_qedsvm_Svm_Ffi(/* builtin = */ 1);
            if leanfsvm_io_result_is_error(res) != 0 {
                leanfsvm_dec_ref(res);
                // Poison the lock — there's no recovery from a
                // failed init.
                panic!(
                    "Svm.Ffi module init failed. Likely cause: stale \
                     .dylib in .lake/build/ from a different Lean version. \
                     Run `lake clean && lake build` and try again."
                );
            }
            leanfsvm_dec_ref(res);
            lean_io_mark_end_initialization();
        }
        *guard = true;
    }
    LeanGuard(guard)
}

/// Allocate a Lean ByteArray and copy `bytes` into it. Returns an
/// owned ref (refcount 1) ready to hand off to a Lean function that
/// consumes it.
///
/// # Safety
/// Caller must hold a [`LeanGuard`] for the duration of this call
/// and any subsequent use of the returned pointer.
pub unsafe fn alloc_bytearray(_g: &LeanGuard<'_>, bytes: &[u8]) -> lean_obj_res {
    let n = bytes.len();
    let arr = unsafe { leanfsvm_alloc_sarray(1, n, n) };
    if n > 0 {
        let dst = unsafe { leanfsvm_sarray_cptr(arr) };
        unsafe { std::ptr::copy_nonoverlapping(bytes.as_ptr(), dst, n) };
    }
    arr
}

/// View a Lean ByteArray's contents as a `&[u8]`.
///
/// # Safety
/// - Caller must hold a [`LeanGuard`].
/// - `obj` must point to a valid Lean ByteArray.
/// - The returned slice borrows from Lean's heap; it must not outlive
///   the caller's ownership of `obj` (i.e. don't use after `dec_ref`).
pub unsafe fn sarray_as_slice<'a>(_g: &'a LeanGuard<'_>, obj: b_lean_obj_arg) -> &'a [u8] {
    let len = unsafe { leanfsvm_sarray_size(obj) };
    let ptr = unsafe { leanfsvm_sarray_cptr(obj) };
    unsafe { core::slice::from_raw_parts(ptr, len) }
}

/// Drop ownership of a Lean object.
///
/// # Safety
/// - Caller must hold a [`LeanGuard`].
/// - `obj` must be a valid owned pointer (refcount > 0) and must not
///   be used after this call.
pub unsafe fn dec_ref(_g: &LeanGuard<'_>, obj: lean_obj_arg) {
    unsafe { leanfsvm_dec_ref(obj) }
}
