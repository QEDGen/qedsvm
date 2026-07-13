//! Low-level Lean FFI surface — thread-safe, init-once.
//!
//! Threading: Lean runtime is NOT thread-safe; a single process-wide `LEAN_LOCK` serializes every
//! entry. Lock poisoning is fatal (Lean heap may be corrupt after a mid-call panic).
//!
//! Ref-count: `b_lean_obj_arg` = borrowed (no change); `lean_obj_arg`/`lean_obj_res` = owned
//! (consumed on call, returned ref is ours — `dec_ref` after copying bytes out).

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

    // ─ Compiled SVM.Ffi module. ───────────────────────────────────
    fn initialize_qedsvm_SVM_Ffi(builtin: u8) -> lean_obj_res;
    /// The Lean `@[export]` entry point. Takes two ByteArrays and a
    /// u64, returns a ByteArray (wire format documented in
    /// `SVM/Ffi.lean`).
    pub fn qedsvm_run_elf_buffer(
        elf: lean_obj_arg,
        input: lean_obj_arg,
        cu_budget: u64,
    ) -> lean_obj_res;

    /// Like `qedsvm_run_elf_buffer` but with a CPI registry ByteArray (u32 n + n×[32B pubkey, u32 len, [u8]]). Same result wire format.
    pub fn qedsvm_run_with_registry(
        elf: lean_obj_arg,
        input: lean_obj_arg,
        registry: lean_obj_arg,
        cu_budget: u64,
    ) -> lean_obj_res;

    /// Like `qedsvm_run_with_registry` but also accepts `pid_bytes` (32B) for `State.progIdBytes`; needed for PDA derivation in `invoke_signed`.
    pub fn qedsvm_run_with_registry_and_pid(
        elf: lean_obj_arg,
        input: lean_obj_arg,
        registry: lean_obj_arg,
        pid_bytes: lean_obj_arg,
        cu_budget: u64,
    ) -> lean_obj_res;

    /// Run `SVM.Native.Precompiles.dispatch` for ed25519/secp256k1/secp256r1 (agave bypasses BPF VM for these).
    /// Returns 16-byte ByteArray: [u64 LE r0, u64 LE cu_consumed].
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

/// Init-once flag: first acquirer runs one-shot Lean init; subsequent acquirers see `true` and skip.
static LEAN_LOCK: Mutex<bool> = Mutex::new(false);

/// RAII guard for exclusive Lean runtime access. Hold for the full alloc → call → read → dec_ref sequence.
pub struct LeanGuard<'a>(#[allow(dead_code)] MutexGuard<'a, bool>);

/// Acquire the Lean runtime lock; first call also performs one-shot runtime + module init.
/// Panics if the lock is poisoned (prior mid-call panic → Lean heap may be corrupt) or if module init fails.
pub fn lock() -> LeanGuard<'static> {
    let mut guard = LEAN_LOCK
        .lock()
        .expect("Lean runtime lock poisoned: a previous call panicked while holding the lock, leaving the Lean heap in an undefined state — this is a fatal harness bug, not a recoverable error");

    if !*guard {
        // SAFETY: we hold the exclusive Lean lock.
        unsafe {
            lean_initialize_runtime_module();
            let res = initialize_qedsvm_SVM_Ffi(/* builtin = */ 1);
            if leanfsvm_io_result_is_error(res) != 0 {
                leanfsvm_dec_ref(res);
                panic!(
                    // no recovery from a failed init
                    "SVM.Ffi module init failed. Likely cause: stale \
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

/// Allocate a Lean ByteArray and copy `bytes` into it. Returns owned ref (refcount=1).
/// # Safety: caller must hold a [`LeanGuard`].
pub unsafe fn alloc_bytearray(_g: &LeanGuard<'_>, bytes: &[u8]) -> lean_obj_res {
    let n = bytes.len();
    let arr = unsafe { leanfsvm_alloc_sarray(1, n, n) };
    if n > 0 {
        let dst = unsafe { leanfsvm_sarray_cptr(arr) };
        unsafe { std::ptr::copy_nonoverlapping(bytes.as_ptr(), dst, n) };
    }
    arr
}

/// View a Lean ByteArray's contents as `&[u8]`.
/// # Safety: caller must hold a [`LeanGuard`]; `obj` must be a valid ByteArray; slice must not outlive ownership of `obj`.
pub unsafe fn sarray_as_slice<'a>(_g: &'a LeanGuard<'_>, obj: b_lean_obj_arg) -> &'a [u8] {
    let len = unsafe { leanfsvm_sarray_size(obj) };
    let ptr = unsafe { leanfsvm_sarray_cptr(obj) };
    unsafe { core::slice::from_raw_parts(ptr, len) }
}

/// Drop ownership of a Lean object.
/// # Safety: caller must hold a [`LeanGuard`]; `obj` must be valid and owned; don't use after.
pub unsafe fn dec_ref(_g: &LeanGuard<'_>, obj: lean_obj_arg) {
    unsafe { leanfsvm_dec_ref(obj) }
}
