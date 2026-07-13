//! Rust driver for the qedsvm Lean reference SVM.
//! Two entry points: [`Svm`] (Mollusk-shaped API for differential tests) and
//! [`run_buffer`] (low-level: raw ELF + serialized input buffer).

mod cursor;
mod deserialize;
mod ffi;
mod serialize;
mod svm;
mod wire;

/// Diff-testing converters + assertion helpers (qedsvm vs Mollusk). Feature-gated: `diff-mollusk`.
#[cfg(feature = "diff-mollusk")]
pub mod diff;

pub use deserialize::{deserialize_account_writes, DeserializeError};
pub use serialize::{serialize_parameters, SerializeError};
pub use svm::{
    vm_fault_name, InstructionResult, PostStateError, ProgramResult, Svm, SvmError,
    ERR_INVALID_POSTSTATE,
};
pub use wire::{decode as decode_wire, DecodeError, ExitOutcome, RawResult};

/// Run one Lean FFI entry point under the runtime lock, enforcing the
/// lock → alloc → call → read → dec_ref protocol in one place.
///
/// `call` receives the held [`ffi::LeanGuard`]; it must allocate its argument
/// ByteArrays via [`ffi::alloc_bytearray`] and return the OWNED result object of
/// one `qedsvm_*` entry point (the entry points *consume* their argument objects,
/// so refcount=1 allocations are handed off exactly once). The result's bytes are
/// copied out and the object released before the lock is dropped.
fn with_lean(call: impl FnOnce(&ffi::LeanGuard<'_>) -> ffi::lean_obj_res) -> Vec<u8> {
    let g = ffi::lock();
    // SAFETY: all Lean-runtime calls happen under `g`; result_obj is owned by
    // us — dec_ref after copying bytes out.
    let bytes = unsafe {
        let result_obj = call(&g);
        let bytes = ffi::sarray_as_slice(&g, result_obj).to_vec();
        ffi::dec_ref(&g, result_obj);
        bytes
    };
    drop(g);
    bytes
}

/// Run an ELF binary under the Lean VM. Low-level entry — for the Mollusk-shaped API see
/// [`Svm::process_instruction`]. Thread-safe: serialized under a process-wide Mutex; init on first call.
pub fn run_buffer(elf: &[u8], input: &[u8], cu_budget: u64) -> Result<RawResult, DecodeError> {
    let bytes = with_lean(|g| unsafe {
        let elf_obj = ffi::alloc_bytearray(g, elf);
        let input_obj = ffi::alloc_bytearray(g, input);
        ffi::qedsvm_run_elf_buffer(elf_obj, input_obj, cu_budget)
    });
    wire::decode(&bytes)
}

/// Like [`run_buffer`] but passes a CPI program registry (pubkey → ELF) the Lean runner
/// consults on `sol_invoke_signed`. See [`encode_registry`] for the blob format.
pub fn run_buffer_with_registry(
    elf: &[u8],
    input: &[u8],
    registry_blob: &[u8],
    cu_budget: u64,
) -> Result<RawResult, DecodeError> {
    let bytes = with_lean(|g| unsafe {
        let elf_obj = ffi::alloc_bytearray(g, elf);
        let input_obj = ffi::alloc_bytearray(g, input);
        let registry_obj = ffi::alloc_bytearray(g, registry_blob);
        ffi::qedsvm_run_with_registry(elf_obj, input_obj, registry_obj, cu_budget)
    });
    wire::decode(&bytes)
}

/// Like [`run_buffer_with_registry`] but also passes `pid_bytes` into `State.progIdBytes`.
/// Required for `invoke_signed` with PDA signer seeds (CPI handler derives PDAs via `callerPid`).
pub fn run_buffer_with_registry_and_pid(
    elf: &[u8],
    input: &[u8],
    registry_blob: &[u8],
    pid_bytes: &[u8; 32],
    cu_budget: u64,
) -> Result<RawResult, DecodeError> {
    let bytes = with_lean(|g| unsafe {
        let elf_obj = ffi::alloc_bytearray(g, elf);
        let input_obj = ffi::alloc_bytearray(g, input);
        let registry_obj = ffi::alloc_bytearray(g, registry_blob);
        let pid_obj = ffi::alloc_bytearray(g, pid_bytes);
        ffi::qedsvm_run_with_registry_and_pid(elf_obj, input_obj, registry_obj, pid_obj, cu_budget)
    });
    wire::decode(&bytes)
}

/// Drive `SVM.Native.Precompiles.dispatch` for the three sig-verify precompiles.
/// Returns `(r0, cu)`: r0=0 success, r0=1 failure. Bypasses the BPF VM (agave does the same).
pub fn run_precompile(pid: &[u8; 32], ix_data: &[u8]) -> Result<(u64, u64), DecodeError> {
    let bytes = with_lean(|g| unsafe {
        let pid_obj = ffi::alloc_bytearray(g, pid);
        let ix_obj = ffi::alloc_bytearray(g, ix_data);
        ffi::qedsvm_precompile_dispatch(pid_obj, ix_obj)
    });
    // Wire format: [u64 LE r0 ‖ u64 LE cu]; surface malformed length as a wire-format error.
    if bytes.len() != 16 {
        return Err(DecodeError::Malformed("precompile FFI: expected 16 bytes"));
    }
    let mut r0_b = [0u8; 8];
    let mut cu_b = [0u8; 8];
    r0_b.copy_from_slice(&bytes[0..8]);
    cu_b.copy_from_slice(&bytes[8..16]);
    Ok((u64::from_le_bytes(r0_b), u64::from_le_bytes(cu_b)))
}

/// Build the canonical registry blob from (pubkey, elf) pairs; matches `SVM.Ffi.parseRegistry`.
pub fn encode_registry(entries: &[(&[u8; 32], &[u8])]) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(&(entries.len() as u32).to_le_bytes());
    for (pubkey, elf) in entries {
        out.extend_from_slice(pubkey.as_slice());
        out.extend_from_slice(&(elf.len() as u32).to_le_bytes());
        out.extend_from_slice(elf);
    }
    out
}
