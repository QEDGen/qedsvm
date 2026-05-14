//! Rust driver for the formal-svm Lean reference SVM.
//!
//! Two entry points:
//! - [`Svm`] — Mollusk-shaped: `add_program(pid, elf)` /
//!   `process_instruction(&ix, &accounts)` returning
//!   `InstructionResult { program_result, logs, return_data,
//!   resulting_accounts, .. }`. This is what you'll use in
//!   differential tests.
//! - [`run_buffer`] — low-level: raw ELF + already-serialized input
//!   buffer. Useful when you want to drive the Lean runner from a
//!   non-Solana-typed test harness, or to short-circuit the
//!   account-buffer marshaling.

mod deserialize;
mod ffi;
mod serialize;
mod svm;
mod wire;

pub use deserialize::{deserialize_account_writes, DeserializeError};
pub use serialize::{serialize_parameters, SerializeError};
pub use svm::{InstructionResult, ProgramResult, Svm, SvmError};
pub use wire::{decode as decode_wire, DecodeError, ExitOutcome, RawResult};

/// Run an ELF binary under the Lean VM with an arbitrary input buffer
/// placed at `INPUT_START`. This is the low-level entry — for the
/// Mollusk-shaped instruction API see [`Svm::process_instruction`].
///
/// `elf` is the raw ELF64 binary; `input` is the bytes written at
/// `INPUT_START` (real Solana programs read accounts + instruction
/// data from this region via the `entrypoint!` deserializer).
///
/// Thread-safe: serialized internally under a process-wide Mutex
/// around the Lean runtime. Init happens on first call.
pub fn run_buffer(elf: &[u8], input: &[u8], cu_budget: u64) -> Result<RawResult, DecodeError> {
    let g = ffi::lock();
    // SAFETY: all of the following Lean-runtime calls happen under
    // the guard `g`. Ref-count discipline:
    //   - alloc_bytearray returns refcount=1 → owned by us
    //   - formal_svm_run_elf_buffer *consumes* elf_obj and input_obj
    //     (Lean's ABI for ByteArray arguments)
    //   - the returned result_obj is owned by us; we dec_ref it
    //     after copying its bytes out
    let bytes = unsafe {
        let elf_obj = ffi::alloc_bytearray(&g, elf);
        let input_obj = ffi::alloc_bytearray(&g, input);
        let result_obj = ffi::formal_svm_run_elf_buffer(elf_obj, input_obj, cu_budget);
        let bytes = ffi::sarray_as_slice(&g, result_obj).to_vec();
        ffi::dec_ref(&g, result_obj);
        bytes
    };
    drop(g);
    wire::decode(&bytes)
}

/// Like [`run_buffer`] but additionally passes a CPI program registry —
/// a flat blob mapping pubkeys to ELF bytes that the Lean runner
/// consults on `sol_invoke_signed{,_c}`. Use this when the program
/// under test may CPI into other programs (Token, ATA, System, etc.).
///
/// `registry_blob` format (all little-endian):
/// ```text
/// u32 num_entries
/// for each entry:
///   [32]u8 pubkey
///   u32 elf_size
///   [u8; elf_size] elf
/// ```
///
/// See [`encode_registry`] for the canonical builder.
pub fn run_buffer_with_registry(
    elf: &[u8],
    input: &[u8],
    registry_blob: &[u8],
    cu_budget: u64,
) -> Result<RawResult, DecodeError> {
    let g = ffi::lock();
    let bytes = unsafe {
        let elf_obj = ffi::alloc_bytearray(&g, elf);
        let input_obj = ffi::alloc_bytearray(&g, input);
        let registry_obj = ffi::alloc_bytearray(&g, registry_blob);
        let result_obj = ffi::formal_svm_run_with_registry(
            elf_obj, input_obj, registry_obj, cu_budget);
        let bytes = ffi::sarray_as_slice(&g, result_obj).to_vec();
        ffi::dec_ref(&g, result_obj);
        bytes
    };
    drop(g);
    wire::decode(&bytes)
}

/// Build the canonical registry blob from a list of (pubkey, elf) pairs.
/// Matches `Svm.Ffi.parseRegistry` in the Lean side.
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
