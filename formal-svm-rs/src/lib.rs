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
