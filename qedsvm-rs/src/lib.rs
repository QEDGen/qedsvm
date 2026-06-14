//! Rust driver for the qedsvm Lean reference SVM.
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

/// Diff-testing utilities — converters + assertion helpers for
/// running the same fixture through both qedsvm and Mollusk. Only
/// compiled when the `diff-mollusk` feature is on (same gate as the
/// `mollusk-svm` dependency).
#[cfg(feature = "diff-mollusk")]
pub mod diff;

/// Shared program-analysis substrate for the qedlift / qedrecover
/// pipeline (issue #41). Only compiled under the `qedrecover` feature,
/// same gate as the `solana-sbpf` dependency it analyses through.
#[cfg(feature = "qedrecover")]
pub mod analysis;

pub use deserialize::{deserialize_account_writes, DeserializeError};
pub use serialize::{serialize_parameters, SerializeError};
pub use svm::{vm_fault_name, InstructionResult, PostStateError, ProgramResult, Svm,
              SvmError, ERR_INVALID_POSTSTATE};
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
    //   - qedsvm_run_elf_buffer *consumes* elf_obj and input_obj
    //     (Lean's ABI for ByteArray arguments)
    //   - the returned result_obj is owned by us; we dec_ref it
    //     after copying its bytes out
    let bytes = unsafe {
        let elf_obj = ffi::alloc_bytearray(&g, elf);
        let input_obj = ffi::alloc_bytearray(&g, input);
        let result_obj = ffi::qedsvm_run_elf_buffer(elf_obj, input_obj, cu_budget);
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
        let result_obj = ffi::qedsvm_run_with_registry(
            elf_obj, input_obj, registry_obj, cu_budget);
        let bytes = ffi::sarray_as_slice(&g, result_obj).to_vec();
        ffi::dec_ref(&g, result_obj);
        bytes
    };
    drop(g);
    wire::decode(&bytes)
}

/// Like [`run_buffer_with_registry`] but also threads the top-level
/// program's 32-byte pubkey into Lean's `State.progIdBytes`. Required
/// for `invoke_signed` with PDA signer seeds: the CPI handler derives
/// the PDA via `create_program_address(seeds, callerPid)`. Without
/// the right `pid_bytes`, the derived PDA won't match any AccountInfo
/// and no signer promotion happens.
pub fn run_buffer_with_registry_and_pid(
    elf: &[u8],
    input: &[u8],
    registry_blob: &[u8],
    pid_bytes: &[u8; 32],
    cu_budget: u64,
) -> Result<RawResult, DecodeError> {
    let g = ffi::lock();
    let bytes = unsafe {
        let elf_obj = ffi::alloc_bytearray(&g, elf);
        let input_obj = ffi::alloc_bytearray(&g, input);
        let registry_obj = ffi::alloc_bytearray(&g, registry_blob);
        let pid_obj = ffi::alloc_bytearray(&g, pid_bytes);
        let result_obj = ffi::qedsvm_run_with_registry_and_pid(
            elf_obj, input_obj, registry_obj, pid_obj, cu_budget);
        let bytes = ffi::sarray_as_slice(&g, result_obj).to_vec();
        ffi::dec_ref(&g, result_obj);
        bytes
    };
    drop(g);
    wire::decode(&bytes)
}

/// Drive the Lean precompile dispatcher
/// (`SVM.Native.Precompiles.dispatch`) for the three sig-verify
/// precompile pubkeys. Returns `(r0, compute_units_consumed)`:
///   - `r0 == 0` → all signatures verified (ProgramResult::Success).
///   - `r0 == 1` → any failure (bad offsets, bad sig, out-of-bounds,
///     non-`0xFFFF` instruction_index, etc).
///   - `cu` is `num_signatures × per_sig_cost` (per agave's
///     cost-model `*_VERIFY_*_COST` constants), charged regardless
///     of pass/fail.
///
/// This bypasses the BPF VM entirely — precompiles never enter it
/// in agave either; the Solana runtime detects their pubkey early
/// in `process_instruction` and routes to a Rust `verify()` closure.
pub fn run_precompile(pid: &[u8; 32], ix_data: &[u8]) -> Result<(u64, u64), DecodeError> {
    let g = ffi::lock();
    let bytes = unsafe {
        let pid_obj = ffi::alloc_bytearray(&g, pid);
        let ix_obj = ffi::alloc_bytearray(&g, ix_data);
        let result_obj = ffi::qedsvm_precompile_dispatch(pid_obj, ix_obj);
        let bytes = ffi::sarray_as_slice(&g, result_obj).to_vec();
        ffi::dec_ref(&g, result_obj);
        bytes
    };
    drop(g);
    // 16-byte wire format: [u64 LE r0 ‖ u64 LE cu]. A malformed length
    // would otherwise panic on the slice below in release — surface it
    // as a wire-format error so callers can decide.
    if bytes.len() != 16 {
        return Err(DecodeError::Malformed("precompile FFI: expected 16 bytes"));
    }
    let mut r0_b = [0u8; 8];
    let mut cu_b = [0u8; 8];
    r0_b.copy_from_slice(&bytes[0..8]);
    cu_b.copy_from_slice(&bytes[8..16]);
    Ok((u64::from_le_bytes(r0_b), u64::from_le_bytes(cu_b)))
}

/// Build the canonical registry blob from a list of (pubkey, elf) pairs.
/// Matches `SVM.Ffi.parseRegistry` in the Lean side.
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
