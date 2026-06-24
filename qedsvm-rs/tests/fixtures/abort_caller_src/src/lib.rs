//! Phase 7 sub-item 3 (emitter half) fixture: a program whose happy
//! path runs a small straight-line prefix and then unconditionally
//! invokes the `abort` syscall — the typed `.abort` fault terminal.
//!
//! The `abort` syscall (Murmur3 hash of "abort") sets
//! `exitCode := ERR_ABORT` and `vmError := .abort` (audit L1's typed
//! fault channel). It never returns, so the lifted prefix ends at the
//! `call abort` and the lift emits a `*_fault_correct` corollary
//! (`cuTripleFaultsWithinMem … .abort`) composing the running prefix
//! with `call_abort_faults_spec`.
//!
//! Cross-engine observable:
//! - agave: the `abort` syscall traps; `program-runtime` reports
//!   `InstructionError::ProgramFailedToComplete`.
//! - qedsvm: the Lean runtime sets `exitCode = ERR_ABORT` /
//!   `vmError = .abort`, surfaced as a VM fault. Both engines fault.

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

extern "C" {
    fn abort() -> !;
}

#[no_mangle]
pub extern "C" fn entrypoint(_input: *mut u8) -> u64 {
    // A volatile constant forces a real `mov64 r0, imm` to land before
    // the abort (LLVM would otherwise drop dead code ahead of a
    // diverging call), giving the lifted prefix a non-empty
    // straight-line block instead of a bare terminal.
    let v: u64 = 5;
    let r0 = unsafe { core::ptr::read_volatile(&v as *const u64) };
    let _ = r0;
    unsafe { abort() }
}
