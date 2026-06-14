//! Out-of-bounds SYSCALL memory write. Forces `sol_memset_` to translate
//! a destination slice well outside any mapped region.
//!
//! Cross-engine observable (audit H6 — syscall memory translation):
//! - agave: `SyscallMemset` calls `translate_slice_mut(dst, n)`, whose
//!   `MemoryMapping::map` traps the out-of-region range with
//!   `AccessViolation`; `program-runtime` reports
//!   `InstructionError::ProgramFailedToComplete`.
//! - Pre-fix qedsvm: `MemOps.execSet` wrote `s.mem` through a total
//!   `Nat -> Nat` function with no region check, so the OOB write
//!   silently succeeded, r0 = 0, exit-status = Success. Asymmetric.
//! - Post-fix qedsvm: `MemOps.execSet` routes the `dst` slice through
//!   `guardWrite`, which consults the runtime region table and traps to
//!   `ERR_ACCESS_VIOLATION` (`vmError := some .accessViolation`). Both
//!   engines fail.

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

extern "C" {
    // The registered SPL/Solana memset syscall: r1 = dst, r2 = c, r3 = n.
    fn sol_memset_(s: *mut u8, c: u8, n: u64);
}

#[no_mangle]
pub extern "C" fn entrypoint(input: *mut u8) -> u64 {
    // 256 MiB past the input pointer. For a zero-account / zero-data
    // instruction the input region is ~48 bytes; this destination is well
    // outside both the input region and any other mapped region.
    let bad: *mut u8 = unsafe { input.add(0x10000000) };
    // No instruction-level deref: the address only faults once the
    // syscall translates the 16-byte destination slice.
    unsafe { sol_memset_(bad, 0, 16) };
    0
}
