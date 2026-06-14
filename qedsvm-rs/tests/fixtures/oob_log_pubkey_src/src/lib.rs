//! Out-of-bounds SYSCALL pubkey log. Forces `sol_log_pubkey` to
//! translate a 32-byte pubkey well outside any mapped region.
//!
//! Cross-engine observable (audit H6 — syscall memory translation):
//! - agave: `SyscallLogPubkey` calls `translate_type::<Pubkey>(addr)`,
//!   whose `MemoryMapping::map` traps the out-of-region 32-byte read with
//!   `AccessViolation`; `program-runtime` reports
//!   `InstructionError::ProgramFailedToComplete`.
//! - Pre-fix qedsvm: `Logging.execLogPubkey` read `s.mem` through a
//!   region-free `Mem`, so the OOB read silently succeeded, r0 = 0,
//!   exit-status = Success. Asymmetric outcome.
//! - Post-fix qedsvm: `execLogPubkey` routes the 32-byte read through
//!   `guardRead`, which consults the runtime region table and traps to
//!   `ERR_ACCESS_VIOLATION` (`vmError := some .accessViolation`). Both
//!   engines fail.

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

extern "C" {
    // The registered pubkey-log syscall: r1 = pubkey pointer.
    fn sol_log_pubkey(pubkey_addr: *const u8);
}

#[no_mangle]
pub extern "C" fn entrypoint(input: *mut u8) -> u64 {
    // 256 MiB past the input pointer — well outside any mapped region.
    let bad: *const u8 = unsafe { input.add(0x10000000) };
    // No instruction-level deref: the address only faults once the
    // syscall translates the 32-byte pubkey.
    unsafe { sol_log_pubkey(bad) };
    0
}
