//! Out-of-bounds SYSCALL message log. Forces `sol_log_` to translate a
//! message slice well outside any mapped region.
//!
//! Cross-engine observable (audit H6 — syscall memory translation):
//! - agave: `SyscallLog` calls `translate_string_and_do` →
//!   `translate_slice::<u8>(ptr, len)`, whose `MemoryMapping::map` traps
//!   the out-of-region read with `AccessViolation`; `program-runtime`
//!   reports `InstructionError::ProgramFailedToComplete`.
//! - Pre-fix qedsvm: `Logging.execLog` read `s.mem` through a region-free
//!   `Mem`, so the OOB read silently succeeded, r0 = 0, Success.
//! - Post-fix qedsvm: `execLog` routes the `[ptr, ptr+len)` read through
//!   `guardRead`, which consults the runtime region table and traps to
//!   `ERR_ACCESS_VIOLATION` (`vmError := some .accessViolation`).

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

extern "C" {
    // The registered message-log syscall: r1 = ptr, r2 = len.
    fn sol_log_(message: *const u8, len: u64);
}

#[no_mangle]
pub extern "C" fn entrypoint(input: *mut u8) -> u64 {
    // 256 MiB past the input pointer — well outside any mapped region.
    let bad: *const u8 = unsafe { input.add(0x10000000) };
    // Non-zero length so the slice is actually translated (agave allows
    // a zero-length log without checking).
    unsafe { sol_log_(bad, 16) };
    0
}
