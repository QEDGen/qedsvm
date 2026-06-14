//! Out-of-bounds `sol_set_return_data` INPUT read. Forces the syscall to
//! translate its input slice from well outside any mapped region (with a
//! length within MAX_RETURN_DATA so the length pre-check passes).
//!
//! Cross-engine observable (audit H6 — syscall memory translation, the
//! return-data family, stage 4b / input read guard):
//! - agave: `SyscallSetReturnData` checks `len > MAX_RETURN_DATA` first
//!   (passes for len = 8), then `translate_slice::<u8>(addr, len)`; its
//!   `MemoryMapping::map` traps the out-of-region read with `AccessViolation`
//!   -> `ProgramFailedToComplete`.
//! - Pre-fix qedsvm: `ReturnData.execSet` read `[r1, r1+r2)` through a
//!   region-free `Mem`, so the OOB read silently succeeded, r0 = 0.
//! - Post-fix qedsvm: `execSet` routes the input through `guardRead`, which
//!   consults the runtime region table and traps to `ERR_ACCESS_VIOLATION`.

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

extern "C" {
    // r1 = *const u8 (return-data bytes), r2 = len.
    fn sol_set_return_data(data: *const u8, len: u64) -> u64;
}

#[no_mangle]
pub extern "C" fn entrypoint(input: *mut u8) -> u64 {
    // 256 MiB past the input pointer — well outside any mapped region.
    let bad: *const u8 = unsafe { input.add(0x10000000) };
    // 8 bytes (<= MAX_RETURN_DATA = 1024, and > 0): the length check passes,
    // so the out-of-region slice translate is the trapping access.
    unsafe { sol_set_return_data(bad, 8) };
    0
}
