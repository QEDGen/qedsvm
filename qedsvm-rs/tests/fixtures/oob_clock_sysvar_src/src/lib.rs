//! Out-of-bounds `sol_get_clock_sysvar` OUTPUT write. Forces the syscall to
//! translate its fixed 40-byte `Clock` output buffer from well outside any
//! mapped region.
//!
//! Cross-engine observable (audit H6 — syscall memory translation, the sysvar
//! family / fixed-size getters):
//! - agave: `SyscallGetClockSysvar` calls `translate_type_mut::<Clock>(addr)`
//!   on the output buffer; its `MemoryMapping::map` traps the out-of-region
//!   (non-writable) store with `AccessViolation` → `ProgramFailedToComplete`.
//! - Pre-fix qedsvm: `Sysvar.execClock` (via `zeroFillR1`) wrote the 40 bytes
//!   through a region-free `Mem`, so the OOB store silently succeeded, r0 = 0.
//! - Post-fix qedsvm: `zeroFillR1` routes the write through `guardWrite`, which
//!   consults the runtime region table and traps to `ERR_ACCESS_VIOLATION`.

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

extern "C" {
    // r1 = *mut [u8; 40] (the Clock output buffer).
    fn sol_get_clock_sysvar(addr: *mut u8) -> u64;
}

#[no_mangle]
pub extern "C" fn entrypoint(input: *mut u8) -> u64 {
    // 256 MiB past the input pointer — well outside any mapped region.
    let bad: *mut u8 = unsafe { input.add(0x10000000) };
    unsafe { sol_get_clock_sysvar(bad) };
    0
}
