//! Whole-transition OOB-FAULT-path fixture (#40): the guarded counter whose
//! guard-fail path performs an out-of-bounds `sol_get_clock_sysvar` write
//! (typed `.accessViolation` fault) — a sloppy error handler, not a clean
//! return.
//!
//! Input layout (16 bytes):
//!   [0..8]  amount  : u64   (under mollusk: the serialized account count)
//!   [8..16] counter : u64
//!
//! amount == 0 → `sol_get_clock_sysvar(input + 256 MiB)` (OOB output buffer;
//! agave AccessViolation → ProgramFailedToComplete); else counter += amount,
//! return 0.

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
    unsafe {
        let amount = core::ptr::read_unaligned(input as *const u64);
        if amount == 0 {
            // 256 MiB past the input pointer — well outside any mapped region.
            let bad: *mut u8 = input.add(0x10000000);
            sol_get_clock_sysvar(bad);
            return 2;
        }
        let counter_ptr = input.add(8) as *mut u64;
        let current = core::ptr::read_unaligned(counter_ptr);
        core::ptr::write_unaligned(counter_ptr, current.wrapping_add(amount));
    }
    0
}
