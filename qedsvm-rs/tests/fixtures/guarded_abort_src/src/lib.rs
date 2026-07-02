//! Whole-transition FAULT-path fixture (#40): the guarded counter whose
//! guard-fail path PANICS (the `abort` syscall — typed `.abort` fault)
//! instead of returning an error code.
//!
//! Input layout (16 bytes):
//!   [0..8]  amount  : u64   (under mollusk: the serialized account count)
//!   [8..16] counter : u64
//!
//! amount == 0 → `abort()` (vmError = .abort, agave
//! ProgramFailedToComplete); else counter += amount, return 0.
//!
//! Expected sBPF shape:
//!   ldxdw r2, [r1 + 0]    ; amount
//!   jeq   r2, 0, +N       ; if amount == 0 jump to the abort landing
//!   ldxdw r3, [r1 + 8]    ; counter
//!   add64 r3, r2
//!   stxdw [r1 + 8], r3
//!   mov64 r0, 0
//!   exit
//!   ; abort landing:
//!   call  abort

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
pub extern "C" fn entrypoint(input: *mut u8) -> u64 {
    unsafe {
        let amount = core::ptr::read_unaligned(input as *const u64);
        if amount == 0 {
            abort();
        }
        let counter_ptr = input.add(8) as *mut u64;
        let current = core::ptr::read_unaligned(counter_ptr);
        core::ptr::write_unaligned(counter_ptr, current.wrapping_add(amount));
    }
    0
}
