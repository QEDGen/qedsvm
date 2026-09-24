//! Minimal NON-token vault program with a PARAMETER delta. The account at the
//! serialized account-data pointer is { owner: [u8;32] @ 0, total: u64 @ 32, bump: u8 @ 40 }.
//! Assumes one non-duplicate 41-byte account in aligned Solana serialization:
//! account data at input+96, instruction data at input+10400.
//! A runtime `amount` (u64) is read from that instruction data and credited to `total`. `owner` and
//! `bump` are untouched.
//!
//! Expected to compile to:
//!   ldxdw r2, [r1 + 128]    ; load total
//!   ldxdw r3, [r1 + 10400]  ; load amount (the parameter)
//!   add64 r2, r3            ; total += amount  (register add, two memory reads)
//!   stxdw [r1 + 128], r2    ; store back
//!   mov64 r0, 0             ; return 0
//!   exit

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[no_mangle]
pub extern "C" fn entrypoint(input: *mut u8) -> u64 {
    unsafe {
        let total_ptr = input.add(128) as *mut u64;
        let amount = core::ptr::read_unaligned(input.add(10400) as *const u64);
        let total = core::ptr::read_unaligned(total_ptr);
        core::ptr::write_unaligned(total_ptr, total.wrapping_add(amount));
    }
    0
}
