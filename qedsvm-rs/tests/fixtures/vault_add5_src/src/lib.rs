//! Minimal NON-token vault program. The account at the input pointer is
//!   { owner: [u8;32] @ 0, total: u64 @ 32, bump: u8 @ 40 }.
//! The handler increments `total` by a constant 5, leaving `owner` and `bump`
//! untouched. So the lift owns only the `total` dword cell at offset 32;
//! `owner` (a pubkey) and `bump` (a byte) are framed. Identical in shape to
//! vault_src, but with a non-1 constant delta to exercise the descriptor
//! seam's arbitrary-literal path (`op.add_const = 5`).
//!
//! Compiles to:
//!   ldxdw r2, [r1 + 32]     ; load total
//!   add64 r2, 5             ; increment by 5
//!   stxdw [r1 + 32], r2     ; store back
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
        let total_ptr = input.add(32) as *mut u64;
        let current = core::ptr::read_unaligned(total_ptr);
        core::ptr::write_unaligned(total_ptr, current.wrapping_add(5));
    }
    0
}
