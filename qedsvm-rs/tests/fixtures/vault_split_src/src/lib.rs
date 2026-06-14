//! Variant of vault_src that PARTIALLY touches the `owner: [u8;32]` blob.
//! The account is { owner: [u8;32] @ 0, total: u64 @ 32, bump: u8 @ 40 }.
//! The handler READS `owner[5]` (volatile, so the read survives optimisation
//! even though its result is discarded), then bumps `total`. So the lift owns
//! the `total` dword AND the `owner[5]` byte cell, READ-ONLY (pre = post). When
//! the IDL types `owner` as a [u8;32] array, the account-codec aggregation must
//! SPLIT the blob into `[.gap, .byte owner5, .gap]` (the mechanized
//! multisig-style split) instead of one opaque gap.
//!
//! The `owner[5]` read RESULT becomes the return value (r0), so it is kept by
//! the optimiser and does not clobber the input pointer (r1).
//!
//! Compiles to:
//!   ldxdw r2, [r1 + 32]     ; load total
//!   add64 r2, 1             ; increment
//!   stxdw [r1 + 32], r2     ; store back
//!   ldxb  r0, [r1 + 5]      ; load owner[5] into the return register
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
        core::ptr::write_unaligned(total_ptr, current.wrapping_add(1));
        *input.add(5) as u64
    }
}
