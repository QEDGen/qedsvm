//! Guarded counter: reads a u64 `amount` at offset 0, asserts it's
//! non-zero, then adds it to a u64 `counter` at offset 8.
//!
//! Input layout (16 bytes):
//!   [0..8]  amount  : u64
//!   [8..16] counter : u64
//!
//! Returns 0 on success; the bare-metal "fail" path returns 1 (a
//! ProgramError discriminator stand-in).
//!
//! Expected sBPF shape (LLVM emits something like):
//!   ldxdw r2, [r1 + 0]    ; amount
//!   jeq   r2, 0, +N       ; if amount == 0 jump to error
//!   ldxdw r3, [r1 + 8]    ; counter
//!   add64 r3, r2          ; counter += amount
//!   stxdw [r1 + 8], r3
//!   mov64 r0, 0
//!   exit
//!   ; error path:
//!   mov64 r0, 1
//!   exit
//!
//! Used as the conditional-branch fixture for qedlift phase 3.

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[no_mangle]
pub extern "C" fn entrypoint(input: *mut u8) -> u64 {
    unsafe {
        let amount_ptr  = input as *const u64;
        let amount      = core::ptr::read_unaligned(amount_ptr);
        if amount == 0 {
            return 1;
        }
        let counter_ptr = input.add(8) as *mut u64;
        let current     = core::ptr::read_unaligned(counter_ptr);
        core::ptr::write_unaligned(counter_ptr, current.wrapping_add(amount));
    }
    0
}
