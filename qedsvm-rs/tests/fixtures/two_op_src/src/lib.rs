//! Two-instruction discriminator-dispatched counter.
//!
//! Input layout (9 bytes):
//!   [0..1] discriminator : u8   — 1 = increment, 2 = decrement
//!   [1..9] counter       : u64  — operand
//!
//! Expected sBPF shape (LLVM emits a flat dispatcher cascade):
//!
//!   entrypoint:
//!     ldxb  r2, [r1 + 0]            ; load discriminator
//!     jeq   r2, 1, +inc_offset      ; if 1 → increment arm
//!     jne   r2, 2, +err_offset      ; if not 2 → error arm
//!     ldxdw r3, [r1 + 1]            ; decrement arm: load counter
//!     sub64 r3, 1
//!     stxdw [r1 + 1], r3
//!     mov64 r0, 0
//!     ja    +exit_offset
//!
//!   increment_arm:
//!     ldxdw r3, [r1 + 1]
//!     add64 r3, 1
//!     stxdw [r1 + 1], r3
//!     mov64 r0, 0
//!     ja    +exit_offset
//!
//!   error_arm:
//!     mov64 r0, 1
//!
//!   exit:
//!     exit
//!
//! Used as the connection demo for qedrecover → qedlift: qedrecover
//! identifies each dispatcher arm and emits the path hypotheses to
//! reach it; qedlift consumes those, walks each arm with the
//! corresponding discriminator pinned, and emits one Lean theorem
//! per instruction.

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[no_mangle]
pub extern "C" fn entrypoint(input: *mut u8) -> u64 {
    unsafe {
        let disc = core::ptr::read(input);
        let counter_ptr = input.add(1) as *mut u64;
        let counter = core::ptr::read_unaligned(counter_ptr);
        match disc {
            1 => {
                core::ptr::write_unaligned(counter_ptr, counter.wrapping_add(1));
            }
            2 => {
                core::ptr::write_unaligned(counter_ptr, counter.wrapping_sub(1));
            }
            _ => return 1,
        }
    }
    0
}
