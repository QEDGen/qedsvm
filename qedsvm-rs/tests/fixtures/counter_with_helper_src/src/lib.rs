//! Counter with a non-inlined helper: the entrypoint loads `amount`,
//! then calls a separate function `increment_by(ptr, amount)` to do
//! the load-add-store on a u64 counter. `#[inline(never)]` forces
//! LLVM to emit a real `call_local` (not inline the helper).
//!
//! Input layout (16 bytes):
//!   [0..8]  amount  : u64
//!   [8..16] counter : u64
//!
//! Expected sBPF shape:
//!   entrypoint:
//!     ldxdw  r2, [r1 + 0]        ; amount
//!     add64  r1, 8               ; counter_ptr = input + 8
//!     ; (Solana ABI: arg0 = r1, arg1 = r2 — already set up)
//!     call_local +N              ; → increment_by
//!     mov64  r0, 0
//!     exit
//!
//!   increment_by:
//!     ldxdw  r3, [r1 + 0]
//!     add64  r3, r2
//!     stxdw  [r1 + 0], r3
//!     exit                       ; pops frame, returns to caller's resume PC
//!
//! Demonstration target for qedlift's "Stage A" call_local handling:
//! the symbolic executor follows call_local into the callee and lets
//! the callee's exit pop back into the caller's chain. The whole
//! lifted theorem covers both PC ranges in one cuTripleWithinMem.

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[inline(never)]
#[no_mangle]
fn increment_by(counter_ptr: *mut u64, amount: u64) {
    unsafe {
        let current = core::ptr::read_unaligned(counter_ptr);
        core::ptr::write_unaligned(counter_ptr, current.wrapping_add(amount));
    }
}

#[no_mangle]
pub extern "C" fn entrypoint(input: *mut u8) -> u64 {
    unsafe {
        let amount_ptr  = input as *const u64;
        let amount      = core::ptr::read_unaligned(amount_ptr);
        let counter_ptr = input.add(8) as *mut u64;
        increment_by(counter_ptr, amount);
    }
    0
}
