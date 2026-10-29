//! One parametric probe for `sol_memcpy_`, `sol_memmove_`, `sol_memset_` and
//! `sol_memcmp_` (#103). Instruction data (no accounts) is
//! `[op, 0 x7, a: u64, b: u64, c: u64, d: u64]`, all addresses absolute, and
//! the call is `op(a, b, c[, d])` with op 0 = memcpy, 1 = memmove,
//! 2 = memset (low byte of b), 3 = memcmp.
//!
//! Before the call the heap window `[HEAP, HEAP + WINDOW)` is filled with
//! `i * 7 + 3 (mod 251)` through volatile stores, so the compiler cannot
//! lower the fill to a memop and the pattern is not periodic at 256. After a
//! successful call the window's sha256 is the return data, which exposes every
//! byte the syscall wrote (or failed to write) to the differential test.

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

use solana_define_syscall::definitions::{
    sol_memcmp_, sol_memcpy_, sol_memmove_, sol_memset_, sol_set_return_data, sol_sha256,
};

const HEAP: u64 = 0x3_0000_0000;
const WINDOW: u64 = 8192;

unsafe fn arg(input: *const u8, i: usize) -> u64 {
    // With zero accounts the data starts after num_accounts and data_len.
    core::ptr::read_unaligned(input.add(16 + 8 + 8 * i) as *const u64)
}

#[no_mangle]
pub extern "C" fn entrypoint(input: *mut u8) -> u64 {
    unsafe {
        let op = *input.add(16);
        let (a, b, c, d) = (arg(input, 0), arg(input, 1), arg(input, 2), arg(input, 3));
        let heap = HEAP as *mut u8;
        let mut i = 0u64;
        while i < WINDOW {
            core::ptr::write_volatile(heap.add(i as usize), ((i * 7 + 3) % 251) as u8);
            i += 1;
        }
        match op {
            0 => sol_memcpy_(a as *mut u8, b as *const u8, c),
            1 => sol_memmove_(a as *mut u8, b as *const u8, c),
            2 => sol_memset_(a as *mut u8, b as u8, c),
            3 => sol_memcmp_(a as *const u8, b as *const u8, c, d as *mut i32),
            _ => return 1,
        }
        // Hash the window into a stack buffer and return the digest.
        let desc: [u64; 2] = [HEAP, WINDOW];
        let mut digest = [0u8; 32];
        sol_sha256(desc.as_ptr() as *const u8, 1, digest.as_mut_ptr());
        sol_set_return_data(digest.as_ptr(), 32);
    }
    0
}
