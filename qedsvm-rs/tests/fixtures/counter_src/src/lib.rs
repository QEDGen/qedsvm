//! Minimal 64-bit counter program: reads a u64 at the input pointer,
//! writes back `counter + 1`, returns 0.
//!
//! Compiles to:
//!   ldxdw r2, [r1 + 0]      ; load 64-bit counter
//!   add64 r2, 1             ; increment
//!   stxdw [r1 + 0], r2      ; store back
//!   mov64 r0, 0             ; return value
//!   exit
//!
//! Same shape as `byte_increment_src` but the load/store width
//! exercises the `MemDwordLoad` / `MemDwordStore` spec families
//! (`ldxdw_spec`, `stxdw_spec`).

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[no_mangle]
pub extern "C" fn entrypoint(input: *mut u8) -> u64 {
    unsafe {
        let counter_ptr = input as *mut u64;
        let current = core::ptr::read_unaligned(counter_ptr);
        core::ptr::write_unaligned(counter_ptr, current.wrapping_add(1));
    }
    0
}
