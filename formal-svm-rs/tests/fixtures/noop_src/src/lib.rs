//! Truly minimal noop: returns 0 (success) without touching anything.
//! Avoids `solana_program::entrypoint!`'s deserialization boilerplate
//! so the resulting `.text` is the smallest possible cargo-build-sbf
//! output we can produce.

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[no_mangle]
pub extern "C" fn entrypoint(_input: *mut u8) -> u64 {
    0
}
