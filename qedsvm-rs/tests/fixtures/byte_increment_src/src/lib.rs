//! Minimal byte-increment program: reads one byte from the input
//! pointer, writes back `byte + 1`, returns 0.
//!
//! Mirrors `noop_src/`'s style — no `solana_program` dep, hand-written
//! `extern "C" fn entrypoint`, panic handler, so `cargo-build-sbf`
//! emits the tightest possible `.text`.

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[no_mangle]
pub extern "C" fn entrypoint(input: *mut u8) -> u64 {
    unsafe {
        let b = core::ptr::read(input);
        core::ptr::write(input, b.wrapping_add(1));
    }
    0
}
