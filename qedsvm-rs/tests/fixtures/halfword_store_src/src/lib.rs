//! Minimal halfword-op program: covers all three halfword memory
//! instructions in one straight line.
//!
//! - `ldxh`: read the u16 at `input[0..2]`
//! - `stxh`: write back `value + 1` (register-sourced halfword store)
//! - `sth` (ST_H_IMM): write the constant `0x1234` at `input[2..4]`
//!
//! Mirrors `byte_increment_src/`'s style — no `solana_program` dep,
//! hand-written `extern "C" fn entrypoint`, so `cargo-build-sbf` emits
//! the tightest possible `.text`.

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

/// Account 0's data region for a single non-dup account: 8 (count) +
/// 88 (per-account header) = 96 bytes into the serialized input.
const ACCOUNT0_DATA: usize = 96;

#[no_mangle]
pub extern "C" fn entrypoint(input: *mut u8) -> u64 {
    unsafe {
        let p = input.add(ACCOUNT0_DATA) as *mut u16;
        let h = core::ptr::read_unaligned(p);
        core::ptr::write_unaligned(p, h.wrapping_add(1));
        core::ptr::write_unaligned(p.add(1), 0x1234u16);
    }
    0
}
