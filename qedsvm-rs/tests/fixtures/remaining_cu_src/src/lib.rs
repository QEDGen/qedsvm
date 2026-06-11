//! Remaining-CU probe: calls `sol_remaining_compute_units()` and writes
//! the returned u64 (LE) into `accounts[0].data[0..8]`, returns 0.
//!
//! The empirical anchor for H7: the cross-engine diff test asserts the
//! 8 bytes are byte-identical between qedsvm and mollusk/agave, pinning
//! qedsvm's remaining-budget formula
//! (`cuBudget − (cuConsumed + 1 + 100)`) against rbpf's real meter.
//!
//! Mirrors `halfword_store_src/`'s style — no `solana_program` dep,
//! hand-written `extern "C" fn entrypoint`, so `cargo-build-sbf` emits
//! the tightest possible `.text`.

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

extern "C" {
    fn sol_remaining_compute_units() -> u64;
}

/// Account 0's data region for a single non-dup account: 8 (count) +
/// 88 (per-account header) = 96 bytes into the serialized input.
const ACCOUNT0_DATA: usize = 96;

#[no_mangle]
pub extern "C" fn entrypoint(input: *mut u8) -> u64 {
    unsafe {
        let remaining = sol_remaining_compute_units();
        let p = input.add(ACCOUNT0_DATA) as *mut u64;
        core::ptr::write_unaligned(p, remaining.to_le());
    }
    0
}
