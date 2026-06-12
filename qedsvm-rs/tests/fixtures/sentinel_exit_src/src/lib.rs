//! L1 experiment fixture: a CLEAN exit whose r0 equals a fault
//! sentinel. The Lean model's `exitCode : Option Nat` cannot
//! distinguish `mov64 r0, ERR_ABORT; exit` from an actual abort
//! (audit L1). This program returns 0xFFFFFFFFFFFFFFFD (= the model's
//! ERR_ABORT sentinel) from a perfectly healthy run; the diff test
//! pins what agave/mollusk observably reports for it, which decides
//! the L1 wire mapping before any exit-shape refactor.

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[no_mangle]
pub extern "C" fn entrypoint(_input: *mut u8) -> u64 {
    // Read back from a volatile to stop LLVM folding the constant into
    // anything clever; the exit value must be the literal sentinel.
    let v: u64 = 0xFFFFFFFFFFFFFFFD;
    let p = &v as *const u64;
    unsafe { core::ptr::read_volatile(p) }
}
