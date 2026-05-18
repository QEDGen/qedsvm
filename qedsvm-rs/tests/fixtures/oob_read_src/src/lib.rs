//! Out-of-bounds memory read. Forces the entrypoint to dereference an
//! address well outside any mapped region.
//!
//! Cross-engine observable:
//! - agave: `solana-sbpf` traps the `ldx` with `EbpfError::AccessViolation`
//!   and `program-runtime` reports the instruction as
//!   `InstructionError::ProgramFailedToComplete`.
//! - Pre-fix qedsvm: total `Mem` returns zero at any unmapped address,
//!   so the read silently succeeds, r0 = 0, exit-status = Success.
//!   Asymmetric outcome — divergence is immediate.
//! - Post-fix qedsvm: `.ldx` consults the runtime region table and
//!   traps to `ERR_ACCESS_VIOLATION`, which the harness surfaces as
//!   `ProgramResult::Failure`. Both engines fail.

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[no_mangle]
pub extern "C" fn entrypoint(input: *mut u8) -> u64 {
    // 256 MiB past the input pointer. For a zero-account / zero-data
    // instruction the input region is ~48 bytes; this access is well
    // outside both the input region and any other mapped region.
    let bad: *const u64 = unsafe { input.add(0x10000000) as *const u64 };
    unsafe { core::ptr::read_volatile(bad) }
}
