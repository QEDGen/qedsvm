//! Out-of-bounds `sol_get_sysvar` sysvar ID (sBPF V3, `cargo-build-sbf
//! --arch v3`). Writes into a valid 17-byte stack buffer but points the 32-byte
//! sysvar id 256 MiB past the heap, outside every region.
//!
//! Cross-engine observable (audit H6, the generic sysvar accessor):
//! - agave: `SyscallGetSysvar` translates the (writable) output slice, then
//!   `translate_type::<Pubkey>` on the id traps the unmapped read with
//!   `AccessViolation` → `ProgramFailedToComplete`.
//! - Pre-fix qedsvm: `Misc.execGetSysvar` read the id through a region-free
//!   `Mem` (zeros, not a cached sysvar), so it returned `SYSVAR_NOT_FOUND = 2`.
//! - Post-fix qedsvm: the id read routes through `guardRead` and traps to
//!   `ERR_ACCESS_VIOLATION`.

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

use solana_define_syscall::definitions::sol_get_sysvar;

/// Heap start + 256 MiB: unmapped, and below `MM_INPUT_START` (0x4_0000_0000).
const BAD: u64 = 0x3_1000_0000;

#[no_mangle]
pub extern "C" fn entrypoint(_input: *mut u8) -> u64 {
    let mut out = [0u8; 17];
    let r = unsafe { sol_get_sysvar(BAD as *const u8, out.as_mut_ptr(), 0, 17) };
    // Keep the buffer live so the call's output pointer is a real stack slot.
    unsafe { core::ptr::read_volatile(&out[0]) as u64 + r }
}
