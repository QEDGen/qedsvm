//! Out-of-bounds `sol_get_sysvar` OUTPUT slice (sBPF V3, `cargo-build-sbf
//! --arch v3`). Asks for the 17-byte rent sysvar with a readable id but an
//! output buffer 256 MiB past the heap: below `MM_INPUT_START` (so the
//! parameter-address restriction does not fire) and outside every region.
//!
//! Cross-engine observable (audit H6, the generic sysvar accessor):
//! - agave: `SyscallGetSysvar` translates `[var_addr, var_addr+length)` with
//!   `translate_mut!` before touching the id; the unmapped store traps with
//!   `AccessViolation` → `ProgramFailedToComplete`.
//! - Pre-fix qedsvm: `Misc.execGetSysvar` wrote the slice through a region-free
//!   `Mem`, so the OOB store silently succeeded with r0 = 0.
//! - Post-fix qedsvm: the output slice routes through `guardWrite` and traps to
//!   `ERR_ACCESS_VIOLATION`.

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

use solana_define_syscall::definitions::sol_get_sysvar;

/// `SysvarRent111111111111111111111111111111111`.
static RENT_ID: [u8; 32] = [
    0x06, 0xa7, 0xd5, 0x17, 0x19, 0x2c, 0x5c, 0x51, 0x21, 0x8c, 0xc9, 0x4c, 0x3d, 0x4a, 0xf1, 0x7f,
    0x58, 0xda, 0xee, 0x08, 0x9b, 0xa1, 0xfd, 0x44, 0xe3, 0xdb, 0xd9, 0x8a, 0x00, 0x00, 0x00, 0x00,
];

/// Heap start + 256 MiB: unmapped, and below `MM_INPUT_START` (0x4_0000_0000).
const BAD: u64 = 0x3_1000_0000;

#[no_mangle]
pub extern "C" fn entrypoint(_input: *mut u8) -> u64 {
    unsafe { sol_get_sysvar(RENT_ID.as_ptr(), BAD as *mut u8, 0, 17) }
}
