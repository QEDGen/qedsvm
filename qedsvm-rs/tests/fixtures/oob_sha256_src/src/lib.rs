//! Out-of-bounds `sol_sha256` OUTPUT write. Forces the syscall to translate
//! its fixed 32-byte result buffer from well outside any mapped region.
//!
//! Cross-engine observable (audit H6 — syscall memory translation, the
//! hashing family, stage 3a / output-write guard):
//! - agave: `SyscallSha256` calls
//!   `translate_slice_mut::<u8>(hash_result_addr, HASH_BYTES = 32)` on the
//!   output buffer FIRST (before reading any input slice); its
//!   `MemoryMapping::map` traps the out-of-region (here also non-writable)
//!   store with `AccessViolation`, and `program-runtime` reports
//!   `InstructionError::ProgramFailedToComplete`.
//! - Pre-fix qedsvm: `Sha256.exec` wrote the 32-byte digest through a
//!   region-free `Mem`, so the OOB store silently succeeded, r0 = 0,
//!   Success — an arbitrary 32-byte write.
//! - Post-fix qedsvm: `Sha256.exec` routes the output through `guardWrite`,
//!   which consults the runtime region table and traps to
//!   `ERR_ACCESS_VIOLATION` (`vmError := some .accessViolation`).
//!
//! The input count is 0, so the descriptor array is never dereferenced;
//! agave checks the output buffer before the (empty) input, so the output
//! translation is the trapping access on both engines.

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

extern "C" {
    // r1 = *const SliceDesc (input descriptors), r2 = n_vals,
    // r3 = *mut [u8; 32] (the digest output buffer).
    fn sol_sha256(vals: *const u8, val_len: u64, hash_result: *mut u8) -> u64;
}

#[no_mangle]
pub extern "C" fn entrypoint(input: *mut u8) -> u64 {
    // 256 MiB past the input pointer — well outside any mapped region.
    let bad_out: *mut u8 = unsafe { input.add(0x10000000) };
    // 0 input slices: `vals` is never dereferenced. agave translates the
    // 32-byte output buffer at `bad_out` first, so that store is the
    // out-of-region access that traps.
    unsafe { sol_sha256(input, 0, bad_out) };
    0
}
