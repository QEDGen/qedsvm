//! Out-of-bounds `sol_sha256` INPUT descriptor array. The output buffer is
//! valid (in the writable input region), but the `SliceDesc` descriptor array
//! is 256 MiB out of region.
//!
//! Cross-engine observable (audit H6 — syscall memory translation, hashing
//! family, stage 3b / input-slice guard):
//! - agave: `SyscallSha256` translates the writable 32-byte output FIRST
//!   (passes), then translates the `&[VmSlice<u8>]` descriptor array at `r1`
//!   via `translate_slice`; its `MemoryMapping::map` traps the out-of-region
//!   read with `AccessViolation` → `ProgramFailedToComplete`.
//! - Pre-fix qedsvm (stage 3a): only the output was guarded, so the OOB
//!   descriptor read silently succeeded (it hashed garbage), r0 = 0, Success.
//! - Post-fix qedsvm (stage 3b): `Sha256.exec` routes the descriptor array
//!   through `guardRead` (and each slice through `guardSlices`), trapping to
//!   `ERR_ACCESS_VIOLATION` (`vmError := some .accessViolation`).

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
    // Output: the start of the writable input region (≥ 32 bytes for an empty
    // instruction context) — agave's output translate passes.
    let good_out: *mut u8 = input;
    // Input descriptor array 256 MiB past the input pointer — out of region.
    let bad_descs: *const u8 = unsafe { input.add(0x10000000) };
    // 1 descriptor: after the output check passes, agave translates the
    // 16-byte descriptor array at `bad_descs`, which is the out-of-region
    // access that traps.
    unsafe { sol_sha256(bad_descs, 1, good_out) };
    0
}
