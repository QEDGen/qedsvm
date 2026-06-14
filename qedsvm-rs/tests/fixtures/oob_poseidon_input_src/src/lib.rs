//! Out-of-bounds `sol_poseidon` INPUT descriptor array. The output buffer is
//! valid (in the writable input region), but the `SliceDesc` descriptor array
//! is 256 MiB out of region.
//!
//! Cross-engine observable (audit H6 — syscall memory translation, hashing
//! family, stage 3c / poseidon input-slice guard):
//! - agave: `SyscallPoseidon` translates the writable 32-byte output FIRST
//!   (passes), then the input descriptor array via `translate_slice`; its
//!   `MemoryMapping::map` traps the out-of-region read with `AccessViolation`
//!   → `ProgramFailedToComplete`.
//! - Pre-fix qedsvm (stage 3a): only the output was guarded, so the OOB
//!   descriptor read silently succeeded (it hashed garbage / returned some),
//!   r0 = 0, Success.
//! - Post-fix qedsvm (stage 3c): `Poseidon.exec`'s `State.guardedCommit` routes
//!   the descriptor array through `guardRead` (and each slice through
//!   `guardSlices`), trapping to `ERR_ACCESS_VIOLATION`.

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

extern "C" {
    // r1 = parameters, r2 = endianness, r3 = *const SliceDesc, r4 = n_vals,
    // r5 = *mut [u8; 32] (the result output buffer).
    fn sol_poseidon(
        parameters: u64,
        endianness: u64,
        vals: *const u8,
        val_len: u64,
        hash_result: *mut u8,
    ) -> u64;
}

#[no_mangle]
pub extern "C" fn entrypoint(input: *mut u8) -> u64 {
    // Output: start of the writable input region — agave's output translate
    // passes, so the descriptor-array translate is the trapping access.
    let good_out: *mut u8 = input;
    // Input descriptor array 256 MiB past the input pointer — out of region.
    let bad_descs: *const u8 = unsafe { input.add(0x10000000) };
    // parameters = 0 (BN254), endianness = 0, 1 input slice.
    unsafe { sol_poseidon(0, 0, bad_descs, 1, good_out) };
    0
}
