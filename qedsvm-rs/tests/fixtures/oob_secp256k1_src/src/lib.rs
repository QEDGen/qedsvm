//! Out-of-bounds `sol_secp256k1_recover`. All three crypto slices (the 32-byte
//! message hash `[r1,32)`, the 64-byte signature `[r3,64)`, the 64-byte output
//! `[r4,64)`) are 256 MiB out of region, so both engines trap on the first one
//! they translate (the hash) regardless of translation order.
//!
//! Cross-engine observable (audit H6 — syscall memory translation, the
//! curve / crypto family, stage 5a):
//! - agave: `SyscallSecp256k1Recover` translates the 32-byte hash slice FIRST
//!   (then the 64-byte signature, then the 64-byte output) before recovering;
//!   its `MemoryMapping::map` traps the out-of-region hash read with
//!   `AccessViolation` -> `ProgramFailedToComplete`. The `libsecp256k1` FFI is
//!   never called.
//! - Pre-fix qedsvm: `Secp256k1.exec` read `[r1,32)` / `[r3,64)` and wrote
//!   `[r4,64)` through a region-free `Mem`, so the OOB read silently
//!   succeeded.
//! - Post-fix qedsvm: `exec` routes hash/sig/output through `guardRead` /
//!   `guardWrite`, trapping to `ERR_ACCESS_VIOLATION` (`exec_faults_oob`).

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

extern "C" {
    // r1 = *const [u8; 32] hash, r2 = recovery_id, r3 = *const [u8; 64] sig,
    // r4 = *mut [u8; 64] out.
    fn sol_secp256k1_recover(
        hash: *const u8,
        recovery_id: u64,
        signature: *const u8,
        result: *mut u8,
    ) -> u64;
}

#[no_mangle]
pub extern "C" fn entrypoint(input: *mut u8) -> u64 {
    // 256 MiB past the input pointer — all three slices land well outside any
    // mapped region (disjoint offsets so none accidentally overlaps a region).
    let bad_hash: *const u8 = unsafe { input.add(0x10000000) };
    let bad_sig: *const u8 = unsafe { input.add(0x10000040) };
    let bad_out: *mut u8 = unsafe { input.add(0x10000080) };
    unsafe { sol_secp256k1_recover(bad_hash, 0, bad_sig, bad_out) };
    0
}
