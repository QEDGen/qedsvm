//! Out-of-bounds `sol_create_program_address`. Zero seeds (so the seed
//! descriptor array is empty and untranslated); the 32-byte program_id `[r3,32)`
//! and the 32-byte output `[r4,32)` are both 256 MiB out of region, so both
//! engines trap on a PDA-region access.
//!
//! Cross-engine observable (audit H6 — syscall memory translation, the PDA
//! family, stage 5b):
//! - agave: `SyscallCreateProgramAddress` translates the seed descriptors +
//!   each seed slice, the 32-byte program_id (Load) and the 32-byte output
//!   (Store); its `MemoryMapping::map` traps the out-of-region access with
//!   `AccessViolation` -> `ProgramFailedToComplete`.
//! - Pre-fix qedsvm: `Pda.execCreate` read the seeds/program_id and wrote the
//!   output through a region-free `Mem`, so the OOB access silently succeeded.
//! - Post-fix qedsvm: `execCreate` routes the program_id through `guardRead`
//!   and the output + seeds through `guardedCommit`, trapping to
//!   `ERR_ACCESS_VIOLATION` (`Pda.execCreate_faults_oob`).

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

extern "C" {
    // r1 = *const [VmSlice; N] seeds, r2 = N, r3 = *const [u8; 32] program_id,
    // r4 = *mut [u8; 32] result.
    fn sol_create_program_address(
        seeds: *const u8,
        seeds_len: u64,
        program_id: *const u8,
        result: *mut u8,
    ) -> u64;
}

#[no_mangle]
pub extern "C" fn entrypoint(input: *mut u8) -> u64 {
    // 256 MiB past the input pointer — out of region.
    let bad_pid: *const u8 = unsafe { input.add(0x10000000) };
    let bad_out: *mut u8 = unsafe { input.add(0x10000040) };
    // 0 seeds: the seed array is empty (not translated); the program_id and
    // output are OOB, so both engines trap on a PDA-region access.
    unsafe { sol_create_program_address(core::ptr::null(), 0, bad_pid, bad_out) };
    0
}
