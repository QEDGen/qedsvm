//! Out-of-bounds `sol_get_return_data` OUTPUT write. First seeds 8 bytes of
//! return data (from the always-mapped input region, so the copy length is
//! non-zero), then asks the syscall to copy them to a return-data output
//! buffer 256 MiB out of region.
//!
//! Cross-engine observable (audit H6 — syscall memory translation, the
//! return-data family, stage 4d / output write guard):
//! - agave: `SyscallGetReturnData` computes `length = min(max_len, data_len)`;
//!   when `length != 0` it `translate_slice_mut::<u8>(out, length)` before the
//!   copy — its `MemoryMapping::map` traps the out-of-region write with
//!   `AccessViolation` -> `ProgramFailedToComplete`.
//! - Pre-fix qedsvm: `ReturnData.execGet` wrote `[r1, r1+copyLen)` and the
//!   32-byte program id `[r3, r3+32)` through a region-free `Mem`, so the OOB
//!   write silently succeeded, r0 = data_len.
//! - Post-fix qedsvm: `execGet` routes BOTH output writes through `guardWrite`,
//!   which consults the runtime region table and traps to
//!   `ERR_ACCESS_VIOLATION` (`execGet_faults_oob`).

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

extern "C" {
    // r1 = *const u8 (return-data bytes), r2 = len.
    fn sol_set_return_data(data: *const u8, len: u64) -> u64;
    // r1 = *mut u8 (output), r2 = max_len, r3 = *mut u8 (program-id output).
    fn sol_get_return_data(out: *mut u8, max_len: u64, program_id: *mut u8) -> u64;
}

#[no_mangle]
pub extern "C" fn entrypoint(input: *mut u8) -> u64 {
    // Seed 8 bytes of return data from the always-mapped input region so the
    // copy length `min(max_len, data_len)` is non-zero (else agave/qedsvm take
    // the no-op `length == 0` branch and never translate the output).
    unsafe { sol_set_return_data(input as *const u8, 8) };
    // 256 MiB past the input pointer — well outside any mapped region.
    let bad_out: *mut u8 = unsafe { input.add(0x10000000) };
    let bad_pid: *mut u8 = unsafe { input.add(0x10000000 + 64) };
    // max_len = 8: copyLen = min(8, 8) = 8 > 0, so the out-of-region output
    // translate is the trapping access.
    unsafe { sol_get_return_data(bad_out, 8, bad_pid) };
    0
}
