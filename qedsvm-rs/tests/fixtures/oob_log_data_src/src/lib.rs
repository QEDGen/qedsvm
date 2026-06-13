//! Out-of-bounds `sol_log_data`. Forces the syscall to translate its
//! descriptor array (`&[VmSlice<u8>]`) from well outside any mapped region.
//!
//! Cross-engine observable (audit H6 — syscall memory translation, the
//! descriptor-array / logging-family tail):
//! - agave: `SyscallLogData` calls
//!   `translate_slice::<VmSlice<u8>>(addr, len)` on the descriptor array
//!   FIRST (before any per-slice deref); its `MemoryMapping::map` traps the
//!   out-of-region read with `AccessViolation`, and `program-runtime`
//!   reports `InstructionError::ProgramFailedToComplete`.
//! - Pre-fix qedsvm: `Logging.execLogData` read the descriptors and every
//!   slice through a region-free `Mem`, so the OOB read silently succeeded,
//!   r0 = 0, Success.
//! - Post-fix qedsvm: `execLogData` routes the descriptor array through
//!   `guardRead` and each slice through `guardSlices`, which consult the
//!   runtime region table and trap to `ERR_ACCESS_VIOLATION`
//!   (`vmError := some .accessViolation`).

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

extern "C" {
    // The registered data-log syscall: r1 = *const VmSlice<u8> (the
    // descriptor array), r2 = number of descriptors.
    fn sol_log_data(data: *const u8, data_len: u64);
}

#[no_mangle]
pub extern "C" fn entrypoint(input: *mut u8) -> u64 {
    // 256 MiB past the input pointer — well outside any mapped region.
    let bad: *const u8 = unsafe { input.add(0x10000000) };
    // One descriptor: agave translates the 16-byte descriptor array at
    // `bad` before dereferencing any slice, so the array read itself is
    // the out-of-region access that traps.
    unsafe { sol_log_data(bad, 1) };
    0
}
