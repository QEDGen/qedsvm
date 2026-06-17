//! Happy-path single-seed `sol_create_program_address`. Writes a one-entry
//! `SliceDesc` { ptr, len } to the heap pointing at an 8-byte seed slice, then
//! derives a PDA from `seed ‖ program_id ‖ "ProgramDerivedAddress"` into a
//! 32-byte heap output buffer.
//!
//! All regions live in the program heap `[0x300000000, +0x8000)`, mapped
//! read+write, and are pairwise disjoint:
//! - descriptor at `base+0`      (16 bytes: ptr = base+0x100, len = 8),
//! - seed slice at `base+0x100`  (8 bytes, read by the syscall),
//! - program_id at `base+0x200`  (32 bytes, read by the syscall),
//! - output at `base+0x300`      (32 bytes, written on the off-curve success).
//!
//! Counterpart to `oob_create_pda_src/`; the trace source for
//! `Pda CreateLifted`, shaped to `call_sol_create_program_address_spec`.

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

extern "C" {
    // r1 = *const [SliceDesc; N] seeds, r2 = N, r3 = *const [u8; 32] program_id,
    // r4 = *mut [u8; 32] result.
    fn sol_create_program_address(
        seeds: *const u8,
        seeds_len: u64,
        program_id: *const u8,
        result: *mut u8,
    ) -> u64;
}

#[no_mangle]
pub extern "C" fn entrypoint(_input: *mut u8) -> u64 {
    let base: usize = 0x300000000;
    let desc = base as *mut u64; // SliceDesc { ptr, len }
    let pid = (base + 0x200) as *const u8; // 32-byte program_id
    let out = (base + 0x300) as *mut u8; // 32-byte PDA output
    unsafe {
        core::ptr::write_volatile(desc, (base + 0x100) as u64); // seed ptr
        core::ptr::write_volatile(desc.add(1), 8u64); // seed len = 8
        sol_create_program_address(desc as *const u8, 1, pid, out);
    }
    0
}
