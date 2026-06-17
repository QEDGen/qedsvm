//! Happy-path single-slice `sol_sha256`. Writes a one-entry `SliceDesc`
//! { ptr, len } to the heap pointing at a 16-byte in-bounds input slice,
//! then hashes it into a 32-byte heap output buffer.
//!
//! All three regions live in the program heap `[0x300000000, +0x8000)`,
//! which the runtime maps read+write, so the syscall succeeds (r0 = 0):
//! - descriptor at `base+0`   (16 bytes: ptr = base+0x100, len = 16),
//! - input slice at `base+0x100` (16 bytes, read by the syscall),
//! - digest output at `base+0x200` (32 bytes, written by the syscall).
//!
//! Disjoint regions, all mapped. Counterpart to `oob_sha256_src/` (which
//! faults on the output write); the trace source for `Sha256CallerLifted`,
//! shaped to `call_sol_sha256_spec` (n = 1: one descriptor cell pair, one
//! input slice, the 32-byte output).

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
pub extern "C" fn entrypoint(_input: *mut u8) -> u64 {
    let base: usize = 0x300000000;
    let desc = base as *mut u64; // SliceDesc { ptr, len }
    let out = (base + 0x200) as *mut u8; // 32-byte digest output
    unsafe {
        // descriptor[0]: ptr -> base+0x100, len = 16 (concrete, written here)
        core::ptr::write_volatile(desc, (base + 0x100) as u64);
        core::ptr::write_volatile(desc.add(1), 16u64);
        // hash the single 16-byte slice into the heap output buffer.
        sol_sha256(desc as *const u8, 1, out);
    }
    0
}
