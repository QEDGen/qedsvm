//! Happy-path SYSCALL memory copy. Calls `sol_memcpy_` with in-bounds
//! source and destination slices inside the BPF program heap.
//!
//! Counterpart to `oob_memset_src/` (which forces an access fault): here
//! both slices sit at fixed heap addresses in `[0x300000000, +0x8000)`,
//! which the runtime maps read+write, so the syscall succeeds (r0 = 0)
//! and the lift gets all-constant args.
//!
//! qedlift target: the `sol_memcpy_` happy path, shaped to
//! `call_sol_memcpy_spec` (src `[r2, r2+r3)` readable, dst `[r1, r1+r3)`
//! writable, 16 bytes copied, disjoint regions).

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

extern "C" {
    // The registered SPL/Solana memcpy syscall: r1 = dst, r2 = src, r3 = n.
    fn sol_memcpy_(dst: *mut u8, src: *const u8, n: u64);
}

#[no_mangle]
pub extern "C" fn entrypoint(_input: *mut u8) -> u64 {
    // Both slices live in the heap region [0x300000000, 0x300000000 + 0x8000).
    // dst = heap base, src = heap + 256: disjoint 16-byte ranges, both mapped.
    let dst: *mut u8 = 0x300000000usize as *mut u8;
    let src: *const u8 = (0x300000000usize + 0x100) as *const u8;
    unsafe { sol_memcpy_(dst, src, 16) };
    0
}
