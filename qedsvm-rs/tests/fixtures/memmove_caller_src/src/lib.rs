//! Happy-path SYSCALL `sol_memmove_` over two disjoint, in-bounds heap
//! slices. Identical shape to `memcpy_caller_src/` but exercises the
//! `is_move` arm of the emitter (`call_sol_memmove_spec`). The SL spec
//! forces src/dst disjoint via two `↦Bytes` atoms, so memmove's
//! overlap support is off-spec; the regions here are disjoint anyway.

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

extern "C" {
    // The registered SPL/Solana memmove syscall: r1 = dst, r2 = src, r3 = n.
    fn sol_memmove_(dst: *mut u8, src: *const u8, n: u64);
}

#[no_mangle]
pub extern "C" fn entrypoint(_input: *mut u8) -> u64 {
    let dst: *mut u8 = 0x300000000usize as *mut u8;
    let src: *const u8 = (0x300000000usize + 0x100) as *const u8;
    unsafe { sol_memmove_(dst, src, 16) };
    0
}
