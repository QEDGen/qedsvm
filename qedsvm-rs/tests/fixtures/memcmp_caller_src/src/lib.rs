//! Happy-path SYSCALL `sol_memcmp_`: compares two disjoint 16-byte heap
//! slices and writes the 4-byte (u32-encoded i32) result to a third,
//! disjoint heap slot. Shaped to `call_sol_memcmp_spec` — two `↦Bytes`
//! inputs (`[r1,r1+r3)`, `[r2,r2+r3)` readable), a 4-byte `↦U32` output
//! at `r4` (writable), all three regions disjoint.

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

extern "C" {
    // r1 = s1, r2 = s2, r3 = n, r4 = result (4-byte i32 out).
    fn sol_memcmp_(s1: *const u8, s2: *const u8, n: u64, result: *mut i32);
}

#[no_mangle]
pub extern "C" fn entrypoint(_input: *mut u8) -> u64 {
    let p1: *const u8 = (0x300000000usize + 0x100) as *const u8;
    let p2: *const u8 = (0x300000000usize + 0x200) as *const u8;
    let out: *mut i32 = 0x300000000usize as *mut i32;
    unsafe { sol_memcmp_(p1, p2, 16, out) };
    0
}
