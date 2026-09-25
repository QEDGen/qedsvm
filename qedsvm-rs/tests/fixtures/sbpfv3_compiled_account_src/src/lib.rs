//! Source-backed V3 conformance program. The Rust guard controls the account
//! byte update; the inline eight-byte instruction exercises JMP32 directly.
//! LLVM's BPF inline assembler does not yet accept the `jeq32` mnemonic, so
//! the two fixed instructions below are encoded as bytes.

#![no_std]
#![feature(asm_experimental_arch)]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

use solana_define_syscall::definitions::sol_log_64_;

#[inline(never)]
unsafe fn update(input: *mut u8) {
    let byte = input.add(96);
    let old = core::ptr::read_volatile(byte);
    core::ptr::write_volatile(byte, old.wrapping_add(1));
    sol_log_64_(old as u64, 0, 0, 0, 0);
}

#[no_mangle]
pub extern "C" fn entrypoint(input: *mut u8) -> u64 {
    let old = unsafe { core::ptr::read_volatile(input.add(96)) };
    unsafe {
        core::arch::asm!(
            // jeq32 w2, 1, +1: branch over a no-op when the byte is 1.
            ".byte 0x16, 0x02, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00",
            // mov64 r0, r0: safe fall-through target.
            ".byte 0xbf, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00",
            in("r2") old as u64,
            options(nostack),
        );
    }
    if old == 1 {
        unsafe { update(input) };
    }
    0
}
