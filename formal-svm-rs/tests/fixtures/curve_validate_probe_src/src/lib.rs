//! Minimal `sol_curve_validate_point` invoker. Calls the syscall once
//! with `curve_id = 0` (Edwards) and a 32-byte buffer (a function-
//! local `static` in `.rodata`), returns r0 as the entrypoint exit
//! code.
//!
//! Used to isolate the Curve25519 FFI SIGSEGV: this fixture exercises
//! the FFI through the compiled-native runtime dispatch with no other
//! moving parts — no Sha256, no PDA loop, no entrypoint deserializer.
//! If this crashes, the bug is purely in
//! `lean_curve_validate_edwards`.

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

extern "C" {
    fn sol_curve_validate_point(
        curve_id: u64,
        point_ptr: *const u8,
    ) -> u64;
}

// 32-byte buffer: the ed25519 basepoint (a known valid Edwards point).
// If validateEdwards works at runtime, the syscall returns 0.
static BASEPOINT: [u8; 32] = [
    0x58, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
    0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
    0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
    0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
];

#[no_mangle]
pub extern "C" fn entrypoint(_input: *mut u8) -> u64 {
    unsafe { sol_curve_validate_point(0, BASEPOINT.as_ptr()) }
}
