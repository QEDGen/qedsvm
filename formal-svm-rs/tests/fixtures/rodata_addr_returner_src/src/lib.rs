//! Surfaces the `R_BPF_64_Relative`-in-`.text` divergence. The
//! program loads the address of a function-local `static` (which
//! lives in `.rodata`) via an `lddw`, forces the load to not be
//! constant-folded, and returns the upper 32 bits of the address as
//! the entrypoint exit code.
//!
//! Cross-engine observable:
//! - agave's loader patches the `lddw` imm by `+= MM_REGION_SIZE`
//!   so the address sits in the program region; upper 32 bits =
//!   `0x1` → entrypoint returns `1` → `Failure(Custom(1))`.
//! - Pre-fix formal-svm leaves the imm as the raw section VA
//!   (typically `< 0x1_0000_0000`); upper 32 bits = `0` → entrypoint
//!   returns `0` → `Success`. Asymmetric outcome — divergence is
//!   immediate.
//!
//! Post-fix both engines return exit code 1 → both `Failure`.

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[no_mangle]
pub extern "C" fn entrypoint(_input: *mut u8) -> u64 {
    // Function-local `static` is not exported into `.dynsym` (which
    // agave's loader rejects for global data), but it still lives
    // in `.rodata` and its address is materialized via an `lddw`
    // with an `R_BPF_64_Relative` reloc.
    static RODATA_CONST: u64 = 0xDEAD_BEEF_CAFE_BABE;

    let p: *const u64 = &RODATA_CONST;
    // `read_volatile` forces the compiler to actually emit the
    // load via the address (rather than constant-folding away).
    let _ = unsafe { core::ptr::read_volatile(p) };
    // Return the upper 32 bits of the loaded address.
    (p as u64) >> 32
}
