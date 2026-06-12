//! Minimal `sol_curve_multiscalar_mul` invoker — the M9 CU referee.
//!
//! Calls the MSM syscall twice on the Edwards curve:
//!   1. n = 1 (the off-by-one boundary: agave charges the bare
//!      `msm_base_cost` = 2273, because the incremental cost is
//!      `incr * (n - 1)` — solana-sbpf agave-syscalls lib.rs:1711-1716)
//!   2. n = 2 (base + one increment = 2273 + 758)
//!
//! The diff test asserts CU equality cross-engine: under the pre-M9
//! model formula (`base + incr * n`) the model would over-charge by
//! 758 per call (1516 total), so this fixture genuinely discriminates
//! the `(n - 1)` form. Returns `r0_1 + r0_2` (0 iff both calls
//! succeeded), so Success/Failure also matches.

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

extern "C" {
    fn sol_curve_multiscalar_mul(
        curve_id: u64,
        scalars_ptr: *const u8,
        points_ptr: *const u8,
        points_len: u64,
        result_ptr: *mut u8,
    ) -> u64;
}

// Two canonical scalars (LE): 1 and 2.
static SCALARS: [u8; 64] = {
    let mut s = [0u8; 64];
    s[0] = 1;
    s[32] = 2;
    s
};

// Two valid compressed Edwards points: the ed25519 basepoint, twice.
static POINTS: [u8; 64] = {
    let bp: [u8; 32] = [
        0x58, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
        0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
        0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
        0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
    ];
    let mut p = [0u8; 64];
    let mut i = 0;
    while i < 32 {
        p[i] = bp[i];
        p[32 + i] = bp[i];
        i += 1;
    }
    p
};

#[no_mangle]
pub extern "C" fn entrypoint(_input: *mut u8) -> u64 {
    let mut out = [0u8; 32];
    let r1 = unsafe {
        sol_curve_multiscalar_mul(
            0, SCALARS.as_ptr(), POINTS.as_ptr(), 1, out.as_mut_ptr())
    };
    let r2 = unsafe {
        sol_curve_multiscalar_mul(
            0, SCALARS.as_ptr(), POINTS.as_ptr(), 2, out.as_mut_ptr())
    };
    r1 + r2
}
