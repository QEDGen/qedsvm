//! Minimal `sol_try_find_program_address` invoker. Calls the syscall
//! once with one seed (`b"vault"`) and a hard-coded program_id,
//! writes the resulting `(PDA, bump)` as 33-byte instruction return
//! data via `sol_set_return_data`.
//!
//! Cross-engine purpose: exercise the per-iteration CU charge for
//! `sol_try_find_program_address`. Agave charges 1500 per bump
//! attempt (initial + each failed iter); a fixture whose chosen
//! bump != 255 forces a CU divergence unless ours scales per-iter.
//!
//! Hand-rolls the syscall (no solana-program dependency) so the
//! emitted binary stays tiny and the ELF doesn't include
//! `#[no_mangle]` static data symbols that agave's loader would
//! reject as `WrongAbi`.

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[repr(C)]
struct VmSlice {
    ptr: u64,
    len: u64,
}

extern "C" {
    fn sol_try_find_program_address(
        seeds_ptr: *const VmSlice,
        seeds_len: u64,
        program_id_ptr: *const u8,
        address_out_ptr: *mut u8,
        bump_out_ptr: *mut u8,
    ) -> u64;
    fn sol_set_return_data(data: *const u8, length: u64);
}

// Hard-coded program ID — matches the test's `pid(50)` (first 8
// bytes = 50 LE, rest zeros).
static PROGRAM_ID: [u8; 32] = [
    50, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
];
static SEED: [u8; 5] = *b"vault";

#[no_mangle]
pub extern "C" fn entrypoint(_input: *mut u8) -> u64 {
    let seeds = [VmSlice {
        ptr: SEED.as_ptr() as u64,
        len: SEED.len() as u64,
    }];
    let mut pda: [u8; 32] = [0; 32];
    let mut bump: u8 = 0;
    let rc = unsafe {
        sol_try_find_program_address(
            seeds.as_ptr(),
            1,
            PROGRAM_ID.as_ptr(),
            pda.as_mut_ptr(),
            &mut bump,
        )
    };
    if rc != 0 {
        return rc;
    }
    let mut result: [u8; 33] = [0; 33];
    result[..32].copy_from_slice(&pda);
    result[32] = bump;
    unsafe { sol_set_return_data(result.as_ptr(), result.len() as u64) };
    0
}
