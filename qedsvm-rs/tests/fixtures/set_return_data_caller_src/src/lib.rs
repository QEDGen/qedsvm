//! Happy-path SYSCALL return-data set. Calls `sol_set_return_data` with an
//! in-bounds input slice inside the BPF program heap.
//!
//! Counterpart to `oob_set_return_data_src/` (which forces an access fault):
//! here the input slice sits at a fixed heap address in
//! `[0x300000000, +0x8000)`, which the runtime maps read+write, so the syscall
//! succeeds (r0 = 0) and the lift gets all-constant args.
//!
//! qedlift target: the `sol_set_return_data` happy path, shaped to
//! `call_sol_set_return_data_spec` (input `[r1, r1+r2)` readable, 16 bytes
//! copied into `State.returnData`, length 16 <= MAX_RETURN_DATA).

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

extern "C" {
    // The registered return-data syscall: r1 = *const u8 input, r2 = len.
    fn sol_set_return_data(data: *const u8, len: u64) -> u64;
}

#[no_mangle]
pub extern "C" fn entrypoint(_input: *mut u8) -> u64 {
    // Input slice lives in the heap region [0x300000000, 0x300000000 + 0x8000),
    // which the runtime maps. 16 bytes (<= MAX_RETURN_DATA = 1024).
    let data: *const u8 = 0x300000000usize as *const u8;
    unsafe { sol_set_return_data(data, 16) };
    0
}
