//! One parametric probe for the sysvar getters (#105). Instruction data (no
//! accounts) is `[op, 0 x7, a: u64, b: u64, c: u64, d: u64]`, all addresses
//! absolute. Ops 0 to 5 are the typed getters with output `a`: clock, rent,
//! epoch_schedule, epoch_rewards, last_restart_slot, fees. Op 6 is
//! `sol_get_sysvar(a, b, c, d)`, op 7 is `sol_get_epoch_stake(a)`, and op 255
//! makes no call, so its CU measures everything before the syscall.
//!
//! The heap window `[HEAP, HEAP + WINDOW)` is filled with `i * 7 + 3 (mod 251)`
//! through volatile stores, then the ids below are written at its end. After a
//! successful call the return data is the window's sha256 followed by the
//! syscall's r0, which exposes every byte written and any in-band result.

#![no_std]
#![allow(unexpected_cfgs, deprecated)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

use solana_define_syscall::definitions::{
    sol_get_clock_sysvar, sol_get_epoch_rewards_sysvar, sol_get_epoch_schedule_sysvar,
    sol_get_epoch_stake, sol_get_fees_sysvar, sol_get_last_restart_slot, sol_get_rent_sysvar,
    sol_get_sysvar, sol_set_return_data, sol_sha256,
};

const HEAP: u64 = 0x3_0000_0000;
const WINDOW: u64 = 0x2100;

const CLOCK_ID: [u8; 32] = [
    0x06, 0xa7, 0xd5, 0x17, 0x18, 0xc7, 0x74, 0xc9, 0x28, 0x56, 0x63, 0x98, 0x69, 0x1d, 0x5e, 0xb6,
    0x8b, 0x5e, 0xb8, 0xa3, 0x9b, 0x4b, 0x6d, 0x5c, 0x73, 0x55, 0x5b, 0x21, 0x00, 0x00, 0x00, 0x00,
];
const RENT_ID: [u8; 32] = [
    0x06, 0xa7, 0xd5, 0x17, 0x19, 0x2c, 0x5c, 0x51, 0x21, 0x8c, 0xc9, 0x4c, 0x3d, 0x4a, 0xf1, 0x7f,
    0x58, 0xda, 0xee, 0x08, 0x9b, 0xa1, 0xfd, 0x44, 0xe3, 0xdb, 0xd9, 0x8a, 0x00, 0x00, 0x00, 0x00,
];
const EPOCH_SCHEDULE_ID: [u8; 32] = [
    0x06, 0xa7, 0xd5, 0x17, 0x18, 0xdc, 0x3f, 0xee, 0x02, 0xd3, 0xe4, 0x7f, 0x01, 0x00, 0xf8, 0xb0,
    0x54, 0xf7, 0x94, 0x2e, 0x60, 0x59, 0x1e, 0x3f, 0x50, 0x87, 0x19, 0xa8, 0x05, 0x00, 0x00, 0x00,
];
const SLOT_HASHES_ID: [u8; 32] = [
    0x06, 0xa7, 0xd5, 0x17, 0x19, 0x2f, 0x0a, 0xaf, 0xc6, 0xf2, 0x65, 0xe3, 0xfb, 0x77, 0xcc, 0x7a,
    0xda, 0x82, 0xc5, 0x29, 0xd0, 0xbe, 0x3b, 0x13, 0x6e, 0x2d, 0x00, 0x55, 0x20, 0x00, 0x00, 0x00,
];

unsafe fn arg(input: *const u8, i: usize) -> u64 {
    // With zero accounts the data starts after num_accounts and data_len.
    core::ptr::read_unaligned(input.add(16 + 8 + 8 * i) as *const u64)
}

unsafe fn put_id(at: u64, id: &[u8; 32]) {
    let mut i = 0;
    while i < 32 {
        core::ptr::write_volatile((HEAP + at + i as u64) as *mut u8, id[i]);
        i += 1;
    }
}

#[no_mangle]
pub extern "C" fn entrypoint(input: *mut u8) -> u64 {
    unsafe {
        let op = *input.add(16);
        let (a, b, c, d) = (arg(input, 0), arg(input, 1), arg(input, 2), arg(input, 3));
        let heap = HEAP as *mut u8;
        let mut i = 0u64;
        while i < WINDOW {
            core::ptr::write_volatile(heap.add(i as usize), ((i * 7 + 3) % 251) as u8);
            i += 1;
        }
        put_id(0x2000, &CLOCK_ID);
        put_id(0x2020, &RENT_ID);
        put_id(0x2040, &EPOCH_SCHEDULE_ID);
        put_id(0x2060, &SLOT_HASHES_ID);
        put_id(0x2080, &[7; 32]);
        put_id(0x20a0, &[9; 32]);
        let r0 = match op {
            0 => sol_get_clock_sysvar(a as *mut u8),
            1 => sol_get_rent_sysvar(a as *mut u8),
            2 => sol_get_epoch_schedule_sysvar(a as *mut u8),
            3 => sol_get_epoch_rewards_sysvar(a as *mut u8),
            4 => sol_get_last_restart_slot(a as *mut u8),
            5 => sol_get_fees_sysvar(a as *mut u8),
            6 => sol_get_sysvar(a as *const u8, b as *mut u8, c, d),
            7 => sol_get_epoch_stake(a as *const u8),
            _ => return 1,
        };
        // Hash the window into a stack buffer and return it with r0.
        let desc: [u64; 2] = [HEAP, WINDOW];
        let mut out = [0u8; 40];
        sol_sha256(desc.as_ptr() as *const u8, 1, out.as_mut_ptr());
        out[32..40].copy_from_slice(&r0.to_le_bytes());
        sol_set_return_data(out.as_ptr(), 40);
    }
    0
}
