//! sBPF V3 account-writing CPI caller (C ABI, `cargo-build-sbf --arch v3`).
//!
//! Accounts: [0] a writable account with 2 data bytes, [1] the callee program.
//! The caller hands account 0 to the callee through `sol_invoke_signed_c`
//! with direct `SolAccountInfo` pointers into the serialized input, so the
//! callee may write its data. After the invoke the caller branches on the
//! result: failure returns `r + 1000`; success reads the byte the callee wrote
//! (`data[0]`) and stores `data[0] + 1` at heap+200. (The account is owned by
//! the callee, so the caller itself may not write its data.)
//!
//! Serialized input: account 0 slot at +8 (key +16, owner +48, lamports +80,
//! data_len +88, data +96, rent epoch +10344); account 1 slot at +10352
//! (key +10360). Heap at 0x300000000: SolInstruction +0 (40 B), one
//! SolAccountMeta +48 (16 B), one SolAccountInfo +64 (56 B).

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

use solana_define_syscall::definitions::sol_invoke_signed_c;

const HEAP: u64 = 0x300000000;

#[no_mangle]
pub extern "C" fn entrypoint(input: *mut u8) -> u64 {
    unsafe {
        let base = input as u64;
        let h = HEAP as *mut u64;
        // SolInstruction { program_id*, accounts*, account_len, data*, data_len }
        core::ptr::write_volatile(h.add(0), base + 10360);
        core::ptr::write_volatile(h.add(1), HEAP + 48);
        core::ptr::write_volatile(h.add(2), 1);
        core::ptr::write_volatile(h.add(3), HEAP + 120);
        core::ptr::write_volatile(h.add(4), 0);
        // SolAccountMeta { pubkey*, is_writable, is_signer }
        core::ptr::write_volatile(h.add(6), base + 16);
        core::ptr::write_volatile(h.add(7), 1);
        // SolAccountInfo { key*, lamports*, data_len, data*, owner*, rent_epoch,
        //                  is_signer, is_writable, executable }
        core::ptr::write_volatile(h.add(8), base + 16);
        core::ptr::write_volatile(h.add(9), base + 80);
        core::ptr::write_volatile(h.add(10), 2);
        core::ptr::write_volatile(h.add(11), base + 96);
        core::ptr::write_volatile(h.add(12), base + 48);
        core::ptr::write_volatile(h.add(13), core::ptr::read_volatile((base + 10344) as *const u64));
        core::ptr::write_volatile(h.add(14), 0x100);
        let r = sol_invoke_signed_c(HEAP as *const u8, (HEAP + 64) as *const u8, 1, input, 0);
        if r != 0 {
            return r.wrapping_add(1000);
        }
        let written = core::ptr::read_volatile(input.add(96));
        core::ptr::write_volatile((HEAP as *mut u8).add(200), written.wrapping_add(1));
    }
    0
}
