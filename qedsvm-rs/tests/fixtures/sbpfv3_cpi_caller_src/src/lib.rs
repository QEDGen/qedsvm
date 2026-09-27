//! sBPF V3 CPI caller fixture (source port of `cpi_envelope_caller_src`,
//! built with `cargo-build-sbf --arch v3`). Hand-builds the Rust-ABI
//! `StableInstruction` on the heap and invokes the program whose id is the
//! 32-byte instruction data, then returns the callee's result code. Used for
//! the V3 CPI bridge proof (`Generated.Sbpfv3CpiCallerLifted`) and the
//! success/rollback Mollusk differential.
//!
//! Serialized input and heap layout are identical to the V0 envelope caller:
//! instruction data (the target id) at input+10352 behind one empty-data
//! account; StableInstruction at 0x300000000, program id at +48, 8 bytes of
//! CPI data at +88.

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

use solana_define_syscall::definitions::sol_invoke_signed_rust;

const HEAP: u64 = 0x300000000;

#[no_mangle]
pub extern "C" fn entrypoint(input: *mut u8) -> u64 {
    unsafe {
        let h = HEAP as *mut u64;
        // StableInstruction: accounts StableVec (ptr, cap, len)
        core::ptr::write_volatile(h.add(0), HEAP + 96);
        core::ptr::write_volatile(h.add(1), 0);
        core::ptr::write_volatile(h.add(2), 0);
        // data StableVec (ptr, cap, len)
        core::ptr::write_volatile(h.add(3), HEAP + 88);
        core::ptr::write_volatile(h.add(4), 8);
        core::ptr::write_volatile(h.add(5), 8);
        // program id: 4 dwords from instruction data (input + 10352 —
        // `instrDataOff [0]`, one empty-data account precedes it)
        let pid = input.add(10352) as *const u64;
        core::ptr::write_volatile(h.add(6), core::ptr::read_unaligned(pid.add(0)));
        core::ptr::write_volatile(h.add(7), core::ptr::read_unaligned(pid.add(1)));
        core::ptr::write_volatile(h.add(8), core::ptr::read_unaligned(pid.add(2)));
        core::ptr::write_volatile(h.add(9), core::ptr::read_unaligned(pid.add(3)));
        // CPI instruction data: 8 constant bytes
        core::ptr::write_volatile(h.add(11), 0x0807060504030201u64);
        // Empty infos/signers lists: agave's stricter-ABI checks reject an
        // account-infos pointer inside the input region (≥ MM_INPUT_START),
        // so the infos point at the heap; the SIGNERS pointer has no such
        // constraint, so `input` goes there (never dereferenced at len 0) —
        // keeping r1 live until the call so LLVM cannot fold a pid load into
        // `ldx r1, [r1+K]` (a dst == src aliasing shape the block tactic's
        // frame extraction does not support).
        let r = sol_invoke_signed_rust(
            HEAP as *const u8,
            (HEAP + 96) as *const u8,
            0,
            input,
            0,
        );
        if r != 0 {
            return r;
        }
    }
    0
}
