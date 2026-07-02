//! Per-call-site CPI envelope fixture (#40 gap 4): hand-builds the Rust-ABI
//! `StableInstruction` on the program heap and invokes it — the memory the
//! lift owns at the call site IS the envelope event (`cpiEnvelope`).
//!
//! Serialized input (1 account — the callee program account, empty data, as
//! agave requires the invoked program in the transaction): count u64 @0, the
//! account slot @8 (88 header + 10240 realloc pad + 8 rent = 10336 bytes),
//! ix-data len u64 @10344, and the 32-byte TARGET pubkey as instruction data
//! @10352..10384 — offsets = `SVM.Solana.InputLayout.instrDataOff [0]`.
//!
//! Heap layout at 0x300000000:
//!   +0..48   StableInstruction: metas (ptr=heap+96, cap=0, len=0),
//!            data (ptr=heap+88, cap=8, len=8)
//!   +48..80  program id (copied from instruction data)
//!   +88..96  8 bytes of CPI instruction data (constant 0x0807060504030201)
//!   +96      (unused) metas pointer target, len 0
//!
//! The runner executes the real CPI (register the target as noop.so); the
//! PROOF-facing walk terminates at the invoke (fail-closed `Cpi.exec`), so
//! the lifted prefix's post owns exactly the envelope cells.

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

extern "C" {
    fn sol_invoke_signed_rust(
        instruction: *const u8,
        account_infos: *const u8,
        account_infos_len: u64,
        signers_seeds: *const u8,
        signers_seeds_len: u64,
    ) -> u64;
}

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
