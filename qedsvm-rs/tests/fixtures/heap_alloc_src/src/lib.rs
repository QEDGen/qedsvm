//! Minimal NON-token program that exercises the embedded bump allocator
//! pattern over the BPF program heap. Unlike `sol_alloc_free_` (the
//! deprecated syscall allocator), modern Solana programs keep their heap
//! position in heap memory at `MM_HEAP_START` (0x300000000) and allocate
//! via plain load/store/ALU — so an allocation is ordinary memory the
//! lifter already handles. This program reads the bump-position slot,
//! commits a new position, writes into the allocated block, and reads it
//! back, all at fixed heap addresses. It touches no accounts, so it
//! diff-tests purely on byte+CU+result parity.
//!
//! Compiles to a straight-line load/store sequence over the heap region.

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[no_mangle]
pub extern "C" fn entrypoint(_input: *mut u8) -> u64 {
    unsafe {
        // The default allocator's bump-position slot lives at the start
        // of the heap; the heap is [0x300000000, 0x300000000 + 0x8000).
        let slot = 0x300000000usize as *mut u64;
        // First 16-byte allocation, taken from the heap end (downward).
        let block = (0x300000000usize + 0x8000 - 16) as *mut u64;
        let old = core::ptr::read_volatile(slot); // read current bump position
        core::ptr::write_volatile(slot, block as u64); // commit new position
        // Write a register-derived value into the allocated block. (A
        // plain immediate store `[block] = 42` would emit ST_DW_IMM, which
        // sl_block_auto's SpecGen does not yet wire — orthogonal to heap.)
        core::ptr::write_volatile(block, old.wrapping_add(42)); // write into the block
        let _v = core::ptr::read_volatile(block); // read it back
    }
    0
}
