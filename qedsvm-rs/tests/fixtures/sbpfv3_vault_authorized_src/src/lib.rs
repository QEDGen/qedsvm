//! Two-account vault deposit with a checked aligned Solana input schema.
//! The runtime supplies the serialized buffer. Validate each record before
//! accessing its data or the next record; reject duplicates and other shapes.
//! Vault data is {owner: Pubkey, total: u64, bump: u8}; the empty authority
//! account must sign and match owner. Vault's program owner must match the
//! executing program ID. This increments a counter, without transferring funds.
#![no_std]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[inline(always)]
unsafe fn word(input: *const u8, offset: usize) -> u64 {
    core::ptr::read_unaligned(input.add(offset).cast::<u64>())
}

#[no_mangle]
pub unsafe extern "C" fn entrypoint(input: *mut u8) -> u64 {
    // Runtime serialization guarantees headers exist for the declared count.
    if word(input, 0) != 2 || *input.add(8) != 255 || word(input, 88) != 41 {
        return 6;
    }
    // For a 41-byte first record, the next record starts at 10392 after
    // data, alignment, growth space and rent_epoch. Only its non-duplicate,
    // zero-data schema gives the trailer position below.
    if *input.add(10392) != 255 || word(input, 10472) != 0 {
        return 6;
    }
    if word(input, 20728) != 16 {
        return 7;
    }
    if *input.add(10) != 1 || *input.add(11) != 0 {
        return 8;
    }
    if *input.add(10393) != 1 {
        return 5;
    }
    // The program ID follows the validated 16-byte instruction data.
    if word(input, 48) != word(input, 20752)
        || word(input, 56) != word(input, 20760)
        || word(input, 64) != word(input, 20768)
        || word(input, 72) != word(input, 20776)
    {
        return 4;
    }
    if word(input, 96) != word(input, 10400)
        || word(input, 104) != word(input, 10408)
        || word(input, 112) != word(input, 10416)
        || word(input, 120) != word(input, 10424)
    {
        return 4;
    }
    if word(input, 20736) != 1 {
        return 2;
    }
    let amount = word(input, 20744);
    if amount == 0 {
        return 1;
    }
    let total = word(input, 128);
    let Some(new_total) = total.checked_add(amount) else {
        return 3;
    };
    core::ptr::write_unaligned(input.add(128).cast::<u64>(), new_total);
    0
}
