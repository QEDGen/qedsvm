//! Source-backed V3 pipeline fixture: one aligned, non-duplicate 41-byte vault.
//! data = {owner: pubkey @0, total: u64 @32, bump: u8 @40}.
//! ix = {discriminator: u64 @0 (=1), amount: u64 @8}.
//! These fixed input layout assumptions are explicit; this fixture omits general parsing and authorization.
#![no_std]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[no_mangle]
pub unsafe extern "C" fn entrypoint(input: *mut u8) -> u64 {
    let discriminator = core::ptr::read_unaligned(input.add(10400) as *const u64);
    if discriminator != 1 {
        return 2;
    }
    let amount = core::ptr::read_unaligned(input.add(10408) as *const u64);
    if amount == 0 {
        return 1;
    }
    let total_ptr = input.add(128) as *mut u64;
    let total = core::ptr::read_unaligned(total_ptr);
    let Some(new_total) = total.checked_add(amount) else {
        return 3;
    };
    core::ptr::write_unaligned(total_ptr, new_total);
    0
}
