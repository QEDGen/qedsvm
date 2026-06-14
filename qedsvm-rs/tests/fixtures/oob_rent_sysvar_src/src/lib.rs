//! Out-of-bounds `sol_get_rent_sysvar` OUTPUT write (the de-simp'd, hand-coded
//! 17-byte Rent struct write). agave's `translate_type_mut::<Rent>` traps the
//! out-of-region store with AccessViolation; post-fix (stage 4c)
//! `Sysvar.execRent`'s `guardWrite` on `[r1, r1+17)` VM-faults.
#![no_std]
#![allow(unexpected_cfgs)]
#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! { loop {} }
extern "C" {
    fn sol_get_rent_sysvar(addr: *mut u8) -> u64;
}
#[no_mangle]
pub extern "C" fn entrypoint(input: *mut u8) -> u64 {
    let bad: *mut u8 = unsafe { input.add(0x10000000) };
    unsafe { sol_get_rent_sysvar(bad) };
    0
}
