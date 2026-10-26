//! A type-layout fixture, not a Solana account deserializer.
#![no_std]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }

#[repr(C)]
pub struct Account {
    pub authority: [u8; 32],
    pub amount: u64,
    pub state: u8,
}

#[repr(u32)]
pub enum Error { Unauthorized = 7, Frozen = 42 }

#[repr(i16)]
pub enum SignedError { Negative = -3, Positive = 5 }

#[inline(always)]
fn authorize(account: &Account) -> Result<(), Error> {
    if account.state == 0 { Ok(()) } else { Err(Error::Frozen) }
}

#[inline(always)]
fn transfer(account: &mut Account, amount: u64) -> Result<(), Error> {
    authorize(account)?;
    account.amount = account.amount.wrapping_add(amount);
    Ok(())
}

#[inline(never)]
#[no_mangle]
pub fn signed_error(error: SignedError) -> i16 { error as i16 }

#[no_mangle]
pub unsafe extern "C" fn entrypoint(input: *mut u8) -> u64 {
    let account = &mut *(input as *mut Account);
    let amount = core::ptr::read_volatile(input.add(48) as *const u64);
    let result = transfer(account, amount);
    let code = match result { Ok(()) => 0, Err(error) => error as u64 };
    let signed = if account.authority[0] == 0 { SignedError::Negative } else { SignedError::Positive };
    code.wrapping_add(signed_error(signed) as u64).wrapping_add(0x123456789abcdef0)
}
