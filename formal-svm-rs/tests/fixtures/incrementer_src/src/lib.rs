//! Incrementer: reads a u64 from accounts[0].data[0..8], adds 1,
//! writes back, returns Ok. First fixture that actually mutates
//! account data — exercises the deserialize_account_writes path
//! in formal-svm's marshaling layer.

use solana_program::{
    account_info::AccountInfo, entrypoint, entrypoint::ProgramResult, pubkey::Pubkey,
};

entrypoint!(process_instruction);

pub fn process_instruction(
    _program_id: &Pubkey,
    accounts: &[AccountInfo],
    _instruction_data: &[u8],
) -> ProgramResult {
    let acct = &accounts[0];
    let mut data = acct.try_borrow_mut_data()?;
    let val = u64::from_le_bytes(data[0..8].try_into().unwrap());
    data[0..8].copy_from_slice(&val.wrapping_add(1).to_le_bytes());
    Ok(())
}
