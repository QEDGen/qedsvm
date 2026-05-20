//! Callee for the PDA signer-seed prober. Writes a marker byte to
//! accounts[0].data[0] based on accounts[1].is_signer:
//!   0xAA -> signer (agave promoted via seeds)
//!   0x55 -> not signer (engine ignored seeds)
//!
//! Test asserts byte equality vs mollusk after the run; divergence
//! pinpoints the PDA-signer-seeds gap in r4/r5 handling.

use solana_program::{
    account_info::AccountInfo, entrypoint, entrypoint::ProgramResult,
    pubkey::Pubkey,
};

entrypoint!(process_instruction);

pub fn process_instruction(
    _program_id: &Pubkey,
    accounts: &[AccountInfo],
    _instruction_data: &[u8],
) -> ProgramResult {
    let marker: u8 = if accounts[1].is_signer { 0xAA } else { 0x55 };
    let mut data = accounts[0].data.borrow_mut();
    data[0] = marker;
    Ok(())
}
