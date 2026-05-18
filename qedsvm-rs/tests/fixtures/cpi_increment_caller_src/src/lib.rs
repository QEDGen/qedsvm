//! CPI caller that forwards its one writable account to a target
//! program embedded in instruction_data[0..32]. Companion fixture to
//! `incrementer.so`: a test registers this program as the caller and
//! `incrementer.so` as the target, observes the data byte get
//! incremented through the CPI write-back path.

use solana_program::{
    account_info::AccountInfo, entrypoint, entrypoint::ProgramResult,
    instruction::{AccountMeta, Instruction}, program::invoke, pubkey::Pubkey,
};

entrypoint!(process_instruction);

pub fn process_instruction(
    _program_id: &Pubkey,
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> ProgramResult {
    let target_pubkey = Pubkey::try_from(&instruction_data[0..32])
        .map_err(|_| solana_program::program_error::ProgramError::InvalidArgument)?;
    let acct = &accounts[0];
    let ix = Instruction {
        program_id: target_pubkey,
        accounts: vec![AccountMeta {
            pubkey: *acct.key,
            is_signer: acct.is_signer,
            is_writable: acct.is_writable,
        }],
        data: vec![],
    };
    invoke(&ix, accounts)?;
    Ok(())
}
