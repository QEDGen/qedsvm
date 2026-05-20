//! Outer layer of a depth-2 CPI chain:
//!   outer (this) -> middle (cpi_increment_caller.so) -> leaf (incrementer.so)
//!
//! ix.data[0..32]  = middle program id
//! ix.data[32..64] = leaf program id
//! accounts[0]     = data account (forwarded all the way down; leaf
//!                   bumps the first u64 by 1)
//!
//! Probes whether the recursion in executeFnCpiWithFuel works at depth 2.

use solana_program::{
    account_info::AccountInfo, entrypoint, entrypoint::ProgramResult,
    instruction::{AccountMeta, Instruction}, program::invoke,
    pubkey::Pubkey,
};

entrypoint!(process_instruction);

pub fn process_instruction(
    _program_id: &Pubkey,
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> ProgramResult {
    let middle = Pubkey::try_from(&instruction_data[0..32])
        .map_err(|_| solana_program::program_error::ProgramError::InvalidArgument)?;
    let leaf = Pubkey::try_from(&instruction_data[32..64])
        .map_err(|_| solana_program::program_error::ProgramError::InvalidArgument)?;
    let acct = &accounts[0];
    // middle (cpi_increment_caller) needs `leaf` in its AccountInfo
    // array so its own invoke(&ix_to_leaf, accounts) can resolve leaf.
    // Forward leaf as a read-only entry alongside the data account.
    let ix = Instruction {
        program_id: middle,
        accounts: vec![
            AccountMeta {
                pubkey: *acct.key,
                is_signer: acct.is_signer,
                is_writable: acct.is_writable,
            },
            AccountMeta::new_readonly(leaf, false),
        ],
        data: leaf.to_bytes().to_vec(),
    };
    invoke(&ix, accounts)?;
    Ok(())
}
