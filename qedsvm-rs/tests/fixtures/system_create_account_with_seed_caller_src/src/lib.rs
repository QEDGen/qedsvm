//! BPF caller exercising `system_instruction::create_account_with_seed`.
//!
//! Accounts:
//!   accounts[0] = payer    (signer, writable)
//!   accounts[1] = derived  (writable; pubkey = SHA256(base || seed || owner))
//!   accounts[2] = base     (signer)
//!   accounts[3] = system_program (read-only)
//!
//! `instruction_data` layout:
//!   0..8    lamports (u64 LE)
//!   8..16   space    (u64 LE)
//!   16..48  owner    (32 B target owner)
//!   48..52  seed_len (u32 LE)
//!   52..52+seed_len  seed bytes (UTF-8)

use solana_program::{
    account_info::AccountInfo, entrypoint, entrypoint::ProgramResult,
    program::invoke, pubkey::Pubkey, system_instruction,
};

entrypoint!(process_instruction);

pub fn process_instruction(
    _program_id: &Pubkey,
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> ProgramResult {
    if instruction_data.len() < 52 || accounts.len() < 4 {
        return Err(solana_program::program_error::ProgramError::InvalidArgument);
    }

    let lamports = u64::from_le_bytes(instruction_data[0..8].try_into().unwrap());
    let space    = u64::from_le_bytes(instruction_data[8..16].try_into().unwrap());
    let owner    = Pubkey::new_from_array(instruction_data[16..48].try_into().unwrap());
    let seed_len = u32::from_le_bytes(instruction_data[48..52].try_into().unwrap()) as usize;

    if instruction_data.len() < 52 + seed_len {
        return Err(solana_program::program_error::ProgramError::InvalidArgument);
    }
    let seed_bytes = &instruction_data[52..52 + seed_len];
    let seed = core::str::from_utf8(seed_bytes)
        .map_err(|_| solana_program::program_error::ProgramError::InvalidArgument)?;

    let payer   = &accounts[0];
    let derived = &accounts[1];
    let base    = &accounts[2];

    let ix = system_instruction::create_account_with_seed(
        payer.key, derived.key, base.key, seed, lamports, space, &owner,
    );
    invoke(&ix, &[payer.clone(), derived.clone(), base.clone()])?;
    Ok(())
}
