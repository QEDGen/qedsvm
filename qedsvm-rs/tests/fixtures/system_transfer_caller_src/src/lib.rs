//! BPF caller that invokes `system_instruction::transfer` between two
//! accounts. Companion fixture for Tier-1 #2 (native programs):
//!
//! - `accounts[0]` = from (signer, writable)
//! - `accounts[1]` = to (writable)
//! - `accounts[2]` = the System program account (read-only)
//!
//! `instruction_data` is a u64 LE: the lamport amount to transfer.
//! Both engines must end with `from.lamports -= n`, `to.lamports += n`.

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
    // The outer Instruction passes the System program's pubkey as a
    // read-only AccountMeta so agave's runtime registers it in the
    // transaction's account_keys for CPI dispatch. The caller itself
    // doesn't need to use that AccountInfo — it just needs to exist
    // in the transaction account-key set.
    if instruction_data.len() < 8 || accounts.len() < 3 {
        return Err(solana_program::program_error::ProgramError::InvalidArgument);
    }
    let mut bytes = [0u8; 8];
    bytes.copy_from_slice(&instruction_data[0..8]);
    let lamports = u64::from_le_bytes(bytes);

    let from = &accounts[0];
    let to   = &accounts[1];

    let ix = system_instruction::transfer(from.key, to.key, lamports);
    // Forward only `from` and `to` — those are the accounts System
    // actually reads. The System program account itself is found via
    // the transaction's account-key set.
    invoke(&ix, &[from.clone(), to.clone()])?;
    Ok(())
}
