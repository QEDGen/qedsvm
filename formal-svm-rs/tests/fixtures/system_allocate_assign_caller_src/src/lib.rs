//! BPF caller that exercises the two simpler System variants:
//! `Allocate { space }` followed by `Assign { owner }` on the same
//! signer account. After this pair the account is the canonical
//! "freshly created" account most non-CreateAccount programs build
//! (e.g. via PDA seeds, where the account has lamports already and
//! just needs data + owner set).
//!
//! Accounts:
//!   accounts[0] = acct (signer, writable, must be uninitialized:
//!                       data_len=0, system-owned)
//!   accounts[1] = system_program (read-only — CPI dispatch registration)
//!
//! `instruction_data` layout (40 bytes):
//!   0..8   space (u64 LE)
//!   8..40  owner (32 B target owner pubkey)

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
    if instruction_data.len() < 40 || accounts.len() < 2 {
        return Err(solana_program::program_error::ProgramError::InvalidArgument);
    }

    let mut space_bytes = [0u8; 8];
    space_bytes.copy_from_slice(&instruction_data[0..8]);
    let space = u64::from_le_bytes(space_bytes);

    let mut owner_bytes = [0u8; 32];
    owner_bytes.copy_from_slice(&instruction_data[8..40]);
    let owner = Pubkey::new_from_array(owner_bytes);

    let acct = &accounts[0];

    // 1) Allocate `space` bytes of data.
    let alloc_ix = system_instruction::allocate(acct.key, space);
    invoke(&alloc_ix, &[acct.clone()])?;

    // 2) Reassign ownership to `owner`.
    let assign_ix = system_instruction::assign(acct.key, &owner);
    invoke(&assign_ix, &[acct.clone()])?;

    Ok(())
}
