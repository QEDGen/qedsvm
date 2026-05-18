//! BPF caller that invokes `system_instruction::create_account`.
//! Companion fixture to Tier-1 #2 (native programs): exercises the
//! end-to-end CreateAccount path through qedsvm's `Native.dispatch`
//! and asserts byte-for-byte parity with mollusk.
//!
//! Accounts:
//!   accounts[0] = payer    (signer, writable, funds source)
//!   accounts[1] = newAcct  (signer, writable, must be uninitialized)
//!   accounts[2] = system_program (read-only — for CPI dispatch
//!                                 registration only)
//!
//! `instruction_data` layout (48 bytes):
//!   0..8   lamports (u64 LE)
//!   8..16  space    (u64 LE)
//!   16..48 owner    (32 B target owner pubkey)

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
    if instruction_data.len() < 48 || accounts.len() < 3 {
        return Err(solana_program::program_error::ProgramError::InvalidArgument);
    }

    let mut lamports_bytes = [0u8; 8];
    lamports_bytes.copy_from_slice(&instruction_data[0..8]);
    let lamports = u64::from_le_bytes(lamports_bytes);

    let mut space_bytes = [0u8; 8];
    space_bytes.copy_from_slice(&instruction_data[8..16]);
    let space = u64::from_le_bytes(space_bytes);

    let mut owner_bytes = [0u8; 32];
    owner_bytes.copy_from_slice(&instruction_data[16..48]);
    let owner = Pubkey::new_from_array(owner_bytes);

    let payer   = &accounts[0];
    let new_acct = &accounts[1];

    let ix = system_instruction::create_account(
        payer.key, new_acct.key, lamports, space, &owner,
    );
    invoke(&ix, &[payer.clone(), new_acct.clone()])?;
    Ok(())
}
