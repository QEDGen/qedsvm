//! CPI callee that attempts to GROW its writable account BEYOND
//! `MAX_PERMITTED_DATA_INCREASE` (10240): `realloc(old_len + 10241)`. Both
//! engines must reject the over-grow and leave the account unchanged.
//!
//! Cross-engine observable (audit M6r — realloc bound, negative case):
//! - agave: the runtime rejects the over-grow (`InstructionError::InvalidRealloc`
//!   / the SDK `realloc` bound check) and the whole instruction fails.
//! - Post-fix qedsvm: `cpiCallNextState`'s `reallocViolated` check
//!   (`postLen > p.dataLen + MAX_PERMITTED_DATA_INCREASE`) fails the CPI with
//!   `ERR_INVALID_REALLOC` and rolls the account back to its pre-CPI state.
//! The exact error code is engine-specific (malicious path); the account state
//! (unchanged) is what both engines must agree on.

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
    let old_len = acct.data_len();
    // 10241 > MAX_PERMITTED_DATA_INCREASE (10240): over the bound.
    acct.realloc(old_len + 10241, false)?;
    Ok(())
}
