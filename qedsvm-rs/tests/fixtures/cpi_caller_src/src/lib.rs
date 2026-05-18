//! Minimal CPI caller. Reads a 32-byte target pubkey from
//! `instruction_data[0..32]`, builds an `Instruction { program_id =
//! target, accounts = [], data = [] }`, invokes it, and returns the
//! callee's outcome.
//!
//! Two fixture roles:
//!   - As a *callee*: nobody calls into this version specifically; it
//!     would just invoke whatever pubkey lives in its own ix-data.
//!   - As a *caller*: register this program under some Pubkey, register
//!     a different program (e.g. `noop.so`) under the pubkey supplied
//!     in `instruction_data`, and watch the qedsvm runner route
//!     the CPI through the registry. Exit code = 0 iff the callee
//!     returned `Ok(())`.

use solana_program::{
    account_info::AccountInfo, entrypoint, entrypoint::ProgramResult,
    instruction::Instruction, program::invoke, pubkey::Pubkey,
};

entrypoint!(process_instruction);

pub fn process_instruction(
    _program_id: &Pubkey,
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> ProgramResult {
    let target_pubkey = Pubkey::try_from(&instruction_data[0..32])
        .map_err(|_| solana_program::program_error::ProgramError::InvalidArgument)?;
    let ix = Instruction {
        program_id: target_pubkey,
        accounts: vec![],
        data: vec![],
    };
    invoke(&ix, accounts)?;
    Ok(())
}
