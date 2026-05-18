//! CPI caller that forwards TWO writable accounts to a target program
//! embedded in instruction_data[0..32]. Companion fixture for the
//! Phase 3-N marshaling tests: when registered alongside an
//! incrementer-style callee, this caller's `invoke(&ix, &[a, b])`
//! must round-trip both accounts through the callee's view (read all
//! N AccountInfo blocks, run, write back via per-slot pointers).
//!
//! The callee may modify accounts[0], accounts[1], or both — the
//! caller is agnostic. The diff harness asserts post-state matches
//! mollusk byte-for-byte.

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
    let a = &accounts[0];
    let b = &accounts[1];
    let ix = Instruction {
        program_id: target_pubkey,
        accounts: vec![
            AccountMeta { pubkey: *a.key, is_signer: a.is_signer, is_writable: a.is_writable },
            AccountMeta { pubkey: *b.key, is_signer: b.is_signer, is_writable: b.is_writable },
        ],
        data: vec![],
    };
    invoke(&ix, accounts)?;
    Ok(())
}
