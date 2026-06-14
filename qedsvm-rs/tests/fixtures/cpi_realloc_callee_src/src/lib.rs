//! CPI callee that GROWS its writable account by 8 bytes (within the
//! `MAX_PERMITTED_DATA_INCREASE` reserve) and writes a sentinel into the newly
//! grown tail. Companion to `cpi_increment_caller.so`: a test registers the
//! caller as the top-level program and this as the CPI target, then observes
//! the grown account length + sentinel through the CPI realloc write-back path.
//!
//! Cross-engine observable (audit M6r — CPI realloc write-back):
//! - agave: the callee's `realloc` updates its serialized account; after the
//!   sub-instruction returns, the runtime re-serializes the grown account into
//!   the caller's view (new `data_len` at block offset 80, new data at 88).
//! - Pre-fix qedsvm: `cpiCallNextState` read the PRE-CPI `dataLen` and never
//!   updated the caller's length slots, so the grow was LOST — the model
//!   reported the old length (true-in-model / false-on-chain).
//! - Post-fix qedsvm: the write-back harvests the callee's post-CPI `data_len`
//!   (block offset 80), writes that many bytes, and dual-writes the new length
//!   to `dataPtr - 8` (the serialized slot the harness deserializes).

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
    let new_len = old_len + 8;
    // Grow without zero-init (we write the sentinel ourselves).
    acct.realloc(new_len, false)?;
    let mut data = acct.try_borrow_mut_data()?;
    // Sentinel u64 in the newly grown 8-byte tail.
    data[old_len..new_len].copy_from_slice(&0xA1A2A3A4A5A6A7A8u64.to_le_bytes());
    Ok(())
}
