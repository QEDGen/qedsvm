//! Caller: invoke a target program (ix.data[0..32] = callee id), then
//! sol_get_return_data and copy the SETTER's program id into
//! accounts[0].data[0..32] and the returned bytes after it. Together
//! with cpi_set_return_data_callee.so this pins that the pubkey the
//! syscall writes to *pubkey_out is the program that last called
//! sol_set_return_data (the CPI callee), not the caller and not a
//! zero placeholder (soundness audit H7).

use solana_program::{
    account_info::AccountInfo, entrypoint, entrypoint::ProgramResult,
    instruction::Instruction,
    program::{get_return_data, invoke},
    pubkey::Pubkey,
};

entrypoint!(process_instruction);

pub fn process_instruction(
    _program_id: &Pubkey,
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> ProgramResult {
    let callee = Pubkey::try_from(&instruction_data[0..32])
        .map_err(|_| solana_program::program_error::ProgramError::InvalidArgument)?;
    let ix = Instruction {
        program_id: callee,
        accounts: vec![],
        data: vec![],
    };
    invoke(&ix, accounts)?;
    if let Some((pid, data)) = get_return_data() {
        let mut out = accounts[0].data.borrow_mut();
        out[..32].copy_from_slice(pid.as_ref());
        let n = data.len().min(out.len() - 32);
        out[32..32 + n].copy_from_slice(&data[..n]);
    }
    Ok(())
}
