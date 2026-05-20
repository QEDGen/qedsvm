//! Caller: invoke a target program (ix.data[0..32] = callee id),
//! then sol_get_return_data and copy the bytes into accounts[0].data.
//! Together with cpi_set_return_data_callee.so this verifies that
//! returnData round-trips across a CPI boundary.

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
    if let Some((_pid, data)) = get_return_data() {
        let mut out = accounts[0].data.borrow_mut();
        let n = data.len().min(out.len());
        out[..n].copy_from_slice(&data[..n]);
    }
    Ok(())
}
