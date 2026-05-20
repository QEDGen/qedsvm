//! Callee that calls sol_set_return_data with a fixed 4-byte payload
//! and exits. Paired with cpi_get_return_data_caller.so to verify
//! returnData propagates across a CPI boundary.

use solana_program::{
    account_info::AccountInfo, entrypoint, entrypoint::ProgramResult,
    program::set_return_data, pubkey::Pubkey,
};

entrypoint!(process_instruction);

pub fn process_instruction(
    _program_id: &Pubkey,
    _accounts: &[AccountInfo],
    _instruction_data: &[u8],
) -> ProgramResult {
    set_return_data(&[0xAB, 0xCD, 0xEF, 0x12]);
    Ok(())
}
