//! Observe actual invocation height before and after a nested call.
//! data = [expected_height, top_level_only_guard]; remaining accounts are
//! the successive program IDs in the chain. No account data is modified.
use solana_program::{
    account_info::AccountInfo,
    entrypoint,
    entrypoint::ProgramResult,
    instruction::{get_stack_height, AccountMeta, Instruction},
    log::sol_log_64,
    program::invoke,
    program_error::ProgramError,
    pubkey::Pubkey,
};

entrypoint!(process_instruction);

pub fn process_instruction(
    _program_id: &Pubkey,
    accounts: &[AccountInfo],
    data: &[u8],
) -> ProgramResult {
    let expected = data[0] as usize;
    let before = get_stack_height();
    sol_log_64(before as u64, 0, 0, 0, 0);
    if data[1] != 0 && before != 1 {
        return Err(ProgramError::Custom(109));
    }
    if before != expected {
        return Err(ProgramError::Custom(110));
    }
    if let Some((next, rest)) = accounts.split_first() {
        invoke(
            &Instruction {
                program_id: *next.key,
                accounts: rest
                    .iter()
                    .map(|a| AccountMeta::new_readonly(*a.key, false))
                    .collect(),
                data: vec![data[0] + 1, data[1]],
            },
            accounts,
        )?;
    }
    let after = get_stack_height();
    sol_log_64(after as u64, 0, 0, 0, 0);
    if after != expected {
        return Err(ProgramError::Custom(111));
    }
    Ok(())
}
