//! Caller that derives a PDA from seed `b"vault"`, then `invoke_signed`s
//! a callee passing the PDA as accounts[1] (with is_signer=false in the
//! AccountMeta — agave promotes it to signer based on the seeds).
//!
//! Together with `cpi_signed_pda_callee.so` this probes whether the
//! engine implements PDA signer-seed promotion (r4/r5 of
//! sol_invoke_signed).
//!
//! ix.data: [0..32] = callee program id
//! accounts: [0] = writable data acct (callee writes a marker byte),
//!           [1] = PDA acct (caller's program_id + b"vault")

use solana_program::{
    account_info::AccountInfo, entrypoint, entrypoint::ProgramResult,
    instruction::{AccountMeta, Instruction}, program::invoke_signed,
    pubkey::Pubkey,
};

entrypoint!(process_instruction);

pub fn process_instruction(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> ProgramResult {
    let callee = Pubkey::try_from(&instruction_data[0..32])
        .map_err(|_| solana_program::program_error::ProgramError::InvalidArgument)?;
    let seed: &[u8] = b"vault";
    let (pda, bump) = Pubkey::find_program_address(&[seed], program_id);
    let ix = Instruction {
        program_id: callee,
        accounts: vec![
            AccountMeta {
                pubkey: *accounts[0].key,
                is_signer: accounts[0].is_signer,
                is_writable: true,
            },
            AccountMeta {
                pubkey: pda,
                // is_signer:true claim is proved by the seeds passed
                // to invoke_signed. Agave promotes the AccountInfo
                // for `pda` to is_signer=true on the callee side.
                is_signer: true,
                is_writable: false,
            },
        ],
        data: vec![],
    };
    invoke_signed(&ix, accounts, &[&[seed, &[bump]]])?;
    Ok(())
}
