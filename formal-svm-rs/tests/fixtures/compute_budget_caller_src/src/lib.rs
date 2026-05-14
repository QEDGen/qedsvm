//! BPF caller that CPIs into the ComputeBudget program with a
//! `SetComputeUnitLimit` instruction. The body is a no-op on agave's
//! side (the runtime processes ComputeBudget at the transaction-
//! prepare stage); CPI just consumes 150 CU and returns success.
//!
//! We construct the `Instruction` manually since solana-program 2.x
//! removed `solana_program::compute_budget`, and dragging in
//! solana-compute-budget-interface causes a Pubkey type clash. The
//! wire format is trivial:
//!
//!   `[discriminant: u8 = 2][units: u32 LE]` = 5 bytes total
//!
//! `instruction_data` from the outer caller layout (4 bytes):
//!   0..4  units (u32 LE)

use solana_program::{
    account_info::AccountInfo, entrypoint, entrypoint::ProgramResult,
    instruction::Instruction, program::invoke, pubkey::Pubkey,
};

entrypoint!(process_instruction);

/// ComputeBudget pubkey bytes
/// (base58-decoded `ComputeBudget111111111111111111111111111111`).
const COMPUTE_BUDGET_ID: Pubkey = Pubkey::new_from_array([
    0x03, 0x06, 0x46, 0x6f, 0xe5, 0x21, 0x17, 0x32,
    0xff, 0xec, 0xad, 0xba, 0x72, 0xc3, 0x9b, 0xe7,
    0xbc, 0x8c, 0xe5, 0xbb, 0xc5, 0xf7, 0x12, 0x6b,
    0x2c, 0x43, 0x9b, 0x3a, 0x40, 0x00, 0x00, 0x00,
]);

pub fn process_instruction(
    _program_id: &Pubkey,
    _accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> ProgramResult {
    if instruction_data.len() < 4 {
        return Err(solana_program::program_error::ProgramError::InvalidArgument);
    }
    let mut units_bytes = [0u8; 4];
    units_bytes.copy_from_slice(&instruction_data[0..4]);

    // Hand-build `SetComputeUnitLimit(units)`:
    //   discriminant = 2 (u8), payload = units (u32 LE).
    let mut data = Vec::with_capacity(5);
    data.push(2u8);
    data.extend_from_slice(&units_bytes);

    let ix = Instruction {
        program_id: COMPUTE_BUDGET_ID,
        accounts: vec![],
        data,
    };
    invoke(&ix, &[])?;
    Ok(())
}
