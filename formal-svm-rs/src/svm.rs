//! The Mollusk-shaped public API.
//!
//! Naming intent: the *engine* is `formal_svm::Svm`; the *shape* (the
//! `add_program` / `process_instruction` / `InstructionResult` triad)
//! mirrors `mollusk_svm::Mollusk` so a real Mollusk test can run
//! through formal-svm by replacing one type name.
//!
//! Out of scope for v1:
//! - CPI: the underlying Lean runner has a v1 CPI stub that takes
//!   program-id as `r1` directly (not the full `SolInstruction`
//!   read). Programs that invoke other programs will get `r0 = 1`
//!   from the CPI call. The `add_program` map is wired but unused
//!   until the Lean side gets a `Pubkey → ByteArray` registry.
//! - Mapping to Mollusk's `ProgramError` enum: we use a coarser
//!   `ProgramResult::{Success, Failure { exit_code }, OutOfBudget}`
//!   that doesn't require dragging in `solana-program-error`.

use std::collections::HashMap;

use solana_account::AccountSharedData;
use solana_instruction::Instruction;
use solana_pubkey::Pubkey;

use crate::deserialize::{deserialize_account_writes, DeserializeError};
use crate::serialize::{serialize_parameters, SerializeError};
use crate::wire::ExitOutcome;

/// Default per-instruction CU cap, matching Solana mainnet's runtime
/// limit (200k CUs per top-level instruction). Override via
/// [`Svm::with_cu_budget`].
pub const DEFAULT_CU_BUDGET: u64 = 200_000;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProgramResult {
    /// Program halted with `exit r0 = 0`.
    Success,
    /// Program halted with non-zero r0, or with one of the runtime
    /// error sentinels in `Svm.SBPF.Execute.ERR_*` (invalid PC, abort,
    /// divide-by-zero). `exit_code` is r0 — interpret per the BPF
    /// program's contract.
    Failure { exit_code: u64 },
    /// The CU budget was exhausted before the program halted.
    OutOfBudget,
}

/// Mirrors the shape of `mollusk_svm::result::InstructionResult`.
/// Difference from Mollusk: we don't surface an `InstructionError`
/// enum — failures land as `ProgramResult::Failure { exit_code }`
/// directly with the raw r0 value.
#[derive(Debug, Clone)]
pub struct InstructionResult {
    pub program_result: ProgramResult,
    /// Compute units consumed at the top-level program. Per v1 CPI
    /// semantics, a CPI call counts as 1 CU at the caller's level
    /// regardless of how much the callee consumed.
    pub compute_units_consumed: u64,
    pub logs: Vec<Vec<u8>>,
    pub return_data: Vec<u8>,
    /// Post-execution accounts, one entry per `AccountMeta` in the
    /// instruction (matching Mollusk's `resulting_accounts`).
    pub resulting_accounts: Vec<(Pubkey, AccountSharedData)>,
}

/// Errors that prevent `process_instruction` from even attempting to
/// run the program (vs. errors *from* the program, which surface as
/// `ProgramResult::Failure`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SvmError {
    /// No ELF registered for the program ID referenced by the
    /// instruction.
    UnknownProgram(Pubkey),
    /// The instruction list / accounts were malformed (missing
    /// account, too many accounts).
    Serialize(SerializeError),
    /// ELF parse failure inside Lean (returned status byte 0).
    ElfDecodeFailed,
    /// Post-execution buffer parse failed — typically buffer
    /// truncation or an account pubkey shift inside the program
    /// (which would indicate Lean's memory model diverged from
    /// agave's).
    BufferParse(DeserializeError),
    /// The Lean side returned a malformed wire response — should be
    /// impossible if `Svm.Ffi` is built from a matching Lean tree.
    InternalWireFormat(crate::DecodeError),
}

impl std::fmt::Display for SvmError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnknownProgram(pk) => write!(f, "no program registered for {pk}"),
            Self::Serialize(e) => write!(f, "input serialization failed: {e}"),
            Self::ElfDecodeFailed => write!(f, "Lean ELF decode failed"),
            Self::BufferParse(e) => write!(f, "post-execution buffer parse failed: {e}"),
            Self::InternalWireFormat(e) => write!(f, "internal Lean wire-format error: {e}"),
        }
    }
}

impl std::error::Error for SvmError {}

impl From<SerializeError> for SvmError {
    fn from(e: SerializeError) -> Self { Self::Serialize(e) }
}

/// Mollusk-shaped reference SVM backed by the formal-svm Lean
/// interpreter.
///
/// Hold one `Svm` per test (or share via clone — registries are cheap
/// to copy). For multi-program differential testing, register each
/// program by its on-chain id with [`add_program`].
pub struct Svm {
    programs: HashMap<Pubkey, Vec<u8>>,
    cu_budget: u64,
}

impl Default for Svm {
    fn default() -> Self { Self::new() }
}

impl Svm {
    pub fn new() -> Self {
        Self { programs: HashMap::new(), cu_budget: DEFAULT_CU_BUDGET }
    }

    /// Lower or raise the per-instruction CU budget. Default is
    /// `DEFAULT_CU_BUDGET = 200_000`.
    pub fn with_cu_budget(mut self, cu_budget: u64) -> Self {
        self.cu_budget = cu_budget;
        self
    }

    /// Register an ELF binary for invocations of `program_id`.
    /// Subsequent calls overwrite.
    pub fn add_program(&mut self, program_id: &Pubkey, elf: &[u8]) -> &mut Self {
        self.programs.insert(*program_id, elf.to_vec());
        self
    }

    /// Run a single top-level instruction. Matches Mollusk's API
    /// shape for swap-in differential testing.
    pub fn process_instruction(
        &self,
        instruction: &Instruction,
        accounts: &[(Pubkey, AccountSharedData)],
    ) -> Result<InstructionResult, SvmError> {
        let elf = self.programs.get(&instruction.program_id)
            .ok_or_else(|| SvmError::UnknownProgram(instruction.program_id))?;
        let input = serialize_parameters(instruction, accounts, &instruction.program_id)?;

        let raw = crate::run_buffer(elf, &input, self.cu_budget)
            .map_err(|e| match e {
                crate::DecodeError::ElfDecodeFailed => SvmError::ElfDecodeFailed,
                other => SvmError::InternalWireFormat(other),
            })?;

        let program_result = match raw.outcome {
            ExitOutcome::OutOfBudget => ProgramResult::OutOfBudget,
            ExitOutcome::Halted(0) => ProgramResult::Success,
            ExitOutcome::Halted(n) => ProgramResult::Failure { exit_code: n },
        };

        let resulting_accounts = if accounts.is_empty() && instruction.accounts.is_empty() {
            Vec::new()
        } else {
            deserialize_account_writes(&raw.modified_input, instruction, accounts)
                .map_err(SvmError::BufferParse)?
        };

        Ok(InstructionResult {
            program_result,
            compute_units_consumed: raw.compute_units_consumed,
            logs: raw.logs,
            return_data: raw.return_data,
            resulting_accounts,
        })
    }

}
