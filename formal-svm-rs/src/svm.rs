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

        // Sysvar read-only enforcement. Agave's loader rejects an
        // instruction that marks a known sysvar account as writable.
        // We mirror by inspecting `ix.accounts` *before* serializing
        // (cheaper than catching after exec). Failures surface as
        // ProgramResult::Failure with the post-state sentinel.
        if let Some(bad) = ix_accounts_writable_sysvar(instruction) {
            return Ok(InstructionResult {
                program_result: ProgramResult::Failure {
                    exit_code: ERR_INVALID_POSTSTATE,
                },
                compute_units_consumed: 0,
                logs: vec![],
                return_data: vec![],
                resulting_accounts: accounts.to_vec(),
            });
        }

        let input = serialize_parameters(instruction, accounts, &instruction.program_id)?;

        // Build a CPI registry of all *other* programs registered with
        // this `Svm`. The main program is fetched via `elf` directly,
        // so we exclude it from the registry to keep the blob small —
        // the Lean runner doesn't need it twice.
        let registry_entries: Vec<(&[u8; 32], &[u8])> = self.programs
            .iter()
            .filter(|(pid, _)| **pid != instruction.program_id)
            .map(|(pid, elf)| (pid.as_array(), elf.as_slice()))
            .collect();
        let raw = if registry_entries.is_empty() {
            // Fast path: no other programs, use the simpler entry that
            // doesn't allocate a registry blob.
            crate::run_buffer(elf, &input, self.cu_budget)
        } else {
            let registry_blob = crate::encode_registry(&registry_entries);
            crate::run_buffer_with_registry(elf, &input, &registry_blob, self.cu_budget)
        }
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

        // Tier-2 post-instruction soundness validation. Runs only on
        // successful program returns — failed programs already have
        // their state semantically rolled back at the harness level
        // (we don't write back to the caller's accounts), so the
        // invariants don't apply. Any violation downgrades the
        // outcome to `Failure { exit_code: ERR_INVALID_POSTSTATE }`.
        let program_result = if matches!(program_result, ProgramResult::Success) {
            match validate_post_state(instruction, accounts, &resulting_accounts) {
                Ok(()) => program_result,
                Err(_) => ProgramResult::Failure { exit_code: ERR_INVALID_POSTSTATE },
            }
        } else {
            program_result
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

/// Sentinel exit code returned when a program returns successfully
/// from the BPF interpreter but violates a post-instruction
/// invariant. Mirrors the family of agave's `InstructionError`
/// variants for these checks (`ExternalAccountDataModified`,
/// `ExternalAccountLamportChange`, `ExecutableModified`,
/// `RentEpochModified`, `UnbalancedInstruction`,
/// `MaxAccountsDataAllocationsExceeded`). We collapse them to a
/// single sentinel since our `ProgramResult` is u64-keyed; the
/// individual checks live in `validate_post_state` below.
pub const ERR_INVALID_POSTSTATE: u64 = 0xFFFFFFFFFFFFFFFB;

/// Returns `Some(pubkey)` if any AccountMeta in `instruction.accounts`
/// references a known sysvar pubkey with `is_writable = true`.
/// Sysvar accounts are read-only by design — the runtime maintains
/// their contents — and agave's loader rejects an instruction that
/// marks one as writable.
///
/// All sysvar pubkeys (Clock, Rent, EpochSchedule, SlotHashes,
/// SlotHistory, StakeHistory, RecentBlockhashes, Fees, Instructions,
/// EpochRewards, LastRestartSlot) share a fixed 4-byte prefix in
/// their *decoded* form: `[0x06, 0xa7, 0xd5, 0x17]`. This comes from
/// the base58 namespacing of `Sysvar...` pubkeys and is unique to
/// the sysvar program (the byte pattern is astronomically unlikely
/// for any non-sysvar pubkey).
fn ix_accounts_writable_sysvar(instruction: &Instruction) -> Option<Pubkey> {
    const SYSVAR_DISCRIMINATOR: [u8; 4] = [0x06, 0xa7, 0xd5, 0x17];
    for meta in &instruction.accounts {
        if meta.is_writable {
            let bytes = meta.pubkey.to_bytes();
            if bytes.starts_with(&SYSVAR_DISCRIMINATOR) {
                return Some(meta.pubkey);
            }
        }
    }
    None
}

/// Per-account / cross-account invariants agave enforces at
/// instruction exit. Failures are mapped to a single sentinel
/// `ERR_INVALID_POSTSTATE` exit code at the program-result level.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PostStateError {
    /// A read-only account's lamports, data, or owner changed.
    ReadOnlyAccountModified(Pubkey),
    /// `executable` flag flipped after the instruction.
    ExecutableModified(Pubkey),
    /// `rent_epoch` field changed (programs may not mutate it).
    RentEpochModified(Pubkey),
    /// Sum of lamports across all listed accounts changed.
    /// Caller wouldn't be able to mint or destroy lamports.
    LamportConservationViolated { pre_sum: u128, post_sum: u128 },
    /// Account data grew past `pre_len + MAX_PERMITTED_DATA_INCREASE`.
    DataLengthOverflow { pubkey: Pubkey, pre: usize, post: usize },
}

fn validate_post_state(
    instruction: &Instruction,
    pre: &[(Pubkey, AccountSharedData)],
    post: &[(Pubkey, AccountSharedData)],
) -> Result<(), PostStateError> {
    use solana_account::ReadableAccount;

    const MAX_PERMITTED_DATA_INCREASE: usize = 10240;

    // Lamport conservation across the *per-call* account list — what
    // the instruction's serialized input region observably owns. The
    // BPF program can move lamports between these accounts but not
    // mint or burn. (System program's create_account / transfer are
    // implemented as redistributions of existing lamports, so this
    // invariant holds even when System mutates balances.)
    let pre_sum: u128  = pre.iter().map(|(_, a)| u128::from(a.lamports())).sum();
    let post_sum: u128 = post.iter().map(|(_, a)| u128::from(a.lamports())).sum();
    if pre_sum != post_sum {
        return Err(PostStateError::LamportConservationViolated { pre_sum, post_sum });
    }

    // Per-account checks. Index alignment between pre/post is
    // guaranteed by `deserialize_account_writes` — it emits one
    // entry per AccountMeta in `instruction.accounts` in order.
    for ((pre_pk, pre_acct), (post_pk, post_acct)) in pre.iter().zip(post.iter()) {
        debug_assert_eq!(pre_pk, post_pk);
        let pk = *post_pk;

        // executable: monotone — once true, must stay true. agave is
        // stricter (no flip in either direction during a normal ix);
        // we mirror.
        if pre_acct.executable() != post_acct.executable() {
            return Err(PostStateError::ExecutableModified(pk));
        }
        // rent_epoch: programs can't mutate; the runtime owns it.
        if pre_acct.rent_epoch() != post_acct.rent_epoch() {
            return Err(PostStateError::RentEpochModified(pk));
        }

        // Read-only enforcement: find this pubkey's AccountMeta. If
        // it's marked `is_writable = false`, lamports / data / owner
        // must all be unchanged. (A program can mutate the
        // `original_data_len` header field via the
        // `entrypoint!`-macro deserializer, but that's not surfaced
        // through `deserialize_account_writes` — we only see the
        // logical fields.)
        let meta_writable = instruction.accounts.iter()
            .find(|m| m.pubkey == pk)
            .map(|m| m.is_writable)
            .unwrap_or(true);  // not in ix.accounts → no constraint
        if !meta_writable {
            if pre_acct.lamports() != post_acct.lamports()
                || pre_acct.data() != post_acct.data()
                || pre_acct.owner() != post_acct.owner()
            {
                return Err(PostStateError::ReadOnlyAccountModified(pk));
            }
        }

        // Per-account data-growth bound (Tier-2 #9).
        let pre_len  = pre_acct.data().len();
        let post_len = post_acct.data().len();
        if post_len > pre_len + MAX_PERMITTED_DATA_INCREASE {
            return Err(PostStateError::DataLengthOverflow {
                pubkey: pk, pre: pre_len, post: post_len,
            });
        }
    }

    Ok(())
}
