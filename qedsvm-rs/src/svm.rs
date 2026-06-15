//! The Mollusk-shaped public API (`add_program`/`process_instruction`/`InstructionResult`).
//! NOTE: this is the diff-testing runner path; proof-facing `step` CPI is a separate stub
//! (SVM/Syscalls/Cpi.lean); runner CPI has known authorization gaps (C4/C5/M6).
use std::collections::HashMap;

use solana_account::AccountSharedData;
use solana_instruction::Instruction;
use solana_program_error::ProgramError;
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
    /// Program halted with non-zero r0, upper 32 bits zero (not a `ProgramError` encoding).
    /// Covers hand-rolled exit codes, `ERR_*` sentinels, and `ERR_INVALID_POSTSTATE`.
    Failure { exit_code: u64 },
    /// Program returned `Err(ProgramError)` (Pinocchio/agave entrypoint packs it as `code << 32`).
    /// Mirrors mollusk's `Failure(InstructionError::ProgramError(_))` for cross-engine diff.
    ProgramError(ProgramError),
    /// The CU budget was exhausted before the program halted.
    OutOfBudget,
    /// VM-level fault (Lean `State.vmError` — audit L1): access violation, div-by-zero, abort, etc.
    /// Distinct from program-returned errors. agave collapses nearly all to `ProgramFailedToComplete`;
    /// `sentinel` is the fine-grained `ERR_*` for diagnostics/M14 divergence list. See `vm_fault_name`.
    VmFault { sentinel: u64 },
}

/// Name for a `VmError` sentinel, in sync with `SVM.SBPF.VmError.toSentinel` (audit M14).
pub const fn vm_fault_name(sentinel: u64) -> &'static str {
    match sentinel {
        0xFFFFFFFFFFFFFFFE => "divideByZero",
        0xFFFFFFFFFFFFFFFF => "invalidPc",
        0xFFFFFFFFFFFFFFFD => "abort",
        0xFFFFFFFFFFFFFFFC => "accessViolation",
        0xFFFFFFFFFFFFFFFA => "unsupportedInstruction",
        0xFFFFFFFFFFFFFFF9 => "callDepthExceeded",
        0xFFFFFFFFFFFFFFF8 => "returnDataTooLarge",
        0xFFFFFFFFFFFFFFF7 => "invalidLength",
        0xFFFFFFFFFFFFFFF6 => "invalidAttribute",
        0xFFFFFFFFFFFFFFF5 => "badSeeds",
        0xFFFFFFFFFFFFFFF4 => "readonlyModified",
        0xFFFFFFFFFFFFFFF3 => "invalidRealloc",
        _ => "unknownFault",
    }
}

impl ProgramResult {
    /// Build a `ProgramResult` from r0: decodes `ProgramError` when upper 32 bits are non-zero
    /// (agave/Pinocchio convention); raw r0 falls through to `Failure { exit_code }`.
    pub(crate) fn from_bpf_r0(r0: u64) -> Self {
        if r0 == 0 {
            return Self::Success;
        }
        if (r0 >> 32) != 0 {
            // `From<u64> for ProgramError` is total; unknown high bits → `Custom(low as u32)`.
            return Self::ProgramError(ProgramError::from(r0));
        }
        Self::Failure { exit_code: r0 }
    }
}

#[cfg(test)]
mod from_bpf_r0_tests {
    use super::*;

    #[test]
    fn r0_zero_is_success() {
        assert_eq!(ProgramResult::from_bpf_r0(0), ProgramResult::Success);
    }

    #[test]
    fn small_raw_exit_code_preserved() {
        // Low-half r0 must NOT decode as ProgramError — breaks existing exit-code matchers.
        assert_eq!(
            ProgramResult::from_bpf_r0(42),
            ProgramResult::Failure { exit_code: 42 },
        );
        assert_eq!(
            ProgramResult::from_bpf_r0(1),
            ProgramResult::Failure { exit_code: 1 },
        );
    }

    #[test]
    fn pinocchio_invalid_account_data_decodes() {
        // issue #9: pyth_resolver InvalidAccountData; entrypoint encodes as (4 << 32).
        assert_eq!(
            ProgramResult::from_bpf_r0(17_179_869_184),
            ProgramResult::ProgramError(ProgramError::InvalidAccountData),
        );
    }

    #[test]
    fn pinocchio_custom_error_decodes() {
        // Custom(7) packs as (CUSTOM_ZERO=1 << 32) | 7.
        let packed = (1u64 << 32) | 7;
        assert_eq!(
            ProgramResult::from_bpf_r0(packed),
            ProgramResult::ProgramError(ProgramError::Custom(7)),
        );
    }

    #[test]
    fn pinocchio_custom_zero_decodes() {
        // Custom(0) = CUSTOM_ZERO with no low-half code; ensure round-trip.
        assert_eq!(
            ProgramResult::from_bpf_r0(1u64 << 32),
            ProgramResult::ProgramError(ProgramError::Custom(0)),
        );
    }

    #[test]
    fn err_invalid_poststate_sentinel_is_explicit_not_decoded() {
        // ERR_INVALID_POSTSTATE is synthesized post-Success, never via `from_bpf_r0`.
        // If it were passed here, the high 0xFFFFFFFF → `From<u64>` catch-all → Custom(0xFFFFFFFB).
        let r = ProgramResult::from_bpf_r0(ERR_INVALID_POSTSTATE);
        assert_eq!(
            r,
            ProgramResult::ProgramError(ProgramError::Custom(0xFFFFFFFB)),
        );
    }
}

/// Mirrors `mollusk_svm::result::InstructionResult`. Difference: failures surface as raw r0,
/// not a typed `InstructionError`.
#[derive(Debug, Clone)]
pub struct InstructionResult {
    pub program_result: ProgramResult,
    /// CU consumed. Per v1 CPI semantics, a CPI call counts as 1 CU at the caller's level.
    pub compute_units_consumed: u64,
    pub logs: Vec<Vec<u8>>,
    pub return_data: Vec<u8>,
    /// Post-execution accounts, one entry per `AccountMeta` in the
    /// instruction (matching Mollusk's `resulting_accounts`).
    pub resulting_accounts: Vec<(Pubkey, AccountSharedData)>,
    /// `Some(e)` iff `Success` was downgraded to `Failure { ERR_INVALID_POSTSTATE }` by the
    /// post-state backstop (M13). On a SOUND VM this is always `None`; `Some` signals either a
    /// model failure to surface a program error, or a Lean-VM soundness bug (minted lamports, etc.).
    /// Cross-engine fixtures assert `None` — the backstop must never silently mask VM bugs.
    /// See `tests/diff_mollusk.rs::assert_no_poststate_backstop`.
    pub poststate_violation: Option<PostStateError>,
}

/// Errors that prevent `process_instruction` from running (vs. errors from the program).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SvmError {
    /// No ELF registered for the program ID.
    UnknownProgram(Pubkey),
    /// Malformed instruction or accounts (missing account, too many accounts).
    Serialize(SerializeError),
    /// ELF parse failure inside Lean (status byte 0).
    ElfDecodeFailed,
    /// Post-execution buffer parse failed — typically truncation or a pubkey shift (Lean memory divergence from agave).
    BufferParse(DeserializeError),
    /// Malformed Lean wire response — impossible if `SVM.Ffi` matches the Lean tree.
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

/// Mollusk-shaped reference SVM backed by the qedsvm Lean interpreter.
/// Hold one `Svm` per test; for multi-program diffs register programs with [`add_program`].
pub struct Svm {
    programs: HashMap<Pubkey, Vec<u8>>,
    cu_budget: u64,
    /// Enforce rent-state transition check at instruction exit. Default OFF: agave applies this at
    /// the transaction layer; mollusk bypasses it too, so enabling here causes false diff divergences.
    /// Enable only when using qedsvm as a transaction-level oracle (not in diff-mollusk mode).
    enforce_rent_state: bool,
}

impl Default for Svm {
    fn default() -> Self { Self::new() }
}

impl Svm {
    pub fn new() -> Self {
        Self {
            programs: HashMap::new(),
            cu_budget: DEFAULT_CU_BUDGET,
            enforce_rent_state: false,
        }
    }

    /// Set the per-instruction CU budget (default: `DEFAULT_CU_BUDGET = 200_000`).
    pub fn with_cu_budget(mut self, cu_budget: u64) -> Self {
        self.cu_budget = cu_budget;
        self
    }

    /// Scan a transaction's instruction list for `ComputeBudgetInstruction::SetComputeUnitLimit`
    /// and apply it to `cu_budget`. Mirrors agave's `ComputeBudgetProcessor` pre-flight scan.
    /// Wire format: discriminant `2` + u32 LE. Last `SetComputeUnitLimit` wins.
    pub fn with_compute_budget_from_instructions(
        mut self,
        instructions: &[Instruction],
    ) -> Self {
        let cb_id = solana_sdk_ids::compute_budget::ID;
        for ix in instructions {
            if ix.program_id != cb_id { continue; }
            if ix.data.is_empty() { continue; }
            // Discriminant 2 = SetComputeUnitLimit(u32).
            if ix.data[0] != 2 { continue; }
            if ix.data.len() < 5 { continue; }
            let units = u32::from_le_bytes([ix.data[1], ix.data[2], ix.data[3], ix.data[4]]);
            self.cu_budget = u64::from(units);
        }
        self
    }

    /// Enable post-state rent-state transition enforcement (off by default — see field doc).
    pub fn with_rent_state_enforcement(mut self, enforce: bool) -> Self {
        self.enforce_rent_state = enforce;
        self
    }

    /// Register an ELF binary for `program_id`. Subsequent calls overwrite.
    pub fn add_program(&mut self, program_id: &Pubkey, elf: &[u8]) -> &mut Self {
        self.programs.insert(*program_id, elf.to_vec());
        self
    }

    /// Run a single top-level instruction (Mollusk API shape for drop-in differential testing).
    pub fn process_instruction(
        &self,
        instruction: &Instruction,
        accounts: &[(Pubkey, AccountSharedData)],
    ) -> Result<InstructionResult, SvmError> {
        // Top-level precompile dispatch: agave routes ed25519/secp256k1/secp256r1 before BPF VM.
        // We call `SVM.Native.Precompiles.dispatch` via FFI directly — no account serialization.
        // Precompiles never mutate accounts or produce logs/return_data.
        if is_precompile(&instruction.program_id) {
            let pid_bytes = instruction.program_id.to_bytes();
            let (r0, cu) = crate::run_precompile(&pid_bytes, &instruction.data)
                .map_err(SvmError::InternalWireFormat)?;
            let program_result = ProgramResult::from_bpf_r0(r0);
            return Ok(InstructionResult {
                program_result,
                compute_units_consumed: cu,
                logs: vec![],
                return_data: vec![],
                resulting_accounts: accounts.to_vec(),
                poststate_violation: None,
            });
        }

        let elf = self.programs.get(&instruction.program_id)
            .ok_or_else(|| SvmError::UnknownProgram(instruction.program_id))?;

        // Sysvar read-only enforcement: agave's loader rejects writable sysvar accounts.
        // We mirror by inspecting `ix.accounts` before serializing
        // (cheaper than catching after exec).
        if let Some(_bad) = ix_accounts_writable_sysvar(instruction) {
            return Ok(InstructionResult {
                program_result: ProgramResult::Failure {
                    exit_code: ERR_INVALID_POSTSTATE,
                },
                compute_units_consumed: 0,
                logs: vec![],
                return_data: vec![],
                resulting_accounts: accounts.to_vec(),
                poststate_violation: None, // pre-exec loader rejection; VM never ran
            });
        }

        // Instruction-ordered account list for post-state validation (pre/post must align positionally)
        // and `resulting_accounts`. Caller-supplied `accounts` is a lookup source only.
        let canonical_accounts = accounts_for_instruction(instruction, accounts)?;

        let input = serialize_parameters(instruction, accounts, &instruction.program_id)?;

        // CPI registry: all OTHER registered programs (main program excluded — Lean doesn't need it twice).
        // Always pass program_id so the Lean runner can derive PDAs for `invoke_signed`.
        let registry_entries: Vec<(&[u8; 32], &[u8])> = self.programs
            .iter()
            .filter(|(pid, _)| **pid != instruction.program_id)
            .map(|(pid, elf)| (pid.as_array(), elf.as_slice()))
            .collect();
        let registry_blob = if registry_entries.is_empty() {
            Vec::new()
        } else {
            crate::encode_registry(&registry_entries)
        };
        let raw = crate::run_buffer_with_registry_and_pid(
            elf,
            &input,
            &registry_blob,
            instruction.program_id.as_array(),
            self.cu_budget,
        )
        .map_err(|e| match e {
            crate::DecodeError::ElfDecodeFailed => SvmError::ElfDecodeFailed,
            other => SvmError::InternalWireFormat(other),
        })?;

        let program_result = match raw.outcome {
            ExitOutcome::OutOfBudget => ProgramResult::OutOfBudget,
            ExitOutcome::Halted(n) => ProgramResult::from_bpf_r0(n),
            // VM fault is distinct from a program error (audit M14/L1); agave → `ProgramFailedToComplete`.
            ExitOutcome::Faulted(n) => ProgramResult::VmFault { sentinel: n },
        };

        let resulting_accounts = if accounts.is_empty() && instruction.accounts.is_empty() {
            Vec::new()
        } else {
            deserialize_account_writes(&raw.modified_input, instruction, accounts)
                .map_err(SvmError::BufferParse)?
        };

        // Post-instruction soundness validation (success only — failures are rolled back at the harness).
        // Any violation downgrades to `Failure { ERR_INVALID_POSTSTATE }`.
        let (program_result, poststate_violation) =
            if matches!(program_result, ProgramResult::Success) {
                match validate_post_state(instruction, &canonical_accounts, &resulting_accounts,
                                           self.enforce_rent_state) {
                    Ok(()) => (program_result, None),
                    Err(e) => (ProgramResult::Failure { exit_code: ERR_INVALID_POSTSTATE }, Some(e)),
                }
            } else {
                (program_result, None)
            };

        Ok(InstructionResult {
            program_result,
            compute_units_consumed: raw.compute_units_consumed,
            logs: raw.logs,
            return_data: raw.return_data,
            resulting_accounts,
            poststate_violation,
        })
    }

}

/// Sentinel for "Success but post-state invariant violated" (M13). Collapses agave's
/// `ExternalAccountDataModified`/`UnbalancedInstruction`/etc. to a single u64 sentinel.
/// `executable`/`rent_epoch` not validated — inherited from pre-state by construction.
pub const ERR_INVALID_POSTSTATE: u64 = 0xFFFFFFFFFFFFFFFB;

/// Build the instruction-ordered account list for serialization, post-state validation,
/// and `resulting_accounts`. Duplicate `AccountMeta`s produce duplicate entries matching
/// `deserialize_account_writes` output so pre/post align positionally in `validate_post_state`.
fn accounts_for_instruction(
    instruction: &Instruction,
    accounts: &[(Pubkey, AccountSharedData)],
) -> Result<Vec<(Pubkey, AccountSharedData)>, SerializeError> {
    let mut out = Vec::with_capacity(instruction.accounts.len());
    for meta in &instruction.accounts {
        let acct = accounts.iter()
            .find(|(k, _)| *k == meta.pubkey)
            .map(|(_, a)| a.clone())
            .ok_or(SerializeError::MissingAccount(meta.pubkey))?;
        out.push((meta.pubkey, acct));
    }
    Ok(out)
}

fn is_sysvar_id(pk: &Pubkey) -> bool {
    use solana_sdk_ids::sysvar;
    *pk == sysvar::clock::ID
        || *pk == sysvar::epoch_rewards::ID
        || *pk == sysvar::epoch_schedule::ID
        || *pk == sysvar::fees::ID
        || *pk == sysvar::instructions::ID
        || *pk == sysvar::last_restart_slot::ID
        || *pk == sysvar::recent_blockhashes::ID
        || *pk == sysvar::rent::ID
        || *pk == sysvar::rewards::ID
        || *pk == sysvar::slot_hashes::ID
        || *pk == sysvar::slot_history::ID
        || *pk == sysvar::stake_history::ID
}

fn ix_accounts_writable_sysvar(instruction: &Instruction) -> Option<Pubkey> {
    instruction.accounts.iter()
        .find(|m| m.is_writable && is_sysvar_id(&m.pubkey))
        .map(|m| m.pubkey)
}

/// Whether `pid` is one of the three sig-verify precompile pubkeys (ed25519/secp256k1/secp256r1).
fn is_precompile(pid: &Pubkey) -> bool {
    *pid == solana_sdk_ids::ed25519_program::ID
        || *pid == solana_sdk_ids::secp256k1_program::ID
        || *pid == solana_sdk_ids::secp256r1_program::ID
}

/// Per-account / cross-account invariants agave enforces at instruction exit; all failures → `ERR_INVALID_POSTSTATE`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PostStateError {
    /// A read-only account's lamports, data, or owner changed.
    ReadOnlyAccountModified(Pubkey),
    /// Lamport sum across listed accounts changed (mint or burn).
    LamportConservationViolated { pre_sum: u128, post_sum: u128 },
    /// Account data grew past `pre_len + MAX_PERMITTED_DATA_INCREASE`.
    DataLengthOverflow { pubkey: Pubkey, pre: usize, post: usize },
    /// Disallowed rent-state transition (mirrors `InsufficientFundsForRent`).
    RentStateTransitionInvalid {
        pubkey: Pubkey,
        pre_lamports: u64,
        pre_data_size: usize,
        post_lamports: u64,
        post_data_size: usize,
    },
}

/// Default Rent: `lamports_per_byte_year(3480) * exemption_threshold(2.0) = 6960` per byte.
const RENT_LAMPORTS_PER_BYTE_EXEMPT: u64 = 6960;

/// Fixed per-account overhead (`ACCOUNT_STORAGE_OVERHEAD`) included in the rent-exempt minimum.
const ACCOUNT_STORAGE_OVERHEAD: u64 = 128;

/// `Rent::minimum_balance(data_len)` with default params: `(128 + data_len) * 6960`.
fn rent_minimum_balance(data_len: usize) -> u64 {
    let bytes = data_len as u64;
    ACCOUNT_STORAGE_OVERHEAD
        .saturating_add(bytes)
        .saturating_mul(RENT_LAMPORTS_PER_BYTE_EXEMPT)
}

/// Rent state of a Solana account (mirrors `solana-svm::rent_calculator::RentState`).
#[derive(Debug, PartialEq, Eq)]
enum RentState {
    Uninitialized,  // lamports == 0
    RentPaying { lamports: u64, data_size: usize },  // 0 < lamports < minimum_balance (legacy only)
    RentExempt,     // lamports >= minimum_balance
}

fn get_account_rent_state(lamports: u64, data_size: usize) -> RentState {
    if lamports == 0 {
        RentState::Uninitialized
    } else if lamports >= rent_minimum_balance(data_size) {
        RentState::RentExempt
    } else {
        RentState::RentPaying { lamports, data_size }
    }
}

/// Whether a rent-state transition is allowed (mirrors `solana-svm::rent_calculator::transition_allowed`).
/// To Uninitialized/RentExempt: always OK. To RentPaying: only from RentPaying with same size and no credit.
fn rent_transition_allowed(pre: &RentState, post: &RentState) -> bool {
    match post {
        RentState::Uninitialized | RentState::RentExempt => true,
        RentState::RentPaying { lamports: post_lamports, data_size: post_data_size } => {
            match pre {
                RentState::Uninitialized | RentState::RentExempt => false,
                RentState::RentPaying { lamports: pre_lamports, data_size: pre_data_size } => {
                    post_data_size == pre_data_size && post_lamports <= pre_lamports
                }
            }
        }
    }
}

fn validate_post_state(
    instruction: &Instruction,
    pre: &[(Pubkey, AccountSharedData)],
    post: &[(Pubkey, AccountSharedData)],
    enforce_rent_state: bool,
) -> Result<(), PostStateError> {
    use solana_account::ReadableAccount;

    const MAX_PERMITTED_DATA_INCREASE: usize = 10240;

    // Lamport conservation across the per-call account list. Programs can redistribute but not mint/burn.
    // System's create_account/transfer are redistributions, so this holds even there.
    let pre_sum: u128  = pre.iter().map(|(_, a)| u128::from(a.lamports())).sum();
    let post_sum: u128 = post.iter().map(|(_, a)| u128::from(a.lamports())).sum();
    if pre_sum != post_sum {
        return Err(PostStateError::LamportConservationViolated { pre_sum, post_sum });
    }

    // Per-account checks. `pre` from `accounts_for_instruction` + `post` from
    // `deserialize_account_writes` are both in `instruction.accounts` order; zip pairs them.
    for ((_, pre_acct), (post_pk, post_acct)) in pre.iter().zip(post.iter()) {
        let pk = *post_pk;

        // `executable`/`rent_epoch` inherited from pre-state by construction — nothing to compare.
        // Read-only enforcement: `is_writable=false` → lamports/data/owner must be unchanged.
        let meta_writable = instruction.accounts.iter()
            .find(|m| m.pubkey == pk)
            .map(|m| m.is_writable)
            .unwrap_or(true); // not in ix.accounts → unconstrained
        if !meta_writable {
            if pre_acct.lamports() != post_acct.lamports()
                || pre_acct.data() != post_acct.data()
                || pre_acct.owner() != post_acct.owner()
            {
                return Err(PostStateError::ReadOnlyAccountModified(pk));
            }
        }

        // Data-growth bound.
        let pre_len  = pre_acct.data().len();
        let post_len = post_acct.data().len();
        if post_len > pre_len + MAX_PERMITTED_DATA_INCREASE {
            return Err(PostStateError::DataLengthOverflow {
                pubkey: pk, pre: pre_len, post: post_len,
            });
        }

        // Rent-state transition enforcement (off by default — see `with_rent_state_enforcement`).
        // Incinerator pubkey is exempt.
        if enforce_rent_state && pk != solana_sdk_ids::incinerator::ID {
            let pre_state  = get_account_rent_state(pre_acct.lamports(),  pre_len);
            let post_state = get_account_rent_state(post_acct.lamports(), post_len);
            if !rent_transition_allowed(&pre_state, &post_state) {
                return Err(PostStateError::RentStateTransitionInvalid {
                    pubkey: pk,
                    pre_lamports: pre_acct.lamports(),
                    pre_data_size: pre_len,
                    post_lamports: post_acct.lamports(),
                    post_data_size: post_len,
                });
            }
        }
    }

    Ok(())
}

#[cfg(test)]
mod rent_state_tests {
    //! Unit tests for `rent_minimum_balance`/`get_account_rent_state`/`rent_transition_allowed`.
    use super::*;

    #[test]
    fn minimum_balance_matches_agave_default_rent() {
        // Default Rent: (128 + n) * 6960.
        assert_eq!(rent_minimum_balance(0),   128 * 6960);          //   891_360
        assert_eq!(rent_minimum_balance(1),   129 * 6960);          //   898_320
        assert_eq!(rent_minimum_balance(165), (128 + 165) * 6960);  // 2_039_280 — SPL Token Mint
        assert_eq!(rent_minimum_balance(200), (128 + 200) * 6960);  // 2_282_880 — Stake account
    }

    #[test]
    fn rent_state_classification() {
        // Uninitialized when lamports = 0 regardless of data size.
        assert_eq!(get_account_rent_state(0, 0),   RentState::Uninitialized);
        assert_eq!(get_account_rent_state(0, 200), RentState::Uninitialized);

        // RentExempt when lamports ≥ minimum_balance.
        let exempt = rent_minimum_balance(200);
        assert_eq!(get_account_rent_state(exempt,     200), RentState::RentExempt);
        assert_eq!(get_account_rent_state(exempt + 1, 200), RentState::RentExempt);

        // RentPaying when 0 < lamports < minimum_balance.
        let half = exempt / 2;
        assert_eq!(
            get_account_rent_state(half, 200),
            RentState::RentPaying { lamports: half, data_size: 200 },
        );
    }

    #[test]
    fn transition_allowed_uninit_to_exempt_ok() {
        let pre  = RentState::Uninitialized;
        let post = RentState::RentExempt;
        assert!(rent_transition_allowed(&pre, &post));
    }

    #[test]
    fn transition_allowed_uninit_to_paying_rejected() {
        let pre  = RentState::Uninitialized;
        let post = RentState::RentPaying { lamports: 100, data_size: 200 };
        assert!(!rent_transition_allowed(&pre, &post));
    }

    #[test]
    fn transition_allowed_paying_to_paying_same_size_no_credit_ok() {
        let pre  = RentState::RentPaying { lamports: 1000, data_size: 200 };
        let post = RentState::RentPaying { lamports: 500,  data_size: 200 };
        assert!(rent_transition_allowed(&pre, &post));
    }

    #[test]
    fn transition_allowed_paying_to_paying_credited_rejected() {
        // Crediting a rent-paying account is forbidden (would "donate" lamports below exemption threshold).
        let pre  = RentState::RentPaying { lamports: 500,  data_size: 200 };
        let post = RentState::RentPaying { lamports: 1000, data_size: 200 };
        assert!(!rent_transition_allowed(&pre, &post));
    }

    #[test]
    fn transition_allowed_paying_to_paying_resized_rejected() {
        // Resizing while rent-paying is forbidden.
        let pre  = RentState::RentPaying { lamports: 1000, data_size: 200 };
        let post = RentState::RentPaying { lamports: 1000, data_size: 100 };
        assert!(!rent_transition_allowed(&pre, &post));
    }

    /// Construct a writable `AccountMeta` for `pk`.
    fn writable_meta(pk: Pubkey) -> solana_instruction::AccountMeta {
        solana_instruction::AccountMeta { pubkey: pk, is_signer: false, is_writable: true }
    }

    /// Build a `(pk, AccountSharedData)` pair with given lamports + data size.
    fn acct(pk: Pubkey, lamports: u64, data_size: usize) -> (Pubkey, AccountSharedData) {
        use solana_account::Account;
        let acct = AccountSharedData::from(Account {
            lamports,
            data: vec![0u8; data_size],
            owner: Pubkey::default(),
            executable: false,
            rent_epoch: 0,
        });
        (pk, acct)
    }

    /// Seed-based test pubkey — stable across runs.
    fn test_pk(seed: u8) -> Pubkey {
        let mut b = [0u8; 32];
        b[0] = seed;
        Pubkey::new_from_array(b)
    }

    #[test]
    fn validate_post_state_off_admits_rent_violating_transition() {
        // B goes Uninitialized → RentPaying (10_000 < minimum_balance(200) ≈ 2.28M); off → OK.
        let a = test_pk(1);
        let b = test_pk(2);
        let ix = Instruction {
            program_id: test_pk(99),
            accounts: vec![writable_meta(a), writable_meta(b)],
            data: vec![],
        };
        let pre  = vec![acct(a, 1_010_000, 0), acct(b, 0, 200)];
        let post = vec![acct(a, 1_000_000, 0), acct(b, 10_000, 200)];
        assert!(validate_post_state(&ix, &pre, &post, false).is_ok());
    }

    #[test]
    fn validate_post_state_on_rejects_uninit_to_paying() {
        let a = test_pk(1);
        let b = test_pk(2);
        let ix = Instruction {
            program_id: test_pk(99),
            accounts: vec![writable_meta(a), writable_meta(b)],
            data: vec![],
        };
        let pre  = vec![acct(a, 1_010_000, 0), acct(b, 0, 200)];
        let post = vec![acct(a, 1_000_000, 0), acct(b, 10_000, 200)];
        match validate_post_state(&ix, &pre, &post, true) {
            Err(PostStateError::RentStateTransitionInvalid { pubkey, .. }) => {
                assert_eq!(pubkey, b);
            }
            other => panic!("expected RentStateTransitionInvalid for {b}, got {other:?}"),
        }
    }

    #[test]
    fn validate_post_state_on_admits_uninit_to_exempt() {
        let a = test_pk(1);
        let b = test_pk(2);
        let ix = Instruction {
            program_id: test_pk(99),
            accounts: vec![writable_meta(a), writable_meta(b)],
            data: vec![],
        };
        // `a` stays above min(0)=891_360 post-debit; `b` reaches min(200)=2_282_880 → RentExempt.
        let pre  = vec![acct(a, 5_000_000, 0), acct(b, 0, 200)];
        let post = vec![acct(a, 2_717_120, 0), acct(b, 2_282_880, 200)];
        assert!(validate_post_state(&ix, &pre, &post, true).is_ok());
    }

    #[test]
    fn validate_post_state_on_exempts_incinerator() {
        // Incinerator is the global lamport-burn sink; rent-state check is skipped for it.
        let a = test_pk(1);
        let inc = solana_sdk_ids::incinerator::ID;
        let ix = Instruction {
            program_id: test_pk(99),
            accounts: vec![writable_meta(a), writable_meta(inc)],
            data: vec![],
        };
        let pre  = vec![acct(a, 1_010_000, 0), acct(inc, 0, 200)];
        let post = vec![acct(a, 1_000_000, 0), acct(inc, 10_000, 200)];
        // Same Uninitialized → RentPaying shape as the rejection
        // test, but on incinerator. Must pass.
        assert!(validate_post_state(&ix, &pre, &post, true).is_ok());
    }

    #[test]
    fn transition_allowed_to_uninit_always_ok() {
        // Closing the account (drain to 0) is always allowed.
        let pre  = RentState::RentExempt;
        let post = RentState::Uninitialized;
        assert!(rent_transition_allowed(&pre, &post));
    }

    #[test]
    fn writable_real_sysvar_is_flagged() {
        let ix = Instruction {
            program_id: test_pk(99),
            accounts: vec![writable_meta(solana_sdk_ids::sysvar::clock::ID)],
            data: vec![],
        };
        assert_eq!(
            ix_accounts_writable_sysvar(&ix),
            Some(solana_sdk_ids::sysvar::clock::ID),
        );
    }

    #[test]
    fn readonly_real_sysvar_is_not_flagged() {
        let meta = solana_instruction::AccountMeta {
            pubkey: solana_sdk_ids::sysvar::rent::ID,
            is_signer: false,
            is_writable: false,
        };
        let ix = Instruction {
            program_id: test_pk(99),
            accounts: vec![meta],
            data: vec![],
        };
        assert_eq!(ix_accounts_writable_sysvar(&ix), None);
    }

    #[test]
    fn accounts_for_instruction_reorders_to_instruction_order() {
        // Caller [B, A], instruction [A, B] → canonical [A, B].
        let a = test_pk(1);
        let b = test_pk(2);
        let ix = Instruction {
            program_id: test_pk(99),
            accounts: vec![writable_meta(a), writable_meta(b)],
            data: vec![],
        };
        let shuffled = vec![acct(b, 200, 0), acct(a, 100, 0)];
        let canonical = accounts_for_instruction(&ix, &shuffled).expect("ok");
        assert_eq!(canonical.len(), 2);
        assert_eq!(canonical[0].0, a);
        assert_eq!(canonical[1].0, b);
        use solana_account::ReadableAccount;
        assert_eq!(canonical[0].1.lamports(), 100);
        assert_eq!(canonical[1].1.lamports(), 200);
    }

    #[test]
    fn accounts_for_instruction_ignores_extras() {
        // Caller passes [A, B, C] but instruction only references [B].
        // Canonical must contain only B.
        let a = test_pk(1);
        let b = test_pk(2);
        let c = test_pk(3);
        let ix = Instruction {
            program_id: test_pk(99),
            accounts: vec![writable_meta(b)],
            data: vec![],
        };
        let supplied = vec![acct(a, 100, 0), acct(b, 200, 0), acct(c, 300, 0)];
        let canonical = accounts_for_instruction(&ix, &supplied).expect("ok");
        assert_eq!(canonical.len(), 1);
        assert_eq!(canonical[0].0, b);
    }

    #[test]
    fn accounts_for_instruction_clones_duplicates() {
        // Same pubkey twice in instruction.accounts → two entries (matching `deserialize_account_writes`).
        let a = test_pk(1);
        let ix = Instruction {
            program_id: test_pk(99),
            accounts: vec![writable_meta(a), writable_meta(a)],
            data: vec![],
        };
        let supplied = vec![acct(a, 500, 0)];
        let canonical = accounts_for_instruction(&ix, &supplied).expect("ok");
        assert_eq!(canonical.len(), 2);
        assert_eq!(canonical[0].0, a);
        assert_eq!(canonical[1].0, a);
    }

    #[test]
    fn accounts_for_instruction_missing_pubkey_errors() {
        let a = test_pk(1);
        let b = test_pk(2);
        let ix = Instruction {
            program_id: test_pk(99),
            accounts: vec![writable_meta(a), writable_meta(b)],
            data: vec![],
        };
        // b is missing from the supplied slice.
        let supplied = vec![acct(a, 100, 0)];
        match accounts_for_instruction(&ix, &supplied) {
            Err(SerializeError::MissingAccount(pk)) => assert_eq!(pk, b),
            other => panic!("expected MissingAccount({b}), got {other:?}"),
        }
    }

    #[test]
    fn fake_sysvar_prefix_pubkey_is_not_flagged() {
        // Old prefix-based detector flagged [0x06, 0xa7, 0xd5, 0x17] prefix; explicit-list must not.
        let mut bytes = [0u8; 32];
        bytes[0] = 0x06; bytes[1] = 0xa7; bytes[2] = 0xd5; bytes[3] = 0x17;
        let fake = Pubkey::new_from_array(bytes);
        let ix = Instruction {
            program_id: test_pk(99),
            accounts: vec![writable_meta(fake)],
            data: vec![],
        };
        assert_eq!(ix_accounts_writable_sysvar(&ix), None);
    }
}
