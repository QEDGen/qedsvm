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
    /// Whether to enforce the rent-state transition check from
    /// `solana-svm::rent_calculator::check_rent_state` at instruction
    /// exit (an account can't move from Uninitialized/RentExempt into
    /// RentPaying, and a RentPaying account can't grow or be
    /// credited).
    ///
    /// Default: **off**. Agave applies this check at the *transaction*
    /// layer (`transaction_processor::execute_loaded_transaction`),
    /// not per-instruction; mollusk's harness — which runs per-
    /// instruction like us — bypasses it. Enabling here while
    /// diff-testing against mollusk would surface false divergences
    /// on fixtures that aren't rent-exempt by design.
    ///
    /// Enable when running formal-svm as a transaction-level oracle
    /// (rather than the diff-mollusk per-instruction comparator).
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

    /// Lower or raise the per-instruction CU budget. Default is
    /// `DEFAULT_CU_BUDGET = 200_000`.
    pub fn with_cu_budget(mut self, cu_budget: u64) -> Self {
        self.cu_budget = cu_budget;
        self
    }

    /// Transaction-level pre-flight equivalent: scan a transaction's
    /// instruction list for a `ComputeBudgetInstruction::SetComputeUnitLimit`
    /// and set [`Self::cu_budget`] from its value.
    ///
    /// formal-svm models per-instruction execution, not the full
    /// transaction pipeline. Agave's `ComputeBudgetProcessor` does
    /// this scan at the transaction level (before invoking each
    /// top-level instruction); callers wanting that behavior can run
    /// this helper themselves over the txn's `ix` list and pipe the
    /// result into [`Self::with_cu_budget`]. We expose it as a
    /// builder for ergonomics.
    ///
    /// Wire format: ComputeBudget's `SetComputeUnitLimit` is
    /// discriminant `2` followed by a u32 LE value. Other variants
    /// (`RequestUnits` legacy / heap frame / unit price / loaded-
    /// accounts-data limit) don't affect the per-instruction CU cap
    /// and are ignored. If multiple `SetComputeUnitLimit` are
    /// present, the *last* wins (matches agave's behavior of
    /// overwriting the running cap as it iterates).
    ///
    /// Returns `Self` unchanged if no `SetComputeUnitLimit` is found.
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

    /// Enable the post-state rent-state transition check
    /// (`solana-svm::rent_calculator::check_rent_state` equivalent).
    /// Off by default — see field-level comment for the rationale.
    pub fn with_rent_state_enforcement(mut self, enforce: bool) -> Self {
        self.enforce_rent_state = enforce;
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
        // Top-level precompile dispatch. Agave's runtime detects
        // ed25519 / secp256k1 / secp256r1 program-ids before
        // invoking the BPF VM and routes to a Rust `verify()` closure.
        // The Lean spec (`Svm.Native.Precompiles.dispatch`) is the
        // source of truth; we call it directly via FFI without
        // serializing parameters or running the interpreter.
        //
        // Precompiles never mutate accounts and never produce logs or
        // return data, so the resulting state mirrors the input
        // verbatim.
        if is_precompile(&instruction.program_id) {
            let pid_bytes = instruction.program_id.to_bytes();
            let (r0, cu) = crate::run_precompile(&pid_bytes, &instruction.data);
            let program_result = if r0 == 0 {
                ProgramResult::Success
            } else {
                ProgramResult::Failure { exit_code: r0 }
            };
            return Ok(InstructionResult {
                program_result,
                compute_units_consumed: cu,
                logs: vec![],
                return_data: vec![],
                resulting_accounts: accounts.to_vec(),
            });
        }

        let elf = self.programs.get(&instruction.program_id)
            .ok_or_else(|| SvmError::UnknownProgram(instruction.program_id))?;

        // Sysvar read-only enforcement. Agave's loader rejects an
        // instruction that marks a known sysvar account as writable.
        // We mirror by inspecting `ix.accounts` *before* serializing
        // (cheaper than catching after exec). Failures surface as
        // ProgramResult::Failure with the post-state sentinel.
        if let Some(_bad) = ix_accounts_writable_sysvar(instruction) {
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
            match validate_post_state(instruction, accounts, &resulting_accounts,
                                       self.enforce_rent_state) {
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

/// Whether `pid` is one of the three sig-verify precompile pubkeys
/// (`Ed25519SigVerify1111…`, `KeccakSecp256k11111…`,
/// `Secp256r1SigVerify1111…`). agave's runtime routes these without
/// entering the BPF VM; we mirror by detecting them in
/// `process_instruction` and calling
/// `Svm.Native.Precompiles.dispatch` via FFI.
fn is_precompile(pid: &Pubkey) -> bool {
    *pid == solana_sdk_ids::ed25519_program::ID
        || *pid == solana_sdk_ids::secp256k1_program::ID
        || *pid == solana_sdk_ids::secp256r1_program::ID
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
    /// Account transitioned to a disallowed rent state. Mirrors
    /// agave's `TransactionError::InsufficientFundsForRent`.
    RentStateTransitionInvalid {
        pubkey: Pubkey,
        pre_lamports: u64,
        pre_data_size: usize,
        post_lamports: u64,
        post_data_size: usize,
    },
}

/// Default Rent's `lamports_per_byte_year * exemption_threshold` —
/// the canonical mainnet value. Default Rent is
/// `lamports_per_byte_year = 3480`, `exemption_threshold = 2.0`, so
/// the product is `3480 * 2 = 6960` lamports per byte per
/// exemption window.
const RENT_LAMPORTS_PER_BYTE_EXEMPT: u64 = 6960;

/// `ACCOUNT_STORAGE_OVERHEAD` — fixed per-account overhead included
/// in the rent-exempt minimum.
const ACCOUNT_STORAGE_OVERHEAD: u64 = 128;

/// `Rent::minimum_balance(data_len)` with the default Rent
/// parameters. Mirrors `solana-rent`'s formula:
/// `(ACCOUNT_STORAGE_OVERHEAD + data_len) * lamports_per_byte_exempt`.
fn rent_minimum_balance(data_len: usize) -> u64 {
    let bytes = data_len as u64;
    ACCOUNT_STORAGE_OVERHEAD
        .saturating_add(bytes)
        .saturating_mul(RENT_LAMPORTS_PER_BYTE_EXEMPT)
}

/// Rent state of a Solana account. Mirrors
/// `solana-svm::rent_calculator::RentState`. -/
#[derive(Debug, PartialEq, Eq)]
enum RentState {
    /// `account.lamports == 0` — account doesn't exist for rent
    /// purposes.
    Uninitialized,
    /// `0 < lamports < minimum_balance`. Rent-paying accounts are
    /// only allowed in legacy form; modern accounts must be
    /// rent-exempt at instruction exit.
    RentPaying { lamports: u64, data_size: usize },
    /// `lamports >= minimum_balance`. The canonical state.
    RentExempt,
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

/// Whether a transition from `pre` to `post` rent state is allowed.
/// Mirrors `solana-svm::rent_calculator::transition_allowed`.
///
/// - Transitioning *to* `Uninitialized` or `RentExempt` is always
///   allowed (you can always close an account or top it up to
///   exempt).
/// - Transitioning *to* `RentPaying` is allowed only when the pre
///   was already `RentPaying` with the *same* data size and the
///   account wasn't credited (post lamports ≤ pre lamports).
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

        // Rent-state transition enforcement. Off by default — see
        // `Svm::with_rent_state_enforcement` for the rationale.
        // Mirrors agave's `solana-svm::rent_calculator::check_rent_state`
        // applied per account at instruction exit. The incinerator
        // pubkey is exempt.
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
    //! Unit tests for the rent-state machinery
    //! (`rent_minimum_balance`, `get_account_rent_state`,
    //! `rent_transition_allowed`). These run regardless of the
    //! `diff-mollusk` feature gate — the math itself is harness-
    //! independent.
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
        // Crediting a rent-paying account is forbidden (would let
        // someone "donate" lamports into a state below rent exemption).
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

    /// Distinct pubkey for test setup. Seed-based so values stay
    /// stable across runs.
    fn test_pk(seed: u8) -> Pubkey {
        let mut b = [0u8; 32];
        b[0] = seed;
        Pubkey::new_from_array(b)
    }

    #[test]
    fn validate_post_state_off_admits_rent_violating_transition() {
        // Pre/post conserve lamports but B goes Uninitialized →
        // RentPaying (10_000 < minimum_balance(200) ≈ 2.28M).
        let a = test_pk(1);
        let b = test_pk(2);
        let ix = Instruction {
            program_id: test_pk(99),
            accounts: vec![writable_meta(a), writable_meta(b)],
            data: vec![],
        };
        let pre  = vec![acct(a, 1_010_000, 0), acct(b, 0, 200)];
        let post = vec![acct(a, 1_000_000, 0), acct(b, 10_000, 200)];
        // Enforcement off: the rent-state machinery is bypassed
        // entirely. All other invariants (executable/rent_epoch
        // immutability, lamport conservation, data-length growth, RO
        // writes) still run, but they're satisfied here.
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
        // Crediting an uninitialized account up to rent-exempt is OK.
        let a = test_pk(1);
        let b = test_pk(2);
        let ix = Instruction {
            program_id: test_pk(99),
            accounts: vec![writable_meta(a), writable_meta(b)],
            data: vec![],
        };
        // `a` must stay above its own exempt min (891_360 for size 0)
        // post-debit, otherwise `a` itself transitions RentExempt →
        // RentPaying (also disallowed). Give `a` enough headroom.
        let pre  = vec![acct(a, 5_000_000, 0), acct(b, 0, 200)];
        let post = vec![acct(a, 2_717_120, 0), acct(b, 2_282_880, 200)];
        // 2_282_880 = (128 + 200) * 6960 = minimum_balance(200) → RentExempt.
        // 2_717_120 ≥ minimum_balance(0) = 891_360 → still RentExempt.
        assert!(validate_post_state(&ix, &pre, &post, true).is_ok());
    }

    #[test]
    fn validate_post_state_on_exempts_incinerator() {
        // The incinerator pubkey is the global lamport-burn sink.
        // Its rent state can be anything; agave (and we) skip the
        // transition check for it.
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
}
