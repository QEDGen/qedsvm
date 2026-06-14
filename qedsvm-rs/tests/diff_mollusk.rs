//! Cross-engine differential test: same instruction through
//! `qedsvm::Svm` and `mollusk_svm::Mollusk`, with byte-level
//! assertions on every observable output.
//!
//! The fixture `tests/fixtures/noop.so` is a real
//! `cargo-build-sbf`-produced SBF ELF whose `.text` is exactly:
//!
//!     mov64 r0, 0    ; b7 00 00 00 00 00 00 00
//!     exit           ; 95 00 00 00 00 00 00 00
//!
//! That's the minimum cargo-build-sbf will emit — a hand-written
//! `extern "C" fn entrypoint(_input: *mut u8) -> u64 { 0 }` — and
//! it's still wrapped in a real Solana ELF (program headers,
//! `.dynsym`, `.shstrtab`, etc.) that agave's loader accepts.
//!
//! Build / rebuild:
//!     cd tests/fixtures/noop_src && cargo-build-sbf
//!     cp target/deploy/qedsvm_noop.so ../noop.so
//!
//! Run:  cargo test --features diff-mollusk
//!
//! Diff target & known limits (M14):
//!   * Reference engine: `mollusk-svm` over agave with
//!     `FeatureSet::all_enabled()` (a future/pre-release feature set,
//!     not the mainnet-active gate set). Fixtures here therefore assert
//!     the model matches all-features-on agave, not today's cluster.
//!   * The Lean semantics are linked from `.lake/build`; this harness
//!     does NOT run `lake build`. Run `lake build` before `cargo test`
//!     (CI does, before this suite) or the linked dylib is stale. The
//!     buildscript now emits `rerun-if-changed` on the linked Lean
//!     dylibs so a fresh `lake build` always forces a relink.
//!   * Precompiles can't be diff-tested against agave (dependency
//!     conflict) and use sibling crates asserted-equivalent in comments;
//!     crypto syscalls are same-crate-vs-same-crate (no independent
//!     signal). Cross-engine error-CODE comparison is not yet wired
//!     (our r0 sentinels have no agave `InstructionError` mapping, and
//!     the malicious-path codes diverge by design — see M6/L1); most
//!     fixtures compare Success/Failure axis + account state + (where
//!     deterministic) logs. `assert_no_poststate_backstop` guards the
//!     one masking hazard that matters (M13).

#![cfg(feature = "diff-mollusk")]

use qedsvm::{ProgramResult as FsProgramResult, Svm};
use mollusk_svm::result::ProgramResult as MlProgramResult;
use mollusk_svm::Mollusk;
use solana_account::{Account, AccountSharedData, ReadableAccount};
use solana_instruction::{AccountMeta, Instruction};
use solana_instruction::error::InstructionError;
use solana_pubkey::Pubkey;

const NOOP_SO: &[u8] = include_bytes!("fixtures/noop.so");
const SOLANA_NOOP_SO: &[u8] = include_bytes!("fixtures/solana_noop.so");
/// `cargo-build-sbf` of a program that calls `msg!("hi")` and exits.
/// First fixture that exercises the `sol_log_` syscall + per-syscall
/// CU table (syscall_base_cost = 100 for a 2-byte message).
const LOGGER_SO: &[u8] = include_bytes!("fixtures/logger.so");
/// `cargo-build-sbf` of a program that reads a u64 from
/// `accounts[0].data[0..8]`, adds 1, writes it back, returns Ok.
/// First fixture that mutates account data — the cross-engine diff
/// verifies our `deserialize_account_writes` actually picks up the
/// program's write, byte-for-byte against mollusk.
const INCREMENTER_SO: &[u8] = include_bytes!("fixtures/incrementer.so");
/// Embedded-bump-allocator demo: reads/commits the heap bump slot at
/// 0x300000000 and writes + reads an allocated block. Exercises the
/// program heap as ordinary memory (no syscall allocator).
const HEAP_ALLOC_SO: &[u8] = include_bytes!("fixtures/heap_alloc.so");
/// Calls `sol_remaining_compute_units()` and writes the returned u64
/// (LE) into accounts[0].data[0..8]. The empirical anchor for H7: the
/// 8-byte cross-engine data equality pins qedsvm's remaining-budget
/// formula against rbpf's real meter.
const REMAINING_CU_SO: &[u8] = include_bytes!("fixtures/remaining_cu.so");
/// Halfword memory ops in one straight line: ldxh (u16 load), stxh
/// (register halfword store), and sth/ST_H_IMM (immediate halfword
/// store) against account 0's data. The only fixture exercising the
/// 16-bit width on the store side.
const HALFWORD_STORE_SO: &[u8] = include_bytes!("fixtures/halfword_store.so");
/// SPL Token program. Real on-chain binary (134 KB, vendored from
/// blueshift-gg/sbpf — see `fixtures/README.md` for provenance).
/// Exercises sysvar getters, deeper syscall surface, and the full
/// `entrypoint!`+`process_instruction` shape of a published program.
const TOKEN_SO: &[u8] = include_bytes!("fixtures/token.so");
/// p-token (pinocchio-based SPL Token reimplementation), release
/// `p-token@v1.0.0-rc.1` from solana-program/token (Apr 2025).
/// Drop-in for `TokenkegQfeZyiN…`, byte-for-byte compatible account
/// layouts with canonical SPL Token. First major mainnet-track
/// program in the harness exercising pinocchio's zero-copy account
/// access pattern (raw pointer casts into the serialized input
/// buffer, no Borsh deserialization). See `fixtures/README.md` for
/// SHA-256 + provenance.
const P_TOKEN_SO: &[u8] = include_bytes!("fixtures/p_token.so");
/// SPL Associated Token Account program (105 KB). Most paths CPI
/// into Token/System; we don't model CPI yet, so we restrict the
/// diff to error paths that fail before CPI.
const ASSOCIATED_TOKEN_SO: &[u8] = include_bytes!("fixtures/associated_token.so");
/// Pinocchio-flavored escrow program (28 KB). Small bare-metal-style
/// program — useful as a sanity check that our ELF loading handles
/// the Pinocchio pattern.
const PINOCCHIO_ESCROW_SO: &[u8] = include_bytes!("fixtures/libupstream_pinocchio_escrow.so");
/// `cargo-build-sbf` of a minimal CPI caller: reads a 32-byte target
/// pubkey from `instruction_data[0..32]` and `invoke()`s it with no
/// accounts and no data. First fixture that exercises the
/// `sol_invoke_signed_c` syscall through real `solana_program::invoke`.
/// Source in `cpi_caller_src/`.
const CPI_CALLER_SO: &[u8] = include_bytes!("fixtures/cpi_caller.so");
/// Like `cpi_caller.so` but forwards its one writable account to the
/// CPI target (Instruction.accounts has 1 entry). Companion to
/// `incrementer.so`: when we register this as the caller and
/// incrementer as the callee, the data byte should get incremented
/// through the CPI write-back path. Source in
/// `cpi_increment_caller_src/`.
const CPI_INCREMENT_CALLER_SO: &[u8] = include_bytes!("fixtures/cpi_increment_caller.so");
/// Forwards TWO writable accounts via `invoke(&ix, &[a, b])` to a
/// target program. Exercises Phase 3-N marshaling: both AccountInfo
/// blocks must serialize into the callee's input region with the
/// correct cumulative offsets, and the per-slot write-back loop must
/// propagate any modifications back through the right pointers.
/// Source in `cpi_two_account_caller_src/`.
const CPI_TWO_ACCOUNT_CALLER_SO: &[u8] = include_bytes!("fixtures/cpi_two_account_caller.so");
/// Loads the address of a `static` (lives in `.rodata`), extracts the
/// upper 32 bits, and writes them as 4-byte instruction `return_data`.
/// Surfaces the `R_BPF_64_Relative`-in-`.text` divergence: agave
/// patches the `lddw` imm by `+= MM_REGION_SIZE` at load time so the
/// upper 32 bits are non-zero; a qedsvm without the matching
/// patch would leave the imm as the raw section VA (upper = 0) and
/// diverge from mollusk on return_data. Source in
/// `rodata_addr_returner_src/`.
const RODATA_ADDR_RETURNER_SO: &[u8] = include_bytes!("fixtures/rodata_addr_returner.so");
/// Calls `sol_curve_multiscalar_mul` (Edwards) with n=1 then n=2 — the
/// M9 CU referee for the `base + incr*(n-1)` formula (the n=1 call
/// charges the bare base). Source in `curve_msm_probe_src/`.
const CURVE_MSM_PROBE_SO: &[u8] = include_bytes!("fixtures/curve_msm_probe.so");
/// CLEAN exit with r0 = 0xFFFFFFFFFFFFFFFD (the model's ERR_ABORT
/// sentinel) — the L1 sentinel-collision experiment. Source in
/// `sentinel_exit_src/`.
const SENTINEL_EXIT_SO: &[u8] = include_bytes!("fixtures/sentinel_exit.so");
/// Calls `sol_try_find_program_address(&[b"vault"], program_id)` and
/// writes the resulting (PDA, bump) as 33-byte return_data. Exercises
/// the per-iteration CU charge for `sol_try_find_program_address`
/// (agave charges 1500 per bump attempt: initial + each failed iter).
/// Source in `pda_finder_src/`.
const PDA_FINDER_SO: &[u8] = include_bytes!("fixtures/pda_finder.so");
/// Dereferences `input.add(0x10000000)` — 256 MiB past the input
/// pointer, well outside any mapped region for a zero-account /
/// zero-data instruction. Surfaces the region-bounds gap: pre-fix
/// qedsvm reads zero silently and returns Success; agave traps
/// with `AccessViolation` and returns Failure. Source in
/// `oob_read_src/`.
const OOB_READ_SO: &[u8] = include_bytes!("fixtures/oob_read.so");
/// Out-of-bounds SYSCALL write (audit H6). Calls `sol_memset_` with a
/// destination 256 MiB past the input pointer; agave's
/// `translate_slice_mut` traps with `AccessViolation`. Pre-fix qedsvm
/// let the syscall write through a region-free `Mem` and returned
/// Success; post-fix `MemOps.execSet`'s `guardWrite` faults. Source in
/// `oob_memset_src/`.
const OOB_MEMSET_SO: &[u8] = include_bytes!("fixtures/oob_memset.so");
/// Out-of-bounds SYSCALL pubkey log (audit H6). Calls `sol_log_pubkey`
/// with a pointer 256 MiB past the input pointer; agave's
/// `translate_type::<Pubkey>` traps the 32-byte read with
/// `AccessViolation`. Pre-fix qedsvm read through a region-free `Mem`
/// and returned Success; post-fix `Logging.execLogPubkey`'s `guardRead`
/// faults. Source in `oob_log_pubkey_src/`.
const OOB_LOG_PUBKEY_SO: &[u8] = include_bytes!("fixtures/oob_log_pubkey.so");
/// Out-of-bounds SYSCALL message log (audit H6). Calls `sol_log_` with a
/// 16-byte message 256 MiB past the input pointer; agave's
/// `translate_slice` traps the read with `AccessViolation`. Pre-fix
/// qedsvm read through a region-free `Mem` and returned Success; post-fix
/// `Logging.execLog`'s `guardRead` faults. Source in `oob_log_src/`.
const OOB_LOG_SO: &[u8] = include_bytes!("fixtures/oob_log.so");
/// Out-of-bounds `sol_log_data` (audit H6, descriptor-array / logging
/// tail). Calls `sol_log_data` with a 1-descriptor array 256 MiB past the
/// input pointer; agave translates the 16-byte descriptor array first and
/// `translate_slice` traps the read with `AccessViolation`. Pre-fix qedsvm
/// read descriptors + slices through a region-free `Mem` and returned
/// Success; post-fix `Logging.execLogData` routes the descriptor array
/// through `guardRead` (and slices through `guardSlices`) and faults.
/// Source in `oob_log_data_src/`.
const OOB_LOG_DATA_SO: &[u8] = include_bytes!("fixtures/oob_log_data.so");
/// Calls `sol_sha256` with a 0-slice input and a 32-byte output buffer
/// 256 MiB past the input pointer. agave's `SyscallSha256` translates the
/// output (`translate_slice_mut`, 32 bytes) before the input, so the
/// out-of-region store traps; post-fix (stage 3a) `Sha256.exec` routes the
/// output through `guardWrite` and faults. Source in `oob_sha256_src/`.
const OOB_SHA256_SO: &[u8] = include_bytes!("fixtures/oob_sha256.so");
/// Calls `sol_sha256` with a VALID (writable, in-region) 32-byte output but a
/// 1-descriptor input array 256 MiB out of region. agave translates the output
/// first (passes), then the descriptor array (out of region → traps); post-fix
/// (stage 3b) `Sha256.exec` routes the input through `guardRead`/`guardSlices`
/// and faults. Source in `oob_sha256_input_src/`.
const OOB_SHA256_INPUT_SO: &[u8] = include_bytes!("fixtures/oob_sha256_input.so");
/// Calls `sol_poseidon` with a VALID 32-byte output but a 1-descriptor input
/// array 256 MiB out of region. agave translates the output first (passes),
/// then the descriptor array (out of region → traps); post-fix (stage 3c)
/// `Poseidon.exec`'s `guardedCommit` routes the input through
/// `guardRead`/`guardSlices` and faults. Source in `oob_poseidon_input_src/`.
const OOB_POSEIDON_INPUT_SO: &[u8] = include_bytes!("fixtures/oob_poseidon_input.so");
/// Calls `sol_get_clock_sysvar` with a 40-byte output buffer 256 MiB out of
/// region. agave translates the output (`translate_type_mut::<Clock>`) and
/// traps; post-fix (stage 4a) `Sysvar.execClock` (via `zeroFillR1`) routes the
/// write through `guardWrite` and faults. Source in `oob_clock_sysvar_src/`.
const OOB_CLOCK_SYSVAR_SO: &[u8] = include_bytes!("fixtures/oob_clock_sysvar.so");
/// Calls `sol_set_return_data` with an 8-byte input slice (<= MAX_RETURN_DATA)
/// 256 MiB out of region. agave checks the length first (passes), then
/// translates the input slice and traps; post-fix (stage 4b) `ReturnData.execSet`
/// routes the input through `guardRead` and faults. Source in
/// `oob_set_return_data_src/`.
const OOB_SET_RETURN_DATA_SO: &[u8] = include_bytes!("fixtures/oob_set_return_data.so");
/// BPF caller that invokes `system_instruction::transfer` between
/// its first two account_infos. Companion fixture for Tier-1 #2
/// (native programs). Source in `system_transfer_caller_src/`.
const SYSTEM_TRANSFER_CALLER_SO: &[u8] =
    include_bytes!("fixtures/system_transfer_caller.so");
/// BPF caller that invokes `system_instruction::create_account` to
/// spawn `accounts[1]` from `accounts[0]`. Companion fixture for the
/// second System variant under Tier-1 #2. Source in
/// `system_create_account_caller_src/`.
const SYSTEM_CREATE_ACCOUNT_CALLER_SO: &[u8] =
    include_bytes!("fixtures/system_create_account_caller.so");
/// BPF caller that chains `Allocate` + `Assign` on one signer
/// account. Exercises both simpler System variants in a single
/// fixture (since each is a strict subset of CreateAccount). Source
/// in `system_allocate_assign_caller_src/`.
const SYSTEM_ALLOCATE_ASSIGN_CALLER_SO: &[u8] =
    include_bytes!("fixtures/system_allocate_assign_caller.so");
/// BPF caller that invokes `system_instruction::create_account_with_seed`.
/// Source in `system_create_account_with_seed_caller_src/`.
const SYSTEM_CREATE_ACCOUNT_WITH_SEED_CALLER_SO: &[u8] =
    include_bytes!("fixtures/system_create_account_with_seed_caller.so");
/// BPF caller that CPIs into the ComputeBudget program. Source in
/// `compute_budget_caller_src/`. Validates dispatch + 150-CU charge
/// for the second native program.
const COMPUTE_BUDGET_CALLER_SO: &[u8] =
    include_bytes!("fixtures/compute_budget_caller.so");
/// Caller for the PDA-signer-seeds prober. Derives a PDA from
/// `b"vault" + caller_id`, then `invoke_signed`s a callee passing the
/// PDA as accounts[1] with is_signer=false. Source in
/// `cpi_signed_pda_caller_src/`.
const CPI_SIGNED_PDA_CALLER_SO: &[u8] =
    include_bytes!("fixtures/cpi_signed_pda_caller.so");
/// Callee for the PDA prober. Writes 0xAA to accounts[0].data[0] if
/// accounts[1].is_signer is true, else 0x55. Source in
/// `cpi_signed_pda_callee_src/`.
const CPI_SIGNED_PDA_CALLEE_SO: &[u8] =
    include_bytes!("fixtures/cpi_signed_pda_callee.so");
/// Caller that invokes a callee and copies its sol_get_return_data
/// output into accounts[0].data. Source in `cpi_get_return_data_caller_src/`.
const CPI_GET_RETURN_DATA_CALLER_SO: &[u8] =
    include_bytes!("fixtures/cpi_get_return_data_caller.so");
/// Callee that sol_set_return_data's a fixed 4-byte payload.
/// Source in `cpi_set_return_data_callee_src/`.
const CPI_SET_RETURN_DATA_CALLEE_SO: &[u8] =
    include_bytes!("fixtures/cpi_set_return_data_callee.so");
/// Caller that invokes a callee, then writes sol_get_return_data's
/// PUBKEY output (the setter's program id) into accounts[0].data[0..32]
/// and the data bytes after it (H7).
/// Source in `cpi_get_return_data_pubkey_src/`.
const CPI_GET_RETURN_DATA_PUBKEY_SO: &[u8] =
    include_bytes!("fixtures/cpi_get_return_data_pubkey.so");
/// Probes the SIMD-0127 `sol_get_sysvar` surface (rent/clock/
/// epoch_schedule/slot_hashes slices, unknown id, length overrun) and
/// dumps every r0 + buffer into accounts[0].data (H7).
/// Source in `sysvar_probe_src/`.
const SYSVAR_PROBE_SO: &[u8] = include_bytes!("fixtures/sysvar_probe.so");
/// Outer layer of a 3-program CPI chain. Forwards accounts[0] through
/// `cpi_increment_caller.so` to `incrementer.so` (depth 2).
/// Source in `cpi_depth_2_outer_src/`.
const CPI_DEPTH_2_OUTER_SO: &[u8] =
    include_bytes!("fixtures/cpi_depth_2_outer.so");

/// Janus slot-height-resolver, devnet-deployed Pinocchio 0.8 binary
/// (`solana program dump --url devnet
/// 3y75gGqFK1KhNF5k1sMy6ydnw6WLcbn1SPRoYbyRkjMj`). Reporter's program
/// from issue #2; used by `janus_slot_height_resolver_initialize_matches_mollusk`
/// to reproduce issue #10 (System Program CreateAccount CPI via
/// `invoke_signed` with a PDA target — the synthetic
/// `system_create_account_cpi_matches_mollusk` covers the non-PDA case).
const JANUS_SLOT_HEIGHT_RESOLVER_SO: &[u8] =
    include_bytes!("fixtures/janus_slot_height_resolver_devnet.so");

fn pid(seed: u64) -> Pubkey {
    let mut b = [0u8; 32];
    b[..8].copy_from_slice(&seed.to_le_bytes());
    Pubkey::from(b)
}

/// M13: the Rust post-state backstop must never fire on a diff fixture.
/// A `Some(_)` means the Lean VM returned `Success` over a post-state
/// agave's invariants forbid (lamport conservation, read-only
/// modification, data-growth, rent) and `validate_post_state` silently
/// downgraded it to `ERR_INVALID_POSTSTATE`. That downgrade can make a
/// Lean-VM soundness bug masquerade as a benign cross-engine
/// `Failure`/`Failure` match, hiding exactly the bug class the diff
/// exists to catch. Asserting `None` proves the VM reproduced agave's
/// invariant itself rather than leaning on the shell to rescue it.
fn assert_no_poststate_backstop(fs_r: &qedsvm::InstructionResult) {
    assert!(
        fs_r.poststate_violation.is_none(),
        "Lean VM relied on the Rust post-state backstop ({:?}); this can mask a \
         model soundness bug behind ERR_INVALID_POSTSTATE",
        fs_r.poststate_violation,
    );
}

/// Cross-engine OUTCOME agreement at the granularity agave observably
/// distinguishes (soundness-audit M14). Before this, the diff tests only
/// asserted "both non-Success" on the fault paths, so the model could
/// report the WRONG outcome class (e.g. a clean exit where agave faults,
/// or the wrong program-error code) undetected.
///
/// agave collapses essentially every VM-level fault to
/// `InstructionError::ProgramFailedToComplete` (mollusk
/// `UnknownError(ProgramFailedToComplete)`) — see the source map in
/// docs/SOUNDNESS_AUDIT_* (M14) — including budget exhaustion
/// (`ExceededMaxInstructions`). So a model `VmFault` / `OutOfBudget`
/// matches that catch-all regardless of WHICH fault it was (the model's
/// finer `sentinel` is diagnostics only). A program-RETURNED error
/// (`ProgramError`, r0 high bits set) compares against mollusk's
/// `Failure(ProgramError)` by the exact code. The by-design divergences
/// (M6/C5 read-only-modified, where the model produces
/// `ERR_READONLY_MODIFIED` and agave a specific account-verification
/// `InstructionError`) are NOT routed here — those tests assert their own
/// expected pair.
fn outcome_matches(fs: &FsProgramResult, ml: &MlProgramResult) -> Result<(), String> {
    use FsProgramResult as F;
    use MlProgramResult as M;
    // agave's catch-all for VM faults + meter exhaustion.
    let is_failed_to_complete =
        |ie: &InstructionError| matches!(ie, InstructionError::ProgramFailedToComplete);
    match (fs, ml) {
        (F::Success, M::Success) => Ok(()),
        (F::VmFault { sentinel }, M::UnknownError(ie)) => {
            if is_failed_to_complete(ie) {
                Ok(())
            } else {
                Err(format!(
                    "model VmFault({}) but mollusk InstructionError {ie:?} \
                     (not the ProgramFailedToComplete catch-all)",
                    qedsvm::vm_fault_name(*sentinel)))
            }
        }
        (F::OutOfBudget, M::UnknownError(ie)) => {
            if is_failed_to_complete(ie) {
                Ok(())
            } else {
                Err(format!("model OutOfBudget but mollusk InstructionError {ie:?}"))
            }
        }
        (F::ProgramError(pe), M::Failure(mpe)) => {
            if pe == mpe { Ok(()) }
            else { Err(format!("ProgramError diverged: model {pe:?} mollusk {mpe:?}")) }
        }
        _ => Err(format!("outcome class diverged: model {fs:?} mollusk {ml:?}")),
    }
}

/// Assert cross-engine outcome agreement (M14); panics with the precise
/// mismatch. The replacement for the old "both non-Success" assertions on
/// fault fixtures.
fn assert_outcome_matches(fs: &FsProgramResult, ml: &MlProgramResult, ctx: &str) {
    if let Err(why) = outcome_matches(fs, ml) {
        panic!("{ctx}: cross-engine outcome mismatch (M14): {why}");
    }
}

/// L10: resolve a resulting account by key instead of indexing
/// positionally (`resulting_accounts[0]`), which silently reads the
/// wrong slot if the engine ever reorders the list. Panics (not a wrong
/// silent read) if the key is absent.
fn fs_acct_by_key<'a>(
    fs_r: &'a qedsvm::InstructionResult,
    key: &Pubkey,
) -> &'a AccountSharedData {
    fs_r.resulting_accounts.iter()
        .find(|(k, _)| k == key)
        .map(|(_, a)| a)
        .unwrap_or_else(|| panic!("account {key} absent from qedsvm resulting_accounts"))
}

/// Both engines accept the real cargo-build-sbf-produced ELF and
/// produce identical observable output for a trivial noop call.
#[test]
fn noop_program_matches_mollusk() {
    let program_id = pid(1);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };

    // ─ qedsvm side ────────────────────────────────────────────
    let mut fs = Svm::default();
    fs.add_program(&program_id, NOOP_SO);
    let fs_r = fs.process_instruction(&ix, &[]).expect("qedsvm runs noop");

    // ─ Mollusk side ───────────────────────────────────────────────
    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        NOOP_SO,
    );
    let m_r = m.process_instruction(&ix, &[]);

    // ─ Diff ───────────────────────────────────────────────────────
    assert!(
        matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success, got {:?}", fs_r.program_result,
    );
    assert!(
        matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success, got {:?}", m_r.program_result,
    );
    assert_eq!(fs_r.return_data, m_r.return_data,
        "return_data diverged: ours={:?} mollusk={:?}", fs_r.return_data, m_r.return_data);
    assert_eq!(
        fs_r.resulting_accounts.len(),
        m_r.resulting_accounts.len(),
        "resulting_accounts count diverged",
    );
    // For accounts that are present in both lists, verify they
    // match field-by-field.
    for ((k_a, a_a), (k_b, a_b)) in
        fs_r.resulting_accounts.iter().zip(m_r.resulting_accounts.iter())
    {
        assert_eq!(k_a, k_b, "pubkey order divergence");
        assert_eq!(a_a.lamports(), a_b.lamports, "lamports diverged for {k_a}");
        assert_eq!(a_a.data(), a_b.data.as_slice(), "data diverged for {k_a}");
        assert_eq!(a_a.owner(), &a_b.owner, "owner diverged for {k_a}");
    }
    // CU equality: agave's program-runtime emits the same
    // "consumed 2 of 1.4M compute units" we report. (This is a
    // stricter check than the others — if the spec layer ever
    // diverges from agave's CU accounting for any instruction,
    // this catches it.)
    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "compute_units_consumed diverged: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// The real `solana_program::entrypoint!`-using noop. This is the
/// program shape every published Solana program ships in: an
/// `entrypoint!` macro that deserializes the input buffer into
/// `(program_id, &[AccountInfo], &[u8])`, calls the user's
/// `process_instruction`, and converts the result back. ~1923 sBPF
/// instructions in `.text`. Cross-engine equality on this shape is
/// the actual "we conform to agave" claim.
#[test]
fn real_solana_program_entrypoint_noop_matches_mollusk() {
    let program_id = pid(3);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };

    let mut fs = Svm::default();
    fs.add_program(&program_id, SOLANA_NOOP_SO);
    let fs_r = fs.process_instruction(&ix, &[]).expect("qedsvm runs");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        SOLANA_NOOP_SO,
    );
    let m_r = m.process_instruction(&ix, &[]);

    // Equal program result.
    match (&fs_r.program_result, &m_r.program_result) {
        (FsProgramResult::Success, MlProgramResult::Success) => {}
        (a, b) => panic!(
            "program_result diverged on real solana_program noop:\n  qedsvm: {a:?}\n  mollusk:    {b:?}",
        ),
    }
    // Equal return data.
    assert_eq!(fs_r.return_data, m_r.return_data,
        "return_data diverged");

    // With proper call/return semantics (Phase D — push retPc on
    // `.call_local`, pop on `.exit`), qedsvm runs the same
    // top-level instruction count as agave for this noop. We assert
    // exact CU equality, which catches any future regression that
    // off-by-one's the call frame logic.
    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "compute_units_consumed diverged on real solana_program noop: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// A program that actually calls a syscall (`sol_log_`). Validates
/// our per-syscall CU table by asserting both engines report the
/// exact same `compute_units_consumed` — equivalent to one
/// `syscall_base_cost = 100` charge on top of the framework
/// instructions both engines have to execute.
#[test]
fn logger_program_matches_mollusk() {
    let program_id = pid(4);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };

    let mut fs = Svm::default();
    fs.add_program(&program_id, LOGGER_SO);
    let fs_r = fs.process_instruction(&ix, &[]).expect("qedsvm runs logger");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        LOGGER_SO,
    );
    let m_r = m.process_instruction(&ix, &[]);

    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success, got {:?}", fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success, got {:?}", m_r.program_result);
    assert_eq!(fs_r.return_data, m_r.return_data, "return_data diverged");
    // Hard CU equality — passing this proves the syscall CU table
    // is at least correct for sol_log_ on a small message.
    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged for msg!(\"hi\"): ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// H5 surcharge-overrun boundary: run the logger with a budget too
/// small for `sol_log_`'s ~100-CU surcharge. The Lean VM's mid-run
/// meter crosses the budget DURING the syscall (not at a per-step
/// fuel boundary), so this exercises exactly the new fail-closed
/// budget halt + the wire-level `min(cuConsumed, budget)` clamp that
/// mirrors agave draining the meter to the full budget on
/// `ComputeBudgetExceeded`. Both engines must (a) NOT succeed and
/// (b) report the SAME consumed CU (= the full budget).
#[test]
fn logger_surcharge_overrun_matches_mollusk() {
    let program_id = pid(60);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };
    const TINY_BUDGET: u64 = 50;

    let mut fs = Svm::default().with_cu_budget(TINY_BUDGET);
    fs.add_program(&program_id, LOGGER_SO);
    let fs_r = fs.process_instruction(&ix, &[]).expect("qedsvm runs logger");

    let mut m = Mollusk::default();
    m.compute_budget.compute_unit_limit = TINY_BUDGET;
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        LOGGER_SO,
    );
    let m_r = m.process_instruction(&ix, &[]);

    assert!(matches!(fs_r.program_result, FsProgramResult::OutOfBudget),
        "qedsvm: expected OutOfBudget on surcharge overrun, got {:?}",
        fs_r.program_result);
    // M14: agave's meter exhaustion (ExceededMaxInstructions) also
    // collapses to UnknownError(ProgramFailedToComplete) — same outcome.
    assert_outcome_matches(&fs_r.program_result, &m_r.program_result,
        "logger_surcharge_overrun");
    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "consumed-CU diverged at the surcharge-overrun boundary: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
    assert_eq!(fs_r.compute_units_consumed, TINY_BUDGET,
        "expected the meter drained to the full budget");
}

/// First fixture that actually *mutates* account data. Reads a u64
/// from `accounts[0].data[0..8]`, adds 1, writes it back. Validates
/// that qedsvm's `deserialize_account_writes` picks up the
/// program's write, that it reports the new data identically to
/// mollusk, and that all other fields (lamports, owner, return data,
/// CU consumption) still match byte-for-byte.
#[test]
fn incrementer_program_matches_mollusk() {
    let program_id = pid(5);
    let acct_key = pid(6);
    // Account owned by the program so both engines permit the write
    // through the loader's ownership invariant check. The two engines
    // pull `solana-account` from different majors (4.x for us, 3.x for
    // mollusk), so we build the same shape twice from a shared spec.
    let lamports = 1_000_000u64;
    let data: Vec<u8> = vec![0u8; 16];

    let pre_shared = AccountSharedData::from(Account {
        lamports, data: data.clone(), owner: program_id,
        executable: false, rent_epoch: 0,
    });
    let pre_mollusk = mollusk_account::Account {
        lamports, data: data.clone(), owner: program_id,
        executable: false, rent_epoch: 0,
    };

    let ix = Instruction {
        program_id,
        accounts: vec![AccountMeta::new(acct_key, false)],
        data: vec![],
    };

    // Real on-chain CU budget. The default (200k) is plenty for this
    // program (mollusk consumes 321), but keep the budgets identical
    // across engines so any future budget-dependent path can't drift.
    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&program_id, INCREMENTER_SO);
    let fs_r = fs
        .process_instruction(&ix, &[(acct_key, pre_shared)])
        .expect("qedsvm runs incrementer");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        INCREMENTER_SO,
    );
    let m_r = m.process_instruction(&ix, &[(acct_key, pre_mollusk)]);

    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success, got {:?}", fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success, got {:?}", m_r.program_result);
    assert_eq!(fs_r.return_data, m_r.return_data, "return_data diverged");

    assert_eq!(fs_r.resulting_accounts.len(), 1, "qedsvm: expected 1 account back");
    assert_eq!(m_r.resulting_accounts.len(), 1, "mollusk: expected 1 account back");
    let (fs_key, fs_acct) = &fs_r.resulting_accounts[0];
    let (m_key, m_acct) = &m_r.resulting_accounts[0];
    assert_eq!(fs_key, &acct_key);
    assert_eq!(m_key, &acct_key);

    // The actual write-back claim: data[0..8] = 1u64.
    let mut want = vec![0u8; 16];
    want[..8].copy_from_slice(&1u64.to_le_bytes());
    assert_eq!(fs_acct.data(), want.as_slice(),
        "qedsvm did not record the increment: got {:?}", fs_acct.data());
    assert_eq!(m_acct.data.as_slice(), want.as_slice(),
        "mollusk did not record the increment: got {:?}", m_acct.data);

    assert_eq!(fs_acct.lamports(), m_acct.lamports, "lamports diverged");
    assert_eq!(fs_acct.data(), m_acct.data.as_slice(), "data diverged");
    assert_eq!(fs_acct.owner(), &m_acct.owner, "owner diverged");

    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged for incrementer: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// Halfword-width memory ops: ldxh reads the u16 at account 0's
/// data[0..2], stxh writes back value+1, and sth (ST_H_IMM, opcode
/// 0x6a) stores the constant 0x1234 at data[2..4]. The only fixture
/// covering 16-bit stores; pre-populated with 0x00ff so the ldxh/stxh
/// increment carries across the byte boundary (0x00ff -> 0x0100),
/// catching any byte/halfword width confusion in either engine.
#[test]
fn halfword_store_program_matches_mollusk() {
    let program_id = pid(70);
    let acct_key = pid(71);
    let lamports = 1_000_000u64;
    let mut data: Vec<u8> = vec![0u8; 16];
    data[..2].copy_from_slice(&0x00ffu16.to_le_bytes());

    let pre_shared = AccountSharedData::from(Account {
        lamports, data: data.clone(), owner: program_id,
        executable: false, rent_epoch: 0,
    });
    let pre_mollusk = mollusk_account::Account {
        lamports, data: data.clone(), owner: program_id,
        executable: false, rent_epoch: 0,
    };

    let ix = Instruction {
        program_id,
        accounts: vec![AccountMeta::new(acct_key, false)],
        data: vec![],
    };

    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&program_id, HALFWORD_STORE_SO);
    let fs_r = fs
        .process_instruction(&ix, &[(acct_key, pre_shared)])
        .expect("qedsvm runs halfword_store");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        HALFWORD_STORE_SO,
    );
    let m_r = m.process_instruction(&ix, &[(acct_key, pre_mollusk)]);

    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success, got {:?}", fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success, got {:?}", m_r.program_result);
    assert_eq!(fs_r.return_data, m_r.return_data, "return_data diverged");

    let (fs_key, fs_acct) = &fs_r.resulting_accounts[0];
    let (m_key, m_acct) = &m_r.resulting_accounts[0];
    assert_eq!(fs_key, &acct_key);
    assert_eq!(m_key, &acct_key);

    // The write-back claim: data[0..2] = 0x0100 (carried increment),
    // data[2..4] = 0x1234 (the ST_H_IMM constant).
    let mut want = vec![0u8; 16];
    want[..2].copy_from_slice(&0x0100u16.to_le_bytes());
    want[2..4].copy_from_slice(&0x1234u16.to_le_bytes());
    assert_eq!(fs_acct.data(), want.as_slice(),
        "qedsvm halfword writes wrong: got {:?}", fs_acct.data());
    assert_eq!(m_acct.data.as_slice(), want.as_slice(),
        "mollusk halfword writes wrong: got {:?}", m_acct.data);

    assert_eq!(fs_acct.lamports(), m_acct.lamports, "lamports diverged");
    assert_eq!(fs_acct.owner(), &m_acct.owner, "owner diverged");

    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged for halfword_store: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// Heap-allocating program: exercises the embedded bump allocator over
/// the program heap (reads/commits the bump slot at 0x300000000, writes
/// and reads an allocated block). It touches no accounts, so this is a
/// pure byte-level conformance check — both engines must run the heap
/// load/store sequence to Success with identical CU and return data,
/// confirming qedsvm models the heap region exactly as agave/mollusk do.
#[test]
fn heap_alloc_program_matches_mollusk() {
    let program_id = pid(7);
    let acct_key = pid(8);
    let lamports = 1_000_000u64;
    let data: Vec<u8> = vec![0u8; 16];

    let pre_shared = AccountSharedData::from(Account {
        lamports, data: data.clone(), owner: program_id,
        executable: false, rent_epoch: 0,
    });
    let pre_mollusk = mollusk_account::Account {
        lamports, data: data.clone(), owner: program_id,
        executable: false, rent_epoch: 0,
    };

    let ix = Instruction {
        program_id,
        accounts: vec![AccountMeta::new(acct_key, false)],
        data: vec![],
    };

    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&program_id, HEAP_ALLOC_SO);
    let fs_r = fs
        .process_instruction(&ix, &[(acct_key, pre_shared)])
        .expect("qedsvm runs heap_alloc");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        HEAP_ALLOC_SO,
    );
    let m_r = m.process_instruction(&ix, &[(acct_key, pre_mollusk)]);

    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success, got {:?}", fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success, got {:?}", m_r.program_result);
    assert_eq!(fs_r.return_data, m_r.return_data, "return_data diverged");
    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged for heap_alloc: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// Empirical anchor for H7 (`sol_remaining_compute_units`): the program
/// calls the syscall and writes the returned u64 LE into
/// accounts[0].data[0..8]. Both engines run with the SAME explicit CU
/// budget; the byte-identical data assertion pins qedsvm's
/// remaining-budget formula (`cuBudget − (cuConsumed + 1 + 100)`)
/// against rbpf's real meter (which syncs through the call insn, then
/// consumes `syscall_base_cost` = 100 before `get_remaining()`).
#[test]
fn remaining_cu_program_matches_mollusk() {
    let program_id = pid(80);
    let acct_key = pid(81);
    let lamports = 1_000_000u64;
    let data: Vec<u8> = vec![0u8; 16];
    const BUDGET: u64 = 1_400_000;

    let pre_shared = AccountSharedData::from(Account {
        lamports, data: data.clone(), owner: program_id,
        executable: false, rent_epoch: 0,
    });
    let pre_mollusk = mollusk_account::Account {
        lamports, data: data.clone(), owner: program_id,
        executable: false, rent_epoch: 0,
    };

    let ix = Instruction {
        program_id,
        accounts: vec![AccountMeta::new(acct_key, false)],
        data: vec![],
    };

    let mut fs = Svm::default().with_cu_budget(BUDGET);
    fs.add_program(&program_id, REMAINING_CU_SO);
    let fs_r = fs
        .process_instruction(&ix, &[(acct_key, pre_shared)])
        .expect("qedsvm runs remaining_cu");

    let mut m = Mollusk::default();
    m.compute_budget.compute_unit_limit = BUDGET;
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        REMAINING_CU_SO,
    );
    let m_r = m.process_instruction(&ix, &[(acct_key, pre_mollusk)]);

    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success, got {:?}", fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success, got {:?}", m_r.program_result);
    assert_eq!(fs_r.return_data, m_r.return_data, "return_data diverged");

    let (fs_key, fs_acct) = &fs_r.resulting_accounts[0];
    let (m_key, m_acct) = &m_r.resulting_accounts[0];
    assert_eq!(fs_key, &acct_key);
    assert_eq!(m_key, &acct_key);

    // THE assertion: the 8-byte remaining-CU value must be
    // byte-identical across engines. Surface both values on failure so
    // a divergence shows exactly what each meter reported.
    let fs_remaining = u64::from_le_bytes(fs_acct.data()[..8].try_into().unwrap());
    let m_remaining = u64::from_le_bytes(m_acct.data[..8].try_into().unwrap());
    eprintln!(
        "remaining_cu: ours={} mollusk={} (budget={}, consumed ours={} mollusk={})",
        fs_remaining, m_remaining, BUDGET,
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
    assert_eq!(fs_remaining, m_remaining,
        "remaining-CU value diverged: ours={} mollusk={} (budget={})",
        fs_remaining, m_remaining, BUDGET);
    assert_eq!(fs_acct.data(), m_acct.data.as_slice(), "data diverged");

    assert_eq!(fs_acct.lamports(), m_acct.lamports, "lamports diverged");
    assert_eq!(fs_acct.owner(), &m_acct.owner, "owner diverged");

    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged for remaining_cu: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// Invoke token.so with empty instruction data. Both engines should
/// fail — token's dispatch tree hits "Error: Invalid instruction" on
/// unknown discriminator, exiting with `TokenError::InvalidInstruction`
/// (= ProgramError::Custom(12)). We assert both engines log the
/// "Error: Invalid instruction" string (so the dispatch path matches)
/// and both surface a non-Success outcome. CU equality is checked
/// loosely (within the same ~200-CU window as the success path).
#[test]
fn token_empty_data_invalid_instruction_matches_mollusk() {
    let program_id = pid(10);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };

    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&program_id, TOKEN_SO);
    let fs_r = fs
        .process_instruction(&ix, &[])
        .expect("qedsvm runs token with empty data");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        TOKEN_SO,
    );
    let m_r = m.process_instruction(&ix, &[]);

    // Both engines must fail (some Failure flavor — exact error
    // encoding diverges: we return raw r0, mollusk maps to typed
    // ProgramError).
    assert!(!matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Failure, got Success");
    assert!(!matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Failure, got Success");
    // Same log content — proves both engines took the same dispatch
    // path through token's match arm tree.
    let our_log = fs_r.logs.first()
        .map(|b| String::from_utf8_lossy(b).into_owned())
        .unwrap_or_default();
    assert!(our_log.contains("Invalid instruction"),
        "qedsvm: expected 'Error: Invalid instruction', got {our_log:?}");
}

/// SPL Token `InitializeMint2` (discriminant 20). Exercises the
/// real spl-token entrypoint dispatch, the `sol_get_rent_sysvar`
/// syscall, the spl-token Mint deserialize/serialize path, and a
/// full Mint struct write to `accounts[0].data` (82 bytes).
///
/// Why this is a useful diff:
/// - First program in the harness that reads a sysvar via syscall.
/// - First program with non-trivial control flow (option decoding,
///   error returns based on input state).
/// - 82-byte structured write to account data — a real write-back
///   surface, not a single u64.
///
/// Setup needs:
/// - The mint account must be owned by the token program (the
///   program checks `mint.owner == program_id` in InitializeMint2).
/// - The mint account must be rent-exempt under agave's *real* Rent
///   values; we use 2_000_000 lamports, which clears the
///   ~1.46M-lamport threshold for an 82-byte account.
/// - Account data must be zeroed (Mint not already initialized).
#[test]
fn token_initialize_mint2_matches_mollusk() {
    let program_id = pid(7);
    let mint_key = pid(8);

    // 82 = spl_token::state::Mint::LEN.
    const MINT_LEN: usize = 82;
    let lamports = 2_000_000u64; // > rent-exemption for 82 bytes
    let data = vec![0u8; MINT_LEN];

    let pre_shared = AccountSharedData::from(Account {
        lamports, data: data.clone(), owner: program_id,
        executable: false, rent_epoch: 0,
    });
    let pre_mollusk = mollusk_account::Account {
        lamports, data: data.clone(), owner: program_id,
        executable: false, rent_epoch: 0,
    };

    // InitializeMint2 instruction data:
    //   [0] = 20 (discriminant)
    //   [1] = decimals (u8) = 9
    //   [2..34] = mint_authority (Pubkey)
    //   [34] = freeze_authority_option = 0 (no freeze authority)
    let mint_authority = pid(9);
    let mut ix_data = Vec::with_capacity(35);
    ix_data.push(20);
    ix_data.push(9);
    ix_data.extend_from_slice(mint_authority.as_ref());
    ix_data.push(0);

    let ix = Instruction {
        program_id,
        accounts: vec![AccountMeta::new(mint_key, false)],
        data: ix_data,
    };

    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&program_id, TOKEN_SO);
    let fs_r = fs
        .process_instruction(&ix, &[(mint_key, pre_shared)])
        .expect("qedsvm runs spl-token InitializeMint2");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        TOKEN_SO,
    );
    let m_r = m.process_instruction(&ix, &[(mint_key, pre_mollusk)]);

    // Both engines must reach the same outcome (Success or Failure).
    // Surface the actual results in the assertion message so a
    // divergence is debuggable.
    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success on InitializeMint2, got {:?}", fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success on InitializeMint2, got {:?}", m_r.program_result);

    assert_eq!(fs_r.return_data, m_r.return_data, "return_data diverged");
    assert_eq!(fs_r.resulting_accounts.len(), 1);
    assert_eq!(m_r.resulting_accounts.len(), 1);
    let (_, fs_acct) = &fs_r.resulting_accounts[0];
    let (_, m_acct) = &m_r.resulting_accounts[0];

    assert_eq!(fs_acct.data(), m_acct.data.as_slice(),
        "Mint data diverged after InitializeMint2");
    assert_eq!(fs_acct.lamports(), m_acct.lamports, "lamports diverged");
    assert_eq!(fs_acct.owner(), &m_acct.owner, "owner diverged");
    // CU exact equality: the 176-CU drift documented prior to
    // 2026-05-14 traced back to our `.call_local` bumping r10 by
    // 0x2000 (V0 + stack-frame-gaps) whereas modern agave 4.x with
    // `FeatureSet::all_enabled()` runs V0 with
    // `enable_stack_frame_gaps = false`, so r10 bumps by 0x1000.
    // Once fixed, byte-for-byte CU equality returns on this fixture.
    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged for InitializeMint2: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// Build a 165-byte `spl_token::state::Account` (TokenAccount) blob
/// with the given mint, owner, and amount. All COption fields are
/// `None`, state is `Initialized`. Layout taken from
/// `spl_token::state::Account::pack_into_slice`:
///
///   0..32   mint
///   32..64  owner
///   64..72  amount             (u64 LE)
///   72..76  delegate tag       (0 = None)
///   76..108 delegate pubkey
///   108     state              (1 = Initialized)
///   109..113 is_native tag     (0 = None)
///   113..121 is_native value
///   121..129 delegated_amount  (u64 LE, 0)
///   129..133 close_authority tag (0 = None)
///   133..165 close_authority pubkey
const TOKEN_ACCOUNT_LEN: usize = 165;
fn build_token_account(mint: &Pubkey, owner: &Pubkey, amount: u64) -> Vec<u8> {
    let mut d = vec![0u8; TOKEN_ACCOUNT_LEN];
    d[0..32].copy_from_slice(mint.as_ref());
    d[32..64].copy_from_slice(owner.as_ref());
    d[64..72].copy_from_slice(&amount.to_le_bytes());
    // delegate tag (72..76) stays 0 (None).
    d[108] = 1; // AccountState::Initialized
    // is_native tag (109..113) stays 0 (None).
    // delegated_amount (121..129) stays 0.
    // close_authority tag (129..133) stays 0 (None).
    d
}

/// Build an 82-byte `spl_token::state::Mint` blob, initialized with a
/// `Some(mint_authority)`, the given supply + decimals, and no freeze
/// authority. Layout (`Mint::pack_into_slice`):
///   0..4    mint_authority COption tag (1 = Some)
///   4..36   mint_authority pubkey
///   36..44  supply              (u64 LE)
///   44      decimals            (u8)
///   45      is_initialized      (1 = true)
///   46..50  freeze_authority tag (0 = None)
///   50..82  freeze_authority pubkey
const MINT_LEN: usize = 82;
fn build_mint_account(mint_authority: &Pubkey, supply: u64, decimals: u8) -> Vec<u8> {
    let mut d = vec![0u8; MINT_LEN];
    d[0..4].copy_from_slice(&1u32.to_le_bytes()); // COption::Some
    d[4..36].copy_from_slice(mint_authority.as_ref());
    d[36..44].copy_from_slice(&supply.to_le_bytes());
    d[44] = decimals;
    d[45] = 1; // is_initialized
    // freeze_authority tag (46..50) stays 0 (None).
    d
}

/// p-token `MintTo` (discriminant 7) — mints 250 tokens to a
/// destination account. Accounts: [mint(w), destination(w),
/// mint authority(signer)]. Exercises the shared account-array
/// parsing loop (pc≈3368-3452, the back-branch that caps the static
/// walker on ~18 arms) plus the supply/balance increment. Domain
/// payoff: `mint.supply += amount` and `dest.amount += amount`.
///
/// Primary purpose here: produce a happy-path TRACE_STEPS trace that
/// crosses the parsing loop, so `qedlift --trace` can unroll it.
#[test]
fn p_token_mint_to_matches_mollusk() {
    let program_id = pid(50);
    let mint_key = pid(51);
    let dest_key = pid(52);
    let authority = pid(53);
    let dest_owner = pid(54);

    const MINT_AMOUNT: u64 = 250;
    const SUPPLY_INITIAL: u64 = 1_000;
    const DEST_INITIAL: u64 = 0;
    const MINT_LAMPORTS: u64 = 2_000_000;
    const ACCT_LAMPORTS: u64 = 2_039_280;

    let mint_data = build_mint_account(&authority, SUPPLY_INITIAL, 9);
    let dest_data = build_token_account(&mint_key, &dest_owner, DEST_INITIAL);

    let mk_shared = |lamports: u64, data: Vec<u8>| AccountSharedData::from(Account {
        lamports, data, owner: program_id, executable: false, rent_epoch: 0,
    });
    let mk_mollusk = |lamports: u64, data: Vec<u8>| mollusk_account::Account {
        lamports, data, owner: program_id, executable: false, rent_epoch: 0,
    };
    let auth_shared = AccountSharedData::from(Account {
        lamports: 1_000_000, data: vec![], owner: Pubkey::default(),
        executable: false, rent_epoch: 0,
    });
    let auth_mollusk = mollusk_account::Account {
        lamports: 1_000_000, data: vec![], owner: Pubkey::default(),
        executable: false, rent_epoch: 0,
    };

    // MintTo instruction data: [7, amount_le_u64] = 9 bytes.
    let mut ix_data = Vec::with_capacity(9);
    ix_data.push(7);
    ix_data.extend_from_slice(&MINT_AMOUNT.to_le_bytes());

    let ix = Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new(mint_key, false),
            AccountMeta::new(dest_key, false),
            AccountMeta::new_readonly(authority, true),
        ],
        data: ix_data,
    };

    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&program_id, P_TOKEN_SO);
    let fs_r = fs
        .process_instruction(&ix, &[
            (mint_key, mk_shared(MINT_LAMPORTS, mint_data.clone())),
            (dest_key, mk_shared(ACCT_LAMPORTS, dest_data.clone())),
            (authority, auth_shared),
        ])
        .expect("qedsvm runs p-token MintTo");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        P_TOKEN_SO,
    );
    let m_r = m.process_instruction(&ix, &[
        (mint_key, mk_mollusk(MINT_LAMPORTS, mint_data.clone())),
        (dest_key, mk_mollusk(ACCT_LAMPORTS, dest_data.clone())),
        (authority, auth_mollusk),
    ]);

    eprintln!("fs.program_result   = {:?}", fs_r.program_result);
    eprintln!("mol.program_result  = {:?}", m_r.program_result);

    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success on p-token MintTo, got {:?}", fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success on p-token MintTo, got {:?}", m_r.program_result);

    assert_eq!(fs_r.resulting_accounts.len(), 3);
    for i in 0..3 {
        let (_, fa) = &fs_r.resulting_accounts[i];
        let (_, ma) = &m_r.resulting_accounts[i];
        assert_eq!(fa.data(), ma.data.as_slice(),
            "p-token MintTo account[{i}] data diverged");
        assert_eq!(fa.lamports(), ma.lamports,
            "p-token MintTo account[{i}] lamports diverged");
    }
}

/// p-token `Burn` (discriminant 8) — burns 250 tokens from an account.
/// Accounts: [account(w), mint(w), owner(signer)]. The debit complement
/// to MintTo: `account.amount -= amount` and `mint.supply -= amount`.
/// Also routes through the shared account-parsing region that caps the
/// static walker — another phantom-loop arm trace guidance handles.
#[test]
fn p_token_burn_matches_mollusk() {
    let program_id = pid(60);
    let mint_key = pid(61);
    let acct_key = pid(62);
    let owner = pid(63);
    let mint_auth = pid(64);

    const BURN_AMOUNT: u64 = 250;
    const ACCT_INITIAL: u64 = 1_000;
    const SUPPLY_INITIAL: u64 = 1_000;
    const MINT_LAMPORTS: u64 = 2_000_000;
    const ACCT_LAMPORTS: u64 = 2_039_280;

    let mint_data = build_mint_account(&mint_auth, SUPPLY_INITIAL, 9);
    let acct_data = build_token_account(&mint_key, &owner, ACCT_INITIAL);

    let mk_shared = |lamports: u64, data: Vec<u8>| AccountSharedData::from(Account {
        lamports, data, owner: program_id, executable: false, rent_epoch: 0,
    });
    let mk_mollusk = |lamports: u64, data: Vec<u8>| mollusk_account::Account {
        lamports, data, owner: program_id, executable: false, rent_epoch: 0,
    };
    let owner_shared = AccountSharedData::from(Account {
        lamports: 1_000_000, data: vec![], owner: Pubkey::default(),
        executable: false, rent_epoch: 0,
    });
    let owner_mollusk = mollusk_account::Account {
        lamports: 1_000_000, data: vec![], owner: Pubkey::default(),
        executable: false, rent_epoch: 0,
    };

    // Burn instruction data: [8, amount_le_u64] = 9 bytes.
    let mut ix_data = Vec::with_capacity(9);
    ix_data.push(8);
    ix_data.extend_from_slice(&BURN_AMOUNT.to_le_bytes());

    let ix = Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new(acct_key, false),
            AccountMeta::new(mint_key, false),
            AccountMeta::new_readonly(owner, true),
        ],
        data: ix_data,
    };

    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&program_id, P_TOKEN_SO);
    let fs_r = fs
        .process_instruction(&ix, &[
            (acct_key, mk_shared(ACCT_LAMPORTS, acct_data.clone())),
            (mint_key, mk_shared(MINT_LAMPORTS, mint_data.clone())),
            (owner, owner_shared),
        ])
        .expect("qedsvm runs p-token Burn");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        P_TOKEN_SO,
    );
    let m_r = m.process_instruction(&ix, &[
        (acct_key, mk_mollusk(ACCT_LAMPORTS, acct_data.clone())),
        (mint_key, mk_mollusk(MINT_LAMPORTS, mint_data.clone())),
        (owner, owner_mollusk),
    ]);

    eprintln!("fs.program_result   = {:?}", fs_r.program_result);
    eprintln!("mol.program_result  = {:?}", m_r.program_result);

    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success on p-token Burn, got {:?}", fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success on p-token Burn, got {:?}", m_r.program_result);

    assert_eq!(fs_r.resulting_accounts.len(), 3);
    for i in 0..3 {
        let (_, fa) = &fs_r.resulting_accounts[i];
        let (_, ma) = &m_r.resulting_accounts[i];
        assert_eq!(fa.data(), ma.data.as_slice(),
            "p-token Burn account[{i}] data diverged");
        assert_eq!(fa.lamports(), ma.lamports,
            "p-token Burn account[{i}] lamports diverged");
    }
}

/// p-token `TransferChecked` (discriminant 12) — like Transfer but with
/// a mint account and a decimals check. Accounts: [source(w), mint,
/// destination(w), authority(signer)]. Same balance shift as Transfer
/// (`src -= amount`, `dst += amount`) plus the decimals == mint.decimals
/// guard. Completes the transfer family under trace guidance.
#[test]
fn p_token_transfer_checked_matches_mollusk() {
    let program_id = pid(70);
    let mint_key = pid(71);
    let source_key = pid(72);
    let dest_key = pid(73);
    let authority = pid(74);
    let mint_auth = pid(75);

    const AMOUNT: u64 = 250;
    const SOURCE_INITIAL: u64 = 1_000;
    const DEST_INITIAL: u64 = 0;
    const DECIMALS: u8 = 9;
    const MINT_LAMPORTS: u64 = 2_000_000;
    const ACCT_LAMPORTS: u64 = 2_039_280;

    let mint_data = build_mint_account(&mint_auth, 1_000, DECIMALS);
    let src_data = build_token_account(&mint_key, &authority, SOURCE_INITIAL);
    let dst_data = build_token_account(&mint_key, &authority, DEST_INITIAL);

    let mk_shared = |lamports: u64, data: Vec<u8>| AccountSharedData::from(Account {
        lamports, data, owner: program_id, executable: false, rent_epoch: 0,
    });
    let mk_mollusk = |lamports: u64, data: Vec<u8>| mollusk_account::Account {
        lamports, data, owner: program_id, executable: false, rent_epoch: 0,
    };
    let auth_shared = AccountSharedData::from(Account {
        lamports: 1_000_000, data: vec![], owner: Pubkey::default(),
        executable: false, rent_epoch: 0,
    });
    let auth_mollusk = mollusk_account::Account {
        lamports: 1_000_000, data: vec![], owner: Pubkey::default(),
        executable: false, rent_epoch: 0,
    };

    // TransferChecked data: [12, amount_le_u64, decimals] = 10 bytes.
    let mut ix_data = Vec::with_capacity(10);
    ix_data.push(12);
    ix_data.extend_from_slice(&AMOUNT.to_le_bytes());
    ix_data.push(DECIMALS);

    let ix = Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new(source_key, false),
            AccountMeta::new_readonly(mint_key, false),
            AccountMeta::new(dest_key, false),
            AccountMeta::new_readonly(authority, true),
        ],
        data: ix_data,
    };

    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&program_id, P_TOKEN_SO);
    let fs_r = fs
        .process_instruction(&ix, &[
            (source_key, mk_shared(ACCT_LAMPORTS, src_data.clone())),
            (mint_key, mk_shared(MINT_LAMPORTS, mint_data.clone())),
            (dest_key, mk_shared(ACCT_LAMPORTS, dst_data.clone())),
            (authority, auth_shared),
        ])
        .expect("qedsvm runs p-token TransferChecked");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        P_TOKEN_SO,
    );
    let m_r = m.process_instruction(&ix, &[
        (source_key, mk_mollusk(ACCT_LAMPORTS, src_data.clone())),
        (mint_key, mk_mollusk(MINT_LAMPORTS, mint_data.clone())),
        (dest_key, mk_mollusk(ACCT_LAMPORTS, dst_data.clone())),
        (authority, auth_mollusk),
    ]);

    eprintln!("fs.program_result   = {:?}", fs_r.program_result);
    eprintln!("mol.program_result  = {:?}", m_r.program_result);

    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success on p-token TransferChecked, got {:?}", fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success on p-token TransferChecked, got {:?}", m_r.program_result);

    assert_eq!(fs_r.resulting_accounts.len(), 4);
    for i in 0..4 {
        let (_, fa) = &fs_r.resulting_accounts[i];
        let (_, ma) = &m_r.resulting_accounts[i];
        assert_eq!(fa.data(), ma.data.as_slice(),
            "p-token TransferChecked account[{i}] data diverged");
    }
}

/// p-token `CloseAccount` (discriminant 9) — closes a zero-balance
/// token account. Accounts: [account(w), destination(w), owner(signer)].
/// Moves the account's lamports to destination and wipes the account.
/// Different effect shape from the arithmetic arms (lamport move + data
/// clear), exercising the immediate-store/zeroing path.
#[test]
fn p_token_close_account_matches_mollusk() {
    let program_id = pid(80);
    let mint_key = pid(81);
    let acct_key = pid(82);
    let dest_key = pid(83);
    let owner = pid(84);

    const ACCT_LAMPORTS: u64 = 2_039_280;
    const DEST_LAMPORTS: u64 = 500_000;

    // Account must have zero token balance to be closeable.
    let acct_data = build_token_account(&mint_key, &owner, 0);

    let mk_shared = |lamports: u64, data: Vec<u8>| AccountSharedData::from(Account {
        lamports, data, owner: program_id, executable: false, rent_epoch: 0,
    });
    let mk_mollusk = |lamports: u64, data: Vec<u8>| mollusk_account::Account {
        lamports, data, owner: program_id, executable: false, rent_epoch: 0,
    };
    let dest_shared = AccountSharedData::from(Account {
        lamports: DEST_LAMPORTS, data: vec![], owner: Pubkey::default(),
        executable: false, rent_epoch: 0,
    });
    let dest_mollusk = mollusk_account::Account {
        lamports: DEST_LAMPORTS, data: vec![], owner: Pubkey::default(),
        executable: false, rent_epoch: 0,
    };
    let owner_shared = AccountSharedData::from(Account {
        lamports: 1_000_000, data: vec![], owner: Pubkey::default(),
        executable: false, rent_epoch: 0,
    });
    let owner_mollusk = mollusk_account::Account {
        lamports: 1_000_000, data: vec![], owner: Pubkey::default(),
        executable: false, rent_epoch: 0,
    };

    let ix = Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new(acct_key, false),
            AccountMeta::new(dest_key, false),
            AccountMeta::new_readonly(owner, true),
        ],
        data: vec![9],
    };

    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&program_id, P_TOKEN_SO);
    let fs_r = fs
        .process_instruction(&ix, &[
            (acct_key, mk_shared(ACCT_LAMPORTS, acct_data.clone())),
            (dest_key, dest_shared),
            (owner, owner_shared),
        ])
        .expect("qedsvm runs p-token CloseAccount");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        P_TOKEN_SO,
    );
    let m_r = m.process_instruction(&ix, &[
        (acct_key, mk_mollusk(ACCT_LAMPORTS, acct_data.clone())),
        (dest_key, dest_mollusk),
        (owner, owner_mollusk),
    ]);

    eprintln!("fs.program_result   = {:?}", fs_r.program_result);
    eprintln!("mol.program_result  = {:?}", m_r.program_result);

    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success on p-token CloseAccount, got {:?}", fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success on p-token CloseAccount, got {:?}", m_r.program_result);
}

/// p-token `InitializeMint2` (discriminant 20) — initializes a mint,
/// taking decimals + mint authority + optional freeze authority from
/// instruction data (no rent sysvar, unlike InitializeMint). Single
/// account: [mint(w)]. The handler `sol_memcpy_`'s the 32-byte mint
/// authority from the input region into the mint's authority field —
/// the first p-token happy path that crosses `sol_memcpy_` (the
/// syscall-verification target for qedlift's copy-spec wiring).
#[test]
fn p_token_initialize_mint2_matches_mollusk() {
    let program_id = pid(90);
    let mint_key = pid(91);
    let mint_authority = pid(94);

    // The mint being initialized starts uninitialized (all-zero data,
    // 82 bytes, owned by the token program, rent-exempt).
    const MINT_LAMPORTS: u64 = 1_461_600;
    let mint_data = vec![0u8; MINT_LEN];

    let mk_shared = |lamports: u64, data: Vec<u8>| AccountSharedData::from(Account {
        lamports, data, owner: program_id, executable: false, rent_epoch: 0,
    });
    let mk_mollusk = |lamports: u64, data: Vec<u8>| mollusk_account::Account {
        lamports, data, owner: program_id, executable: false, rent_epoch: 0,
    };

    // Instruction data: [20, decimals(u8), mintAuthority(32),
    // freezeAuthority option tag(0 = None)].
    let mut data = vec![20u8, 6u8];
    data.extend_from_slice(mint_authority.as_ref());
    data.push(0); // freeze authority: None

    let ix = Instruction {
        program_id,
        accounts: vec![AccountMeta::new(mint_key, false)],
        data,
    };

    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&program_id, P_TOKEN_SO);
    let fs_r = fs
        .process_instruction(&ix, &[
            (mint_key, mk_shared(MINT_LAMPORTS, mint_data.clone())),
        ])
        .expect("qedsvm runs p-token InitializeMint2");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        P_TOKEN_SO,
    );
    let m_r = m.process_instruction(&ix, &[
        (mint_key, mk_mollusk(MINT_LAMPORTS, mint_data.clone())),
    ]);

    eprintln!("fs.program_result   = {:?}", fs_r.program_result);
    eprintln!("mol.program_result  = {:?}", m_r.program_result);

    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success on p-token InitializeMint2, got {:?}", fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success on p-token InitializeMint2, got {:?}", m_r.program_result);
    // Full-equality referee (enabled by the H7 `sol_get_sysvar` fix:
    // pinocchio's Rent::get crosses the generic accessor on this path,
    // so pre-fix the engines diverged in CU and were only compared on
    // Success/Success).
    assert_no_poststate_backstop(&fs_r);
    let (_, fs_mint) = &fs_r.resulting_accounts[0];
    let (_, ml_mint) = &m_r.resulting_accounts[0];
    assert_eq!(fs_mint.data(), ml_mint.data.as_slice(),
        "Mint data diverged after p-token InitializeMint2");
    assert_eq!(fs_mint.lamports(), ml_mint.lamports, "lamports diverged");
    assert_eq!(fs_mint.owner(), &ml_mint.owner, "owner diverged");
    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged for p-token InitializeMint2: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// SPL Token `Transfer` (discriminant 3). Moves 250 lamports of a
/// token from `source` to `destination`, both owned by the same
/// authority. Real on-chain Token path — exercises the same .text
/// region as InitializeMint2 plus a memcpy/memmove-style data
/// rearrangement, two TokenAccount unpack/pack round-trips, and the
/// 64-bit checked-add/sub arithmetic.
///
/// This is the "should just work" claim from production-parity.md:
/// Transfer has no CPI, no PDA derivation, no sysvar read beyond
/// what's already wired. If it diverges, the divergence is a real
/// new bug.
#[test]
fn token_transfer_matches_mollusk() {
    let program_id = pid(7);
    let mint = pid(30);
    let authority = pid(31);
    let source_key = pid(32);
    let dest_key = pid(33);

    const TRANSFER_AMOUNT: u64 = 250;
    const SOURCE_INITIAL: u64 = 1_000;
    const DEST_INITIAL: u64 = 0;
    const LAMPORTS: u64 = 2_039_280; // standard rent-exempt for 165 bytes

    let source_data = build_token_account(&mint, &authority, SOURCE_INITIAL);
    let dest_data = build_token_account(&mint, &authority, DEST_INITIAL);

    let pre_src_shared = AccountSharedData::from(Account {
        lamports: LAMPORTS, data: source_data.clone(), owner: program_id,
        executable: false, rent_epoch: 0,
    });
    let pre_dst_shared = AccountSharedData::from(Account {
        lamports: LAMPORTS, data: dest_data.clone(), owner: program_id,
        executable: false, rent_epoch: 0,
    });
    let pre_auth_shared = AccountSharedData::from(Account {
        lamports: 1_000_000, data: vec![], owner: Pubkey::default(),
        executable: false, rent_epoch: 0,
    });

    let pre_src_mollusk = mollusk_account::Account {
        lamports: LAMPORTS, data: source_data.clone(), owner: program_id,
        executable: false, rent_epoch: 0,
    };
    let pre_dst_mollusk = mollusk_account::Account {
        lamports: LAMPORTS, data: dest_data.clone(), owner: program_id,
        executable: false, rent_epoch: 0,
    };
    let pre_auth_mollusk = mollusk_account::Account {
        lamports: 1_000_000, data: vec![], owner: Pubkey::default(),
        executable: false, rent_epoch: 0,
    };

    // Transfer instruction data: [3, amount_le_u64...] = 9 bytes.
    let mut ix_data = Vec::with_capacity(9);
    ix_data.push(3);
    ix_data.extend_from_slice(&TRANSFER_AMOUNT.to_le_bytes());

    let ix = Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new(source_key, false),       // writable, not signer
            AccountMeta::new(dest_key, false),         // writable, not signer
            AccountMeta::new_readonly(authority, true), // readonly, signer
        ],
        data: ix_data,
    };

    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&program_id, TOKEN_SO);
    let fs_r = fs
        .process_instruction(&ix, &[
            (source_key, pre_src_shared),
            (dest_key, pre_dst_shared),
            (authority, pre_auth_shared),
        ])
        .expect("qedsvm runs spl-token Transfer");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        TOKEN_SO,
    );
    let m_r = m.process_instruction(&ix, &[
        (source_key, pre_src_mollusk),
        (dest_key, pre_dst_mollusk),
        (authority, pre_auth_mollusk),
    ]);

    // Surface both results before asserting so a divergence is debuggable.
    eprintln!("fs.program_result   = {:?}", fs_r.program_result);
    eprintln!("mol.program_result  = {:?}", m_r.program_result);
    eprintln!("fs.cu_consumed      = {}", fs_r.compute_units_consumed);
    eprintln!("mol.cu_consumed     = {}", m_r.compute_units_consumed);
    if !fs_r.logs.is_empty() {
        eprintln!("fs.logs ({}):", fs_r.logs.len());
        for (i, l) in fs_r.logs.iter().enumerate() {
            eprintln!("  [{i}] {}", String::from_utf8_lossy(l));
        }
    }

    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success on Transfer, got {:?}", fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success on Transfer, got {:?}", m_r.program_result);

    assert_eq!(fs_r.return_data, m_r.return_data, "return_data diverged");
    assert_eq!(fs_r.resulting_accounts.len(), 3);
    assert_eq!(m_r.resulting_accounts.len(), 3);

    // Source and destination data should diverge from the initial in
    // a structured way (amount field at offset 64..72). Assert the
    // exact post-state matches mollusk byte-for-byte.
    for i in 0..3 {
        let (_, fa) = &fs_r.resulting_accounts[i];
        let (_, ma) = &m_r.resulting_accounts[i];
        assert_eq!(fa.data(), ma.data.as_slice(),
            "account[{i}] data diverged after Transfer");
        assert_eq!(fa.lamports(), ma.lamports,
            "account[{i}] lamports diverged after Transfer");
        assert_eq!(fa.owner(), &ma.owner,
            "account[{i}] owner diverged after Transfer");
    }

    // Strict CU match — Transfer should be deterministic.
    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged for Transfer: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// p-token `Transfer` (discriminant 3) — the same instruction shape
/// as `token_transfer_matches_mollusk`, but invoking the pinocchio
/// reimplementation (`p_token.so`) instead of the canonical
/// `token.so`. Since p-token is byte-for-byte compatible with SPL
/// Token at the account layout, `build_token_account` works as-is
/// and only the program ID + binary swap.
///
/// What this validates beyond the SPL Token Transfer test:
/// - **Pinocchio entrypoint**: zero-copy account access via raw
///   pointer casts into the serialized input buffer (no Borsh
///   deserialization, no AccountInfo reconstruction). Different
///   `.text` and different relocation pattern than canonical Token.
/// - **CU parity on a CU-optimized program**: pinocchio's whole
///   pitch is dramatic CU reduction (transfers in ~3-5k CU vs
///   ~15k for the canonical Token program). If our model is off
///   by one anywhere in the inner loops, it will surface here
///   loud and obvious.
/// - **First major mainnet-track program in the harness** — gives
///   the README a recognizable artifact to point at.
#[test]
fn p_token_transfer_matches_mollusk() {
    let program_id = pid(40);
    let mint = pid(41);
    let authority = pid(42);
    let source_key = pid(43);
    let dest_key = pid(44);

    const TRANSFER_AMOUNT: u64 = 250;
    const SOURCE_INITIAL: u64 = 1_000;
    const DEST_INITIAL: u64 = 0;
    const LAMPORTS: u64 = 2_039_280; // standard rent-exempt for 165 bytes

    let source_data = build_token_account(&mint, &authority, SOURCE_INITIAL);
    let dest_data = build_token_account(&mint, &authority, DEST_INITIAL);

    let pre_src_shared = AccountSharedData::from(Account {
        lamports: LAMPORTS, data: source_data.clone(), owner: program_id,
        executable: false, rent_epoch: 0,
    });
    let pre_dst_shared = AccountSharedData::from(Account {
        lamports: LAMPORTS, data: dest_data.clone(), owner: program_id,
        executable: false, rent_epoch: 0,
    });
    let pre_auth_shared = AccountSharedData::from(Account {
        lamports: 1_000_000, data: vec![], owner: Pubkey::default(),
        executable: false, rent_epoch: 0,
    });

    let pre_src_mollusk = mollusk_account::Account {
        lamports: LAMPORTS, data: source_data.clone(), owner: program_id,
        executable: false, rent_epoch: 0,
    };
    let pre_dst_mollusk = mollusk_account::Account {
        lamports: LAMPORTS, data: dest_data.clone(), owner: program_id,
        executable: false, rent_epoch: 0,
    };
    let pre_auth_mollusk = mollusk_account::Account {
        lamports: 1_000_000, data: vec![], owner: Pubkey::default(),
        executable: false, rent_epoch: 0,
    };

    // Transfer instruction data: [3, amount_le_u64...] = 9 bytes.
    let mut ix_data = Vec::with_capacity(9);
    ix_data.push(3);
    ix_data.extend_from_slice(&TRANSFER_AMOUNT.to_le_bytes());

    let ix = Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new(source_key, false),
            AccountMeta::new(dest_key, false),
            AccountMeta::new_readonly(authority, true),
        ],
        data: ix_data,
    };

    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&program_id, P_TOKEN_SO);
    let fs_r = fs
        .process_instruction(&ix, &[
            (source_key, pre_src_shared),
            (dest_key, pre_dst_shared),
            (authority, pre_auth_shared),
        ])
        .expect("qedsvm runs p-token Transfer");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        P_TOKEN_SO,
    );
    let m_r = m.process_instruction(&ix, &[
        (source_key, pre_src_mollusk),
        (dest_key, pre_dst_mollusk),
        (authority, pre_auth_mollusk),
    ]);

    eprintln!("fs.program_result   = {:?}", fs_r.program_result);
    eprintln!("mol.program_result  = {:?}", m_r.program_result);
    eprintln!("fs.cu_consumed      = {}", fs_r.compute_units_consumed);
    eprintln!("mol.cu_consumed     = {}", m_r.compute_units_consumed);
    if !fs_r.logs.is_empty() {
        eprintln!("fs.logs ({}):", fs_r.logs.len());
        for (i, l) in fs_r.logs.iter().enumerate() {
            eprintln!("  [{i}] {}", String::from_utf8_lossy(l));
        }
    }

    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success on p-token Transfer, got {:?}", fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success on p-token Transfer, got {:?}", m_r.program_result);

    assert_eq!(fs_r.return_data, m_r.return_data, "return_data diverged");
    assert_eq!(fs_r.resulting_accounts.len(), 3);
    assert_eq!(m_r.resulting_accounts.len(), 3);

    for i in 0..3 {
        let (_, fa) = &fs_r.resulting_accounts[i];
        let (_, ma) = &m_r.resulting_accounts[i];
        assert_eq!(fa.data(), ma.data.as_slice(),
            "p-token account[{i}] data diverged after Transfer");
        assert_eq!(fa.lamports(), ma.lamports,
            "p-token account[{i}] lamports diverged after Transfer");
        assert_eq!(fa.owner(), &ma.owner,
            "p-token account[{i}] owner diverged after Transfer");
    }

    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged for p-token Transfer: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// Invoke `associated_token.so` with empty instruction data. Both
/// engines should fail before any CPI is attempted. This is a
/// "the ELF loads + the entry path runs to a fail point" probe — it
/// validates ELF loading, relocation handling, and dispatch
/// resolution for the larger ATA binary, without depending on CPI
/// (which our engine still stubs). We assert both engines reach
/// Failure and we don't crash.
#[test]
fn associated_token_empty_data_fails_on_both() {
    let program_id = pid(20);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };

    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&program_id, ASSOCIATED_TOKEN_SO);
    let fs_r = fs
        .process_instruction(&ix, &[])
        .expect("qedsvm runs ATA with empty data (must not crash the harness)");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        ASSOCIATED_TOKEN_SO,
    );
    let m_r = m.process_instruction(&ix, &[]);

    assert!(!matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Failure, got Success");
    assert!(!matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Failure, got Success");
}

/// Phase-3-full CPI write-back: caller forwards a writable account
/// to `incrementer.so` via CPI. The callee mutates the first 8 bytes
/// of the account's data (treats as little-endian u64 and adds 1).
/// We assert the post-state reflects the increment on both engines —
/// the strongest claim about CPI plumbing yet: AccountInfo decoding
/// through the `Rc<RefCell<…>>` chain, fresh sub-input construction,
/// per-byte write-back, and harness-side deserialization all have to
/// agree with mollusk byte-for-byte.
#[test]
fn cpi_caller_forwards_account_to_incrementer() {
    let caller_id = pid(50);
    let callee_id = pid(51);
    let acct_key  = pid(52);

    let lamports = 1_000_000u64;
    let data: Vec<u8> = vec![0u8; 16];
    let pre_shared = AccountSharedData::from(Account {
        lamports, data: data.clone(), owner: callee_id,
        executable: false, rent_epoch: 0,
    });
    let pre_mollusk = mollusk_account::Account {
        lamports, data: data.clone(), owner: callee_id,
        executable: false, rent_epoch: 0,
    };
    // The callee program account must be passed through too — agave
    // needs it visible in the caller's AccountInfos so the CPI can
    // resolve `instruction.program_id` to a loaded executable.
    let callee_program_shared = AccountSharedData::from(Account {
        lamports: 1, data: vec![],
        owner: solana_sdk_ids::bpf_loader_upgradeable::id(),
        executable: true, rent_epoch: 0,
    });
    let callee_program_mollusk = mollusk_account::Account {
        lamports: 1, data: vec![],
        owner: solana_sdk_ids::bpf_loader_upgradeable::id(),
        executable: true, rent_epoch: 0,
    };

    let ix = Instruction {
        program_id: caller_id,
        accounts: vec![
            AccountMeta::new(acct_key, false),
            AccountMeta::new_readonly(callee_id, false),
        ],
        data: callee_id.to_bytes().to_vec(),
    };

    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&caller_id, CPI_INCREMENT_CALLER_SO);
    fs.add_program(&callee_id, INCREMENTER_SO);
    let fs_r = fs.process_instruction(&ix, &[
        (acct_key, pre_shared),
        (callee_id, callee_program_shared),
    ]).expect("qedsvm runs CPI→incrementer");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &caller_id, &solana_sdk_ids::bpf_loader_upgradeable::id(),
        CPI_INCREMENT_CALLER_SO);
    m.add_program_with_loader_and_elf(
        &callee_id, &solana_sdk_ids::bpf_loader_upgradeable::id(), INCREMENTER_SO);
    let m_r = m.process_instruction(&ix, &[
        (acct_key, pre_mollusk),
        (callee_id, callee_program_mollusk),
    ]);

    let our_logs: Vec<String> = fs_r.logs.iter()
        .map(|b| String::from_utf8_lossy(b).into_owned()).collect();
    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success on CPI→incrementer, got {:?}; logs: {our_logs:?}",
        fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success on CPI→incrementer, got {:?}", m_r.program_result);

    let mut expected = vec![0u8; 16];
    expected[..8].copy_from_slice(&1u64.to_le_bytes());

    // resulting_accounts is in the same order as `ix.accounts`: the
    // writable account first, then the callee program account. Look it up
    // by key (L10) and confirm the write-back came from the VM, not the
    // post-state backstop (M13).
    assert_no_poststate_backstop(&fs_r);
    let fs_acct = fs_acct_by_key(&fs_r, &acct_key);
    assert_eq!(fs_acct.data(), expected.as_slice(),
        "qedsvm: increment not visible after CPI; got {:?}", fs_acct.data());

    let (_, m_acct) = &m_r.resulting_accounts[0];
    assert_eq!(m_acct.data.as_slice(), expected.as_slice());
}

/// M6 read-only write-back protection. The SAME caller -> incrementer CPI
/// as `cpi_caller_forwards_account_to_incrementer`, but the forwarded
/// account is passed READ-ONLY at the top level. agave rejects the
/// caller's attempt to re-forward it writable (privilege escalation), so
/// the callee's `+1` is never committed. Our model reaches the same
/// observable state by a different internal route: the C5 clamp
/// downgrades the forged-writable AccountInfo back to read-only, and the
/// M6 guard then (a) never writes a read-only slot back to caller memory
/// and (b) flags the callee's attempted mutation as a violation
/// (`ERR_READONLY_MODIFIED` in r0). Either way the account's data MUST be
/// unchanged on both engines. Pre-M6 (C5 only) the unconditional
/// write-back committed the increment, so this is the precise M6
/// regression guard. The exact error code / CU on this malicious path is
/// engine-specific (agave errors at invoke; we clamp + roll back) and is
/// deliberately NOT asserted -- only the soundness-critical account state.
#[test]
fn cpi_readonly_account_not_committed_by_callee() {
    let caller_id = pid(53);
    let callee_id = pid(54);
    let acct_key  = pid(55);

    let lamports = 1_000_000u64;
    let data: Vec<u8> = vec![0u8; 16];
    let pre_shared = AccountSharedData::from(Account {
        lamports, data: data.clone(), owner: callee_id,
        executable: false, rent_epoch: 0,
    });
    let pre_mollusk = mollusk_account::Account {
        lamports, data: data.clone(), owner: callee_id,
        executable: false, rent_epoch: 0,
    };
    let callee_program_shared = AccountSharedData::from(Account {
        lamports: 1, data: vec![],
        owner: solana_sdk_ids::bpf_loader_upgradeable::id(),
        executable: true, rent_epoch: 0,
    });
    let callee_program_mollusk = mollusk_account::Account {
        lamports: 1, data: vec![],
        owner: solana_sdk_ids::bpf_loader_upgradeable::id(),
        executable: true, rent_epoch: 0,
    };

    // acct_key forwarded READ-ONLY at the top level (vs `new` -- writable
    // -- in the sibling test).
    let ix = Instruction {
        program_id: caller_id,
        accounts: vec![
            AccountMeta::new_readonly(acct_key, false),
            AccountMeta::new_readonly(callee_id, false),
        ],
        data: callee_id.to_bytes().to_vec(),
    };

    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&caller_id, CPI_INCREMENT_CALLER_SO);
    fs.add_program(&callee_id, INCREMENTER_SO);
    let fs_r = fs.process_instruction(&ix, &[
        (acct_key, pre_shared),
        (callee_id, callee_program_shared),
    ]).expect("qedsvm runs CPI->incrementer (read-only acct)");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &caller_id, &solana_sdk_ids::bpf_loader_upgradeable::id(),
        CPI_INCREMENT_CALLER_SO);
    m.add_program_with_loader_and_elf(
        &callee_id, &solana_sdk_ids::bpf_loader_upgradeable::id(), INCREMENTER_SO);
    let m_r = m.process_instruction(&ix, &[
        (acct_key, pre_mollusk),
        (callee_id, callee_program_mollusk),
    ]);

    // The read-only account's data MUST remain its original zeros on BOTH
    // engines: agave blocks the escalation, we clamp + roll back. And the
    // VM must reach that state itself, not via the post-state backstop.
    assert_no_poststate_backstop(&fs_r);
    let fs_acct = fs_acct_by_key(&fs_r, &acct_key);
    assert_eq!(fs_acct.data(), data.as_slice(),
        "qedsvm: read-only account was modified across CPI (M6 leak); got {:?}",
        fs_acct.data());
    let (_, m_acct) = &m_r.resulting_accounts[0];
    assert_eq!(m_acct.data.as_slice(), data.as_slice(),
        "mollusk: read-only account modified (unexpected)");
    assert_eq!(fs_acct.data(), m_acct.data.as_slice(),
        "read-only account data diverged across engines");
}

/// CPI caller invokes the `logger.so` callee. Stronger claim than
/// the noop variant: the callee actually does work (calls `sol_log_`
/// with "hi"), so this test only passes if (a) our Phase 3 sub-input
/// construction places a deserializable buffer at the callee's
/// `INPUT_START`, and (b) logs from the sub-VM propagate back into
/// the caller's `State.log`. Mollusk reports two `Program log`
/// messages (one per program); ours should at least contain "hi".
#[test]
fn cpi_caller_invokes_logger_propagates_log() {
    let caller_id = pid(40);
    let callee_id = pid(41);
    let ix = Instruction {
        program_id: caller_id,
        accounts: vec![AccountMeta::new_readonly(callee_id, false)],
        data: callee_id.to_bytes().to_vec(),
    };

    let callee_shared = AccountSharedData::from(Account {
        lamports: 1, data: vec![],
        owner: solana_sdk_ids::bpf_loader_upgradeable::id(),
        executable: true, rent_epoch: 0,
    });
    let callee_mollusk = mollusk_account::Account {
        lamports: 1, data: vec![],
        owner: solana_sdk_ids::bpf_loader_upgradeable::id(),
        executable: true, rent_epoch: 0,
    };

    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&caller_id, CPI_CALLER_SO);
    fs.add_program(&callee_id, LOGGER_SO);
    let fs_r = fs.process_instruction(&ix, &[(callee_id, callee_shared)])
        .expect("qedsvm runs CPI → logger");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &caller_id, &solana_sdk_ids::bpf_loader_upgradeable::id(), CPI_CALLER_SO);
    m.add_program_with_loader_and_elf(
        &callee_id, &solana_sdk_ids::bpf_loader_upgradeable::id(), LOGGER_SO);
    let m_r = m.process_instruction(&ix, &[(callee_id, callee_mollusk)]);

    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success on CPI→logger, got {:?}", fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success on CPI→logger, got {:?}", m_r.program_result);

    // The callee logs "hi" — it must show up in our captured log stream.
    let our_logs: Vec<String> = fs_r.logs.iter()
        .map(|b| String::from_utf8_lossy(b).into_owned()).collect();
    assert!(our_logs.iter().any(|l| l == "hi"),
        "expected 'hi' in qedsvm logs, got: {our_logs:?}");
}

/// First end-to-end CPI test: a real `cargo-build-sbf` caller that
/// uses `solana_program::invoke` to CPI into a target whose pubkey is
/// embedded in its instruction data. We register two programs — the
/// caller and `noop.so` as the callee — and ask the caller to invoke
/// the callee. Asserts both engines succeed; this is the simplest
/// possible "CPI is plumbed end-to-end" claim. Account write-back is
/// not yet tested (Phase 3 of CPI is TODO).
#[test]
fn cpi_caller_invokes_registered_noop() {
    let caller_id = pid(30);
    let callee_id = pid(31);
    let ix = Instruction {
        program_id: caller_id,
        // The CPI caller passes the callee account through `accounts`
        // (solana_program::invoke requires the callee's program
        // account info to be present); we register `noop.so` so the
        // callee account is also a program account.
        accounts: vec![AccountMeta::new_readonly(callee_id, false)],
        // First 32 bytes = the target pubkey (callee_id).
        data: callee_id.to_bytes().to_vec(),
    };

    let callee_account_shared = AccountSharedData::from(Account {
        lamports: 1,
        data: vec![],
        owner: solana_sdk_ids::bpf_loader_upgradeable::id(),
        executable: true,
        rent_epoch: 0,
    });
    let callee_account_mollusk = mollusk_account::Account {
        lamports: 1,
        data: vec![],
        owner: solana_sdk_ids::bpf_loader_upgradeable::id(),
        executable: true,
        rent_epoch: 0,
    };

    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&caller_id, CPI_CALLER_SO);
    fs.add_program(&callee_id, NOOP_SO);
    let fs_r = fs
        .process_instruction(&ix, &[(callee_id, callee_account_shared)])
        .expect("qedsvm runs CPI caller");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &caller_id, &solana_sdk_ids::bpf_loader_upgradeable::id(), CPI_CALLER_SO,
    );
    m.add_program_with_loader_and_elf(
        &callee_id, &solana_sdk_ids::bpf_loader_upgradeable::id(), NOOP_SO,
    );
    let m_r = m.process_instruction(&ix, &[(callee_id, callee_account_mollusk)]);

    // Both engines must successfully complete the CPI. (We don't yet
    // assert CU equality — without Phase 3 write-back our CPI elides
    // a chunk of agave's per-call serialization work.)
    let our_logs: Vec<String> = fs_r.logs.iter()
        .map(|b| String::from_utf8_lossy(b).into_owned()).collect();
    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success on CPI, got {:?}; logs: {:?}",
        fs_r.program_result, our_logs);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success on CPI, got {:?}", m_r.program_result);
}

/// Invoke the Pinocchio escrow with empty instruction data. Probes
/// ELF loading + first-instruction dispatch for the smallest of the
/// three vendored real programs. Pinocchio programs typically check
/// `account_infos.len()` first and fail with NotEnoughAccountKeys
/// before doing real work, so empty input is a usable error probe.
#[test]
fn pinocchio_escrow_empty_data_fails_on_both() {
    let program_id = pid(21);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };

    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&program_id, PINOCCHIO_ESCROW_SO);
    let fs_r = fs
        .process_instruction(&ix, &[])
        .expect("qedsvm runs pinocchio escrow with empty data");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        PINOCCHIO_ESCROW_SO,
    );
    let m_r = m.process_instruction(&ix, &[]);

    assert!(!matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Failure, got Success");
    assert!(!matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Failure, got Success");
}

/// Inputs reach the program: pass non-empty `instruction.data` and
/// confirm both engines accept it without divergence.
#[test]
fn noop_with_instruction_data_matches_mollusk() {
    let program_id = pid(2);
    let data = b"\x01\x02\x03\x04".to_vec();
    let ix = Instruction { program_id, accounts: vec![], data };

    let mut fs = Svm::default();
    fs.add_program(&program_id, NOOP_SO);
    let fs_r = fs.process_instruction(&ix, &[]).expect("qedsvm runs");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        NOOP_SO,
    );
    let m_r = m.process_instruction(&ix, &[]);

    assert!(matches!(fs_r.program_result, FsProgramResult::Success));
    assert!(matches!(m_r.program_result, MlProgramResult::Success));
    assert_eq!(fs_r.return_data, m_r.return_data);
}

/// Phase 3-N CPI: caller forwards TWO writable accounts to
/// `incrementer.so`. The callee operates on `accounts[0]` only,
/// incrementing its `data[0..8]` u64. `accounts[1]` is passed through
/// unmodified. Asserts both engines agree on the full post-state —
/// proving N=2 marshaling (cumulative per-block offsets, per-slot
/// write-back pointers) is byte-for-byte correct, *and* that an
/// account that the callee reads but doesn't mutate still round-trips.
#[test]
fn cpi_two_account_caller_forwards_to_incrementer() {
    let caller_id = pid(60);
    let callee_id = pid(61);
    let acct0_key = pid(62);
    let acct1_key = pid(63);

    let lamports = 1_000_000u64;
    let data: Vec<u8> = vec![0u8; 16];
    let mk_shared = || AccountSharedData::from(Account {
        lamports, data: data.clone(), owner: callee_id,
        executable: false, rent_epoch: 0,
    });
    let mk_mollusk = || mollusk_account::Account {
        lamports, data: data.clone(), owner: callee_id,
        executable: false, rent_epoch: 0,
    };
    let callee_program_shared = AccountSharedData::from(Account {
        lamports: 1, data: vec![],
        owner: solana_sdk_ids::bpf_loader_upgradeable::id(),
        executable: true, rent_epoch: 0,
    });
    let callee_program_mollusk = mollusk_account::Account {
        lamports: 1, data: vec![],
        owner: solana_sdk_ids::bpf_loader_upgradeable::id(),
        executable: true, rent_epoch: 0,
    };

    let ix = Instruction {
        program_id: caller_id,
        accounts: vec![
            AccountMeta::new(acct0_key, false),
            AccountMeta::new(acct1_key, false),
            AccountMeta::new_readonly(callee_id, false),
        ],
        data: callee_id.to_bytes().to_vec(),
    };

    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&caller_id, CPI_TWO_ACCOUNT_CALLER_SO);
    fs.add_program(&callee_id, INCREMENTER_SO);
    let fs_r = fs.process_instruction(&ix, &[
        (acct0_key, mk_shared()),
        (acct1_key, mk_shared()),
        (callee_id, callee_program_shared),
    ]).expect("qedsvm runs N=2 CPI");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &caller_id, &solana_sdk_ids::bpf_loader_upgradeable::id(),
        CPI_TWO_ACCOUNT_CALLER_SO);
    m.add_program_with_loader_and_elf(
        &callee_id, &solana_sdk_ids::bpf_loader_upgradeable::id(), INCREMENTER_SO);
    let m_r = m.process_instruction(&ix, &[
        (acct0_key, mk_mollusk()),
        (acct1_key, mk_mollusk()),
        (callee_id, callee_program_mollusk),
    ]);

    let our_logs: Vec<String> = fs_r.logs.iter()
        .map(|b| String::from_utf8_lossy(b).into_owned()).collect();
    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success on N=2 CPI, got {:?}; logs: {our_logs:?}",
        fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success on N=2 CPI, got {:?}", m_r.program_result);

    // accounts[0] must be incremented to 1 (incrementer's effect),
    // accounts[1] must be unchanged (still 0). Both engines must
    // agree on both account contents.
    let mut expected_a = vec![0u8; 16];
    expected_a[..8].copy_from_slice(&1u64.to_le_bytes());
    let expected_b = vec![0u8; 16];

    let (_, fs_a) = &fs_r.resulting_accounts[0];
    let (_, fs_b) = &fs_r.resulting_accounts[1];
    let (_, m_a)  = &m_r.resulting_accounts[0];
    let (_, m_b)  = &m_r.resulting_accounts[1];

    assert_eq!(fs_a.data(), expected_a.as_slice(),
        "qedsvm: accounts[0] not incremented; got {:?}", fs_a.data());
    assert_eq!(fs_b.data(), expected_b.as_slice(),
        "qedsvm: accounts[1] changed unexpectedly; got {:?}", fs_b.data());
    assert_eq!(m_a.data.as_slice(), expected_a.as_slice());
    assert_eq!(m_b.data.as_slice(), expected_b.as_slice());

    // Cross-engine byte-for-byte agreement on every account.
    assert_eq!(fs_a.data(), m_a.data.as_slice(), "accounts[0] diverged");
    assert_eq!(fs_b.data(), m_b.data.as_slice(), "accounts[1] diverged");
    assert_eq!(fs_a.lamports(), m_a.lamports, "accounts[0] lamports diverged");
    assert_eq!(fs_b.lamports(), m_b.lamports, "accounts[1] lamports diverged");
}

/// Surfaces the `R_BPF_64_Relative`-in-`.text` loader bug. The
/// program (built from `rodata_addr_returner_src/`) takes the address
/// of a `#[used] static RODATA_CONST: u64` (which lives in
/// `.rodata`), forces a volatile read so the compiler can't fold the
/// address, and returns the upper 32 bits as the entrypoint exit
/// code.
///
/// On agave: the loader patches the `lddw` imm `+= MM_REGION_SIZE`
/// so the address sits in the program region; upper 32 bits = `0x1`
/// → entrypoint returns `1` → `ProgramResult::Failure(Custom(1))`.
///
/// Pre-fix qedsvm: `applyRelocations` left `R_BPF_64_Relative`
/// in `.text` unpatched; the loaded address was the raw section VA
/// (typically `< 0x1_0000_0000`); upper 32 bits = `0` → entrypoint
/// returns `0` → `ProgramResult::Success`. Asymmetric outcome
/// (Failure vs Success) — divergence is immediate and unmissable.
///
/// Post-fix (this test): both engines return exit code 1 → both
/// `Failure(Custom(1))`. Asserts on `program_result` matching, plus
/// CU equality.
#[test]
fn rodata_addr_returner_matches_mollusk() {
    let program_id = pid(40);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };

    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&program_id, RODATA_ADDR_RETURNER_SO);
    let fs_r = fs
        .process_instruction(&ix, &[])
        .expect("qedsvm runs rodata_addr_returner");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        RODATA_ADDR_RETURNER_SO,
    );
    let m_r = m.process_instruction(&ix, &[]);

    eprintln!("fs.program_result   = {:?}", fs_r.program_result);
    eprintln!("mol.program_result  = {:?}", m_r.program_result);
    eprintln!("fs.cu_consumed      = {}", fs_r.compute_units_consumed);
    eprintln!("mol.cu_consumed     = {}", m_r.compute_units_consumed);

    // Both engines must reach the *same* outcome (post-fix: Failure
    // because the relocated address has upper bits = 1 → exit code 1
    // → Failure(Custom(1))). Pre-fix, ours would land at Success
    // (exit 0) and mollusk at Failure — that's the divergence the
    // fix closes.
    assert!(!matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected non-Success (exit code = upper 32 bits = 1), \
         got {:?} — this means R_BPF_64_Relative-in-.text isn't being applied",
        fs_r.program_result);
    assert!(!matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected non-Success, got {:?}", m_r.program_result);

    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );

    // Soundness-audit M5 pin (lddw CU weight): this `.text` is 5 byte-slots
    // = 4 LOGICAL instructions — `lddw` (slots 0-1, the rodata address
    // materialization), `ldx`, `rsh`, `exit` — and the entrypoint is
    // branchless, so all 4 execute exactly once. Both engines report CU=4,
    // NOT 5. That refutes the audit's "lddw is metered by slot-delta so it
    // costs 2" hypothesis: agave meters `lddw` as ONE logical instruction
    // (the interpreter's meter ticks once per step even though `lddw`
    // advances pc by 2), exactly as the Lean model's `chargeCu` does. A
    // regression that double-charged `lddw` would make ours=4, mollusk=4
    // still agree, so pin the concrete agave value too.
    assert_eq!(m_r.compute_units_consumed, 4,
        "M5: agave must meter the 4-logical-insn (1 lddw) program at 4 CU, \
         got {} — lddw CU weight changed in agave", m_r.compute_units_consumed);
}

/// `sol_curve_multiscalar_mul` CU referee (soundness-audit M9). The
/// fixture calls Edwards MSM with n=1 (boundary: agave charges the bare
/// `msm_base_cost` 2273 — the incremental cost is `758*(n-1)`,
/// agave-syscalls lib.rs:1711-1716) and n=2 (2273 + 758), returning
/// `r0_1 + r0_2` (0 iff both succeed). Under the pre-M9 model formula
/// (`base + incr*n`) the model would over-charge by 758 per call (1516
/// total), so CU equality here discriminates the `(n-1)` form, n=1
/// boundary included.
#[test]
fn curve_msm_cu_matches_mollusk() {
    let program_id = pid(73);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };

    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&program_id, CURVE_MSM_PROBE_SO);
    let fs_r = fs
        .process_instruction(&ix, &[])
        .expect("qedsvm runs curve_msm_probe");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        CURVE_MSM_PROBE_SO,
    );
    let m_r = m.process_instruction(&ix, &[]);

    eprintln!("fs.program_result   = {:?}", fs_r.program_result);
    eprintln!("mol.program_result  = {:?}", m_r.program_result);
    eprintln!("fs.cu_consumed      = {}", fs_r.compute_units_consumed);
    eprintln!("mol.cu_consumed     = {}", m_r.compute_units_consumed);

    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: both MSM calls must succeed (r0=0), got {:?}",
        fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: both MSM calls must succeed, got {:?}", m_r.program_result);

    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "M9 MSM CU diverged (the base + 758*(n-1) formula): ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// L1 sentinel-collision experiment (soundness-audit L1, closure-plan
/// phase 3 step 0): a healthy program CLEANLY exits with
/// r0 = 0xFFFFFFFFFFFFFFFD — numerically identical to the model's
/// ERR_ABORT fault sentinel. This prints what each engine observably
/// reports, pinning the wire mapping BEFORE the vmError exit-shape
/// refactor. Both engines must at least agree (the clean exit and the
/// fault land in the same observable class today — that sameness is
/// exactly the L1 incompleteness being closed).
#[test]
fn sentinel_clean_exit_observability() {
    let program_id = pid(74);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };

    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&program_id, SENTINEL_EXIT_SO);
    let fs_r = fs
        .process_instruction(&ix, &[])
        .expect("qedsvm runs sentinel_exit");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        SENTINEL_EXIT_SO,
    );
    let m_r = m.process_instruction(&ix, &[]);

    eprintln!("L1 EXPERIMENT: clean exit with r0 = 0xFFFFFFFFFFFFFFFD");
    eprintln!("fs.program_result   = {:?}", fs_r.program_result);
    eprintln!("mol.program_result  = {:?}", m_r.program_result);
    eprintln!("fs.cu_consumed      = {}", fs_r.compute_units_consumed);
    eprintln!("mol.cu_consumed     = {}", m_r.compute_units_consumed);

    // Cross-engine agreement on the observable class: both non-Success.
    assert!(!matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: nonzero r0 must not be Success, got {:?}", fs_r.program_result);
    assert!(!matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: nonzero r0 must not be Success, got {:?}", m_r.program_result);
    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// Exercises `sol_try_find_program_address` end-to-end with one seed
/// (`b"vault"`) and a hard-coded program_id. Asserts:
/// - Both engines reach `Success`.
/// - The 33-byte `return_data` (PDA + bump) is byte-identical — so
///   the PDA derivation itself matches agave.
/// - CU consumed is equal — load-bearing for the
///   `Pda.cuTryFind`-via-`syscallCu` per-iteration charge.
///
/// This fixture also exercises `lean_curve_validate_edwards` through
/// the compiled-native runtime FFI; it was blocked by a missing
/// dynamic-symbol-table export (build.rs FFI symbol pull-in) until
/// that fix landed alongside this test.
#[test]
fn pda_finder_matches_mollusk() {
    let program_id = pid(50);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };

    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&program_id, PDA_FINDER_SO);
    let fs_r = fs
        .process_instruction(&ix, &[])
        .expect("qedsvm runs pda_finder");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        PDA_FINDER_SO,
    );
    let m_r = m.process_instruction(&ix, &[]);

    eprintln!("fs.program_result   = {:?}", fs_r.program_result);
    eprintln!("mol.program_result  = {:?}", m_r.program_result);
    eprintln!("fs.return_data      = {:?}", fs_r.return_data);
    eprintln!("mol.return_data     = {:?}", m_r.return_data);
    eprintln!("fs.cu_consumed      = {}", fs_r.compute_units_consumed);
    eprintln!("mol.cu_consumed     = {}", m_r.compute_units_consumed);
    if fs_r.return_data.len() == 33 {
        eprintln!("fs.bump             = {}", fs_r.return_data[32]);
    }

    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success, got {:?}", fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success, got {:?}", m_r.program_result);

    assert_eq!(fs_r.return_data, m_r.return_data,
        "return_data diverged: fs={:?} mol={:?}", fs_r.return_data, m_r.return_data);
    assert_eq!(fs_r.return_data.len(), 33,
        "expected 33-byte return_data (32-byte PDA + 1-byte bump)");

    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged: ours={} mollusk={} — Pda.cuTryFind per-iteration \
         charge must match agave's per-attempt model",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// Tier-1 #1 region bounds enforcement. The program dereferences
/// `input.add(0x10000000)` — well outside any mapped region. Both
/// engines must fail; pre-fix qedsvm let the read slide and
/// returned Success.
#[test]
fn oob_read_fails_on_both() {
    let program_id = pid(51);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };

    let mut fs = Svm::default();
    fs.add_program(&program_id, OOB_READ_SO);
    let fs_r = fs
        .process_instruction(&ix, &[])
        .expect("qedsvm runs oob_read");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        OOB_READ_SO,
    );
    let m_r = m.process_instruction(&ix, &[]);

    eprintln!("fs.program_result  = {:?}", fs_r.program_result);
    eprintln!("mol.program_result = {:?}", m_r.program_result);

    // M14: the model VM-faults (access violation) and agave surfaces it
    // as UnknownError(ProgramFailedToComplete) — same observable outcome,
    // not merely "both non-Success".
    assert!(matches!(fs_r.program_result, FsProgramResult::VmFault { .. }),
        "qedsvm should VM-fault on OOB read, got {:?}", fs_r.program_result);
    assert_outcome_matches(&fs_r.program_result, &m_r.program_result, "oob_read");
}

/// Audit H6 (syscall memory translation). The program calls
/// `sol_memset_` with a destination 256 MiB past the input pointer.
/// agave's `translate_slice_mut` traps with `AccessViolation`; pre-fix
/// qedsvm wrote through a region-free `Mem` and returned Success. Post-fix
/// `MemOps.execSet`'s `guardWrite` consults the runtime region table and
/// VM-faults. Both engines must fail with the same observable outcome.
#[test]
fn oob_memset_fails_on_both() {
    let program_id = pid(52);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };

    let mut fs = Svm::default();
    fs.add_program(&program_id, OOB_MEMSET_SO);
    let fs_r = fs
        .process_instruction(&ix, &[])
        .expect("qedsvm runs oob_memset");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        OOB_MEMSET_SO,
    );
    let m_r = m.process_instruction(&ix, &[]);

    eprintln!("fs.program_result  = {:?}", fs_r.program_result);
    eprintln!("mol.program_result = {:?}", m_r.program_result);

    // The syscall's region check fails closed: the model VM-faults
    // (access violation), agave surfaces it as
    // UnknownError(ProgramFailedToComplete) — same observable outcome.
    assert!(matches!(fs_r.program_result, FsProgramResult::VmFault { .. }),
        "qedsvm should VM-fault on OOB sol_memset_, got {:?}", fs_r.program_result);
    assert_outcome_matches(&fs_r.program_result, &m_r.program_result, "oob_memset");
}

/// Audit H6 (syscall memory translation, logging family). The program
/// calls `sol_log_pubkey` with a pointer 256 MiB past the input pointer.
/// agave's `translate_type::<Pubkey>` traps the 32-byte read with
/// `AccessViolation`; post-fix `Logging.execLogPubkey`'s `guardRead`
/// VM-faults. Both engines must fail with the same observable outcome.
#[test]
fn oob_log_pubkey_fails_on_both() {
    let program_id = pid(53);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };

    let mut fs = Svm::default();
    fs.add_program(&program_id, OOB_LOG_PUBKEY_SO);
    let fs_r = fs
        .process_instruction(&ix, &[])
        .expect("qedsvm runs oob_log_pubkey");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        OOB_LOG_PUBKEY_SO,
    );
    let m_r = m.process_instruction(&ix, &[]);

    eprintln!("fs.program_result  = {:?}", fs_r.program_result);
    eprintln!("mol.program_result = {:?}", m_r.program_result);

    assert!(matches!(fs_r.program_result, FsProgramResult::VmFault { .. }),
        "qedsvm should VM-fault on OOB sol_log_pubkey, got {:?}", fs_r.program_result);
    assert_outcome_matches(&fs_r.program_result, &m_r.program_result, "oob_log_pubkey");
}

/// Audit H6 (syscall memory translation, logging family). The program
/// calls `sol_log_` with a 16-byte message 256 MiB past the input
/// pointer. agave's `translate_slice` traps the read with
/// `AccessViolation`; post-fix `Logging.execLog`'s `guardRead` VM-faults.
/// Both engines must fail with the same observable outcome.
#[test]
fn oob_log_fails_on_both() {
    let program_id = pid(54);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };

    let mut fs = Svm::default();
    fs.add_program(&program_id, OOB_LOG_SO);
    let fs_r = fs
        .process_instruction(&ix, &[])
        .expect("qedsvm runs oob_log");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        OOB_LOG_SO,
    );
    let m_r = m.process_instruction(&ix, &[]);

    eprintln!("fs.program_result  = {:?}", fs_r.program_result);
    eprintln!("mol.program_result = {:?}", m_r.program_result);

    assert!(matches!(fs_r.program_result, FsProgramResult::VmFault { .. }),
        "qedsvm should VM-fault on OOB sol_log_, got {:?}", fs_r.program_result);
    assert_outcome_matches(&fs_r.program_result, &m_r.program_result, "oob_log");
}

/// Audit H6 (syscall memory translation, descriptor-array / logging tail).
/// The program calls `sol_log_data` with a 1-descriptor array 256 MiB past
/// the input pointer. agave translates the 16-byte descriptor array via
/// `translate_slice::<VmSlice<u8>>` BEFORE dereferencing any slice, so the
/// array read itself traps with `AccessViolation`; post-fix
/// `Logging.execLogData`'s `guardRead` on `[r1, r1 + count*16)` VM-faults.
/// Both engines must fail with the same observable outcome.
#[test]
fn oob_log_data_fails_on_both() {
    let program_id = pid(56);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };

    let mut fs = Svm::default();
    fs.add_program(&program_id, OOB_LOG_DATA_SO);
    let fs_r = fs
        .process_instruction(&ix, &[])
        .expect("qedsvm runs oob_log_data");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        OOB_LOG_DATA_SO,
    );
    let m_r = m.process_instruction(&ix, &[]);

    eprintln!("fs.program_result  = {:?}", fs_r.program_result);
    eprintln!("mol.program_result = {:?}", m_r.program_result);

    assert!(matches!(fs_r.program_result, FsProgramResult::VmFault { .. }),
        "qedsvm should VM-fault on OOB sol_log_data, got {:?}", fs_r.program_result);
    assert_outcome_matches(&fs_r.program_result, &m_r.program_result, "oob_log_data");
}

/// Audit H6 (syscall memory translation, hashing family, stage 3a /
/// output-write guard). The program calls `sol_sha256` with a 0-slice input
/// and a 32-byte output buffer 256 MiB past the input pointer. agave
/// translates the output via `translate_slice_mut::<u8>(out, 32)` BEFORE the
/// (empty) input, so the out-of-region store traps with `AccessViolation`;
/// post-fix `Sha256.exec`'s `guardWrite` on `[r3, r3 + 32)` VM-faults.
/// Both engines must fail with the same observable outcome.
#[test]
fn oob_sha256_output_fails_on_both() {
    let program_id = pid(242);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };

    let mut fs = Svm::default();
    fs.add_program(&program_id, OOB_SHA256_SO);
    let fs_r = fs
        .process_instruction(&ix, &[])
        .expect("qedsvm runs oob_sha256");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        OOB_SHA256_SO,
    );
    let m_r = m.process_instruction(&ix, &[]);

    eprintln!("fs.program_result  = {:?}", fs_r.program_result);
    eprintln!("mol.program_result = {:?}", m_r.program_result);

    assert!(matches!(fs_r.program_result, FsProgramResult::VmFault { .. }),
        "qedsvm should VM-fault on OOB sol_sha256 output, got {:?}", fs_r.program_result);
    assert_outcome_matches(&fs_r.program_result, &m_r.program_result, "oob_sha256");
}

/// Audit H6 (syscall memory translation, hashing family, stage 3b /
/// input-slice guard). The program calls `sol_sha256` with a valid writable
/// output but a 1-descriptor input array 256 MiB out of region. agave
/// translates the output first (passes), then the descriptor array (out of
/// region → `AccessViolation`); post-fix `Sha256.exec`'s `guardRead` on
/// `[r1, r1 + r2*16)` VM-faults. Both engines fail with the same outcome.
#[test]
fn oob_sha256_input_fails_on_both() {
    let program_id = pid(243);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };

    let mut fs = Svm::default();
    fs.add_program(&program_id, OOB_SHA256_INPUT_SO);
    let fs_r = fs
        .process_instruction(&ix, &[])
        .expect("qedsvm runs oob_sha256_input");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        OOB_SHA256_INPUT_SO,
    );
    let m_r = m.process_instruction(&ix, &[]);

    eprintln!("fs.program_result  = {:?}", fs_r.program_result);
    eprintln!("mol.program_result = {:?}", m_r.program_result);

    assert!(matches!(fs_r.program_result, FsProgramResult::VmFault { .. }),
        "qedsvm should VM-fault on OOB sol_sha256 input, got {:?}", fs_r.program_result);
    assert_outcome_matches(&fs_r.program_result, &m_r.program_result, "oob_sha256_input");
}

/// Audit H6 (syscall memory translation, hashing family, stage 3c / poseidon
/// input-slice guard). The program calls `sol_poseidon` with a valid writable
/// output but a 1-descriptor input array 256 MiB out of region. agave
/// translates the output first (passes), then the descriptor array (out of
/// region → `AccessViolation`); post-fix `Poseidon.exec`'s `guardedCommit`
/// `guardRead` on `[r3, r3 + r4*16)` VM-faults. Both engines fail alike.
#[test]
fn oob_poseidon_input_fails_on_both() {
    let program_id = pid(244);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };

    let mut fs = Svm::default();
    fs.add_program(&program_id, OOB_POSEIDON_INPUT_SO);
    let fs_r = fs
        .process_instruction(&ix, &[])
        .expect("qedsvm runs oob_poseidon_input");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        OOB_POSEIDON_INPUT_SO,
    );
    let m_r = m.process_instruction(&ix, &[]);

    eprintln!("fs.program_result  = {:?}", fs_r.program_result);
    eprintln!("mol.program_result = {:?}", m_r.program_result);

    assert!(matches!(fs_r.program_result, FsProgramResult::VmFault { .. }),
        "qedsvm should VM-fault on OOB sol_poseidon input, got {:?}", fs_r.program_result);
    assert_outcome_matches(&fs_r.program_result, &m_r.program_result, "oob_poseidon_input");
}

/// Audit H6 (syscall memory translation, sysvar family / fixed-size getters,
/// stage 4a). The program calls `sol_get_clock_sysvar` with a 40-byte output
/// buffer 256 MiB out of region. agave's `translate_type_mut::<Clock>` traps
/// with `AccessViolation`; post-fix `Sysvar.execClock` (via `zeroFillR1`)
/// `guardWrite` on `[r1, r1 + 40)` VM-faults. Both engines fail alike.
#[test]
fn oob_clock_sysvar_fails_on_both() {
    let program_id = pid(245);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };

    let mut fs = Svm::default();
    fs.add_program(&program_id, OOB_CLOCK_SYSVAR_SO);
    let fs_r = fs
        .process_instruction(&ix, &[])
        .expect("qedsvm runs oob_clock_sysvar");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        OOB_CLOCK_SYSVAR_SO,
    );
    let m_r = m.process_instruction(&ix, &[]);

    eprintln!("fs.program_result  = {:?}", fs_r.program_result);
    eprintln!("mol.program_result = {:?}", m_r.program_result);

    assert!(matches!(fs_r.program_result, FsProgramResult::VmFault { .. }),
        "qedsvm should VM-fault on OOB sol_get_clock_sysvar, got {:?}", fs_r.program_result);
    assert_outcome_matches(&fs_r.program_result, &m_r.program_result, "oob_clock_sysvar");
}

/// Audit H6 (syscall memory translation, return-data family, stage 4b /
/// input read guard). The program calls `sol_set_return_data` with an 8-byte
/// input slice (within MAX_RETURN_DATA) 256 MiB out of region. agave checks
/// the length first (passes), then `translate_slice` traps with
/// `AccessViolation`; post-fix `ReturnData.execSet`'s `guardRead` on
/// `[r1, r1 + r2)` VM-faults. Both engines fail alike.
#[test]
fn oob_set_return_data_fails_on_both() {
    let program_id = pid(246);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };

    let mut fs = Svm::default();
    fs.add_program(&program_id, OOB_SET_RETURN_DATA_SO);
    let fs_r = fs
        .process_instruction(&ix, &[])
        .expect("qedsvm runs oob_set_return_data");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        OOB_SET_RETURN_DATA_SO,
    );
    let m_r = m.process_instruction(&ix, &[]);

    eprintln!("fs.program_result  = {:?}", fs_r.program_result);
    eprintln!("mol.program_result = {:?}", m_r.program_result);

    assert!(matches!(fs_r.program_result, FsProgramResult::VmFault { .. }),
        "qedsvm should VM-fault on OOB sol_set_return_data, got {:?}", fs_r.program_result);
    assert_outcome_matches(&fs_r.program_result, &m_r.program_result, "oob_set_return_data");
}

/// Tier-1 #2 native programs (System, foremost). A BPF caller does
/// `invoke(&system_instruction::transfer(...), &[from, to])`. Mollusk
/// has System registered by default; qedsvm's `Native.dispatch`
/// recognises the all-zero program-id and routes to
/// `System::execTransfer`. Both engines must end with
/// `from -= n`, `to += n`.
#[test]
fn system_transfer_cpi_matches_mollusk() {
    let caller_id = pid(60);
    let from_pk   = pid(61);
    let to_pk     = pid(62);

    let lamports_to_send: u64 = 1_000;
    let initial_from: u64 = 5_000_000;
    let initial_to: u64   =   100_000;

    // The System program's pubkey (all-zero). Passing it as a
    // read-only AccountMeta on the outer ix registers it in the
    // transaction's account-key set so agave can dispatch the CPI.
    let system_program_id = Pubkey::new_from_array([0u8; 32]);

    let ix = Instruction {
        program_id: caller_id,
        // System::Transfer wants accounts[0] = from (signer, writable),
        // accounts[1] = to (writable), accounts[2] = system_program
        // (read-only — needed for CPI dispatch registration only).
        accounts: vec![
            AccountMeta::new(from_pk, true),
            AccountMeta::new(to_pk,   false),
            AccountMeta::new_readonly(system_program_id, false),
        ],
        data: lamports_to_send.to_le_bytes().to_vec(),
    };

    // Lamport-bearing accounts are owned by the System program
    // (all-zero pubkey).
    let system_owner = Pubkey::new_from_array([0u8; 32]);

    let from_pre = AccountSharedData::from(Account {
        lamports: initial_from, data: vec![],
        owner: system_owner, executable: false, rent_epoch: 0,
    });
    let to_pre = AccountSharedData::from(Account {
        lamports: initial_to, data: vec![],
        owner: system_owner, executable: false, rent_epoch: 0,
    });
    let from_pre_m = mollusk_account::Account {
        lamports: initial_from, data: vec![],
        owner: system_owner, executable: false, rent_epoch: 0,
    };
    let to_pre_m = mollusk_account::Account {
        lamports: initial_to, data: vec![],
        owner: system_owner, executable: false, rent_epoch: 0,
    };

    // Stub account for the System program. Both engines need this
    // entry in the per-call accounts to satisfy the serializer's
    // AccountMeta → AccountSharedData lookup; the program impl
    // itself is registered separately (built-in in mollusk,
    // `Native.dispatch` keyed on pubkey in qedsvm). Mirror
    // mollusk's stub byte-for-byte so the resulting_accounts
    // comparison stays clean.
    let (mollusk_system_id, mollusk_system_acct) =
        mollusk_svm::program::keyed_account_for_system_program();
    let system_stub_fs = AccountSharedData::from(Account {
        lamports: mollusk_system_acct.lamports,
        data: mollusk_system_acct.data.clone(),
        owner: mollusk_system_acct.owner,
        executable: mollusk_system_acct.executable,
        rent_epoch: mollusk_system_acct.rent_epoch,
    });

    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&caller_id, SYSTEM_TRANSFER_CALLER_SO);
    let fs_r = fs.process_instruction(&ix, &[
        (from_pk, from_pre),
        (to_pk,   to_pre),
        (system_program_id, system_stub_fs),
    ]).expect("qedsvm runs CPI → System::Transfer");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &caller_id, &solana_sdk_ids::bpf_loader_upgradeable::id(),
        SYSTEM_TRANSFER_CALLER_SO);
    let m_r = m.process_instruction(&ix, &[
        (from_pk, from_pre_m),
        (to_pk,   to_pre_m),
        (mollusk_system_id, mollusk_system_acct),
    ]);

    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success, got {:?}", fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success, got {:?}", m_r.program_result);
    // Lamport conservation here must hold in the VM itself, not via the
    // Rust backstop downgrading a mint to ERR_INVALID_POSTSTATE (M13).
    assert_no_poststate_backstop(&fs_r);

    // Lamport equality between the two engines on each account.
    assert_eq!(fs_r.resulting_accounts.len(), m_r.resulting_accounts.len(),
        "resulting_accounts count diverged");
    for ((k_a, a_a), (k_b, a_b)) in
        fs_r.resulting_accounts.iter().zip(m_r.resulting_accounts.iter())
    {
        assert_eq!(k_a, k_b, "pubkey order divergence");
        assert_eq!(a_a.lamports(), a_b.lamports,
            "lamports diverged for {k_a}: ours={} mollusk={}",
            a_a.lamports(), a_b.lamports);
    }

    // Concrete post-state values both engines must agree on.
    let fs_from = fs_r.resulting_accounts.iter().find(|(k, _)| *k == from_pk)
        .expect("from account present").1.lamports();
    let fs_to   = fs_r.resulting_accounts.iter().find(|(k, _)| *k == to_pk)
        .expect("to account present").1.lamports();
    assert_eq!(fs_from, initial_from - lamports_to_send,
        "from balance: expected {}, got {}", initial_from - lamports_to_send, fs_from);
    assert_eq!(fs_to,   initial_to   + lamports_to_send,
        "to balance: expected {}, got {}", initial_to + lamports_to_send, fs_to);

    // CU equality: caller's BPF insns + Cpi.cu (946 invoke_signed) +
    // 150 (System::Transfer's per-instruction cost). Mollusk reports
    // the same breakdown.
    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged for system_transfer CPI: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// Tier-1 #2 native, variant 2: System::CreateAccount. A BPF caller
/// CPIs `system_instruction::create_account(payer, newAcct,
/// lamports, space, owner)`. Both engines must mutate `newAcct` from
/// "uninitialized" (0 lamports, empty data, system-owned) to
/// (lamports, `space` zero bytes, target owner). Payer's balance
/// decrements by `lamports`.
#[test]
fn system_create_account_cpi_matches_mollusk() {
    let caller_id  = pid(70);
    let payer_pk   = pid(71);
    let new_pk     = pid(72);
    let target_owner = pid(73);  // arbitrary "program owner" for the new acct

    let lamports_to_send: u64 = 2_000_000;
    let space: u64 = 165;        // SPL Token's mint account size — common
                                  // real-world value, exercises a non-zero
                                  // space allocation through the syscall.
    let initial_payer: u64 = 5_000_000;

    let system_program_id = Pubkey::new_from_array([0u8; 32]);

    // Outer ix.data: 8 B lamports | 8 B space | 32 B owner = 48 B.
    let mut ix_data = Vec::with_capacity(48);
    ix_data.extend_from_slice(&lamports_to_send.to_le_bytes());
    ix_data.extend_from_slice(&space.to_le_bytes());
    ix_data.extend_from_slice(&target_owner.to_bytes());

    let ix = Instruction {
        program_id: caller_id,
        accounts: vec![
            AccountMeta::new(payer_pk, true),
            AccountMeta::new(new_pk,   true),  // newAcct must sign too
            AccountMeta::new_readonly(system_program_id, false),
        ],
        data: ix_data,
    };

    // pre-states: payer is funded + system-owned; newAcct is
    // uninitialized (0 lamports, empty data, system-owned).
    let payer_pre = AccountSharedData::from(Account {
        lamports: initial_payer, data: vec![],
        owner: system_program_id, executable: false, rent_epoch: 0,
    });
    let new_pre = AccountSharedData::from(Account {
        lamports: 0, data: vec![],
        owner: system_program_id, executable: false, rent_epoch: 0,
    });
    let payer_pre_m = mollusk_account::Account {
        lamports: initial_payer, data: vec![],
        owner: system_program_id, executable: false, rent_epoch: 0,
    };
    let new_pre_m = mollusk_account::Account {
        lamports: 0, data: vec![],
        owner: system_program_id, executable: false, rent_epoch: 0,
    };

    let (mollusk_system_id, mollusk_system_acct) =
        mollusk_svm::program::keyed_account_for_system_program();
    let system_stub_fs = AccountSharedData::from(Account {
        lamports: mollusk_system_acct.lamports,
        data: mollusk_system_acct.data.clone(),
        owner: mollusk_system_acct.owner,
        executable: mollusk_system_acct.executable,
        rent_epoch: mollusk_system_acct.rent_epoch,
    });

    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&caller_id, SYSTEM_CREATE_ACCOUNT_CALLER_SO);
    let fs_r = fs.process_instruction(&ix, &[
        (payer_pk, payer_pre),
        (new_pk,   new_pre),
        (system_program_id, system_stub_fs),
    ]).expect("qedsvm runs CPI → System::CreateAccount");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &caller_id, &solana_sdk_ids::bpf_loader_upgradeable::id(),
        SYSTEM_CREATE_ACCOUNT_CALLER_SO);
    let m_r = m.process_instruction(&ix, &[
        (payer_pk, payer_pre_m),
        (new_pk,   new_pre_m),
        (mollusk_system_id, mollusk_system_acct),
    ]);

    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success, got {:?}", fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success, got {:?}", m_r.program_result);

    assert_eq!(fs_r.resulting_accounts.len(), m_r.resulting_accounts.len(),
        "resulting_accounts count diverged");
    for ((k_a, a_a), (k_b, a_b)) in
        fs_r.resulting_accounts.iter().zip(m_r.resulting_accounts.iter())
    {
        assert_eq!(k_a, k_b, "pubkey order divergence");
        assert_eq!(a_a.lamports(), a_b.lamports,
            "lamports diverged for {k_a}: ours={} mollusk={}",
            a_a.lamports(), a_b.lamports);
        assert_eq!(a_a.data(), a_b.data.as_slice(),
            "data diverged for {k_a}: ours.len={} mollusk.len={}",
            a_a.data().len(), a_b.data.len());
        assert_eq!(a_a.owner(), &a_b.owner,
            "owner diverged for {k_a}");
    }

    // Concrete post-state checks for the new account.
    let new_acct = fs_r.resulting_accounts.iter().find(|(k, _)| *k == new_pk)
        .expect("newAcct present").1.clone();
    assert_eq!(new_acct.lamports(), lamports_to_send,
        "newAcct.lamports: expected {}, got {}", lamports_to_send, new_acct.lamports());
    assert_eq!(new_acct.data().len(), space as usize,
        "newAcct.data.len: expected {}, got {}", space, new_acct.data().len());
    assert!(new_acct.data().iter().all(|&b| b == 0),
        "newAcct.data should be all zeros");
    assert_eq!(new_acct.owner(), &target_owner,
        "newAcct.owner: expected {}, got {}", target_owner, new_acct.owner());

    let payer = fs_r.resulting_accounts.iter().find(|(k, _)| *k == payer_pk)
        .expect("payer present").1.clone();
    assert_eq!(payer.lamports(), initial_payer - lamports_to_send,
        "payer.lamports: expected {}, got {}",
        initial_payer - lamports_to_send, payer.lamports());

    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged for system_create_account CPI: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// Tier-1 #2 native, variants 3 + 4: `System::Allocate` and
/// `System::Assign`. A BPF caller chains both on the same signer
/// account: Allocate(space) then Assign(owner). After: data.len() =
/// space (zeros), owner = target. Each CPI charges
/// `Cpi.cu + 150`, so the chain is 2 * (946 + 150) = 2192 atop the
/// caller's BPF insns.
#[test]
fn system_allocate_assign_cpi_matches_mollusk() {
    let caller_id    = pid(80);
    let acct_pk      = pid(81);
    let target_owner = pid(82);

    let space: u64 = 165;
    let initial_lamports: u64 = 7_000_000;  // not touched by either op

    let system_program_id = Pubkey::new_from_array([0u8; 32]);

    let mut ix_data = Vec::with_capacity(40);
    ix_data.extend_from_slice(&space.to_le_bytes());
    ix_data.extend_from_slice(&target_owner.to_bytes());

    let ix = Instruction {
        program_id: caller_id,
        accounts: vec![
            AccountMeta::new(acct_pk, true),  // signer for both ops
            AccountMeta::new_readonly(system_program_id, false),
        ],
        data: ix_data,
    };

    // Pre-state: uninitialized (data_len=0, system-owned). Lamports
    // are non-zero — Allocate doesn't require a zero balance, only
    // the data + owner predicates.
    let acct_pre = AccountSharedData::from(Account {
        lamports: initial_lamports, data: vec![],
        owner: system_program_id, executable: false, rent_epoch: 0,
    });
    let acct_pre_m = mollusk_account::Account {
        lamports: initial_lamports, data: vec![],
        owner: system_program_id, executable: false, rent_epoch: 0,
    };

    let (mollusk_system_id, mollusk_system_acct) =
        mollusk_svm::program::keyed_account_for_system_program();
    let system_stub_fs = AccountSharedData::from(Account {
        lamports: mollusk_system_acct.lamports,
        data: mollusk_system_acct.data.clone(),
        owner: mollusk_system_acct.owner,
        executable: mollusk_system_acct.executable,
        rent_epoch: mollusk_system_acct.rent_epoch,
    });

    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&caller_id, SYSTEM_ALLOCATE_ASSIGN_CALLER_SO);
    let fs_r = fs.process_instruction(&ix, &[
        (acct_pk, acct_pre),
        (system_program_id, system_stub_fs),
    ]).expect("qedsvm runs CPI → Allocate + Assign");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &caller_id, &solana_sdk_ids::bpf_loader_upgradeable::id(),
        SYSTEM_ALLOCATE_ASSIGN_CALLER_SO);
    let m_r = m.process_instruction(&ix, &[
        (acct_pk, acct_pre_m),
        (mollusk_system_id, mollusk_system_acct),
    ]);

    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success, got {:?}", fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success, got {:?}", m_r.program_result);

    assert_eq!(fs_r.resulting_accounts.len(), m_r.resulting_accounts.len());
    for ((k_a, a_a), (k_b, a_b)) in
        fs_r.resulting_accounts.iter().zip(m_r.resulting_accounts.iter())
    {
        assert_eq!(k_a, k_b);
        assert_eq!(a_a.lamports(), a_b.lamports,
            "lamports diverged for {k_a}: ours={} mollusk={}",
            a_a.lamports(), a_b.lamports);
        assert_eq!(a_a.data(), a_b.data.as_slice(),
            "data diverged for {k_a}");
        assert_eq!(a_a.owner(), &a_b.owner, "owner diverged for {k_a}");
    }

    let post = fs_r.resulting_accounts.iter().find(|(k, _)| *k == acct_pk)
        .expect("acct present").1.clone();
    assert_eq!(post.lamports(), initial_lamports, "lamports should be unchanged");
    assert_eq!(post.data().len(), space as usize,
        "expected {} bytes, got {}", space, post.data().len());
    assert!(post.data().iter().all(|&b| b == 0), "data should be all zeros");
    assert_eq!(post.owner(), &target_owner, "owner should be reassigned");

    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged for allocate+assign chain: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// Tier-1 #2 native, variant 5: `System::CreateAccountWithSeed`.
/// The derived account address must equal `SHA256(base || seed ||
/// owner)` — this is the deterministic-PDA-like pattern most vault
/// programs use to spawn per-user accounts without an extra signer
/// keypair. Verifies the seed-derivation arithmetic agrees with
/// agave's `Pubkey::create_with_seed`.
#[test]
fn system_create_account_with_seed_cpi_matches_mollusk() {
    let caller_id    = pid(90);
    let payer_pk     = pid(91);
    let base_pk      = pid(92);
    let target_owner = pid(93);

    let seed = "vault";
    let lamports_to_send: u64 = 2_000_000;
    let space: u64 = 64;
    let initial_payer: u64 = 5_000_000;

    // Derive the seed account address the same way agave / our
    // execCreateAccountWithSeed will:
    let derived_pk = Pubkey::create_with_seed(&base_pk, seed, &target_owner)
        .expect("create_with_seed");

    let system_program_id = Pubkey::new_from_array([0u8; 32]);

    let mut ix_data = Vec::with_capacity(52 + seed.len());
    ix_data.extend_from_slice(&lamports_to_send.to_le_bytes());
    ix_data.extend_from_slice(&space.to_le_bytes());
    ix_data.extend_from_slice(&target_owner.to_bytes());
    ix_data.extend_from_slice(&(seed.len() as u32).to_le_bytes());
    ix_data.extend_from_slice(seed.as_bytes());

    let ix = Instruction {
        program_id: caller_id,
        // Outer ix.accounts:
        //   [0] payer        (signer, writable)
        //   [1] derived      (writable; matches SHA256(base||seed||owner))
        //   [2] base         (signer)
        //   [3] system_program (read-only, dispatch registration)
        accounts: vec![
            AccountMeta::new(payer_pk, true),
            AccountMeta::new(derived_pk, false),
            AccountMeta::new_readonly(base_pk, true),
            AccountMeta::new_readonly(system_program_id, false),
        ],
        data: ix_data,
    };

    let payer_pre = AccountSharedData::from(Account {
        lamports: initial_payer, data: vec![],
        owner: system_program_id, executable: false, rent_epoch: 0,
    });
    let derived_pre = AccountSharedData::from(Account {
        lamports: 0, data: vec![],
        owner: system_program_id, executable: false, rent_epoch: 0,
    });
    let base_pre = AccountSharedData::from(Account {
        lamports: 1, data: vec![],
        owner: system_program_id, executable: false, rent_epoch: 0,
    });
    let payer_pre_m = mollusk_account::Account {
        lamports: initial_payer, data: vec![],
        owner: system_program_id, executable: false, rent_epoch: 0,
    };
    let derived_pre_m = mollusk_account::Account {
        lamports: 0, data: vec![],
        owner: system_program_id, executable: false, rent_epoch: 0,
    };
    let base_pre_m = mollusk_account::Account {
        lamports: 1, data: vec![],
        owner: system_program_id, executable: false, rent_epoch: 0,
    };

    let (mollusk_system_id, mollusk_system_acct) =
        mollusk_svm::program::keyed_account_for_system_program();
    let system_stub_fs = AccountSharedData::from(Account {
        lamports: mollusk_system_acct.lamports,
        data: mollusk_system_acct.data.clone(),
        owner: mollusk_system_acct.owner,
        executable: mollusk_system_acct.executable,
        rent_epoch: mollusk_system_acct.rent_epoch,
    });

    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&caller_id, SYSTEM_CREATE_ACCOUNT_WITH_SEED_CALLER_SO);
    let fs_r = fs.process_instruction(&ix, &[
        (payer_pk,   payer_pre),
        (derived_pk, derived_pre),
        (base_pk,    base_pre),
        (system_program_id, system_stub_fs),
    ]).expect("qedsvm runs CPI → CreateAccountWithSeed");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &caller_id, &solana_sdk_ids::bpf_loader_upgradeable::id(),
        SYSTEM_CREATE_ACCOUNT_WITH_SEED_CALLER_SO);
    let m_r = m.process_instruction(&ix, &[
        (payer_pk,   payer_pre_m),
        (derived_pk, derived_pre_m),
        (base_pk,    base_pre_m),
        (mollusk_system_id, mollusk_system_acct),
    ]);

    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success, got {:?}", fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success, got {:?}", m_r.program_result);

    // Lamport + data + owner equality across all accounts.
    assert_eq!(fs_r.resulting_accounts.len(), m_r.resulting_accounts.len());
    for ((k_a, a_a), (k_b, a_b)) in
        fs_r.resulting_accounts.iter().zip(m_r.resulting_accounts.iter())
    {
        assert_eq!(k_a, k_b);
        assert_eq!(a_a.lamports(), a_b.lamports,
            "lamports diverged for {k_a}: ours={} mollusk={}",
            a_a.lamports(), a_b.lamports);
        assert_eq!(a_a.data(), a_b.data.as_slice(),
            "data diverged for {k_a}");
        assert_eq!(a_a.owner(), &a_b.owner, "owner diverged for {k_a}");
    }

    // Post-state of the derived account specifically.
    let derived = fs_r.resulting_accounts.iter().find(|(k, _)| *k == derived_pk)
        .expect("derived present").1.clone();
    assert_eq!(derived.lamports(), lamports_to_send);
    assert_eq!(derived.data().len(), space as usize);
    assert!(derived.data().iter().all(|&b| b == 0));
    assert_eq!(derived.owner(), &target_owner);

    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged for CreateAccountWithSeed: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// Tier-1 #2: ComputeBudget native program. The CPI body is a
/// no-op on agave's side (the runtime handles ComputeBudget at
/// transaction-prepare time, not in-program); CPI through it just
/// charges 150 CU and returns success. Both engines must agree.
#[test]
fn compute_budget_cpi_matches_mollusk() {
    let caller_id = pid(100);

    let units: u32 = 200_000;
    let mut ix_data = Vec::with_capacity(4);
    ix_data.extend_from_slice(&units.to_le_bytes());

    let compute_budget_id = Pubkey::new_from_array([
        0x03, 0x06, 0x46, 0x6f, 0xe5, 0x21, 0x17, 0x32,
        0xff, 0xec, 0xad, 0xba, 0x72, 0xc3, 0x9b, 0xe7,
        0xbc, 0x8c, 0xe5, 0xbb, 0xc5, 0xf7, 0x12, 0x6b,
        0x2c, 0x43, 0x9b, 0x3a, 0x40, 0x00, 0x00, 0x00,
    ]);

    let ix = Instruction {
        program_id: caller_id,
        accounts: vec![
            // ComputeBudget needs to be in the transaction's
            // account-key set for the CPI's program-id lookup, even
            // though the BPF caller doesn't pass it through `invoke`.
            AccountMeta::new_readonly(compute_budget_id, false),
        ],
        data: ix_data,
    };

    // Mollusk's `keyed_account_for_builtin_program` only handles
    // System / loader stubs. ComputeBudget is a built-in too; we
    // construct an equivalent stub manually.
    let cb_stub_fs = AccountSharedData::from(Account {
        lamports: 1, data: b"compute_budget_program".to_vec(),
        owner: solana_sdk_ids::native_loader::id(),
        executable: true, rent_epoch: 0,
    });
    let cb_stub_m = mollusk_account::Account {
        lamports: 1, data: b"compute_budget_program".to_vec(),
        owner: solana_sdk_ids::native_loader::id(),
        executable: true, rent_epoch: 0,
    };

    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&caller_id, COMPUTE_BUDGET_CALLER_SO);
    let fs_r = fs.process_instruction(&ix, &[
        (compute_budget_id, cb_stub_fs),
    ]).expect("qedsvm runs CPI → ComputeBudget");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &caller_id, &solana_sdk_ids::bpf_loader_upgradeable::id(),
        COMPUTE_BUDGET_CALLER_SO);
    let m_r = m.process_instruction(&ix, &[
        (compute_budget_id, cb_stub_m),
    ]);

    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success, got {:?}", fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success, got {:?}", m_r.program_result);

    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged for ComputeBudget CPI: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// Gap-prober for the PDA signer-seeds path of CPI. Caller derives
/// a PDA from `b"vault" + caller_id`, passes it as accounts[1] in an
/// `invoke_signed(...)` call with seeds `[&[b"vault", &[bump]]]`. The
/// callee writes `0xAA` to `accounts[0].data[0]` if accounts[1]
/// is_signer, else `0x55`. Mollusk promotes the PDA via the seeds;
/// qedsvm currently ignores r4/r5 so the byte diverges. After
/// implementing seed-derived signer promotion in the Lean executor,
/// both engines should write `0xAA`.
#[test]
fn cpi_signed_pda_promotes_signer() {
    let caller_id = pid(200);
    let callee_id = pid(201);
    let data_key  = pid(202);

    let seed: &[u8] = b"vault";
    let (pda, _bump) = Pubkey::find_program_address(&[seed], &caller_id);

    let data: Vec<u8> = vec![0u8; 4];
    let data_pre_fs = AccountSharedData::from(Account {
        lamports: 1_000_000, data: data.clone(),
        owner: callee_id, executable: false, rent_epoch: 0,
    });
    let data_pre_ml = mollusk_account::Account {
        lamports: 1_000_000, data: data.clone(),
        owner: callee_id, executable: false, rent_epoch: 0,
    };

    // PDA account has no data; just exists so the AccountInfo can be
    // located by the CPI handler.
    let pda_pre_fs = AccountSharedData::from(Account {
        lamports: 0, data: vec![],
        owner: solana_sdk_ids::system_program::id(),
        executable: false, rent_epoch: 0,
    });
    let pda_pre_ml = mollusk_account::Account {
        lamports: 0, data: vec![],
        owner: solana_sdk_ids::system_program::id(),
        executable: false, rent_epoch: 0,
    };

    let callee_program_fs = AccountSharedData::from(Account {
        lamports: 1, data: vec![],
        owner: solana_sdk_ids::bpf_loader_upgradeable::id(),
        executable: true, rent_epoch: 0,
    });
    let callee_program_ml = mollusk_account::Account {
        lamports: 1, data: vec![],
        owner: solana_sdk_ids::bpf_loader_upgradeable::id(),
        executable: true, rent_epoch: 0,
    };

    let ix = Instruction {
        program_id: caller_id,
        accounts: vec![
            AccountMeta::new(data_key, false),
            AccountMeta::new_readonly(pda, false),
            AccountMeta::new_readonly(callee_id, false),
        ],
        data: callee_id.to_bytes().to_vec(),
    };

    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&caller_id, CPI_SIGNED_PDA_CALLER_SO);
    fs.add_program(&callee_id, CPI_SIGNED_PDA_CALLEE_SO);
    let fs_r = fs.process_instruction(&ix, &[
        (data_key, data_pre_fs),
        (pda, pda_pre_fs),
        (callee_id, callee_program_fs),
    ]).expect("qedsvm runs CPI signed PDA");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &caller_id, &solana_sdk_ids::bpf_loader_upgradeable::id(),
        CPI_SIGNED_PDA_CALLER_SO);
    m.add_program_with_loader_and_elf(
        &callee_id, &solana_sdk_ids::bpf_loader_upgradeable::id(),
        CPI_SIGNED_PDA_CALLEE_SO);
    let m_r = m.process_instruction(&ix, &[
        (data_key, data_pre_ml),
        (pda, pda_pre_ml),
        (callee_id, callee_program_ml),
    ]);

    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success, got {:?}", fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success, got {:?}", m_r.program_result);

    let (_, fs_data) = &fs_r.resulting_accounts[0];
    let (_, ml_data) = &m_r.resulting_accounts[0];
    assert_eq!(
        fs_data.data()[0], 0xAA,
        "qedsvm: PDA was not promoted to signer (got 0x{:02X}); mollusk byte is 0x{:02X}",
        fs_data.data()[0], ml_data.data[0],
    );
    assert_eq!(ml_data.data[0], 0xAA, "mollusk PDA promotion sanity");
}

/// Caller invokes a callee that sol_set_return_data's [0xAB, 0xCD,
/// 0xEF, 0x12], then sol_get_return_data and writes the bytes into
/// accounts[0].data. Verifies returnData propagation across a CPI
/// boundary.
#[test]
fn cpi_returns_data_propagates() {
    let caller_id = pid(210);
    let callee_id = pid(211);
    let data_key  = pid(212);

    let data: Vec<u8> = vec![0u8; 4];
    // Caller writes to data_key after reading return_data, so caller
    // must own it (agave enforces "only owner can mutate data").
    let data_pre_fs = AccountSharedData::from(Account {
        lamports: 1_000_000, data: data.clone(),
        owner: caller_id, executable: false, rent_epoch: 0,
    });
    let data_pre_ml = mollusk_account::Account {
        lamports: 1_000_000, data: data.clone(),
        owner: caller_id, executable: false, rent_epoch: 0,
    };

    let callee_program_fs = AccountSharedData::from(Account {
        lamports: 1, data: vec![],
        owner: solana_sdk_ids::bpf_loader_upgradeable::id(),
        executable: true, rent_epoch: 0,
    });
    let callee_program_ml = mollusk_account::Account {
        lamports: 1, data: vec![],
        owner: solana_sdk_ids::bpf_loader_upgradeable::id(),
        executable: true, rent_epoch: 0,
    };

    let ix = Instruction {
        program_id: caller_id,
        accounts: vec![
            AccountMeta::new(data_key, false),
            AccountMeta::new_readonly(callee_id, false),
        ],
        data: callee_id.to_bytes().to_vec(),
    };

    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&caller_id, CPI_GET_RETURN_DATA_CALLER_SO);
    fs.add_program(&callee_id, CPI_SET_RETURN_DATA_CALLEE_SO);
    let fs_r = fs.process_instruction(&ix, &[
        (data_key, data_pre_fs),
        (callee_id, callee_program_fs),
    ]).expect("qedsvm runs CPI returnData round-trip");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &caller_id, &solana_sdk_ids::bpf_loader_upgradeable::id(),
        CPI_GET_RETURN_DATA_CALLER_SO);
    m.add_program_with_loader_and_elf(
        &callee_id, &solana_sdk_ids::bpf_loader_upgradeable::id(),
        CPI_SET_RETURN_DATA_CALLEE_SO);
    let m_r = m.process_instruction(&ix, &[
        (data_key, data_pre_ml),
        (callee_id, callee_program_ml),
    ]);

    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success, got {:?}", fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success, got {:?}", m_r.program_result);

    let (_, fs_data) = &fs_r.resulting_accounts[0];
    let (_, ml_data) = &m_r.resulting_accounts[0];
    let expected = [0xAB, 0xCD, 0xEF, 0x12];
    assert_eq!(fs_data.data(), &expected,
        "qedsvm: return_data not propagated (got {:?})", fs_data.data());
    assert_eq!(ml_data.data.as_slice(), &expected,
        "mollusk: return_data not propagated (got {:?})", ml_data.data);
}

/// H7 pin: `sol_get_return_data` writes the SETTER's program id (the
/// CPI callee that called sol_set_return_data) into *pubkey_out — not
/// the caller's id and not a zero placeholder. The caller copies the
/// returned (pubkey, data) pair into accounts[0].data[0..36]; both
/// engines must produce the callee's id followed by the payload,
/// byte-identically.
#[test]
fn cpi_get_return_data_setter_pubkey_matches_mollusk() {
    let caller_id = pid(230);
    let callee_id = pid(231);
    let data_key  = pid(232);

    let data: Vec<u8> = vec![0u8; 36];
    let data_pre_fs = AccountSharedData::from(Account {
        lamports: 1_000_000, data: data.clone(),
        owner: caller_id, executable: false, rent_epoch: 0,
    });
    let data_pre_ml = mollusk_account::Account {
        lamports: 1_000_000, data: data.clone(),
        owner: caller_id, executable: false, rent_epoch: 0,
    };

    let callee_program_fs = AccountSharedData::from(Account {
        lamports: 1, data: vec![],
        owner: solana_sdk_ids::bpf_loader_upgradeable::id(),
        executable: true, rent_epoch: 0,
    });
    let callee_program_ml = mollusk_account::Account {
        lamports: 1, data: vec![],
        owner: solana_sdk_ids::bpf_loader_upgradeable::id(),
        executable: true, rent_epoch: 0,
    };

    let ix = Instruction {
        program_id: caller_id,
        accounts: vec![
            AccountMeta::new(data_key, false),
            AccountMeta::new_readonly(callee_id, false),
        ],
        data: callee_id.to_bytes().to_vec(),
    };

    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&caller_id, CPI_GET_RETURN_DATA_PUBKEY_SO);
    fs.add_program(&callee_id, CPI_SET_RETURN_DATA_CALLEE_SO);
    let fs_r = fs.process_instruction(&ix, &[
        (data_key, data_pre_fs),
        (callee_id, callee_program_fs),
    ]).expect("qedsvm runs CPI get_return_data pubkey round-trip");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &caller_id, &solana_sdk_ids::bpf_loader_upgradeable::id(),
        CPI_GET_RETURN_DATA_PUBKEY_SO);
    m.add_program_with_loader_and_elf(
        &callee_id, &solana_sdk_ids::bpf_loader_upgradeable::id(),
        CPI_SET_RETURN_DATA_CALLEE_SO);
    let m_r = m.process_instruction(&ix, &[
        (data_key, data_pre_ml),
        (callee_id, callee_program_ml),
    ]);

    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success, got {:?}", fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success, got {:?}", m_r.program_result);
    assert_no_poststate_backstop(&fs_r);

    let (_, fs_data) = &fs_r.resulting_accounts[0];
    let (_, ml_data) = &m_r.resulting_accounts[0];
    let mut expected = [0u8; 36];
    expected[..32].copy_from_slice(callee_id.as_ref());
    expected[32..].copy_from_slice(&[0xAB, 0xCD, 0xEF, 0x12]);
    assert_eq!(fs_data.data(), &expected,
        "qedsvm: setter pubkey/data mismatch (got {:?})", fs_data.data());
    assert_eq!(ml_data.data.as_slice(), &expected,
        "mollusk: setter pubkey/data mismatch (got {:?})", ml_data.data);
}

/// H7 pin: the SIMD-0127 generic `sol_get_sysvar` accessor. The probe
/// program reads rent (full + an offset slice + a length overrun),
/// clock, epoch_schedule, the slot_hashes length prefix, and an
/// unknown id, dumping every r0 and buffer into accounts[0].data.
/// Both engines must agree byte-for-byte (in-band error codes 1/2
/// included) and on CU (the length-dependent
/// `sysvar_base + max(len/250, mem_op_base)` formula).
#[test]
fn sysvar_probe_matches_mollusk() {
    let program_id = pid(240);
    let data_key = pid(241);

    let data = vec![0u8; 128];
    let pre_fs = AccountSharedData::from(Account {
        lamports: 2_000_000, data: data.clone(), owner: program_id,
        executable: false, rent_epoch: 0,
    });
    let pre_ml = mollusk_account::Account {
        lamports: 2_000_000, data: data.clone(), owner: program_id,
        executable: false, rent_epoch: 0,
    };

    let ix = Instruction {
        program_id,
        accounts: vec![AccountMeta::new(data_key, false)],
        data: vec![],
    };

    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&program_id, SYSVAR_PROBE_SO);
    let fs_r = fs
        .process_instruction(&ix, &[(data_key, pre_fs)])
        .expect("qedsvm runs sysvar probe");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        SYSVAR_PROBE_SO,
    );
    let m_r = m.process_instruction(&ix, &[(data_key, pre_ml)]);

    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success on sysvar probe, got {:?}", fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success on sysvar probe, got {:?}", m_r.program_result);
    assert_no_poststate_backstop(&fs_r);

    let (_, fs_data) = &fs_r.resulting_accounts[0];
    let (_, ml_data) = &m_r.resulting_accounts[0];
    assert_eq!(fs_data.data(), ml_data.data.as_slice(),
        "sysvar probe data diverged:\n ours    = {:?}\n mollusk = {:?}",
        fs_data.data(), ml_data.data);

    // Spot-pin the layout so a silently-zero probe can't pass: rent
    // bytes, the in-band error codes, and the slot_hashes 512-entry
    // length prefix.
    let d = ml_data.data.as_slice();
    assert_eq!(d[0], 0, "rent r0");
    assert_eq!(&d[1..18],
        &[0x98, 0x0d, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x40, 0x32],
        "rent bytes");
    assert_eq!(&d[19..28], &[0, 0, 0, 0, 0, 0, 0, 0x40, 0x32],
        "rent offset-8 slice");
    assert_eq!(d[69], 2, "unknown id must be SYSVAR_NOT_FOUND (2)");
    assert_eq!(d[70], 1, "rent len-18 must be OFFSET_LENGTH_EXCEEDS_SYSVAR (1)");
    assert_eq!(&d[72..80], &[0x80, 0x97, 0x06, 0, 0, 0, 0, 0],
        "epoch_schedule slots_per_epoch");
    assert_eq!(&d[106..114], &[0x00, 0x02, 0, 0, 0, 0, 0, 0],
        "slot_hashes length prefix (512)");

    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged for sysvar probe: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// 3-program CPI chain: outer → cpi_increment_caller → incrementer.
/// Exercises depth-2 recursion in executeFnCpiWithFuel. The leaf
/// bumps accounts[0].data[0..8] from 0 to 1; the test asserts that
/// the increment is visible after the chain returns, on both engines.
#[test]
fn cpi_depth_2_chain_matches_mollusk() {
    let outer_id  = pid(220);
    let middle_id = pid(221);
    let leaf_id   = pid(222);
    let acct_key  = pid(223);

    let data: Vec<u8> = vec![0u8; 16];
    let acct_pre_fs = AccountSharedData::from(Account {
        lamports: 1_000_000, data: data.clone(),
        owner: leaf_id, executable: false, rent_epoch: 0,
    });
    let acct_pre_ml = mollusk_account::Account {
        lamports: 1_000_000, data: data.clone(),
        owner: leaf_id, executable: false, rent_epoch: 0,
    };

    let middle_prog_fs = AccountSharedData::from(Account {
        lamports: 1, data: vec![],
        owner: solana_sdk_ids::bpf_loader_upgradeable::id(),
        executable: true, rent_epoch: 0,
    });
    let middle_prog_ml = mollusk_account::Account {
        lamports: 1, data: vec![],
        owner: solana_sdk_ids::bpf_loader_upgradeable::id(),
        executable: true, rent_epoch: 0,
    };
    let leaf_prog_fs = AccountSharedData::from(Account {
        lamports: 1, data: vec![],
        owner: solana_sdk_ids::bpf_loader_upgradeable::id(),
        executable: true, rent_epoch: 0,
    });
    let leaf_prog_ml = mollusk_account::Account {
        lamports: 1, data: vec![],
        owner: solana_sdk_ids::bpf_loader_upgradeable::id(),
        executable: true, rent_epoch: 0,
    };

    // ix.data = middle_id || leaf_id (64 bytes)
    let mut ix_data = Vec::with_capacity(64);
    ix_data.extend_from_slice(&middle_id.to_bytes());
    ix_data.extend_from_slice(&leaf_id.to_bytes());

    let ix = Instruction {
        program_id: outer_id,
        accounts: vec![
            AccountMeta::new(acct_key, false),
            AccountMeta::new_readonly(middle_id, false),
            AccountMeta::new_readonly(leaf_id, false),
        ],
        data: ix_data,
    };

    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&outer_id, CPI_DEPTH_2_OUTER_SO);
    fs.add_program(&middle_id, CPI_INCREMENT_CALLER_SO);
    fs.add_program(&leaf_id, INCREMENTER_SO);
    let fs_r = fs.process_instruction(&ix, &[
        (acct_key, acct_pre_fs),
        (middle_id, middle_prog_fs),
        (leaf_id, leaf_prog_fs),
    ]).expect("qedsvm runs depth-2 CPI chain");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &outer_id, &solana_sdk_ids::bpf_loader_upgradeable::id(),
        CPI_DEPTH_2_OUTER_SO);
    m.add_program_with_loader_and_elf(
        &middle_id, &solana_sdk_ids::bpf_loader_upgradeable::id(),
        CPI_INCREMENT_CALLER_SO);
    m.add_program_with_loader_and_elf(
        &leaf_id, &solana_sdk_ids::bpf_loader_upgradeable::id(),
        INCREMENTER_SO);
    let m_r = m.process_instruction(&ix, &[
        (acct_key, acct_pre_ml),
        (middle_id, middle_prog_ml),
        (leaf_id, leaf_prog_ml),
    ]);

    let our_logs: Vec<String> = fs_r.logs.iter()
        .map(|b| String::from_utf8_lossy(b).into_owned()).collect();
    eprintln!("DEPTH2 qedsvm cu={} result={:?} logs={our_logs:?}",
        fs_r.compute_units_consumed, fs_r.program_result);
    eprintln!("DEPTH2 mollusk cu={} result={:?}",
        m_r.compute_units_consumed, m_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success on depth-2 chain, got {:?}", m_r.program_result);
    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success on depth-2 chain, got {:?}; logs: {our_logs:?}",
        fs_r.program_result);

    let (_, fs_acct) = &fs_r.resulting_accounts[0];
    let (_, ml_acct) = &m_r.resulting_accounts[0];
    let mut expected = vec![0u8; 16];
    expected[..8].copy_from_slice(&1u64.to_le_bytes());
    assert_eq!(fs_acct.data(), expected.as_slice(),
        "qedsvm: leaf increment not visible through depth-2 chain; got {:?}",
        fs_acct.data());
    assert_eq!(ml_acct.data.as_slice(), expected.as_slice(),
        "mollusk: leaf increment not visible (sanity); got {:?}", ml_acct.data);
}

/// Reproduces issue #10 against the deployed Janus slot-height-resolver
/// binary. The `Initialize` handler issues a System Program
/// `CreateAccount` CPI via `invoke_signed` with the state PDA's seeds —
/// the new account is a PDA (not a regular signer), so the dispatcher
/// must promote it to `isSigner = true` based on seed derivation
/// before `execCreateAccount`'s signer check runs.
///
/// The synthetic `system_create_account_cpi_matches_mollusk` test
/// passes because it uses a non-PDA `new_pk` that signs the outer
/// instruction (`AccountMeta::new(*, true)`). PDA-target CreateAccount
/// is structurally different and is what the reporter hits.
///
/// Expected outcome: mollusk Success (allocates 48-byte state
/// account), qedsvm should match. Asserts on `program_result`,
/// CU, and `account[1].data.len() == 48`.
#[test]
fn janus_slot_height_resolver_initialize_matches_mollusk() {
    use solana_account::WritableAccount;

    let program_id: Pubkey = "3y75gGqFK1KhNF5k1sMy6ydnw6WLcbn1SPRoYbyRkjMj".parse().unwrap();
    let system_program = solana_sdk_ids::system_program::id();

    let payer = Pubkey::new_unique();
    let authority = Pubkey::new_unique();
    let seed_key = Pubkey::new_unique();
    let (state, bump) = Pubkey::find_program_address(
        &[b"slot-resolver", seed_key.as_ref()],
        &program_id,
    );

    // Initialize tag = 1, then outcome | bump | 6B padding | u64 target_slot | 32B seed_key.
    let mut data = Vec::with_capacity(49);
    data.push(1u8); // Initialize
    data.push(1u8); // outcome
    data.push(bump);
    data.extend_from_slice(&[0u8; 6]);
    data.extend_from_slice(&500u64.to_le_bytes()); // target_slot
    data.extend_from_slice(seed_key.as_ref());

    let ix = Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new(payer, true),
            AccountMeta::new(state, false),         // PDA target — not a hard signer
            AccountMeta::new_readonly(authority, true),
            AccountMeta::new_readonly(system_program, false),
        ],
        data,
    };

    // Pre-states: payer is funded + system-owned, state empty (the
    // PDA hasn't been initialized yet), authority empty + system-owned.
    let payer_pre_fs = {
        let mut a = AccountSharedData::default();
        a.set_lamports(1_000_000_000_000);
        a.set_owner(system_program);
        a
    };
    let payer_pre_ml = mollusk_account::Account {
        lamports: 1_000_000_000_000, data: vec![],
        owner: system_program, executable: false, rent_epoch: 0,
    };
    let state_pre_fs = AccountSharedData::default();
    let state_pre_ml = mollusk_account::Account::default();
    let authority_pre_fs = {
        let mut a = AccountSharedData::default();
        a.set_owner(system_program);
        a
    };
    let authority_pre_ml = mollusk_account::Account {
        lamports: 0, data: vec![], owner: system_program,
        executable: false, rent_epoch: 0,
    };
    let (mollusk_system_id, mollusk_system_acct) =
        mollusk_svm::program::keyed_account_for_system_program();
    let system_stub_fs = AccountSharedData::from(Account {
        lamports: mollusk_system_acct.lamports,
        data: mollusk_system_acct.data.clone(),
        owner: mollusk_system_acct.owner,
        executable: mollusk_system_acct.executable,
        rent_epoch: mollusk_system_acct.rent_epoch,
    });

    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&program_id, JANUS_SLOT_HEIGHT_RESOLVER_SO);
    let fs_r = fs.process_instruction(&ix, &[
        (payer, payer_pre_fs),
        (state, state_pre_fs),
        (authority, authority_pre_fs),
        (system_program, system_stub_fs),
    ]).expect("qedsvm runs slot_height_resolver Initialize");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id, &solana_sdk_ids::bpf_loader_upgradeable::id(),
        JANUS_SLOT_HEIGHT_RESOLVER_SO);
    let m_r = m.process_instruction(&ix, &[
        (payer, payer_pre_ml),
        (state, state_pre_ml),
        (authority, authority_pre_ml),
        (mollusk_system_id, mollusk_system_acct),
    ]);

    eprintln!("mollusk: {:?} cu={} accounts={}",
        m_r.program_result, m_r.compute_units_consumed, m_r.resulting_accounts.len());
    eprintln!("qedsvm:  {:?} cu={} accounts={}",
        fs_r.program_result, fs_r.compute_units_consumed, fs_r.resulting_accounts.len());
    let m_state = m_r.resulting_accounts.iter()
        .find(|(k, _)| *k == state).expect("mollusk state present").1.clone();
    let fs_state = fs_r.resulting_accounts.iter()
        .find(|(k, _)| *k == state).expect("qedsvm state present").1.clone();
    eprintln!("mollusk state.data.len={} lamports={} owner={}",
        m_state.data.len(), m_state.lamports, m_state.owner);
    eprintln!("qedsvm  state.data.len={} lamports={} owner={}",
        fs_state.data().len(), fs_state.lamports(), fs_state.owner());

    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success, got {:?}", m_r.program_result);
    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success, got {:?}", fs_r.program_result);
    assert_eq!(fs_state.data().len(), 48,
        "state.data.len: expected 48, got {}", fs_state.data().len());
    assert_eq!(fs_state.data(), m_state.data.as_slice(),
        "state.data divergence");
    assert_eq!(fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU divergence: qedsvm={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed);
}

