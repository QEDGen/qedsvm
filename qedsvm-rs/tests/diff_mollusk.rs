//! Cross-engine differential test: qedsvm::Svm vs mollusk_svm::Mollusk, byte-level assertions on all outputs.
//!
//! Run: cargo test --features diff-mollusk
//!
//! Known limits (M14): reference is mollusk with `FeatureSet::all_enabled()` (not mainnet-active).
//! Lean dylibs are linked from .lake/build — run `lake build` before `cargo test` (CI does this).
//! Precompiles can't be diff-tested (dependency conflict). `assert_no_poststate_backstop` guards M13.

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
/// Guard-cascade fixture for the whole-transition obligation (#40): reads a
/// u64 `amount` at input[0] (= the serialized account count), aborts with
/// r0 = 1 when zero, else adds it to the u64 at input[8]. The two tests
/// below are the trace sources for the success/abort path lifts.
const GUARDED_COUNTER_SO: &[u8] = include_bytes!("fixtures/guarded_counter.so");
/// The FAULT-path variant (#40): same guard, but amount == 0 invokes the
/// `abort` syscall (typed `.abort` fault) instead of returning an error
/// code. Trace sources for the `GuardedAbort{Panic,Success}` path lifts.
const GUARDED_ABORT_SO: &[u8] = include_bytes!("fixtures/guarded_abort.so");
/// The OOB-FAULT-path variant (#40): same guard, but amount == 0 performs an
/// out-of-bounds `sol_get_clock_sysvar` write (typed `.accessViolation`).
/// Trace sources for the `GuardedOob{Oob,Success}` path lifts.
const GUARDED_OOB_SO: &[u8] = include_bytes!("fixtures/guarded_oob.so");
/// Per-call-site CPI envelope fixture (#40 gap 4): hand-builds a Rust-ABI
/// `StableInstruction` on the heap (target pubkey from its instruction
/// data) and invokes it. Lifted as `Generated.CpiEnvelopeCallerLifted`;
/// the envelope theorem is `CpiEnvelopeDemo.cpi_envelope_at_call_site`.
const CPI_ENVELOPE_CALLER_SO: &[u8] =
    include_bytes!("fixtures/cpi_envelope_caller.so");
/// Embedded-bump-allocator demo: reads/commits the heap bump slot at
/// 0x300000000 and writes + reads an allocated block. Exercises the
/// program heap as ordinary memory (no syscall allocator).
const HEAP_ALLOC_SO: &[u8] = include_bytes!("fixtures/heap_alloc.so");
/// Happy-path `sol_memcpy_`: copies 16 bytes between two disjoint heap
/// slices (`0x300000000` and `+0x100`), both mapped read+write. The
/// success-direction counterpart to `oob_memset` for the memory-op
/// syscalls; drives the `MemcpyLifted` lift trace.
const MEMCPY_CALLER_SO: &[u8] = include_bytes!("fixtures/memcpy_caller.so");
/// Happy-path single-slice `sol_sha256`: writes a one-entry `SliceDesc`
/// { ptr = base+0x100, len = 16 } to the heap base, hashes the 16-byte
/// input slice into a 32-byte heap output buffer. All three regions are
/// disjoint and mapped read+write. Success-direction counterpart to
/// `oob_sha256`; the trace source for `Sha256CallerLifted`.
const SHA256_CALLER_SO: &[u8] = include_bytes!("fixtures/sha256_caller.so");
/// Happy-path single-seed `sol_create_program_address`: writes a one-entry
/// SliceDesc { ptr = base+0x100, len = 8 } to the heap, derives a PDA from the
/// 8-byte seed + 32-byte program_id into a 32-byte heap output. Disjoint,
/// in-bounds heap regions. The trace source for `PdaCreateLifted`.
const PDA_CREATE_SO: &[u8] = include_bytes!("fixtures/pda_create.so");
/// Happy-path `sol_memmove_`: same disjoint-heap-slice shape as
/// `memcpy_caller`, exercising the `is_move` arm of the lift emitter.
const MEMMOVE_CALLER_SO: &[u8] = include_bytes!("fixtures/memmove_caller.so");
/// Happy-path `sol_memcmp_`: compares two disjoint 16-byte heap slices,
/// writes the 4-byte result to a third disjoint slot. Trace source for
/// `MemcmpLifted` (two `↦Bytes` inputs + one `↦U32` output).
const MEMCMP_CALLER_SO: &[u8] = include_bytes!("fixtures/memcmp_caller.so");
/// Happy-path `sol_set_return_data`: copies a 16-byte in-bounds heap slice
/// into `State.returnData`. Trace source for `SetReturnDataLifted`
/// (one `↦Bytes` input + the framed `↦ReturnData` atom).
const SET_RETURN_DATA_CALLER_SO: &[u8] =
    include_bytes!("fixtures/set_return_data_caller.so");
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
/// CPI callee that GROWS its writable account by 8 bytes (within the
/// `MAX_PERMITTED_DATA_INCREASE` reserve) and writes a sentinel into the grown
/// tail. Paired with `cpi_increment_caller.so` to exercise the M6r CPI realloc
/// write-back. Source in `cpi_realloc_callee_src/`.
const CPI_REALLOC_CALLEE_SO: &[u8] = include_bytes!("fixtures/cpi_realloc_callee.so");
/// CPI callee that attempts to grow its account BEYOND
/// `MAX_PERMITTED_DATA_INCREASE` (`realloc(old + 10241)`). Both engines reject
/// the over-grow and leave the account unchanged. Source in
/// `cpi_realloc_overflow_callee_src/`.
const CPI_REALLOC_OVERFLOW_CALLEE_SO: &[u8] =
    include_bytes!("fixtures/cpi_realloc_overflow_callee.so");
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
/// Typed-fault terminal (Phase 7 sub-item 3): a happy path that runs a
/// small straight-line prefix and then invokes the `abort` syscall.
/// agave's `SyscallAbort` traps; program-runtime reports
/// `ProgramFailedToComplete`. qedsvm sets `exitCode = ERR_ABORT` /
/// `vmError = .abort`, surfaced as a VM fault. Both engines fault.
/// Source in `abort_caller_src/`; lifted as `Generated.AbortCallerLifted`
/// with a mechanized `AbortCaller_fault_correct` typed-fault corollary.
const ABORT_CALLER_SO: &[u8] = include_bytes!("fixtures/abort_caller.so");
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
/// Calls `sol_get_rent_sysvar` with a 17-byte output buffer 256 MiB out of
/// region. agave's `translate_type_mut::<Rent>` traps; post-fix (stage 4c)
/// `Sysvar.execRent` (de-simp'd) routes the write through `guardWrite` and
/// faults. Source in `oob_rent_sysvar_src/`.
const OOB_RENT_SYSVAR_SO: &[u8] = include_bytes!("fixtures/oob_rent_sysvar.so");
/// Seeds 8 bytes of return data, then calls `sol_get_return_data` with a
/// return-data output buffer 256 MiB out of region. agave's
/// `translate_slice_mut::<u8>` traps; post-fix (stage 4d) `ReturnData.execGet`
/// routes both output writes through `guardWrite` and faults. Source in
/// `oob_get_return_data_src/`.
const OOB_GET_RETURN_DATA_SO: &[u8] = include_bytes!("fixtures/oob_get_return_data.so");
/// Calls `sol_secp256k1_recover` with a 32-byte message hash 256 MiB out of
/// region. agave's `translate_slice::<u8>(hash, 32)` traps before the FFI
/// recovery; post-fix (stage 5a) `Secp256k1.exec` routes the hash/sig/output
/// through `guardRead`/`guardWrite` and faults. Source in `oob_secp256k1_src/`.
const OOB_SECP256K1_SO: &[u8] = include_bytes!("fixtures/oob_secp256k1.so");
/// Calls `sol_create_program_address` with zero seeds and a program_id /
/// output buffer 256 MiB out of region. agave's `translate_slice` traps;
/// post-fix (stage 5b) `Pda.execCreate` routes the program_id through
/// `guardRead` and the output + seeds through `guardedCommit` and faults.
/// Source in `oob_create_pda_src/`.
const OOB_CREATE_PDA_SO: &[u8] = include_bytes!("fixtures/oob_create_pda.so");
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

/// M13: assert the post-state backstop never fired. A `Some(_)` means the Lean VM relied on
/// `validate_post_state` to downgrade a bad Success — masking a soundness bug as a Failure match.
fn assert_no_poststate_backstop(fs_r: &qedsvm::InstructionResult) {
    assert!(
        fs_r.poststate_violation.is_none(),
        "Lean VM relied on the Rust post-state backstop ({:?}); this can mask a \
         model soundness bug behind ERR_INVALID_POSTSTATE",
        fs_r.poststate_violation,
    );
}

/// M14: cross-engine outcome comparison. agave collapses all VM faults + meter exhaustion to
/// `InstructionError::ProgramFailedToComplete` (mollusk `UnknownError(ProgramFailedToComplete)`),
/// so VmFault/OutOfBudget match that catch-all. Program-returned errors compare by exact code.
/// By-design divergences (M6/C5 readonly) are asserted separately and NOT routed here.
fn outcome_matches(fs: &FsProgramResult, ml: &MlProgramResult) -> Result<(), String> {
    use FsProgramResult as F;
    use MlProgramResult as M;
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

/// Assert M14 outcome agreement; panics with the mismatch on divergence.
fn assert_outcome_matches(fs: &FsProgramResult, ml: &MlProgramResult, ctx: &str) {
    if let Err(why) = outcome_matches(fs, ml) {
        panic!("{ctx}: cross-engine outcome mismatch (M14): {why}");
    }
}

/// L10: look up a resulting account by key, not position — panics if absent rather than silently misreading.
fn fs_acct_by_key<'a>(
    fs_r: &'a qedsvm::InstructionResult,
    key: &Pubkey,
) -> &'a AccountSharedData {
    fs_r.resulting_accounts.iter()
        .find(|(k, _)| k == key)
        .map(|(_, a)| a)
        .unwrap_or_else(|| panic!("account {key} absent from qedsvm resulting_accounts"))
}

/// Both engines produce identical output for a trivial noop.
#[test]
fn noop_program_matches_mollusk() {
    let program_id = pid(1);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };

    let mut fs = Svm::default();
    fs.add_program(&program_id, NOOP_SO);
    let fs_r = fs.process_instruction(&ix, &[]).expect("qedsvm runs noop");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        NOOP_SO,
    );
    let m_r = m.process_instruction(&ix, &[]);

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
    for ((k_a, a_a), (k_b, a_b)) in
        fs_r.resulting_accounts.iter().zip(m_r.resulting_accounts.iter())
    {
        assert_eq!(k_a, k_b, "pubkey order divergence");
        assert_eq!(a_a.lamports(), a_b.lamports, "lamports diverged for {k_a}");
        assert_eq!(a_a.data(), a_b.data.as_slice(), "data diverged for {k_a}");
        assert_eq!(a_a.owner(), &a_b.owner, "owner diverged for {k_a}");
    }
    // Strict CU equality — catches any drift in per-instruction CU accounting.
    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "compute_units_consumed diverged: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// Cross-engine equality on the real `entrypoint!` noop shape (~1923 sBPF instructions) — the actual "we conform to agave" claim.
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

    match (&fs_r.program_result, &m_r.program_result) {
        (FsProgramResult::Success, MlProgramResult::Success) => {}
        (a, b) => panic!(
            "program_result diverged on real solana_program noop:\n  qedsvm: {a:?}\n  mollusk:    {b:?}",
        ),
    }
    assert_eq!(fs_r.return_data, m_r.return_data,
        "return_data diverged");

    // Exact CU equality catches call-frame off-by-ones.
    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "compute_units_consumed diverged on real solana_program noop: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// Validates per-syscall CU table: both engines must report identical CU for `sol_log_`.
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
    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged for msg!(\"hi\"): ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// H5: budget too small for `sol_log_`'s surcharge. Both engines must (a) not succeed
/// and (b) report consumed = full budget (agave's meter-drain-to-budget behavior).
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
    assert_outcome_matches(&fs_r.program_result, &m_r.program_result, // M14: ExceededMaxInstructions → same catch-all
        "logger_surcharge_overrun");
    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "consumed-CU diverged at the surcharge-overrun boundary: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
    assert_eq!(fs_r.compute_units_consumed, TINY_BUDGET,
        "expected the meter drained to the full budget");
}

/// First fixture that mutates account data (u64+1). Validates `deserialize_account_writes` and full field equality.
#[test]
fn incrementer_program_matches_mollusk() {
    let program_id = pid(5);
    let acct_key = pid(6);
    // Account owned by the program (required for write permission). Two `solana-account` majors (4.x/3.x) — built twice.
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

    let mut fs = Svm::default().with_cu_budget(1_400_000); // keep budgets identical across engines
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

    let mut want = vec![0u8; 16]; // expected post-state: data[0..8] = 1u64
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

/// Guarded-counter SUCCESS path (#40): one account → serialized count u64 = 1
/// = `amount` ≠ 0, so the guard passes and the program adds it to the u64 at
/// input[8..16] (serialization metadata — ignored by post-deserialize, so the
/// account round-trips unchanged) and returns 0. Trace source for
/// `GuardedCounterSuccessLifted`.
#[test]
fn guarded_counter_success_matches_mollusk() {
    let program_id = pid(90);
    let acct_key = pid(91);
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
    fs.add_program(&program_id, GUARDED_COUNTER_SO);
    let fs_r = fs
        .process_instruction(&ix, &[(acct_key, pre_shared)])
        .expect("qedsvm runs guarded_counter (success)");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        GUARDED_COUNTER_SO,
    );
    let m_r = m.process_instruction(&ix, &[(acct_key, pre_mollusk)]);

    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success, got {:?}", fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success, got {:?}", m_r.program_result);

    let (_, fs_acct) = &fs_r.resulting_accounts[0];
    let (_, m_acct) = &m_r.resulting_accounts[0];
    assert_eq!(fs_acct.data(), m_acct.data.as_slice(), "data diverged");
    assert_eq!(fs_acct.lamports(), m_acct.lamports, "lamports diverged");
    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged for guarded_counter success: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// Guarded-counter ABORT path (#40): zero accounts → serialized count u64 = 0
/// = `amount`, so the guard fails and the program returns 1 without touching
/// memory. Exact error encoding diverges by design (raw r0 vs typed
/// ProgramError) — assert non-Success on both + CU parity. Trace source for
/// `GuardedCounterAbortLifted`.
#[test]
fn guarded_counter_abort_matches_mollusk() {
    let program_id = pid(92);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };

    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&program_id, GUARDED_COUNTER_SO);
    let fs_r = fs
        .process_instruction(&ix, &[])
        .expect("qedsvm runs guarded_counter (abort)");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        GUARDED_COUNTER_SO,
    );
    let m_r = m.process_instruction(&ix, &[]);

    assert!(!matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Failure, got Success");
    assert!(!matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Failure, got Success");
    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged for guarded_counter abort: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// guarded_abort SUCCESS path (#40): one account → `amount` = 1 ≠ 0, the
/// guard passes, counter credited, returns 0. Trace source for
/// `GuardedAbortSuccessLifted`.
#[test]
fn guarded_abort_success_matches_mollusk() {
    let program_id = pid(93);
    let acct_key = pid(94);
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
    fs.add_program(&program_id, GUARDED_ABORT_SO);
    let fs_r = fs
        .process_instruction(&ix, &[(acct_key, pre_shared)])
        .expect("qedsvm runs guarded_abort (success)");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        GUARDED_ABORT_SO,
    );
    let m_r = m.process_instruction(&ix, &[(acct_key, pre_mollusk)]);

    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success, got {:?}", fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success, got {:?}", m_r.program_result);
    let (_, fs_acct) = &fs_r.resulting_accounts[0];
    let (_, m_acct) = &m_r.resulting_accounts[0];
    assert_eq!(fs_acct.data(), m_acct.data.as_slice(), "data diverged");
    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged for guarded_abort success: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// guarded_abort PANIC path (#40): zero accounts → `amount` = 0, the guard
/// fails into the `abort` syscall — both engines fault (qedsvm
/// `vmError = .abort` → VmFault; agave ProgramFailedToComplete). Trace
/// source for `GuardedAbortPanicLifted`.
#[test]
fn guarded_abort_panic_matches_mollusk() {
    let program_id = pid(95);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };

    let mut fs = Svm::default();
    fs.add_program(&program_id, GUARDED_ABORT_SO);
    let fs_r = fs
        .process_instruction(&ix, &[])
        .expect("qedsvm runs guarded_abort (panic)");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        GUARDED_ABORT_SO,
    );
    let m_r = m.process_instruction(&ix, &[]);

    assert!(matches!(fs_r.program_result, FsProgramResult::VmFault { .. }),
        "qedsvm should VM-fault on the abort syscall, got {:?}", fs_r.program_result);
    assert_outcome_matches(&fs_r.program_result, &m_r.program_result, "guarded_abort");
}

/// guarded_oob SUCCESS path (#40): one account → `amount` = 1 ≠ 0, guard
/// passes, counter credited, returns 0. Trace source for
/// `GuardedOobSuccessLifted`.
#[test]
fn guarded_oob_success_matches_mollusk() {
    let program_id = pid(98);
    let acct_key = pid(99);
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
    fs.add_program(&program_id, GUARDED_OOB_SO);
    let fs_r = fs
        .process_instruction(&ix, &[(acct_key, pre_shared)])
        .expect("qedsvm runs guarded_oob (success)");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        GUARDED_OOB_SO,
    );
    let m_r = m.process_instruction(&ix, &[(acct_key, pre_mollusk)]);

    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success, got {:?}", fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success, got {:?}", m_r.program_result);
    let (_, fs_acct) = &fs_r.resulting_accounts[0];
    let (_, m_acct) = &m_r.resulting_accounts[0];
    assert_eq!(fs_acct.data(), m_acct.data.as_slice(), "data diverged");
    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged for guarded_oob success: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// guarded_oob OOB path (#40): zero accounts → `amount` = 0, the guard fails
/// into an out-of-bounds `sol_get_clock_sysvar` write — both engines fault
/// (qedsvm `vmError = .accessViolation` → VmFault; agave AccessViolation →
/// ProgramFailedToComplete). Trace source for `GuardedOobOobLifted`.
#[test]
fn guarded_oob_oob_matches_mollusk() {
    let program_id = pid(100);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };

    let mut fs = Svm::default();
    fs.add_program(&program_id, GUARDED_OOB_SO);
    let fs_r = fs
        .process_instruction(&ix, &[])
        .expect("qedsvm runs guarded_oob (oob)");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        GUARDED_OOB_SO,
    );
    let m_r = m.process_instruction(&ix, &[]);

    assert!(matches!(fs_r.program_result, FsProgramResult::VmFault { .. }),
        "qedsvm should VM-fault on the OOB clock write, got {:?}", fs_r.program_result);
    assert_outcome_matches(&fs_r.program_result, &m_r.program_result, "guarded_oob");
}

/// cpi_envelope_caller (#40 gap 4): builds the StableInstruction on the heap
/// and invokes the pubkey from its instruction data (= noop). One account —
/// the callee program (agave requires the invoked program in the tx), so the
/// instruction data sits at `instrDataOff [0]` = 10352. Success + CU parity
/// on both engines.
#[test]
fn cpi_envelope_caller_matches_mollusk() {
    let caller_id = pid(96);
    let callee_id = pid(97);

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
        accounts: vec![AccountMeta::new_readonly(callee_id, false)],
        data: callee_id.to_bytes().to_vec(),
    };

    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&caller_id, CPI_ENVELOPE_CALLER_SO);
    fs.add_program(&callee_id, NOOP_SO);
    let fs_r = fs
        .process_instruction(&ix, &[(callee_id, callee_program_shared)])
        .expect("qedsvm runs cpi_envelope_caller");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &caller_id, &solana_sdk_ids::bpf_loader_upgradeable::id(),
        CPI_ENVELOPE_CALLER_SO);
    m.add_program_with_loader_and_elf(
        &callee_id, &solana_sdk_ids::bpf_loader_upgradeable::id(),
        NOOP_SO);
    let m_r = m.process_instruction(&ix, &[(callee_id, callee_program_mollusk)]);

    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success, got {:?}", fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success, got {:?}", m_r.program_result);
    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged for cpi_envelope_caller: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// 16-bit store coverage: ldxh/stxh increment (0x00ff→0x0100) + sth constant (0x1234). Only fixture exercising 16-bit stores.
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

    let mut want = vec![0u8; 16]; // data[0..2]=0x0100 (carried increment), data[2..4]=0x1234 (ST_H_IMM)
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

/// Heap bump-allocator: reads/commits 0x300000000, writes+reads a block. Pure byte-level conformance on the heap region.
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

/// H6 happy path: `sol_memcpy_` over two disjoint, in-bounds heap slices
/// succeeds on both engines with matching CU. The success-direction pair
/// to `oob_memset_fails_on_both`, and the trace source for `MemcpyLifted`.
#[test]
fn memcpy_caller_program_matches_mollusk() {
    let program_id = pid(9);
    let acct_key = pid(10);
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
    fs.add_program(&program_id, MEMCPY_CALLER_SO);
    let fs_r = fs
        .process_instruction(&ix, &[(acct_key, pre_shared)])
        .expect("qedsvm runs memcpy_caller");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        MEMCPY_CALLER_SO,
    );
    let m_r = m.process_instruction(&ix, &[(acct_key, pre_mollusk)]);

    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success, got {:?}", fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success, got {:?}", m_r.program_result);
    assert_eq!(fs_r.return_data, m_r.return_data, "return_data diverged");
    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged for memcpy_caller: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// H6 happy path: single-slice `sol_sha256` over disjoint, in-bounds heap
/// regions (descriptor + 16-byte input + 32-byte output) succeeds on both
/// engines with matching CU and return_data. The success direction to
/// `oob_sha256_*_fails_on_both`, and the trace source for `Sha256CallerLifted`.
#[test]
fn sha256_caller_program_matches_mollusk() {
    let program_id = pid(57);
    let acct_key = pid(58);
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
    fs.add_program(&program_id, SHA256_CALLER_SO);
    let fs_r = fs
        .process_instruction(&ix, &[(acct_key, pre_shared)])
        .expect("qedsvm runs sha256_caller");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        SHA256_CALLER_SO,
    );
    let m_r = m.process_instruction(&ix, &[(acct_key, pre_mollusk)]);

    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success, got {:?}", fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success, got {:?}", m_r.program_result);
    assert_eq!(fs_r.return_data, m_r.return_data, "return_data diverged");
    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged for sha256_caller: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// H6 happy path: single-seed `sol_create_program_address` over disjoint,
/// in-bounds heap regions (descriptor + 8-byte seed + 32-byte program_id +
/// 32-byte output) succeeds on both engines with matching CU and return_data.
/// The success direction to `oob_create_pda_*`, and the trace source for
/// `PdaCreateLifted`.
#[test]
fn pda_create_program_matches_mollusk() {
    let program_id = pid(61);
    let acct_key = pid(62);
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
    fs.add_program(&program_id, PDA_CREATE_SO);
    let fs_r = fs
        .process_instruction(&ix, &[(acct_key, pre_shared)])
        .expect("qedsvm runs pda_create");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        PDA_CREATE_SO,
    );
    let m_r = m.process_instruction(&ix, &[(acct_key, pre_mollusk)]);

    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success, got {:?}", fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success, got {:?}", m_r.program_result);
    assert_eq!(fs_r.return_data, m_r.return_data, "return_data diverged");
    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged for pda_create: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// H6 happy path: `sol_set_return_data` over an in-bounds 16-byte heap slice
/// succeeds on both engines with matching CU and return_data. The success
/// direction to `oob_set_return_data_fails_on_both`, and the trace source for
/// `SetReturnDataLifted`.
#[test]
fn set_return_data_caller_program_matches_mollusk() {
    let program_id = pid(41);
    let acct_key = pid(42);
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
    fs.add_program(&program_id, SET_RETURN_DATA_CALLER_SO);
    let fs_r = fs
        .process_instruction(&ix, &[(acct_key, pre_shared)])
        .expect("qedsvm runs set_return_data_caller");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        SET_RETURN_DATA_CALLER_SO,
    );
    let m_r = m.process_instruction(&ix, &[(acct_key, pre_mollusk)]);

    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success, got {:?}", fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success, got {:?}", m_r.program_result);
    assert_eq!(fs_r.return_data, m_r.return_data, "return_data diverged");
    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged for set_return_data_caller: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// H6 happy path: `sol_memmove_` over two disjoint, in-bounds heap slices.
/// Same shape as `memcpy_caller`; the trace source for `MemmoveLifted`.
#[test]
fn memmove_caller_program_matches_mollusk() {
    let program_id = pid(11);
    let acct_key = pid(12);
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
    fs.add_program(&program_id, MEMMOVE_CALLER_SO);
    let fs_r = fs
        .process_instruction(&ix, &[(acct_key, pre_shared)])
        .expect("qedsvm runs memmove_caller");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        MEMMOVE_CALLER_SO,
    );
    let m_r = m.process_instruction(&ix, &[(acct_key, pre_mollusk)]);

    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success, got {:?}", fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success, got {:?}", m_r.program_result);
    assert_eq!(fs_r.return_data, m_r.return_data, "return_data diverged");
    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged for memmove_caller: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// H6 happy path: `sol_memcmp_` over two disjoint 16-byte heap slices +
/// a disjoint 4-byte output. The trace source for `MemcmpLifted`.
#[test]
fn memcmp_caller_program_matches_mollusk() {
    let program_id = pid(13);
    let acct_key = pid(14);
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
    fs.add_program(&program_id, MEMCMP_CALLER_SO);
    let fs_r = fs
        .process_instruction(&ix, &[(acct_key, pre_shared)])
        .expect("qedsvm runs memcmp_caller");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        MEMCMP_CALLER_SO,
    );
    let m_r = m.process_instruction(&ix, &[(acct_key, pre_mollusk)]);

    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success, got {:?}", fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success, got {:?}", m_r.program_result);
    assert_eq!(fs_r.return_data, m_r.return_data, "return_data diverged");
    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged for memcmp_caller: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// H7 anchor: pins `sol_remaining_compute_units` formula (`cuBudget − (cuConsumed + 1 + 100)`) against rbpf's meter.
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

/// Both engines fail on empty token instruction data (unknown discriminator → `TokenError::InvalidInstruction`).
/// Asserts same log string proves the same dispatch path was taken.
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

    // Exact error encoding diverges by design (raw r0 vs typed ProgramError) — just assert non-Success.
    assert!(!matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Failure, got Success");
    assert!(!matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Failure, got Success");
    let our_log = fs_r.logs.first()
        .map(|b| String::from_utf8_lossy(b).into_owned())
        .unwrap_or_default();
    assert!(our_log.contains("Invalid instruction"),
        "qedsvm: expected 'Error: Invalid instruction', got {our_log:?}");
}

/// SPL Token `InitializeMint2` (discriminant 20): exercises rent sysvar, Mint serialize/deserialize, 82-byte write.
#[test]
fn token_initialize_mint2_matches_mollusk() {
    let program_id = pid(7);
    let mint_key = pid(8);

    const MINT_LEN: usize = 82; // spl_token::state::Mint::LEN
    let lamports = 2_000_000u64; // > rent-exemption threshold for 82 bytes
    let data = vec![0u8; MINT_LEN];

    let pre_shared = AccountSharedData::from(Account {
        lamports, data: data.clone(), owner: program_id,
        executable: false, rent_epoch: 0,
    });
    let pre_mollusk = mollusk_account::Account {
        lamports, data: data.clone(), owner: program_id,
        executable: false, rent_epoch: 0,
    };

    // [20, decimals, mint_authority(32), freeze_authority_option=0]
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
    // Exact CU equality (prior 176-CU drift from r10 stack-frame-gap was fixed 2026-05-14).
    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged for InitializeMint2: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// Build a 165-byte SPL TokenAccount (all COption fields None, state=Initialized).
/// Layout: 0..32 mint, 32..64 owner, 64..72 amount, 108 state=1. See `Account::pack_into_slice`.
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

/// Build an 82-byte SPL Mint (Some(mint_authority), no freeze authority).
/// Layout: 0..4 tag=Some, 4..36 authority, 36..44 supply, 44 decimals, 45 initialized=1.
const MINT_LEN: usize = 82;
fn build_mint_account(mint_authority: &Pubkey, supply: u64, decimals: u8) -> Vec<u8> {
    let mut d = vec![0u8; MINT_LEN];
    d[0..4].copy_from_slice(&1u32.to_le_bytes()); // COption::Some
    d[4..36].copy_from_slice(mint_authority.as_ref());
    d[36..44].copy_from_slice(&supply.to_le_bytes());
    d[44] = decimals;
    d[45] = 1; // is_initialized; freeze_authority tag (46..50) stays 0
    d
}

/// p-token `MintTo` (discriminant 7): mint.supply += amount, dest.amount += amount.
/// Also a TRACE_STEPS trace target for qedlift (crosses the account-parsing loop at pc≈3368-3452).
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

    let mut ix_data = Vec::with_capacity(9); // [7, amount_le_u64]
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

/// p-token `Burn` (discriminant 8): account.amount -= amount, mint.supply -= amount.
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

    let mut ix_data = Vec::with_capacity(9); // [8, amount_le_u64]
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

/// p-token `TransferChecked` (discriminant 12): src -= amount, dst += amount + decimals guard.
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

    let mut ix_data = Vec::with_capacity(10); // [12, amount_le_u64, decimals]
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

/// p-token `CloseAccount` (discriminant 9): moves lamports to destination, wipes account. Exercises lamport-move + zero path.
#[test]
fn p_token_close_account_matches_mollusk() {
    let program_id = pid(80);
    let mint_key = pid(81);
    let acct_key = pid(82);
    let dest_key = pid(83);
    let owner = pid(84);

    const ACCT_LAMPORTS: u64 = 2_039_280;
    const DEST_LAMPORTS: u64 = 500_000;

    let acct_data = build_token_account(&mint_key, &owner, 0); // zero balance required

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

/// p-token `InitializeMint2` (discriminant 20): no rent sysvar; first p-token path crossing `sol_memcpy_`.
#[test]
fn p_token_initialize_mint2_matches_mollusk() {
    let program_id = pid(90);
    let mint_key = pid(91);
    let mint_authority = pid(94);

    const MINT_LAMPORTS: u64 = 1_461_600; // rent-exempt for 82 bytes, uninitialized
    let mint_data = vec![0u8; MINT_LEN];

    let mk_shared = |lamports: u64, data: Vec<u8>| AccountSharedData::from(Account {
        lamports, data, owner: program_id, executable: false, rent_epoch: 0,
    });
    let mk_mollusk = |lamports: u64, data: Vec<u8>| mollusk_account::Account {
        lamports, data, owner: program_id, executable: false, rent_epoch: 0,
    };

    // [20, decimals, mintAuthority(32), freezeAuthority tag=0(None)]
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
    // Full equality enabled by H7 sol_get_sysvar fix (pinocchio Rent::get crosses generic accessor).
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

/// SPL Token `Transfer` (discriminant 3): no CPI, no PDA, no new syscalls. Divergence = real bug.
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

    let mut ix_data = Vec::with_capacity(9); // [3, amount_le_u64]
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

/// p-token Transfer with INSUFFICIENT balance (amount > source balance): the
/// balance guard at the real `jlt` diverts to the error handler, both engines
/// fail, accounts untouched. Exact error encoding diverges by design (raw r0
/// vs typed ProgramError) — assert non-Success on both + account/CU parity.
/// Trace source for `PTokenTransferInsufficientLifted` (the pattern library's
/// Layer-3 balance guard, ENFORCES direction on the real error path).
#[test]
fn p_token_transfer_insufficient_balance_matches_mollusk() {
    let program_id = pid(40);
    let mint = pid(41);
    let authority = pid(42);
    let source_key = pid(43);
    let dest_key = pid(44);

    const TRANSFER_AMOUNT: u64 = 2_000; // > SOURCE_INITIAL: guard must fire
    const SOURCE_INITIAL: u64 = 1_000;
    const DEST_INITIAL: u64 = 0;
    const LAMPORTS: u64 = 2_039_280;

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

    let mut ix_data = Vec::with_capacity(9); // [3, amount_le_u64]
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
        .expect("qedsvm runs p-token Transfer (insufficient)");

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

    assert!(!matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: the balance guard must fail an insufficient transfer, got Success");
    assert!(!matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: the balance guard must fail an insufficient transfer, got Success");

    // Accounts untouched: the effect is never reached on the violating branch.
    for (key, name) in [(source_key, "source"), (dest_key, "dest")] {
        let fa = fs_acct_by_key(&fs_r, &key);
        let ma = m_r.resulting_accounts.iter().find(|(k, _)| *k == key)
            .map(|(_, a)| a).expect("mollusk account");
        assert_eq!(fa.data(), ma.data.as_slice(),
            "{name} data must be untouched by a failed Transfer");
        assert_eq!(fa.lamports(), ma.lamports,
            "{name} lamports must be untouched by a failed Transfer");
    }

    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged for insufficient p-token Transfer: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// p-token Transfer from a FROZEN source account (state byte = 2): the frozen
/// guard (`jeq state, 2` before the balance check) diverts to the error
/// handler, both engines fail, accounts untouched. Trace source for
/// `PTokenTransferFrozenLifted` (the pattern library's Layer-3 frozen guard,
/// ENFORCES direction — TokenError::AccountFrozen = 17).
#[test]
fn p_token_transfer_frozen_matches_mollusk() {
    let program_id = pid(40);
    let mint = pid(41);
    let authority = pid(42);
    let source_key = pid(43);
    let dest_key = pid(44);

    const TRANSFER_AMOUNT: u64 = 250;
    const SOURCE_INITIAL: u64 = 1_000;
    const DEST_INITIAL: u64 = 0;
    const LAMPORTS: u64 = 2_039_280;

    let mut source_data = build_token_account(&mint, &authority, SOURCE_INITIAL);
    source_data[108] = 2; // AccountState::Frozen
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

    let mut ix_data = Vec::with_capacity(9); // [3, amount_le_u64]
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
        .expect("qedsvm runs p-token Transfer (frozen)");

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

    assert!(!matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: the frozen guard must fail a Transfer from a frozen source, got Success");
    assert!(!matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: the frozen guard must fail a Transfer from a frozen source, got Success");

    for (key, name) in [(source_key, "source"), (dest_key, "dest")] {
        let fa = fs_acct_by_key(&fs_r, &key);
        let ma = m_r.resulting_accounts.iter().find(|(k, _)| *k == key)
            .map(|(_, a)| a).expect("mollusk account");
        assert_eq!(fa.data(), ma.data.as_slice(),
            "{name} data must be untouched by a frozen-source Transfer");
        assert_eq!(fa.lamports(), ma.lamports,
            "{name} lamports must be untouched by a frozen-source Transfer");
    }

    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged for frozen p-token Transfer: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// p-token Transfer into a FROZEN destination account (state byte = 2): the
/// sibling of the frozen-source guard, one `jeq` later (`jeq r5, 2` at pc 4012
/// vs the source's pc 4011), same error handler, TokenError::AccountFrozen.
/// Trace source for `PTokenTransferDestFrozenLifted` (pattern library Layer-3
/// dest-frozen guard, ENFORCES direction).
#[test]
fn p_token_transfer_dest_frozen_matches_mollusk() {
    let program_id = pid(45);
    let mint = pid(46);
    let authority = pid(47);
    let source_key = pid(48);
    let dest_key = pid(49);

    const TRANSFER_AMOUNT: u64 = 250;
    const SOURCE_INITIAL: u64 = 1_000;
    const DEST_INITIAL: u64 = 0;
    const LAMPORTS: u64 = 2_039_280;

    let source_data = build_token_account(&mint, &authority, SOURCE_INITIAL);
    let mut dest_data = build_token_account(&mint, &authority, DEST_INITIAL);
    dest_data[108] = 2; // AccountState::Frozen

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

    let mut ix_data = Vec::with_capacity(9); // [3, amount_le_u64]
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
        .expect("qedsvm runs p-token Transfer (dest frozen)");

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

    assert!(!matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: the frozen guard must fail a Transfer into a frozen dest, got Success");
    assert!(!matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: the frozen guard must fail a Transfer into a frozen dest, got Success");

    for (key, name) in [(source_key, "source"), (dest_key, "dest")] {
        let fa = fs_acct_by_key(&fs_r, &key);
        let ma = m_r.resulting_accounts.iter().find(|(k, _)| *k == key)
            .map(|(_, a)| a).expect("mollusk account");
        assert_eq!(fa.data(), ma.data.as_slice(),
            "{name} data must be untouched by a frozen-dest Transfer");
        assert_eq!(fa.lamports(), ma.lamports,
            "{name} lamports must be untouched by a frozen-dest Transfer");
    }

    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged for frozen-dest p-token Transfer: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// p-token Transfer between accounts of DIFFERENT mints: the mint-equality
/// compare (four unrolled dword compares of source mint vs dest mint at
/// pc 4017-4028) diverts to the error handler, TokenError::MintMismatch (3).
/// Passes the state and balance checks first (both accounts initialized,
/// unfrozen, sufficient balance), so the mint compare is the violated check.
/// Trace source for `PTokenTransferMintMismatchLifted` (pattern library
/// Layer-3 mint guard, ENFORCES direction — the first pubkey-inequality
/// guard).
#[test]
fn p_token_transfer_mint_mismatch_matches_mollusk() {
    let program_id = pid(50);
    let mint_a = pid(51);
    let mint_b = pid(52);
    let authority = pid(53);
    let source_key = pid(54);
    let dest_key = pid(55);

    const TRANSFER_AMOUNT: u64 = 250;
    const SOURCE_INITIAL: u64 = 1_000;
    const DEST_INITIAL: u64 = 0;
    const LAMPORTS: u64 = 2_039_280;

    let source_data = build_token_account(&mint_a, &authority, SOURCE_INITIAL);
    let dest_data = build_token_account(&mint_b, &authority, DEST_INITIAL);

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

    let mut ix_data = Vec::with_capacity(9); // [3, amount_le_u64]
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
        .expect("qedsvm runs p-token Transfer (mint mismatch)");

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

    assert!(!matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: the mint guard must fail a cross-mint Transfer, got Success");
    assert!(!matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: the mint guard must fail a cross-mint Transfer, got Success");

    for (key, name) in [(source_key, "source"), (dest_key, "dest")] {
        let fa = fs_acct_by_key(&fs_r, &key);
        let ma = m_r.resulting_accounts.iter().find(|(k, _)| *k == key)
            .map(|(_, a)| a).expect("mollusk account");
        assert_eq!(fa.data(), ma.data.as_slice(),
            "{name} data must be untouched by a cross-mint Transfer");
        assert_eq!(fa.lamports(), ma.lamports,
            "{name} lamports must be untouched by a cross-mint Transfer");
    }

    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged for mint-mismatch p-token Transfer: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// Shared driver for p-token Transfer fixtures that must FAIL on both engines
/// (pattern library Layer-3 violating traces): 3-account Transfer
/// (source, dest, authority-as-signer), asserts both engines fail, both
/// accounts untouched, CU identical. Callers pass the violating pre-state.
fn assert_p_token_transfer_fails(
    label: &str,
    seed: u64,
    source_data: Vec<u8>,
    dest_data: Vec<u8>,
    ix_data: Vec<u8>,
) {
    assert_p_token_transfer_fails_auth(label, seed, source_data, dest_data, ix_data, true)
}

/// `assert_p_token_transfer_fails` with control over the authority's signer
/// flag (the authority tri-case guards violate the signer side).
fn assert_p_token_transfer_fails_auth(
    label: &str,
    seed: u64,
    source_data: Vec<u8>,
    dest_data: Vec<u8>,
    ix_data: Vec<u8>,
    authority_is_signer: bool,
) {
    let program_id = pid(seed);
    let authority = pid(seed + 1);
    let source_key = pid(seed + 2);
    let dest_key = pid(seed + 3);
    const LAMPORTS: u64 = 2_039_280;

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

    let ix = Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new(source_key, false),
            AccountMeta::new(dest_key, false),
            AccountMeta::new_readonly(authority, authority_is_signer),
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
        .unwrap_or_else(|e| panic!("qedsvm runs p-token Transfer ({label}): {e:?}"));

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

    eprintln!("[{label}] fs.program_result   = {:?}", fs_r.program_result);
    eprintln!("[{label}] mol.program_result  = {:?}", m_r.program_result);

    assert!(!matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: {label} must fail the Transfer, got Success");
    assert!(!matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: {label} must fail the Transfer, got Success");

    for (key, name) in [(source_key, "source"), (dest_key, "dest")] {
        let fa = fs_acct_by_key(&fs_r, &key);
        let ma = m_r.resulting_accounts.iter().find(|(k, _)| *k == key)
            .map(|(_, a)| a).expect("mollusk account");
        assert_eq!(fa.data(), ma.data.as_slice(),
            "{name} data must be untouched by a failed Transfer ({label})");
        assert_eq!(fa.lamports(), ma.lamports,
            "{name} lamports must be untouched by a failed Transfer ({label})");
    }

    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged for {label} p-token Transfer: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

fn transfer_ix_data(amount: u64) -> Vec<u8> {
    let mut d = Vec::with_capacity(9); // [3, amount_le_u64]
    d.push(3);
    d.extend_from_slice(&amount.to_le_bytes());
    d
}

/// p-token Transfer from an UNINITIALIZED source (state byte = 0): the
/// `jeq state, 0` at pc 4005 diverts. Trace source for the uninitialized
/// guard (ENFORCES direction).
#[test]
fn p_token_transfer_src_uninit_matches_mollusk() {
    let mint = pid(61);
    let auth = pid(57);
    let mut src = build_token_account(&mint, &auth, 1_000);
    src[108] = 0; // AccountState::Uninitialized
    let dst = build_token_account(&mint, &auth, 0);
    assert_p_token_transfer_fails("src-uninit", 56, src, dst, transfer_ix_data(250));
}

/// p-token Transfer into an UNINITIALIZED destination (state byte = 0): the
/// `jeq state, 0` at pc 4008 diverts.
#[test]
fn p_token_transfer_dest_uninit_matches_mollusk() {
    let mint = pid(66);
    let auth = pid(63);
    let src = build_token_account(&mint, &auth, 1_000);
    let mut dst = build_token_account(&mint, &auth, 0);
    dst[108] = 0; // AccountState::Uninitialized
    assert_p_token_transfer_fails("dest-uninit", 62, src, dst, transfer_ix_data(250));
}

/// p-token Transfer from a source with an INVALID state byte (> 2): the
/// `jgt state, 2` at pc 4004 diverts (r6 = 3, r7 = 0 — the
/// ProgramError::InvalidAccountData encoding, not a TokenError).
#[test]
fn p_token_transfer_src_bad_state_matches_mollusk() {
    let mint = pid(72);
    let auth = pid(69);
    let mut src = build_token_account(&mint, &auth, 1_000);
    src[108] = 3; // invalid AccountState tag
    let dst = build_token_account(&mint, &auth, 0);
    assert_p_token_transfer_fails("src-bad-state", 68, src, dst, transfer_ix_data(250));
}

/// p-token Transfer with an INVALID destination state byte (> 2): the
/// `jgt state, 2` at pc 4007 diverts.
#[test]
fn p_token_transfer_dest_bad_state_matches_mollusk() {
    let mint = pid(78);
    let auth = pid(75);
    let src = build_token_account(&mint, &auth, 1_000);
    let mut dst = build_token_account(&mint, &auth, 0);
    dst[108] = 3; // invalid AccountState tag
    assert_p_token_transfer_fails("dest-bad-state", 74, src, dst, transfer_ix_data(250));
}

/// p-token Transfer with SHORT instruction data (1 byte, just the
/// discriminator — no amount): the `jlt ix_len, 9` at pc 3998 diverts.
#[test]
fn p_token_transfer_short_ix_matches_mollusk() {
    let mint = pid(84);
    let auth = pid(81);
    let src = build_token_account(&mint, &auth, 1_000);
    let dst = build_token_account(&mint, &auth, 0);
    assert_p_token_transfer_fails("short-ix", 80, src, dst, vec![3]);
}

/// Cross-mint Transfer where the mints differ ONLY in the given 8-byte limb
/// of the pubkey: exercises the corresponding `jne` of the unrolled 4-limb
/// mint compare (pcs 4019/4022/4025/4028 for limbs 0-3). The limb-0 case is
/// `p_token_transfer_mint_mismatch_matches_mollusk`; these cover the
/// remaining sibling error paths of the same mint guard.
fn mint_mismatch_limb(label: &str, seed: u64, limb: usize) {
    let mint_a = pid(seed + 4);
    let mut b = [0u8; 32];
    b.copy_from_slice(mint_a.as_ref());
    b[limb * 8] ^= 0xFF; // differ only within limb `limb`
    let mint_b = Pubkey::from(b);
    let auth = pid(seed + 1);
    let src = build_token_account(&mint_a, &auth, 1_000);
    let dst = build_token_account(&mint_b, &auth, 0);
    assert_p_token_transfer_fails(label, seed, src, dst, transfer_ix_data(250));
}

#[test]
fn p_token_transfer_mint_mismatch_limb1_matches_mollusk() {
    mint_mismatch_limb("mint-mismatch-limb1", 86, 1);
}

#[test]
fn p_token_transfer_mint_mismatch_limb2_matches_mollusk() {
    mint_mismatch_limb("mint-mismatch-limb2", 92, 2);
}

#[test]
fn p_token_transfer_mint_mismatch_limb3_matches_mollusk() {
    mint_mismatch_limb("mint-mismatch-limb3", 98, 3);
}

/// Set the SPL token-account delegate fields: COption tag @72 = Some,
/// delegate key @76..108, delegated_amount @121..129.
fn set_delegate(data: &mut [u8], delegate: &Pubkey, delegated_amount: u64) {
    data[72..76].copy_from_slice(&1u32.to_le_bytes());
    data[76..108].copy_from_slice(delegate.as_ref());
    data[121..129].copy_from_slice(&delegated_amount.to_le_bytes());
}

/// Authority tri-case, leg 1: the authority IS the token owner but is NOT a
/// signer: ProgramError::MissingRequiredSignature (builtin, 8<<32).
#[test]
fn p_token_transfer_owner_not_signer_matches_mollusk() {
    let mint = pid(108);
    let auth = pid(105); // = driver authority (seed+1) = token owner
    let src = build_token_account(&mint, &auth, 1_000);
    let dst = build_token_account(&mint, &auth, 0);
    assert_p_token_transfer_fails_auth(
        "owner-not-signer", 104, src, dst, transfer_ix_data(250), false);
}

/// Authority tri-case, leg 2: the authority is the account's DELEGATE (not
/// the owner) but is NOT a signer: MissingRequiredSignature via the
/// delegate branch of validate_owner.
#[test]
fn p_token_transfer_delegate_not_signer_matches_mollusk() {
    let mint = pid(114);
    let owner = pid(115); // NOT the driver authority
    let delegate = pid(111); // = driver authority (seed+1)
    let mut src = build_token_account(&mint, &owner, 1_000);
    set_delegate(&mut src, &delegate, 1_000);
    let dst = build_token_account(&mint, &owner, 0);
    assert_p_token_transfer_fails_auth(
        "delegate-not-signer", 110, src, dst, transfer_ix_data(250), false);
}

/// Authority tri-case, leg 3: the authority is NEITHER the owner NOR the
/// delegate (a properly signing stranger): TokenError::OwnerMismatch (4).
#[test]
fn p_token_transfer_owner_mismatch_matches_mollusk() {
    let mint = pid(120);
    let owner = pid(121); // NOT the driver authority, no delegate set
    let src = build_token_account(&mint, &owner, 1_000);
    let dst = build_token_account(&mint, &owner, 0);
    assert_p_token_transfer_fails_auth(
        "owner-mismatch", 116, src, dst, transfer_ix_data(250), true);
}

/// Delegate leg 4: a properly signing delegate whose DELEGATED allowance is
/// smaller than the transfer amount: TokenError::InsufficientFunds (1) via
/// the delegated_amount check (a distinct check from the source-balance one
/// — the source holds plenty).
#[test]
fn p_token_transfer_delegate_insufficient_matches_mollusk() {
    let mint = pid(126);
    let owner = pid(127);
    let delegate = pid(123); // = driver authority (seed+1)
    let mut src = build_token_account(&mint, &owner, 1_000);
    set_delegate(&mut src, &delegate, 100); // allowance 100 < 250
    let dst = build_token_account(&mint, &owner, 0);
    assert_p_token_transfer_fails_auth(
        "delegate-insufficient", 122, src, dst, transfer_ix_data(250), true);
}

/// PINNED NON-GUARD (pattern library finding): p-token does NOT enforce a
/// destination-balance overflow check on Transfer. Where SPL Token uses
/// `checked_add(...).ok_or(TokenError::Overflow)`, the p-token binary WRAPS
/// the destination amount — both engines SUCCEED and the dest balance wraps
/// mod 2^64. This is REQUIRES-without-ENFORCES: the check is protected only
/// by the global supply invariant (balances sum to supply ≤ u64::MAX, upheld
/// by MintTo), not by the Transfer arm itself. Pinned here so a future
/// p-token that adds the check surfaces as a diff.
#[test]
fn p_token_transfer_dest_overflow_wraps_on_both() {
    let program_id = pid(128);
    let authority = pid(129);
    let source_key = pid(130);
    let dest_key = pid(131);
    let mint = pid(132);
    const LAMPORTS: u64 = 2_039_280;
    const DEST_INITIAL: u64 = u64::MAX - 100;
    const AMOUNT: u64 = 250;
    const WRAPPED: u64 = DEST_INITIAL.wrapping_add(AMOUNT); // = 149

    let src = build_token_account(&mint, &authority, 1_000);
    let dst = build_token_account(&mint, &authority, DEST_INITIAL);

    let ix = Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new(source_key, false),
            AccountMeta::new(dest_key, false),
            AccountMeta::new_readonly(authority, true),
        ],
        data: transfer_ix_data(AMOUNT),
    };

    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&program_id, P_TOKEN_SO);
    let fs_r = fs
        .process_instruction(&ix, &[
            (source_key, AccountSharedData::from(Account {
                lamports: LAMPORTS, data: src.clone(), owner: program_id,
                executable: false, rent_epoch: 0,
            })),
            (dest_key, AccountSharedData::from(Account {
                lamports: LAMPORTS, data: dst.clone(), owner: program_id,
                executable: false, rent_epoch: 0,
            })),
            (authority, AccountSharedData::from(Account {
                lamports: 1_000_000, data: vec![], owner: Pubkey::default(),
                executable: false, rent_epoch: 0,
            })),
        ])
        .expect("qedsvm runs p-token Transfer (dest overflow)");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        P_TOKEN_SO,
    );
    let m_r = m.process_instruction(&ix, &[
        (source_key, mollusk_account::Account {
            lamports: LAMPORTS, data: src.clone(), owner: program_id,
            executable: false, rent_epoch: 0,
        }),
        (dest_key, mollusk_account::Account {
            lamports: LAMPORTS, data: dst.clone(), owner: program_id,
            executable: false, rent_epoch: 0,
        }),
        (authority, mollusk_account::Account {
            lamports: 1_000_000, data: vec![], owner: Pubkey::default(),
            executable: false, rent_epoch: 0,
        }),
    ]);

    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected the UNCHECKED dest add to succeed, got {:?}",
        fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected the UNCHECKED dest add to succeed, got {:?}",
        m_r.program_result);

    for (result_name, data) in [
        ("qedsvm", fs_acct_by_key(&fs_r, &dest_key).data().to_vec()),
        ("mollusk", m_r.resulting_accounts.iter()
            .find(|(k, _)| *k == dest_key).map(|(_, a)| a.data.clone())
            .expect("mollusk dest")),
    ] {
        let post = u64::from_le_bytes(data[64..72].try_into().unwrap());
        assert_eq!(post, WRAPPED,
            "{result_name}: dest balance must WRAP (not saturate/abort) on \
             the unchecked add");
    }

    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged for overflow p-token Transfer: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// Generic p-token failing-instruction driver for the fan-out arms
/// (MintTo/Burn/TransferChecked/CloseAccount guard fixtures): runs the given
/// instruction on both engines, asserts both FAIL, post-states byte-identical
/// across engines, CU identical. `accounts` = (key, lamports, data, owner).
fn assert_p_token_ix_fails(
    label: &str,
    program_id: Pubkey,
    ix: Instruction,
    accounts: Vec<(Pubkey, u64, Vec<u8>, Pubkey)>,
) {
    let fs_accounts: Vec<_> = accounts.iter().map(|(k, l, d, o)| {
        (*k, AccountSharedData::from(Account {
            lamports: *l, data: d.clone(), owner: *o,
            executable: false, rent_epoch: 0,
        }))
    }).collect();
    let m_accounts: Vec<_> = accounts.iter().map(|(k, l, d, o)| {
        (*k, mollusk_account::Account {
            lamports: *l, data: d.clone(), owner: *o,
            executable: false, rent_epoch: 0,
        })
    }).collect();

    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&program_id, P_TOKEN_SO);
    let fs_r = fs.process_instruction(&ix, &fs_accounts)
        .unwrap_or_else(|e| panic!("qedsvm runs p-token ({label}): {e:?}"));

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        P_TOKEN_SO,
    );
    let m_r = m.process_instruction(&ix, &m_accounts);

    eprintln!("[{label}] fs.program_result   = {:?}", fs_r.program_result);
    eprintln!("[{label}] mol.program_result  = {:?}", m_r.program_result);

    assert!(!matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: {label} must fail, got Success");
    assert!(!matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: {label} must fail, got Success");

    for (key, _, _, _) in &accounts {
        let fa = fs_acct_by_key(&fs_r, key);
        let ma = m_r.resulting_accounts.iter().find(|(k, _)| k == key)
            .map(|(_, a)| a).expect("mollusk account");
        assert_eq!(fa.data(), ma.data.as_slice(),
            "{label}: post data diverged for {key}");
        assert_eq!(fa.lamports(), ma.lamports,
            "{label}: post lamports diverged for {key}");
    }

    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged for {label}: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

fn mint_to_ix_data(amount: u64) -> Vec<u8> {
    let mut d = Vec::with_capacity(9); // [7, amount_le_u64]
    d.push(7);
    d.extend_from_slice(&amount.to_le_bytes());
    d
}

fn burn_ix_data(amount: u64) -> Vec<u8> {
    let mut d = Vec::with_capacity(9); // [8, amount_le_u64]
    d.push(8);
    d.extend_from_slice(&amount.to_le_bytes());
    d
}

fn transfer_checked_ix_data(amount: u64, decimals: u8) -> Vec<u8> {
    let mut d = Vec::with_capacity(10); // [12, amount_le_u64, decimals]
    d.push(12);
    d.extend_from_slice(&amount.to_le_bytes());
    d.push(decimals);
    d
}

const MINT_LAMPORTS: u64 = 2_000_000;
const ACCT_LAMPORTS: u64 = 2_039_280;

/// MintTo violating-fixture driver: (mint, dest, authority) 3-account shape.
fn mint_to_fails(label: &str, seed: u64, mint_data: Vec<u8>, dest_data: Vec<u8>,
                 amount: u64) {
    let program_id = pid(seed);
    let mint_key = pid(seed + 1);
    let dest_key = pid(seed + 2);
    let authority = pid(seed + 3);
    let ix = Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new(mint_key, false),
            AccountMeta::new(dest_key, false),
            AccountMeta::new_readonly(authority, true),
        ],
        data: mint_to_ix_data(amount),
    };
    assert_p_token_ix_fails(label, program_id, ix, vec![
        (mint_key, MINT_LAMPORTS, mint_data, program_id),
        (dest_key, ACCT_LAMPORTS, dest_data, program_id),
        (authority, 1_000_000, vec![], Pubkey::default()),
    ]);
}

/// MintTo SUPPLY-OVERFLOW: supply + amount does not fit u64. This is the
/// check the (absent) Transfer dest-overflow check leans on — see
/// `p_token_transfer_dest_overflow_wraps_on_both`. If THIS also wrapped, the
/// supply invariant would be unsound program-wide.
#[test]
fn p_token_mint_to_supply_overflow_matches_mollusk() {
    let seed = 140;
    let mint_key = pid(seed + 1);
    let authority = pid(seed + 3);
    let dest_owner = pid(seed + 4);
    let mint_data = build_mint_account(&authority, u64::MAX - 100, 9);
    let dest_data = build_token_account(&mint_key, &dest_owner, 0);
    mint_to_fails("mint-to-supply-overflow", seed, mint_data, dest_data, 250);
}

/// MintTo into a FIXED-SUPPLY mint (mint_authority = COption::None):
/// TokenError::FixedSupply (5).
#[test]
fn p_token_mint_to_fixed_supply_matches_mollusk() {
    let seed = 144;
    let mint_key = pid(seed + 1);
    let authority = pid(seed + 3);
    let dest_owner = pid(seed + 4);
    let mut mint_data = build_mint_account(&authority, 1_000, 9);
    mint_data[0..4].copy_from_slice(&0u32.to_le_bytes()); // COption::None
    mint_data[4..36].fill(0);
    let dest_data = build_token_account(&mint_key, &dest_owner, 0);
    mint_to_fails("mint-to-fixed-supply", seed, mint_data, dest_data, 250);
}

/// MintTo signed by an authority that is NOT the mint authority:
/// TokenError::OwnerMismatch (4) on the MINT-authority check.
#[test]
fn p_token_mint_to_authority_mismatch_matches_mollusk() {
    let seed = 148;
    let mint_key = pid(seed + 1);
    let real_auth = pid(seed + 4); // NOT the signing authority (seed+3)
    let dest_owner = pid(seed + 5);
    let mint_data = build_mint_account(&real_auth, 1_000, 9);
    let dest_data = build_token_account(&mint_key, &dest_owner, 0);
    mint_to_fails("mint-to-authority-mismatch", seed, mint_data, dest_data, 250);
}

/// MintTo into a token account of a DIFFERENT mint:
/// TokenError::MintMismatch (3).
#[test]
fn p_token_mint_to_mint_mismatch_matches_mollusk() {
    let seed = 152;
    let authority = pid(seed + 3);
    let other_mint = pid(seed + 4);
    let dest_owner = pid(seed + 5);
    let mint_data = build_mint_account(&authority, 1_000, 9);
    let dest_data = build_token_account(&other_mint, &dest_owner, 0);
    mint_to_fails("mint-to-mint-mismatch", seed, mint_data, dest_data, 250);
}

/// MintTo into a FROZEN destination: TokenError::AccountFrozen (17).
#[test]
fn p_token_mint_to_dest_frozen_matches_mollusk() {
    let seed = 156;
    let mint_key = pid(seed + 1);
    let authority = pid(seed + 3);
    let dest_owner = pid(seed + 4);
    let mint_data = build_mint_account(&authority, 1_000, 9);
    let mut dest_data = build_token_account(&mint_key, &dest_owner, 0);
    dest_data[108] = 2; // AccountState::Frozen
    mint_to_fails("mint-to-dest-frozen", seed, mint_data, dest_data, 250);
}

/// Burn violating-fixture driver: (account, mint, owner) 3-account shape.
fn burn_fails(label: &str, seed: u64, acct_data: Vec<u8>, mint_data: Vec<u8>,
              amount: u64) {
    let program_id = pid(seed);
    let mint_key = pid(seed + 1);
    let acct_key = pid(seed + 2);
    let owner = pid(seed + 3);
    let ix = Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new(acct_key, false),
            AccountMeta::new(mint_key, false),
            AccountMeta::new_readonly(owner, true),
        ],
        data: burn_ix_data(amount),
    };
    assert_p_token_ix_fails(label, program_id, ix, vec![
        (acct_key, ACCT_LAMPORTS, acct_data, program_id),
        (mint_key, MINT_LAMPORTS, mint_data, program_id),
        (owner, 1_000_000, vec![], Pubkey::default()),
    ]);
}

/// Burn more than the account balance: TokenError::InsufficientFunds (1) —
/// the balance guard's twin on the Burn arm.
#[test]
fn p_token_burn_insufficient_matches_mollusk() {
    let seed = 160;
    let mint_key = pid(seed + 1);
    let owner = pid(seed + 3);
    let mint_auth = pid(seed + 4);
    let acct_data = build_token_account(&mint_key, &owner, 100);
    let mint_data = build_mint_account(&mint_auth, 1_000, 9);
    burn_fails("burn-insufficient", seed, acct_data, mint_data, 250);
}

/// Burn from a FROZEN account: TokenError::AccountFrozen (17).
#[test]
fn p_token_burn_frozen_matches_mollusk() {
    let seed = 164;
    let mint_key = pid(seed + 1);
    let owner = pid(seed + 3);
    let mint_auth = pid(seed + 4);
    let mut acct_data = build_token_account(&mint_key, &owner, 1_000);
    acct_data[108] = 2; // AccountState::Frozen
    let mint_data = build_mint_account(&mint_auth, 1_000, 9);
    burn_fails("burn-frozen", seed, acct_data, mint_data, 250);
}

/// TransferChecked violating-fixture driver: (source, mint, dest, authority).
fn transfer_checked_fails(label: &str, seed: u64, src_data: Vec<u8>,
                          mint_data: Vec<u8>, dst_data: Vec<u8>,
                          amount: u64, decimals: u8) {
    let program_id = pid(seed);
    let mint_key = pid(seed + 1);
    let source_key = pid(seed + 2);
    let dest_key = pid(seed + 3);
    let authority = pid(seed + 4);
    let ix = Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new(source_key, false),
            AccountMeta::new_readonly(mint_key, false),
            AccountMeta::new(dest_key, false),
            AccountMeta::new_readonly(authority, true),
        ],
        data: transfer_checked_ix_data(amount, decimals),
    };
    assert_p_token_ix_fails(label, program_id, ix, vec![
        (source_key, ACCT_LAMPORTS, src_data, program_id),
        (mint_key, MINT_LAMPORTS, mint_data, program_id),
        (dest_key, ACCT_LAMPORTS, dst_data, program_id),
        (authority, 1_000_000, vec![], Pubkey::default()),
    ]);
}

/// TransferChecked with the WRONG decimals argument (6 vs the mint's 9):
/// TokenError::MintDecimalsMismatch (18) — the check the *Checked family
/// exists for.
#[test]
fn p_token_transfer_checked_decimals_mismatch_matches_mollusk() {
    let seed = 168;
    let mint_key = pid(seed + 1);
    let authority = pid(seed + 4);
    let mint_auth = pid(seed + 5);
    let mint_data = build_mint_account(&mint_auth, 1_000, 9);
    let src = build_token_account(&mint_key, &authority, 1_000);
    let dst = build_token_account(&mint_key, &authority, 0);
    transfer_checked_fails("transfer-checked-decimals", seed,
        src, mint_data, dst, 250, 6);
}

/// TransferChecked where the accounts belong to a DIFFERENT mint than the
/// provided mint account: TokenError::MintMismatch (3) against the
/// EXPLICIT mint (a distinct check from the src-vs-dest compare on the
/// unchecked Transfer).
#[test]
fn p_token_transfer_checked_mint_mismatch_matches_mollusk() {
    let seed = 172;
    let authority = pid(seed + 4);
    let mint_auth = pid(seed + 5);
    let other_mint = pid(seed + 6);
    let mint_data = build_mint_account(&mint_auth, 1_000, 9);
    let src = build_token_account(&other_mint, &authority, 1_000);
    let dst = build_token_account(&other_mint, &authority, 0);
    transfer_checked_fails("transfer-checked-mint-mismatch", seed,
        src, mint_data, dst, 250, 9);
}

/// CloseAccount with a NONZERO token balance:
/// TokenError::NonNativeHasBalance (11).
#[test]
fn p_token_close_account_nonzero_matches_mollusk() {
    let seed = 176;
    let program_id = pid(seed);
    let mint_key = pid(seed + 1);
    let acct_key = pid(seed + 2);
    let dest_key = pid(seed + 3);
    let owner = pid(seed + 4);
    let acct_data = build_token_account(&mint_key, &owner, 250);
    let ix = Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new(acct_key, false),
            AccountMeta::new(dest_key, false),
            AccountMeta::new_readonly(owner, true),
        ],
        data: vec![9],
    };
    assert_p_token_ix_fails("close-account-nonzero", program_id, ix, vec![
        (acct_key, ACCT_LAMPORTS, acct_data, program_id),
        (dest_key, 500_000, vec![], Pubkey::default()),
        (owner, 1_000_000, vec![], Pubkey::default()),
    ]);
}

/// ELF-load probe for ATA binary: both engines fail before CPI. Validates loading + entry dispatch without CPI dependency.
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

/// CPI write-back: caller forwards writable account → incrementer adds 1. Validates full CPI plumbing byte-for-byte.
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
    // Callee program account must be in caller's AccountInfos for CPI program_id resolution.
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

    assert_no_poststate_backstop(&fs_r); // M13: write-back must come from VM, not Rust backstop
    let fs_acct = fs_acct_by_key(&fs_r, &acct_key);
    assert_eq!(fs_acct.data(), expected.as_slice(),
        "qedsvm: increment not visible after CPI; got {:?}", fs_acct.data());

    let (_, m_acct) = &m_r.resulting_accounts[0];
    assert_eq!(m_acct.data.as_slice(), expected.as_slice());
}

/// M6r: CPI realloc write-back. Callee grows 16→24 bytes, writes sentinel into tail.
/// `assert_no_poststate_backstop` proves the VM harvested the grow, not the M13 Rust backstop.
#[test]
fn cpi_callee_reallocs_account_grow() {
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
    fs.add_program(&callee_id, CPI_REALLOC_CALLEE_SO);
    let fs_r = fs.process_instruction(&ix, &[
        (acct_key, pre_shared),
        (callee_id, callee_program_shared),
    ]).expect("qedsvm runs CPI→realloc");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &caller_id, &solana_sdk_ids::bpf_loader_upgradeable::id(),
        CPI_INCREMENT_CALLER_SO);
    m.add_program_with_loader_and_elf(
        &callee_id, &solana_sdk_ids::bpf_loader_upgradeable::id(), CPI_REALLOC_CALLEE_SO);
    let m_r = m.process_instruction(&ix, &[
        (acct_key, pre_mollusk),
        (callee_id, callee_program_mollusk),
    ]);

    let our_logs: Vec<String> = fs_r.logs.iter()
        .map(|b| String::from_utf8_lossy(b).into_owned()).collect();
    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success on CPI→realloc, got {:?}; logs: {our_logs:?}",
        fs_r.program_result);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success on CPI→realloc, got {:?}", m_r.program_result);

    let mut expected = vec![0u8; 24]; // [0..16) original zeros, [16..24) callee sentinel
    expected[16..24].copy_from_slice(&0xA1A2A3A4A5A6A7A8u64.to_le_bytes());

    assert_no_poststate_backstop(&fs_r);
    let fs_acct = fs_acct_by_key(&fs_r, &acct_key);
    assert_eq!(fs_acct.data(), expected.as_slice(),
        "qedsvm: realloc grow not visible after CPI; got {:?}", fs_acct.data());

    let (_, m_acct) = &m_r.resulting_accounts[0];
    assert_eq!(m_acct.data.as_slice(), expected.as_slice(),
        "mollusk: realloc grow mismatch");
    assert_eq!(fs_acct.data(), m_acct.data.as_slice(),
        "cross-engine realloc data mismatch");
}

/// M6r negative: callee tries to grow +10241 bytes (over MAX_PERMITTED_DATA_INCREASE). Both engines reject;
/// asserts account state unchanged — error codes diverge by design so we don't assert them.
#[test]
fn cpi_callee_realloc_overflow_rejected_on_both() {
    let caller_id = pid(56);
    let callee_id = pid(57);
    let acct_key  = pid(58);

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
    fs.add_program(&callee_id, CPI_REALLOC_OVERFLOW_CALLEE_SO);
    let fs_r = fs.process_instruction(&ix, &[
        (acct_key, pre_shared),
        (callee_id, callee_program_shared),
    ]).expect("qedsvm runs CPI→realloc-overflow");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &caller_id, &solana_sdk_ids::bpf_loader_upgradeable::id(),
        CPI_INCREMENT_CALLER_SO);
    m.add_program_with_loader_and_elf(
        &callee_id, &solana_sdk_ids::bpf_loader_upgradeable::id(),
        CPI_REALLOC_OVERFLOW_CALLEE_SO);
    let m_r = m.process_instruction(&ix, &[
        (acct_key, pre_mollusk),
        (callee_id, callee_program_mollusk),
    ]);

    eprintln!("fs.program_result  = {:?}", fs_r.program_result);
    eprintln!("mol.program_result = {:?}", m_r.program_result);

    assert!(!matches!(fs_r.program_result, FsProgramResult::Success), // both must reject over-grow
        "qedsvm: over-grow realloc should fail, got {:?}", fs_r.program_result);
    assert!(!matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: over-grow realloc should fail, got {:?}", m_r.program_result);

    let unchanged = vec![0u8; 16]; // rolled back on both engines
    let fs_acct = fs_acct_by_key(&fs_r, &acct_key);
    assert_eq!(fs_acct.data(), unchanged.as_slice(),
        "qedsvm: over-grow account should be unchanged; got len {}", fs_acct.data().len());
    let (_, m_acct) = &m_r.resulting_accounts[0];
    assert_eq!(m_acct.data.as_slice(), unchanged.as_slice(),
        "mollusk: over-grow account should be unchanged; got len {}", m_acct.data.len());
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

    let ix = Instruction { // acct_key READ-ONLY at top level — escalation to writable in CPI must fail
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

    assert_no_poststate_backstop(&fs_r); // read-only account must stay unchanged on both engines
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

/// CPI caller → logger.so: callee logs "hi"; asserts sub-VM logs propagate back to caller State.
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

    let our_logs: Vec<String> = fs_r.logs.iter()
        .map(|b| String::from_utf8_lossy(b).into_owned()).collect();
    assert!(our_logs.iter().any(|l| l == "hi"),
        "expected 'hi' in qedsvm logs, got: {our_logs:?}");
}

/// Simplest CPI end-to-end: caller invokes noop.so (target pubkey in ix.data); asserts both engines succeed.
#[test]
fn cpi_caller_invokes_registered_noop() {
    let caller_id = pid(30);
    let callee_id = pid(31);
    let ix = Instruction {
        program_id: caller_id,
        accounts: vec![AccountMeta::new_readonly(callee_id, false)],
        data: callee_id.to_bytes().to_vec(), // first 32 bytes = target pubkey
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

    let our_logs: Vec<String> = fs_r.logs.iter()
        .map(|b| String::from_utf8_lossy(b).into_owned()).collect();
    assert!(matches!(fs_r.program_result, FsProgramResult::Success),
        "qedsvm: expected Success on CPI, got {:?}; logs: {:?}",
        fs_r.program_result, our_logs);
    assert!(matches!(m_r.program_result, MlProgramResult::Success),
        "mollusk: expected Success on CPI, got {:?}", m_r.program_result);
}

/// Pinocchio escrow with empty ix: probes ELF load + first-dispatch; fails before real work on both engines.
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

/// Non-empty ix.data passes through to noop without divergence.
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

/// N=2 CPI: caller forwards two accounts to incrementer; accounts[0] incremented, accounts[1] unchanged; byte-identical.
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

    // accounts[0] += 1, accounts[1] unchanged; both engines agree.
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

    assert_eq!(fs_a.data(), m_a.data.as_slice(), "accounts[0] diverged");
    assert_eq!(fs_b.data(), m_b.data.as_slice(), "accounts[1] diverged");
    assert_eq!(fs_a.lamports(), m_a.lamports, "accounts[0] lamports diverged");
    assert_eq!(fs_b.lamports(), m_b.lamports, "accounts[1] lamports diverged");
}

/// R_BPF_64_Relative-in-.text relocation pin: pre-fix exit=0 (Success), post-fix exit=1 (Failure); both engines agree.
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

    // M5: lddw is ONE logical insn (meter ticks once per step); 4-insn program = CU=4, NOT 5.
    assert_eq!(m_r.compute_units_consumed, 4,
        "M5: agave must meter the 4-logical-insn (1 lddw) program at 4 CU, \
         got {} — lddw CU weight changed in agave", m_r.compute_units_consumed);
}

/// M9: MSM CU = base + 758*(n-1); n=1+n=2 boundary confirms (n-1) form, not (n).
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

/// L1: clean exit with r0 = ERR_ABORT sentinel value; both engines must agree on the observable class.
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

/// sol_try_find_program_address end-to-end: 33-byte return_data (PDA+bump) and CU equal on both engines.
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

/// Tier-1 OOB read: input+0x10000000 is unmapped; pre-fix returned Success, now both VM-fault.
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

    // M14: VM-fault (accessViolation) → agave UnknownError(ProgramFailedToComplete); assert_outcome_matches checks equivalence.
    assert!(matches!(fs_r.program_result, FsProgramResult::VmFault { .. }),
        "qedsvm should VM-fault on OOB read, got {:?}", fs_r.program_result);
    assert_outcome_matches(&fs_r.program_result, &m_r.program_result, "oob_read");
}

/// Phase 7 sub-item 3: a program that calls the `abort` syscall faults on
/// both engines (qedsvm `vmError = .abort` → VmFault; agave
/// `ProgramFailedToComplete`). The diff-side counterpart to the lifted
/// `AbortCaller_fault_correct` typed-fault corollary.
#[test]
fn abort_caller_fails_on_both() {
    let program_id = pid(58);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };

    let mut fs = Svm::default();
    fs.add_program(&program_id, ABORT_CALLER_SO);
    let fs_r = fs
        .process_instruction(&ix, &[])
        .expect("qedsvm runs abort_caller");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        ABORT_CALLER_SO,
    );
    let m_r = m.process_instruction(&ix, &[]);

    eprintln!("fs.program_result  = {:?}", fs_r.program_result);
    eprintln!("mol.program_result = {:?}", m_r.program_result);

    assert!(matches!(fs_r.program_result, FsProgramResult::VmFault { .. }),
        "qedsvm should VM-fault on the abort syscall, got {:?}", fs_r.program_result);
    assert_outcome_matches(&fs_r.program_result, &m_r.program_result, "abort_caller");
}

/// H6: sol_memset_ with dst 256 MiB OOB; pre-fix wrote through, post-fix guardWrite VM-faults on both.
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

    assert!(matches!(fs_r.program_result, FsProgramResult::VmFault { .. }),
        "qedsvm should VM-fault on OOB sol_memset_, got {:?}", fs_r.program_result);
    assert_outcome_matches(&fs_r.program_result, &m_r.program_result, "oob_memset");
}

/// H6: sol_log_pubkey with ptr 256 MiB OOB; translate_type::<Pubkey> → guardRead VM-faults on both.
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

/// H6: sol_log_ with msg 256 MiB OOB; translate_slice → guardRead VM-faults on both.
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

/// H6: sol_log_data with descriptor array 256 MiB OOB; array read traps before slice deref on both.
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

/// H6: sol_sha256 output buffer 256 MiB OOB; translate_slice_mut on output traps first; guardWrite VM-faults on both.
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

/// H6: sol_sha256 valid output, input descriptor array 256 MiB OOB; guardRead traps after output pass.
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

/// H6: sol_poseidon valid output, input array 256 MiB OOB; guardedCommit guardRead VM-faults on both.
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

/// H6: sol_get_clock_sysvar output 256 MiB OOB; translate_type_mut::<Clock> → zeroFillR1 guardWrite VM-faults on both.
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

/// H6: sol_set_return_data input 256 MiB OOB (within MAX_RETURN_DATA); length passes then translate_slice traps.
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

/// H6: sol_get_rent_sysvar output 256 MiB OOB; translate_type_mut::<Rent> → guardWrite VM-faults on both.
#[test]
fn oob_rent_sysvar_fails_on_both() {
    let program_id = pid(247);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };

    let mut fs = Svm::default();
    fs.add_program(&program_id, OOB_RENT_SYSVAR_SO);
    let fs_r = fs
        .process_instruction(&ix, &[])
        .expect("qedsvm runs oob_rent_sysvar");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        OOB_RENT_SYSVAR_SO,
    );
    let m_r = m.process_instruction(&ix, &[]);

    eprintln!("fs.program_result  = {:?}", fs_r.program_result);
    eprintln!("mol.program_result = {:?}", m_r.program_result);

    assert!(matches!(fs_r.program_result, FsProgramResult::VmFault { .. }),
        "qedsvm should VM-fault on OOB sol_get_rent_sysvar, got {:?}", fs_r.program_result);
    assert_outcome_matches(&fs_r.program_result, &m_r.program_result, "oob_rent_sysvar");
}

/// H6: sol_get_return_data output 256 MiB OOB (copyLen=8); translate_slice_mut → guardWrite VM-faults on both.
#[test]
fn oob_get_return_data_fails_on_both() {
    let program_id = pid(248);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };

    let mut fs = Svm::default();
    fs.add_program(&program_id, OOB_GET_RETURN_DATA_SO);
    let fs_r = fs
        .process_instruction(&ix, &[])
        .expect("qedsvm runs oob_get_return_data");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        OOB_GET_RETURN_DATA_SO,
    );
    let m_r = m.process_instruction(&ix, &[]);

    eprintln!("fs.program_result  = {:?}", fs_r.program_result);
    eprintln!("mol.program_result = {:?}", m_r.program_result);

    assert!(matches!(fs_r.program_result, FsProgramResult::VmFault { .. }),
        "qedsvm should VM-fault on OOB sol_get_return_data, got {:?}", fs_r.program_result);
    assert_outcome_matches(&fs_r.program_result, &m_r.program_result, "oob_get_return_data");
}

/// H6: sol_secp256k1_recover hash 256 MiB OOB; representative of whole curve/crypto family's guardRead coverage.
#[test]
fn oob_secp256k1_fails_on_both() {
    let program_id = pid(249);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };

    let mut fs = Svm::default();
    fs.add_program(&program_id, OOB_SECP256K1_SO);
    let fs_r = fs
        .process_instruction(&ix, &[])
        .expect("qedsvm runs oob_secp256k1");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        OOB_SECP256K1_SO,
    );
    let m_r = m.process_instruction(&ix, &[]);

    eprintln!("fs.program_result  = {:?}", fs_r.program_result);
    eprintln!("mol.program_result = {:?}", m_r.program_result);

    assert!(matches!(fs_r.program_result, FsProgramResult::VmFault { .. }),
        "qedsvm should VM-fault on OOB sol_secp256k1_recover, got {:?}", fs_r.program_result);
    assert_outcome_matches(&fs_r.program_result, &m_r.program_result, "oob_secp256k1");
}

/// H6: sol_create_program_address with OOB program_id/output; guardRead/guardedCommit VM-faults on both.
#[test]
fn oob_create_pda_fails_on_both() {
    let program_id = pid(250);
    let ix = Instruction { program_id, accounts: vec![], data: vec![] };

    let mut fs = Svm::default();
    fs.add_program(&program_id, OOB_CREATE_PDA_SO);
    let fs_r = fs
        .process_instruction(&ix, &[])
        .expect("qedsvm runs oob_create_pda");

    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id,
        &solana_sdk_ids::bpf_loader_upgradeable::id(),
        OOB_CREATE_PDA_SO,
    );
    let m_r = m.process_instruction(&ix, &[]);

    eprintln!("fs.program_result  = {:?}", fs_r.program_result);
    eprintln!("mol.program_result = {:?}", m_r.program_result);

    assert!(matches!(fs_r.program_result, FsProgramResult::VmFault { .. }),
        "qedsvm should VM-fault on OOB sol_create_program_address, got {:?}", fs_r.program_result);
    assert_outcome_matches(&fs_r.program_result, &m_r.program_result, "oob_create_pda");
}

/// Tier-1 native System::Transfer CPI: from -= n, to += n; lamport conservation without Rust backstop.
#[test]
fn system_transfer_cpi_matches_mollusk() {
    let caller_id = pid(60);
    let from_pk   = pid(61);
    let to_pk     = pid(62);

    let lamports_to_send: u64 = 1_000;
    let initial_from: u64 = 5_000_000;
    let initial_to: u64   =   100_000;

    let system_program_id = Pubkey::new_from_array([0u8; 32]); // all-zero pubkey = System program

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

    let system_owner = Pubkey::new_from_array([0u8; 32]); // lamport-bearing accounts are system-owned

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

    // System program stub: mirrors mollusk's keyed_account_for_system_program so resulting_accounts compares cleanly.
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
    assert_no_poststate_backstop(&fs_r); // M13: lamport conservation in VM, not via Rust backstop

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

    let fs_from = fs_r.resulting_accounts.iter().find(|(k, _)| *k == from_pk)
        .expect("from account present").1.lamports();
    let fs_to   = fs_r.resulting_accounts.iter().find(|(k, _)| *k == to_pk)
        .expect("to account present").1.lamports();
    assert_eq!(fs_from, initial_from - lamports_to_send,
        "from balance: expected {}, got {}", initial_from - lamports_to_send, fs_from);
    assert_eq!(fs_to,   initial_to   + lamports_to_send,
        "to balance: expected {}, got {}", initial_to + lamports_to_send, fs_to);

    // M6r: BPF insns + 946 (Cpi.cu invoke_signed) + 150 (System::Transfer) = total.
    assert_eq!(
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
        "CU diverged for system_transfer CPI: ours={} mollusk={}",
        fs_r.compute_units_consumed, m_r.compute_units_consumed,
    );
}

/// System::CreateAccount CPI: newAcct initialized to (lamports, space zeros, target owner); payer decremented.
#[test]
fn system_create_account_cpi_matches_mollusk() {
    let caller_id  = pid(70);
    let payer_pk   = pid(71);
    let new_pk     = pid(72);
    let target_owner = pid(73);  // arbitrary "program owner" for the new acct

    let lamports_to_send: u64 = 2_000_000;
    let space: u64 = 165; // SPL Token's mint account size — exercises non-zero space allocation
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

/// System::Allocate+Assign chained CPI: data.len()=space, owner=target; 2*(946+150)=2192 CU overhead.
#[test]
fn system_allocate_assign_cpi_matches_mollusk() {
    let caller_id    = pid(80);
    let acct_pk      = pid(81);
    let target_owner = pid(82);

    let space: u64 = 165;
    let initial_lamports: u64 = 7_000_000; // neither Allocate nor Assign touches lamports

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

/// System::CreateAccountWithSeed CPI: derived = SHA256(base||seed||owner); verifies seed arithmetic vs agave.
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

/// ComputeBudget CPI: runtime handles at prepare-time; in-CPI no-op (150 CU), both engines agree.
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
            AccountMeta::new_readonly(compute_budget_id, false), // must be in account-key set for CPI dispatch
        ],
        data: ix_data,
    };

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

/// PDA signer promotion via invoke_signed seeds: callee writes 0xAA iff PDA is_signer; both engines must agree.
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

/// CPI returnData round-trip: callee sets [0xAB,0xCD,0xEF,0x12], caller gets+writes to accounts[0].data.
#[test]
fn cpi_returns_data_propagates() {
    let caller_id = pid(210);
    let callee_id = pid(211);
    let data_key  = pid(212);

    let data: Vec<u8> = vec![0u8; 4];
    let data_pre_fs = AccountSharedData::from(Account {
        lamports: 1_000_000, data: data.clone(),
        owner: caller_id, executable: false, rent_epoch: 0, // caller must own data_key to write it
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

/// H7: sol_get_return_data writes the SETTER's program id into *pubkey_out; accounts[0] = callee_id || payload, byte-identical.
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

/// H7: sol_get_sysvar probe (rent+offset+overrun, clock, epoch_schedule, slot_hashes, unknown); byte-identical + CU.
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

    // Spot-pin the layout: rent bytes, in-band error codes, slot_hashes 512-entry length prefix.
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

/// Depth-2 CPI chain (outer→middle→leaf): leaf increments accounts[0]; visible on both engines after chain returns.
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

    let mut ix_data = Vec::with_capacity(64); // ix.data = middle_id || leaf_id
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

/// Janus issue #10: PDA-target CreateAccount via invoke_signed; dispatcher must promote PDA to isSigner before signer check.
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

    let mut data = Vec::with_capacity(49); // Initialize tag=1 | outcome | bump | 6B pad | u64 target_slot | 32B seed_key
    data.push(1u8);
    data.push(1u8); // outcome
    data.push(bump);
    data.extend_from_slice(&[0u8; 6]);
    data.extend_from_slice(&500u64.to_le_bytes()); // target_slot
    data.extend_from_slice(seed_key.as_ref());

    let ix = Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new(payer, true),
            AccountMeta::new(state, false), // PDA target — not a hard signer; must be promoted via seeds
            AccountMeta::new_readonly(authority, true),
            AccountMeta::new_readonly(system_program, false),
        ],
        data,
    };

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

