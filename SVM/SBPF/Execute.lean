-- sBPF execution semantics: single- and multi-step evaluation.

import SVM.SBPF.ISA
import SVM.SBPF.Memory
import SVM.SBPF.Machine
-- Crypto syscall modules: each provides `exec` + `cu`; the dispatchers below
-- are the only place a `Syscall` variant maps to those bodies.
import SVM.Syscalls.Sha256
import SVM.Syscalls.Sha512
import SVM.Syscalls.Keccak256
import SVM.Syscalls.Blake3
import SVM.Syscalls.Poseidon
import SVM.Syscalls.Secp256k1
import SVM.Syscalls.Curve25519
import SVM.Syscalls.Bls12_381
import SVM.Syscalls.AltBn128
import SVM.Syscalls.BigModExp
import SVM.Syscalls.Pda
-- Non-crypto syscall modules (same shape: `exec` + `cu`).
import SVM.Syscalls.Logging
import SVM.Syscalls.MemOps
import SVM.Syscalls.Sysvar
import SVM.Syscalls.ReturnData
import SVM.Syscalls.Abort
import SVM.Syscalls.Misc
import SVM.Syscalls.Cpi

namespace SVM.SBPF

open Memory

/-! ## Per-syscall CU costs

Pure dispatcher mirroring agave's `SVMTransactionExecutionCost::default()`
(`program-runtime/src/execution_budget.rs`); each charge's value lives next to
its syscall body. The `step` caller subtracts the per-instruction baseline of 1
before bumping `State.cuConsumed`. -/

def syscallCu (sc : Syscall) (s : State) : Nat :=
  match sc with
  -- Logging
  | .sol_log_                                    => Logging.cuLog s
  | .sol_log_64_                                 => Logging.cuLog64
  | .sol_log_compute_units_                      => Logging.cuLogComputeUnits
  | .sol_log_pubkey                              => Logging.cuLogPubkey
  | .sol_log_data                                => Logging.cuLogData
  -- Hashing (base + per-byte)
  | .sol_sha256                                  => Sha256.cu s
  | .sol_sha512                                  => Sha512.cu s
  | .sol_keccak256                               => Keccak256.cu s
  | .sol_blake3                                  => Blake3.cu s
  | .sol_poseidon                                => Poseidon.cu s
  -- Memory ops
  | .sol_memcpy  | .sol_memmove
  | .sol_memcmp  | .sol_memset                   => MemOps.cu s
  -- Curve / crypto
  | .sol_secp256k1_recover                       => Secp256k1.cu
  | .sol_curve_validate_point                    => Curve25519.cuValidatePoint s
  | .sol_curve_group_op                          => Curve25519.cuGroupOp s
  | .sol_curve_multiscalar_mul                   => Curve25519.cuMSM s
  | .sol_curve_decompress                        => Bls12_381.cuDecompress
  | .sol_curve_pairing_map                       => Bls12_381.cuPairing
  | .sol_alt_bn128_group_op                      => AltBn128.cuGroupOp s
  | .sol_alt_bn128_compression                   => AltBn128.cuCompression s
  | .sol_big_mod_exp                             => BigModExp.cu s
  -- PDA: `create` fixed; `try_find` scales per bump-loop iteration (matches
  -- agave's pre-loop + per-failed-iter charging in `SyscallTryFindProgramAddress::rust`).
  | .sol_create_program_address                  => Pda.cuCreate
  | .sol_try_find_program_address                => Pda.cuTryFind s
  -- CPI
  | .sol_invoke_signed | .sol_invoke_signed_c    => Cpi.cu
  -- Sysvars — agave charges `sysvar_base_cost + size_of::<T>()`, so each typed
  -- getter has its own constant. The size-parameterized `sol_get_sysvar`
  -- charges length-dependent `cuGetSysvar`; `sol_get_epoch_stake` (fetches no
  -- struct) stays on the bare base cost.
  | .sol_get_clock_sysvar                        => Sysvar.cuClock
  | .sol_get_rent_sysvar                         => Sysvar.cuRent
  | .sol_get_epoch_schedule_sysvar               => Sysvar.cuEpochSchedule
  | .sol_get_last_restart_slot                   => Sysvar.cuLastRestartSlot
  | .sol_get_fees_sysvar                         => Sysvar.cuFees
  | .sol_get_epoch_rewards_sysvar                => Sysvar.cuEpochRewards
  | .sol_get_sysvar                              => Sysvar.cuGetSysvar s
  | .sol_get_epoch_stake                         => Sysvar.cu
  -- Return data — per-byte, see `ReturnData.cuSet` / `ReturnData.cuGet`.
  | .sol_set_return_data                         => ReturnData.cuSet s
  | .sol_get_return_data                         => ReturnData.cuGet s
  -- Abort / panic
  | .abort | .sol_panic_                         => Abort.cu
  -- Misc (alloc, remaining CU, stack height, sibling instr, unknown)
  | .sol_alloc_free_
  | .sol_remaining_compute_units
  | .sol_get_stack_height
  | .sol_get_processed_sibling_instruction
  | .unknown _                                   => Misc.cu

/-! ## Syscall execution -/

/-- Execute a syscall.

    Logging syscalls write into `State.log`; `sol_log_data` emits space-joined
    hex fields, diverging from agave's base64 (see `SVM.SBPF.Logging` docstring).
    Memory syscalls have real byte-move/compare semantics on `Mem`.
    Unmodeled syscalls fall through to the default arm (set `r0 := 0`). -/

@[simp] def execSyscall (sc : Syscall) (s : State) : State :=
  match sc with
  -- Logging
  | .sol_log_                                    => Logging.execLog s
  | .sol_log_pubkey                              => Logging.execLogPubkey s
  | .sol_log_64_                                 => Logging.execLog64 s
  | .sol_log_compute_units_                      => Logging.execLogComputeUnits s
  | .sol_log_data                                => Logging.execLogData s
  -- Hashing
  | .sol_sha256                                  => Sha256.exec s
  | .sol_sha512                                  => Sha512.exec s
  | .sol_keccak256                               => Keccak256.exec s
  | .sol_blake3                                  => Blake3.exec s
  | .sol_poseidon                                => Poseidon.exec s
  -- Memory ops
  | .sol_memcpy | .sol_memmove                   => MemOps.execCopy s
  | .sol_memset                                  => MemOps.execSet s
  | .sol_memcmp                                  => MemOps.execCmp s
  -- Curve / crypto
  | .sol_secp256k1_recover                       => Secp256k1.exec s
  | .sol_curve_validate_point                    => Curve25519.execValidate s
  | .sol_curve_group_op                          => Curve25519.execGroupOp s
  | .sol_curve_multiscalar_mul                   => Curve25519.execMSM s
  | .sol_curve_decompress                        => Bls12_381.execDecompress s
  | .sol_curve_pairing_map                       => Bls12_381.execPairing s
  | .sol_alt_bn128_group_op                      => AltBn128.execGroupOp s
  | .sol_alt_bn128_compression                   => AltBn128.execCompression s
  | .sol_big_mod_exp                             => BigModExp.exec s
  -- PDA
  | .sol_create_program_address                  => Pda.execCreate s
  | .sol_try_find_program_address                => Pda.execTryFind s
  -- CPI
  | .sol_invoke_signed | .sol_invoke_signed_c    => Cpi.exec s
  -- Sysvars
  | .sol_get_clock_sysvar                        => Sysvar.execClock s
  | .sol_get_rent_sysvar                         => Sysvar.execRent s
  | .sol_get_epoch_schedule_sysvar               => Sysvar.execEpochSchedule s
  | .sol_get_last_restart_slot                   => Sysvar.execLastRestartSlot s
  | .sol_get_fees_sysvar                         => Sysvar.execFees s
  | .sol_get_epoch_rewards_sysvar                => Sysvar.execEpochRewards s
  | .sol_get_sysvar                              => Misc.execGetSysvar s
  | .sol_get_epoch_stake                         => Sysvar.execEpochStake s
  -- Return data
  | .sol_set_return_data                         => ReturnData.execSet s
  | .sol_get_return_data                         => ReturnData.execGet s
  -- Abort / panic
  | .abort                                       => Abort.execAbort s
  | .sol_panic_                                  => Abort.execPanic s
  -- Misc
  | .sol_alloc_free_                             => Misc.execAllocFree s
  | .sol_remaining_compute_units                 => Misc.execRemainingComputeUnits s
  | .sol_get_stack_height                        => Misc.execGetStackHeight s
  | .sol_get_processed_sibling_instruction       => Misc.execProcessedSibling s
  | .unknown _                                   => Misc.execUnknown s

/-! ## Single-step semantics -/

/-- Execute one instruction, returning the new state. -/
@[simp] def step (insn : Insn) (s : State) : State :=
  let rf := s.regs
  let mem := s.mem
  let pc' := s.pc + 1
  match insn with

  | .lddw dst imm =>
    { s with regs := rf.set dst (toU64 imm), pc := pc' }

  | .ldx w dst src off =>
    let addr := effectiveAddr (rf.get src) off
    if s.regions.containsRange addr w.bytes then
      let val := readByWidth mem addr w
      { s with regs := rf.set dst val, pc := pc' }
    else
      { s with exitCode := some ERR_ACCESS_VIOLATION, vmError := some .accessViolation }

  | .st w dst off imm =>
    let addr := effectiveAddr (rf.get dst) off
    if s.regions.containsWritable addr w.bytes then
      let val := (toU64 imm) % (2 ^ (w.bytes * 8))
      { s with mem := writeByWidth mem addr val w, pc := pc' }
    else
      { s with exitCode := some ERR_ACCESS_VIOLATION, vmError := some .accessViolation }

  | .stx w dst off src =>
    let addr := effectiveAddr (rf.get dst) off
    if s.regions.containsWritable addr w.bytes then
      let val := rf.get src % (2 ^ (w.bytes * 8))
      { s with mem := writeByWidth mem addr val w, pc := pc' }
    else
      { s with exitCode := some ERR_ACCESS_VIOLATION, vmError := some .accessViolation }

  | .add64 dst src =>
    { s with regs := rf.set dst (wrapAdd (rf.get dst) (resolveSrc rf src)), pc := pc' }
  | .sub64 dst src =>
    { s with regs := rf.set dst (wrapSub (rf.get dst) (resolveSrc rf src)), pc := pc' }
  | .mul64 dst src =>
    { s with regs := rf.set dst (wrapMul (rf.get dst) (resolveSrc rf src)), pc := pc' }
  | .div64 dst src =>
    let b := resolveSrc rf src
    if b = 0 then { s with exitCode := some ERR_DIVIDE_BY_ZERO, vmError := some .divideByZero }
    else { s with regs := rf.set dst ((rf.get dst / b) % U64_MODULUS), pc := pc' }
  | .mod64 dst src =>
    let b := resolveSrc rf src
    if b = 0 then { s with exitCode := some ERR_DIVIDE_BY_ZERO, vmError := some .divideByZero }
    else { s with regs := rf.set dst (rf.get dst % b), pc := pc' }
  | .or64 dst src =>
    { s with regs := rf.set dst ((rf.get dst ||| resolveSrc rf src) % U64_MODULUS), pc := pc' }
  | .and64 dst src =>
    { s with regs := rf.set dst ((rf.get dst &&& resolveSrc rf src) % U64_MODULUS), pc := pc' }
  | .xor64 dst src =>
    { s with regs := rf.set dst ((rf.get dst ^^^ resolveSrc rf src) % U64_MODULUS), pc := pc' }
  | .lsh64 dst src =>
    let shift := resolveSrc rf src % 64
    { s with regs := rf.set dst ((rf.get dst <<< shift) % U64_MODULUS), pc := pc' }
  | .rsh64 dst src =>
    let shift := resolveSrc rf src % 64
    { s with regs := rf.set dst (rf.get dst >>> shift), pc := pc' }
  | .arsh64 dst src =>
    let shift := resolveSrc rf src % 64
    let a := rf.get dst
    let v := if a < U64_MODULUS / 2 then a >>> shift
      else let shifted := a >>> shift
           let highBits := (U64_MODULUS - 1) - (U64_MODULUS / (2 ^ shift) - 1)
           (shifted ||| highBits) % U64_MODULUS
    { s with regs := rf.set dst v, pc := pc' }
  | .mov64 dst src =>
    { s with regs := rf.set dst (resolveSrc rf src), pc := pc' }
  | .neg64 dst =>
    { s with regs := rf.set dst (wrapNeg (rf.get dst)), pc := pc' }

  -- 32-bit ALU: result zero-extended to 64 bits
  | .add32 dst src =>
    { s with regs := rf.set dst (wrapAdd32 (rf.get dst) (resolveSrc rf src)), pc := pc' }
  | .sub32 dst src =>
    { s with regs := rf.set dst (wrapSub32 (rf.get dst) (resolveSrc rf src)), pc := pc' }
  | .mul32 dst src =>
    { s with regs := rf.set dst (wrapMul32 (rf.get dst) (resolveSrc rf src)), pc := pc' }
  | .div32 dst src =>
    let b := resolveSrc rf src % U32_MODULUS
    if b = 0 then { s with exitCode := some ERR_DIVIDE_BY_ZERO, vmError := some .divideByZero }
    else { s with regs := rf.set dst ((rf.get dst % U32_MODULUS / b) % U32_MODULUS), pc := pc' }
  | .mod32 dst src =>
    let b := resolveSrc rf src % U32_MODULUS
    if b = 0 then { s with exitCode := some ERR_DIVIDE_BY_ZERO, vmError := some .divideByZero }
    else { s with regs := rf.set dst (rf.get dst % U32_MODULUS % b), pc := pc' }
  | .or32 dst src =>
    { s with regs := rf.set dst ((rf.get dst ||| resolveSrc rf src) % U32_MODULUS), pc := pc' }
  | .and32 dst src =>
    { s with regs := rf.set dst ((rf.get dst &&& resolveSrc rf src) % U32_MODULUS), pc := pc' }
  | .xor32 dst src =>
    { s with regs := rf.set dst ((rf.get dst ^^^ resolveSrc rf src) % U32_MODULUS), pc := pc' }
  | .lsh32 dst src =>
    let shift := resolveSrc rf src % 32
    { s with regs := rf.set dst ((rf.get dst <<< shift) % U32_MODULUS), pc := pc' }
  | .rsh32 dst src =>
    let shift := resolveSrc rf src % 32
    { s with regs := rf.set dst ((rf.get dst % U32_MODULUS) >>> shift), pc := pc' }
  | .arsh32 dst src =>
    let shift := resolveSrc rf src % 32
    let a := rf.get dst % U32_MODULUS
    let v := if a < U32_MODULUS / 2 then a >>> shift
      else let shifted := a >>> shift
           let highBits := (U32_MODULUS - 1) - (U32_MODULUS / (2 ^ shift) - 1)
           (shifted ||| highBits) % U32_MODULUS
    { s with regs := rf.set dst v, pc := pc' }
  | .mov32 dst src =>
    { s with regs := rf.set dst (resolveSrc rf src % U32_MODULUS), pc := pc' }
  | .neg32 dst =>
    { s with regs := rf.set dst (wrapNeg32 (rf.get dst)), pc := pc' }

  | .jeq dst src target =>
    { s with pc := if rf.get dst = resolveSrc rf src then target else pc' }
  | .jne dst src target =>
    { s with pc := if rf.get dst ≠ resolveSrc rf src then target else pc' }
  | .jgt dst src target =>
    { s with pc := if rf.get dst > resolveSrc rf src then target else pc' }
  | .jge dst src target =>
    { s with pc := if rf.get dst ≥ resolveSrc rf src then target else pc' }
  | .jlt dst src target =>
    { s with pc := if rf.get dst < resolveSrc rf src then target else pc' }
  | .jle dst src target =>
    { s with pc := if rf.get dst ≤ resolveSrc rf src then target else pc' }
  | .jsgt dst src target =>
    { s with pc := if toSigned64 (rf.get dst) > toSigned64 (resolveSrc rf src) then target else pc' }
  | .jsge dst src target =>
    { s with pc := if toSigned64 (rf.get dst) ≥ toSigned64 (resolveSrc rf src) then target else pc' }
  | .jslt dst src target =>
    { s with pc := if toSigned64 (rf.get dst) < toSigned64 (resolveSrc rf src) then target else pc' }
  | .jsle dst src target =>
    { s with pc := if toSigned64 (rf.get dst) ≤ toSigned64 (resolveSrc rf src) then target else pc' }
  | .jset dst src target =>
    { s with pc := if rf.get dst &&& resolveSrc rf src ≠ 0 then target else pc' }
  | .ja target =>
    { s with pc := target }

  | .call syscall =>
    let s' := execSyscall syscall s
    -- Agave charges `1 (baseline) + syscallCu`; the baseline 1 is already
    -- handled per-step, so bump `cuConsumed` by the full `syscallCu`.
    { s' with pc := pc'
              cuConsumed := s'.cuConsumed + syscallCu syscall s }

  | .call_local target =>
    -- Push a `CallFrame`, jump, bump r10 by one V0 frame. r10 bumps by
    -- `stack_frame_size = 0x1000` not 0x2000: agave under `FeatureSet::all_enabled()`
    -- (mollusk's config) leaves `enable_stack_frame_gaps` off, so effective
    -- num_frames is 1 despite V0 reporting `stack_frame_gaps() = true`.
    -- r6–r9 are snapshotted for `.exit` to restore (LLVM callee-saved). r10 uses
    -- direct record syntax (not `RegFile.set`) so the r10-write no-op lemma holds.
    -- Call-depth limit (H4): solana-sbpf aborts the 65th frame; fail closed at MAX_CALL_DEPTH.
    if s.callStack.length ≥ MAX_CALL_DEPTH then
      { s with exitCode := some ERR_CALL_DEPTH_EXCEEDED, vmError := some .callDepthExceeded }
    else
      let frame : CallFrame := {
        retPc := pc', savedR6 := rf.r6, savedR7 := rf.r7,
        savedR8 := rf.r8, savedR9 := rf.r9, savedR10 := rf.r10 }
      { s with pc := target
               regs := { rf with r10 := rf.r10 + 0x1000 }
               callStack := frame :: s.callStack }

  | .callx _reg =>
    -- Indirect call: V0's frame push + VA→PC translation + depth check aren't
    -- modeled (and the target-register field varies across SBPF versions). Fail
    -- closed rather than fabricate a bare jump that could prove a false exit code.
    -- See docs/SOUNDNESS_AUDIT_*.md (C2).
    { s with exitCode := some ERR_UNSUPPORTED_INSTRUCTION, vmError := some .unsupportedInstruction }

  | .exit =>
    match s.callStack with
    | frame :: rest =>
        { s with pc := frame.retPc
                 regs := { rf with
                           r6 := frame.savedR6, r7 := frame.savedR7,
                           r8 := frame.savedR8, r9 := frame.savedR9,
                           r10 := frame.savedR10 }
                 callStack := rest }
    | [] => { s with exitCode := some (rf.get .r0) }

/-! ## Multi-step execution -/

abbrev Program := Array Insn

/-- Charge one instruction's baseline compute unit. `cuConsumed` is the total CU
    meter (baseline 1/instruction + the syscall surcharge `step` adds), so the
    budget check sees the real agave-CU total. Only `cuConsumed` changes. -/
@[simp] def chargeCu (s : State) : State :=
  { s with cuConsumed := s.cuConsumed + 1 }

/-- Execute using a function-based instruction fetch (O(1) per step).

    Fails closed on compute-budget overrun (H5): if `cuConsumed` exceeds
    `cuBudget` before an instruction, halt with `exitCode = none` (wire
    `OutOfBudget`, matching agave's `ComputeBudgetExceeded`). Idempotent. -/
def executeFn (fetch : Nat → Option Insn) (s : State) (fuel : Nat) : State :=
  match fuel with
  | 0 => s
  | fuel' + 1 =>
    match s.exitCode with
    | some _ => s
    | none =>
      if s.cuConsumed > s.cuBudget then s
      else match fetch s.pc with
      | none => { s with exitCode := some ERR_INVALID_PC, vmError := some .invalidPc }
      | some insn => executeFn fetch (chargeCu (step insn s)) fuel'

/-- Initial machine state, r1 → input buffer. `regions` is the memory map;
    `.ldx`/`.st`/`.stx` check against it and trap `ERR_ACCESS_VIOLATION` on miss. -/
@[simp] def initState (inputAddr : Nat) (mem : Mem) (regions : RegionTable)
    (cuBudget : Nat := 200000) : State where
  regs := { r1 := inputAddr, r10 := STACK_START + 0x1000 }
  mem := mem
  regions := regions
  pc := 0
  cuBudget := cuBudget

/-- Two-pointer initial state for SIMD-0321 programs: r1 = input buffer,
    r2 = instruction data pointer. `entryPc` allows a non-zero entrypoint.
    `cuBudget` defaults to 200k (the tx default, matching `Runner.RunConfig`):
    runs are budget-metered (H5), so a default of 0 would halt after one step. -/
@[simp] def initState2 (inputAddr insnAddr : Nat) (mem : Mem) (regions : RegionTable)
    (entryPc : Nat := 0) (cuBudget : Nat := 200000) : State where
  regs := { r1 := inputAddr, r2 := insnAddr, r10 := STACK_START + 0x1000 }
  mem := mem
  regions := regions
  pc := entryPc
  cuBudget := cuBudget

/-! ## Execution unrolling lemmas -/

@[simp] theorem executeFn_halted (fetch : Nat → Option Insn) (s : State) (n : Nat) (code : Nat)
    (h : s.exitCode = some code) :
    executeFn fetch s n = s := by
  cases n with
  | zero => simp [executeFn]
  | succ n => simp [executeFn, h]

@[simp] theorem executeFn_zero (fetch : Nat → Option Insn) (s : State) :
    executeFn fetch s 0 = s := by
  simp [executeFn]

/-- An over-budget running state is a fixed point of `executeFn` (budget check
    halts for any fuel). Companion to `executeFn_halted` (`exitCode = some`). -/
theorem executeFn_overBudget (fetch : Nat → Option Insn) (s : State) (n : Nat)
    (h_run : s.exitCode = none) (h_over : s.cuConsumed > s.cuBudget) :
    executeFn fetch s n = s := by
  cases n with
  | zero => simp [executeFn]
  | succ n => simp [executeFn, h_run, if_pos h_over]

theorem executeFn_step (fetch : Nat → Option Insn) (s : State) (n : Nat) (insn : Insn)
    (h_running : s.exitCode = none)
    (h_budget : s.cuConsumed ≤ s.cuBudget)
    (h_fetch : fetch s.pc = some insn) :
    executeFn fetch s (n + 1) = executeFn fetch (chargeCu (step insn s)) n := by
  simp [executeFn, h_running, h_fetch, Nat.not_lt.mpr h_budget]

/-- Composability of deterministic execution: running n+m steps is the same as
    running n steps then running m steps from the resulting state. -/
theorem executeFn_compose (fetch : Nat → Option Insn) (s : State) (n m : Nat) :
    executeFn fetch s (n + m) = executeFn fetch (executeFn fetch s n) m := by
  induction n generalizing s with
  | zero => simp [executeFn]
  | succ n ih =>
    cases h_ec : s.exitCode with
    | some code =>
      -- halted: both sides stay at `s`
      rw [executeFn_halted fetch s (n + 1 + m) code h_ec,
          executeFn_halted fetch s (n + 1) code h_ec,
          executeFn_halted fetch s m code h_ec]
    | none =>
      by_cases h_over : s.cuConsumed > s.cuBudget
      · -- over budget: both sides collapse to `s` (fixed point)
        rw [executeFn_overBudget fetch s (n + 1 + m) h_ec h_over,
            executeFn_overBudget fetch s (n + 1) h_ec h_over,
            executeFn_overBudget fetch s m h_ec h_over]
      · -- in budget: peel one step, then induction
        have h_le : s.cuConsumed ≤ s.cuBudget := Nat.le_of_not_lt h_over
        cases h_f : fetch s.pc with
        | none =>
          -- invalid PC: first step sets exitCode, then both sides stay halted
          have hbad : ∀ k, executeFn fetch s (k + 1) = { s with exitCode := some ERR_INVALID_PC, vmError := some .invalidPc } := by
            intro k; simp [executeFn, h_ec, h_f, Nat.not_lt.mpr h_le]
          rw [show n + 1 + m = (n + m) + 1 from by omega, hbad (n + m), hbad n,
              executeFn_halted fetch _ m ERR_INVALID_PC rfl]
        | some insn =>
          rw [show n + 1 + m = (n + m) + 1 from by omega,
              executeFn_step fetch s (n + m) insn h_ec h_le h_f,
              executeFn_step fetch s n insn h_ec h_le h_f]
          exact ih (chargeCu (step insn s))

/-! ## Frame pointer (r10) — user-write invariance

`RegFile.set .r10 v = rf` is a no-op (see `RegFile.set_r10`), and user ALU/load
arms all route through `RegFile.set`, so r10 is constant under user code. The
runtime updates r10 via direct record syntax (`.call_local` +0x1000, `.exit`
restores), bypassing `RegFile.set`, so the no-op lemma is untouched. -/

@[simp] theorem execSyscall_preserves_r10 (sc : Syscall) (s : State) :
    (execSyscall sc s).regs.r10 = s.regs.r10 := by
  -- No syscall writes r10. `simp` unfolds bodies; `repeat' split` breaks
  -- residual `if`/`match` guards (validate's curve-id ifs, Pda/Poseidon Option).
  cases sc <;> simp [execSyscall, commitOptional] <;> (repeat' split) <;>
    (first | rfl | simp)

/-- Whether an instruction is `.call_local` — the only `step` arm that pushes
    onto `callStack` (`.exit` pops, but the run starts `callStack = []` and only
    grows via `.call_local`). Used by the conditional r10 lemmas below. -/
def Insn.isCallLocal : Insn → Bool
  | .call_local _ => true
  | _             => false

/-- `execTryFind` preserves `callStack` in both arms. Companion to
    `execTryFind_preserves_regions` at `Pda.lean:193`. -/
@[simp] theorem execTryFind_preserves_callStack (s : State) :
    (Pda.execTryFind s).callStack = s.callStack := by
  simp only [Pda.execTryFind]
  refine State.guardRead_proj_eq_of_k (·.callStack) s _ _ _ rfl ?_
  refine State.guardRead_proj_eq_of_k (·.callStack) s _ _ _ rfl ?_
  refine State.guardSlices_proj_eq_of_k (·.callStack) s _ _ _ rfl ?_
  split
  · refine State.guardWrite_proj_eq_of_k (·.callStack) s _ _ _ rfl ?_
    refine State.guardWrite_proj_eq_of_k (·.callStack) s _ _ _ rfl ?_
    rfl
  · rfl

/-- `execSyscall` never modifies `callStack` (CPI-stub `Cpi.exec` sets `r0 := 0`;
    other syscalls touch only `regs`/`mem`/`log`/`returnData`). -/
@[simp] theorem execSyscall_preserves_callStack (sc : Syscall) (s : State) :
    (execSyscall sc s).callStack = s.callStack := by
  cases sc <;> simp [execSyscall, commitOptional] <;> (repeat' split) <;>
    (first | rfl | simp)

/-! ## Conditional r10 frame lemmas (#32 item 4)

Blanket r10 preservation is FALSE: `.call_local` bumps r10, `.exit` restores it.
The honest form is conditional on no `.call_local` being fetched in the window —
then with an empty stack `.exit` halts (no pop), `.callx` pushes nothing, and
every other arm routes through `RegFile.set` (r10 no-op) or a syscall
(`execSyscall_preserves_r10`). Upstream replacements for the four blanket lemmas
in qedgen's vendored copy. -/

/-- One step preserves r10 when the instruction is not `.call_local`
    and the call stack is empty. -/
theorem step_preserves_r10_of_no_push (insn : Insn) (s : State)
    (h_nf : insn.isCallLocal = false) (h_cs : s.callStack = []) :
    (step insn s).regs.r10 = s.regs.r10 := by
  cases insn <;>
    first
    | (simp [Insn.isCallLocal] at h_nf; done)
    | (simp only [step] <;> simp [h_cs, -RegFile.set]; done)
    | (simp only [step] <;> split <;> simp [h_cs, -RegFile.set]; done)
    | (simp only [step];
       first
       | exact execSyscall_preserves_r10 _ _
       | (show (execSyscall _ s).callStack = ([] : List CallFrame);
          rw [execSyscall_preserves_callStack]; exact h_cs))

/-- One step keeps the call stack empty when the instruction is not
    `.call_local` (nothing else pushes; `.exit` on an empty stack
    halts). -/
theorem step_preserves_callStack_of_no_push (insn : Insn) (s : State)
    (h_nf : insn.isCallLocal = false) (h_cs : s.callStack = []) :
    (step insn s).callStack = [] := by
  cases insn <;>
    first
    | (simp [Insn.isCallLocal] at h_nf; done)
    | (simp only [step] <;> simp [h_cs, -RegFile.set]; done)
    | (simp only [step] <;> split <;> simp [h_cs, -RegFile.set]; done)
    | (simp only [step];
       first
       | exact execSyscall_preserves_r10 _ _
       | (show (execSyscall _ s).callStack = ([] : List CallFrame);
          rw [execSyscall_preserves_callStack]; exact h_cs))

/-- r10 and the empty call stack are preserved across any fuel window
    in which the fetch function never yields a `.call_local`. -/
theorem executeFn_preserves_r10_of_no_push
    (fetch : Nat → Option Insn) (s : State) (fuel : Nat)
    (h_nf : ∀ a i, fetch a = some i → i.isCallLocal = false)
    (h_cs : s.callStack = []) :
    (executeFn fetch s fuel).regs.r10 = s.regs.r10 ∧
      (executeFn fetch s fuel).callStack = [] := by
  induction fuel generalizing s with
  | zero => exact ⟨rfl, h_cs⟩
  | succ n ih =>
    unfold executeFn
    cases h : s.exitCode with
    | some _ => exact ⟨rfl, h_cs⟩
    | none =>
      by_cases h_over : s.cuConsumed > s.cuBudget
      · rw [if_pos h_over]; exact ⟨rfl, h_cs⟩
      · rw [if_neg h_over]
        cases hf : fetch s.pc with
        | none => exact ⟨rfl, h_cs⟩
        | some insn =>
          have h_insn := h_nf _ _ hf
          have h_cs' := step_preserves_callStack_of_no_push insn s h_insn h_cs
          obtain ⟨h1, h2⟩ := ih (chargeCu (step insn s)) (by simpa using h_cs')
          exact ⟨h1.trans (by simpa using step_preserves_r10_of_no_push insn s h_insn h_cs), h2⟩

/-- From `initState`, r10 stays at the frame top for the whole run
    when no `.call_local` is ever fetched. -/
theorem executeFn_r10_initState
    (fetch : Nat → Option Insn) (inputAddr : Nat) (mem : Mem)
    (regions : RegionTable) (fuel : Nat)
    (h_nf : ∀ a i, fetch a = some i → i.isCallLocal = false) :
    (executeFn fetch (initState inputAddr mem regions) fuel).regs.r10
      = STACK_START + 0x1000 :=
  (executeFn_preserves_r10_of_no_push fetch _ fuel h_nf rfl).1

/-- `initState2` variant of `executeFn_r10_initState`. -/
theorem executeFn_r10_initState2
    (fetch : Nat → Option Insn) (inputAddr insnAddr : Nat) (mem : Mem)
    (regions : RegionTable) (entryPc fuel : Nat)
    (h_nf : ∀ a i, fetch a = some i → i.isCallLocal = false) :
    (executeFn fetch (initState2 inputAddr insnAddr mem regions entryPc) fuel).regs.r10
      = STACK_START + 0x1000 :=
  (executeFn_preserves_r10_of_no_push fetch _ fuel h_nf rfl).1

/-! ## Region table — execution invariant

`step` never mutates `s.regions`; multi-step pattern proofs need this to carry a
bounds obligation into the new state. Syscall bodies and ALU/jump arms are pure
record-updates not mentioning `regions`; the branchy arms (`ldx`/`st`/`stx`/`div*`/`mod*`/`exit`)
need a `split` or match-case to surface the record-update. -/

@[simp] theorem execSyscall_preserves_regions (sc : Syscall) (s : State) :
    (execSyscall sc s).regions = s.regions := by
  cases sc <;> simp [execSyscall, commitOptional] <;> (repeat' split) <;>
    (first | rfl | simp)

@[simp] theorem step_preserves_regions (insn : Insn) (s : State) :
    (step insn s).regions = s.regions := by
  cases insn <;>
    first
    | rfl
    | (simp only [step]; rfl)
    | (simp only [step]; split <;> rfl)
    | (simp only [step]; cases s.callStack <;> rfl)
    | (simp only [step]; exact execSyscall_preserves_regions _ _)

@[simp] theorem executeFn_preserves_regions
    (fetch : Nat → Option Insn) (s : State) (fuel : Nat) :
    (executeFn fetch s fuel).regions = s.regions := by
  induction fuel generalizing s with
  | zero => rfl
  | succ n ih =>
    unfold executeFn
    cases h : s.exitCode with
    | some _ => rfl
    | none =>
      by_cases h_over : s.cuConsumed > s.cuBudget
      · rw [if_pos h_over]
      · rw [if_neg h_over]
        cases hf : fetch s.pc with
        | none => rfl
        | some insn => rw [ih (chargeCu (step insn s))]; simpa using step_preserves_regions insn s

/-! ## cuBudget invariance (H5)

`cuBudget` is set once at state creation and never mutated by `step`, any syscall,
or `chargeCu` (bumps only `cuConsumed`). This is why the budget side-condition in
`cuTripleWithin` survives sequential composition: intermediate budget = initial. -/

/-- `execTryFind` preserves `cuBudget` in both arms. Companion to
    `execTryFind_preserves_regions`/`_callStack`; `simp` needs it at the PDA leaf. -/
@[simp] theorem execTryFind_preserves_cuBudget (s : State) :
    (Pda.execTryFind s).cuBudget = s.cuBudget := by
  simp only [Pda.execTryFind]
  refine State.guardRead_proj_eq_of_k (·.cuBudget) s _ _ _ rfl ?_
  refine State.guardRead_proj_eq_of_k (·.cuBudget) s _ _ _ rfl ?_
  refine State.guardSlices_proj_eq_of_k (·.cuBudget) s _ _ _ rfl ?_
  split
  · refine State.guardWrite_proj_eq_of_k (·.cuBudget) s _ _ _ rfl ?_
    refine State.guardWrite_proj_eq_of_k (·.cuBudget) s _ _ _ rfl ?_
    rfl
  · rfl

@[simp] theorem execSyscall_preserves_cuBudget (sc : Syscall) (s : State) :
    (execSyscall sc s).cuBudget = s.cuBudget := by
  cases sc <;> simp [execSyscall, commitOptional] <;> (repeat' split) <;>
    (first | rfl | simp)

@[simp] theorem step_preserves_cuBudget (insn : Insn) (s : State) :
    (step insn s).cuBudget = s.cuBudget := by
  cases insn <;>
    first
    | rfl
    | (simp only [step]; rfl)
    | (simp only [step]; split <;> rfl)
    | (simp only [step]; cases s.callStack <;> rfl)
    | (simp only [step]; exact execSyscall_preserves_cuBudget _ _)

@[simp] theorem executeFn_preserves_cuBudget
    (fetch : Nat → Option Insn) (s : State) (fuel : Nat) :
    (executeFn fetch s fuel).cuBudget = s.cuBudget := by
  induction fuel generalizing s with
  | zero => rfl
  | succ n ih =>
    unfold executeFn
    cases h : s.exitCode with
    | some _ => rfl
    | none =>
      by_cases h_over : s.cuConsumed > s.cuBudget
      · rw [if_pos h_over]
      · rw [if_neg h_over]
        cases hf : fetch s.pc with
        | none => rfl
        | some insn =>
          rw [ih (chargeCu (step insn s))]
          simpa using step_preserves_cuBudget insn s

/-! ## Paired execution (for tactic automation)

`execInsn`/`execSegment` mirror `step`/`executeFn` but return `PUnit × State`.
The pairing lets `wp_exec` unfold one instruction at a time via `dsimp` at O(1)
kernel depth, avoiding the blowup of unfolding `executeFn` directly. -/

/-- A paired state transition `s ↦ ((), newState)`; the `PUnit` tag lets `dsimp`
    reduce one instruction without unfolding the full recursion. -/
abbrev Step := State → PUnit × State

/-- Single-step paired transition: mirrors `step`, returns `PUnit × State`. -/
@[simp] def execInsn (insn : Insn) : Step := fun s =>
  let rf := s.regs
  let mem := s.mem
  let pc' := s.pc + 1
  match insn with

  | .lddw dst imm =>
    ((), { s with regs := rf.set dst (toU64 imm), pc := pc' })

  | .ldx w dst src off =>
    let addr := effectiveAddr (rf.get src) off
    if s.regions.containsRange addr w.bytes then
      let val := readByWidth mem addr w
      ((), { s with regs := rf.set dst val, pc := pc' })
    else
      ((), { s with exitCode := some ERR_ACCESS_VIOLATION, vmError := some .accessViolation })

  | .st w dst off imm =>
    let addr := effectiveAddr (rf.get dst) off
    if s.regions.containsWritable addr w.bytes then
      let val := (toU64 imm) % (2 ^ (w.bytes * 8))
      ((), { s with mem := writeByWidth mem addr val w, pc := pc' })
    else
      ((), { s with exitCode := some ERR_ACCESS_VIOLATION, vmError := some .accessViolation })

  | .stx w dst off src =>
    let addr := effectiveAddr (rf.get dst) off
    if s.regions.containsWritable addr w.bytes then
      let val := rf.get src % (2 ^ (w.bytes * 8))
      ((), { s with mem := writeByWidth mem addr val w, pc := pc' })
    else
      ((), { s with exitCode := some ERR_ACCESS_VIOLATION, vmError := some .accessViolation })

  | .add64 dst src =>
    ((), { s with regs := rf.set dst (wrapAdd (rf.get dst) (resolveSrc rf src)), pc := pc' })
  | .sub64 dst src =>
    ((), { s with regs := rf.set dst (wrapSub (rf.get dst) (resolveSrc rf src)), pc := pc' })
  | .mul64 dst src =>
    ((), { s with regs := rf.set dst (wrapMul (rf.get dst) (resolveSrc rf src)), pc := pc' })
  | .div64 dst src =>
    let b := resolveSrc rf src
    if b = 0 then ((), { s with exitCode := some ERR_DIVIDE_BY_ZERO, vmError := some .divideByZero })
    else ((), { s with regs := rf.set dst ((rf.get dst / b) % U64_MODULUS), pc := pc' })
  | .mod64 dst src =>
    let b := resolveSrc rf src
    if b = 0 then ((), { s with exitCode := some ERR_DIVIDE_BY_ZERO, vmError := some .divideByZero })
    else ((), { s with regs := rf.set dst (rf.get dst % b), pc := pc' })
  | .or64 dst src =>
    ((), { s with regs := rf.set dst ((rf.get dst ||| resolveSrc rf src) % U64_MODULUS), pc := pc' })
  | .and64 dst src =>
    ((), { s with regs := rf.set dst ((rf.get dst &&& resolveSrc rf src) % U64_MODULUS), pc := pc' })
  | .xor64 dst src =>
    ((), { s with regs := rf.set dst ((rf.get dst ^^^ resolveSrc rf src) % U64_MODULUS), pc := pc' })
  | .lsh64 dst src =>
    let shift := resolveSrc rf src % 64
    ((), { s with regs := rf.set dst ((rf.get dst <<< shift) % U64_MODULUS), pc := pc' })
  | .rsh64 dst src =>
    let shift := resolveSrc rf src % 64
    ((), { s with regs := rf.set dst (rf.get dst >>> shift), pc := pc' })
  | .arsh64 dst src =>
    let shift := resolveSrc rf src % 64
    let a := rf.get dst
    let v := if a < U64_MODULUS / 2 then a >>> shift
      else let shifted := a >>> shift
           let highBits := (U64_MODULUS - 1) - (U64_MODULUS / (2 ^ shift) - 1)
           (shifted ||| highBits) % U64_MODULUS
    ((), { s with regs := rf.set dst v, pc := pc' })
  | .mov64 dst src =>
    ((), { s with regs := rf.set dst (resolveSrc rf src), pc := pc' })
  | .neg64 dst =>
    ((), { s with regs := rf.set dst (wrapNeg (rf.get dst)), pc := pc' })

  -- 32-bit ALU
  | .add32 dst src =>
    ((), { s with regs := rf.set dst (wrapAdd32 (rf.get dst) (resolveSrc rf src)), pc := pc' })
  | .sub32 dst src =>
    ((), { s with regs := rf.set dst (wrapSub32 (rf.get dst) (resolveSrc rf src)), pc := pc' })
  | .mul32 dst src =>
    ((), { s with regs := rf.set dst (wrapMul32 (rf.get dst) (resolveSrc rf src)), pc := pc' })
  | .div32 dst src =>
    let b := resolveSrc rf src % U32_MODULUS
    if b = 0 then ((), { s with exitCode := some ERR_DIVIDE_BY_ZERO, vmError := some .divideByZero })
    else ((), { s with regs := rf.set dst ((rf.get dst % U32_MODULUS / b) % U32_MODULUS), pc := pc' })
  | .mod32 dst src =>
    let b := resolveSrc rf src % U32_MODULUS
    if b = 0 then ((), { s with exitCode := some ERR_DIVIDE_BY_ZERO, vmError := some .divideByZero })
    else ((), { s with regs := rf.set dst (rf.get dst % U32_MODULUS % b), pc := pc' })
  | .or32 dst src =>
    ((), { s with regs := rf.set dst ((rf.get dst ||| resolveSrc rf src) % U32_MODULUS), pc := pc' })
  | .and32 dst src =>
    ((), { s with regs := rf.set dst ((rf.get dst &&& resolveSrc rf src) % U32_MODULUS), pc := pc' })
  | .xor32 dst src =>
    ((), { s with regs := rf.set dst ((rf.get dst ^^^ resolveSrc rf src) % U32_MODULUS), pc := pc' })
  | .lsh32 dst src =>
    let shift := resolveSrc rf src % 32
    ((), { s with regs := rf.set dst ((rf.get dst <<< shift) % U32_MODULUS), pc := pc' })
  | .rsh32 dst src =>
    let shift := resolveSrc rf src % 32
    ((), { s with regs := rf.set dst ((rf.get dst % U32_MODULUS) >>> shift), pc := pc' })
  | .arsh32 dst src =>
    let shift := resolveSrc rf src % 32
    let a := rf.get dst % U32_MODULUS
    let v := if a < U32_MODULUS / 2 then a >>> shift
      else let shifted := a >>> shift
           let highBits := (U32_MODULUS - 1) - (U32_MODULUS / (2 ^ shift) - 1)
           (shifted ||| highBits) % U32_MODULUS
    ((), { s with regs := rf.set dst v, pc := pc' })
  | .mov32 dst src =>
    ((), { s with regs := rf.set dst (resolveSrc rf src % U32_MODULUS), pc := pc' })
  | .neg32 dst =>
    ((), { s with regs := rf.set dst (wrapNeg32 (rf.get dst)), pc := pc' })

  -- Conditional jumps
  | .jeq dst src target =>
    ((), { s with pc := if rf.get dst = resolveSrc rf src then target else pc' })
  | .jne dst src target =>
    ((), { s with pc := if rf.get dst ≠ resolveSrc rf src then target else pc' })
  | .jgt dst src target =>
    ((), { s with pc := if rf.get dst > resolveSrc rf src then target else pc' })
  | .jge dst src target =>
    ((), { s with pc := if rf.get dst ≥ resolveSrc rf src then target else pc' })
  | .jlt dst src target =>
    ((), { s with pc := if rf.get dst < resolveSrc rf src then target else pc' })
  | .jle dst src target =>
    ((), { s with pc := if rf.get dst ≤ resolveSrc rf src then target else pc' })
  | .jsgt dst src target =>
    ((), { s with pc := if toSigned64 (rf.get dst) > toSigned64 (resolveSrc rf src) then target else pc' })
  | .jsge dst src target =>
    ((), { s with pc := if toSigned64 (rf.get dst) ≥ toSigned64 (resolveSrc rf src) then target else pc' })
  | .jslt dst src target =>
    ((), { s with pc := if toSigned64 (rf.get dst) < toSigned64 (resolveSrc rf src) then target else pc' })
  | .jsle dst src target =>
    ((), { s with pc := if toSigned64 (rf.get dst) ≤ toSigned64 (resolveSrc rf src) then target else pc' })
  | .jset dst src target =>
    ((), { s with pc := if rf.get dst &&& resolveSrc rf src ≠ 0 then target else pc' })
  | .ja target =>
    ((), { s with pc := target })

  -- Syscall — see step's `.call` arm for the cuConsumed accounting.
  | .call syscall =>
    let s' := execSyscall syscall s
    ((), { s' with pc := pc'
                   cuConsumed := s'.cuConsumed + syscallCu syscall s })

  -- Internal call — see step's `.call_local` arm.
  | .call_local target =>
    -- Call-depth limit (H4) — mirror of step's `.call_local` guard.
    if s.callStack.length ≥ MAX_CALL_DEPTH then
      ((), { s with exitCode := some ERR_CALL_DEPTH_EXCEEDED, vmError := some .callDepthExceeded })
    else
      let frame : CallFrame := {
        retPc := pc', savedR6 := rf.r6, savedR7 := rf.r7,
        savedR8 := rf.r8, savedR9 := rf.r9, savedR10 := rf.r10 }
      ((), { s with pc := target
                    regs := { rf with r10 := rf.r10 + 0x1000 }
                    callStack := frame :: s.callStack })

  -- Indirect call — see step's `.callx` arm (fail closed, C2).
  | .callx _reg =>
    ((), { s with exitCode := some ERR_UNSUPPORTED_INSTRUCTION, vmError := some .unsupportedInstruction })

  -- Exit
  | .exit =>
    match s.callStack with
    | frame :: rest =>
        ((), { s with pc := frame.retPc
                      regs := { rf with
                                r6 := frame.savedR6, r7 := frame.savedR7,
                                r8 := frame.savedR8, r9 := frame.savedR9,
                                r10 := frame.savedR10 }
                      callStack := rest })
    | [] => ((), { s with exitCode := some (rf.get .r0) })

/-- execInsn produces the same state as step (just wrapped in a PUnit pair). -/
theorem step_eq_execInsn (insn : Insn) (s : State) :
    step insn s = (execInsn insn s).2 := by
  cases insn <;> simp only [step, execInsn] <;> split <;> rfl

/-- Multi-step paired execution using function-based fetch. -/
def execSegment (fetch : Nat → Option Insn) : Nat → Step
  | 0 => fun s => ((), s)
  | fuel + 1 => fun s =>
    match s.exitCode with
    | some _ => ((), s)
    | none =>
      if s.cuConsumed > s.cuBudget then ((), s)
      else match fetch s.pc with
      | none => ((), { s with exitCode := some ERR_INVALID_PC, vmError := some .invalidPc })
      | some insn =>
        let (_, s') := execInsn insn s
        execSegment fetch fuel (chargeCu s')

/-- executeFn and execSegment produce the same final state. -/
theorem executeFn_eq_execSegment (fetch : Nat → Option Insn) (s : State) (fuel : Nat) :
    executeFn fetch s fuel = (execSegment fetch fuel s).2 := by
  induction fuel generalizing s with
  | zero => rfl
  | succ n ih =>
    unfold executeFn execSegment
    cases h_exit : s.exitCode with
    | some _ => rfl
    | none =>
      by_cases h_over : s.cuConsumed > s.cuBudget
      · simp only [if_pos h_over]
      · simp only [if_neg h_over]
        cases h_fetch : fetch s.pc with
        | none => rfl
        | some insn =>
          simp (config := { failIfUnchanged := false }) only []
          have heq : step insn s = (execInsn insn s).2 := step_eq_execInsn insn s
          rw [heq]
          exact ih (chargeCu (execInsn insn s).2)

end SVM.SBPF
