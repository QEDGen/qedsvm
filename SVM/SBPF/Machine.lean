-- Machine state for sBPF execution: registers, call frames, State, runtime
-- error codes, wrapping arithmetic. Lifted out of Execute.lean so syscall-body
-- modules can spell `def exec : State → State` without an import cycle.

import SVM.SBPF.ISA
import SVM.SBPF.Memory

namespace SVM.SBPF

open Memory

/-! ## Register file as a concrete structure

Named fields (not `Reg → Nat`) keep projections simp-reducible, avoiding the
nested if-then-else chains that time out in proofs. -/

structure RegFile where
  r0 : Nat := 0
  r1 : Nat := 0
  r2 : Nat := 0
  r3 : Nat := 0
  r4 : Nat := 0
  r5 : Nat := 0
  r6 : Nat := 0
  r7 : Nat := 0
  r8 : Nat := 0
  r9 : Nat := 0
  r10 : Nat := 0
  deriving Repr, Inhabited, DecidableEq, BEq

@[simp] def RegFile.get (rf : RegFile) : Reg → Nat
  | .r0 => rf.r0 | .r1 => rf.r1 | .r2 => rf.r2 | .r3 => rf.r3
  | .r4 => rf.r4 | .r5 => rf.r5 | .r6 => rf.r6 | .r7 => rf.r7
  | .r8 => rf.r8 | .r9 => rf.r9 | .r10 => rf.r10

/-- Set a register value (r10 is read-only: writes are silently ignored) -/
@[simp] def RegFile.set (rf : RegFile) (r : Reg) (v : Nat) : RegFile :=
  match r with
  | .r0 => { rf with r0 := v } | .r1 => { rf with r1 := v }
  | .r2 => { rf with r2 := v } | .r3 => { rf with r3 := v }
  | .r4 => { rf with r4 := v } | .r5 => { rf with r5 := v }
  | .r6 => { rf with r6 := v } | .r7 => { rf with r7 := v }
  | .r8 => { rf with r8 := v } | .r9 => { rf with r9 := v }
  | .r10 => rf

/-- Writing to r10 is a no-op (frame pointer is read-only). -/
@[simp] theorem RegFile.set_r10 (rf : RegFile) (v : Nat) :
    rf.set .r10 v = rf := rfl

/-- Any register write preserves the r10 field (frame pointer is read-only). -/
@[simp] theorem RegFile.set_preserves_r10 (rf : RegFile) (r : Reg) (v : Nat) :
    (rf.set r v).r10 = rf.r10 := by
  cases r <;> rfl

/-- Reading the just-written register returns the written value (r0-r9 only). -/
theorem RegFile.get_set_self (rf : RegFile) (r : Reg) (v : Nat) (h : r ≠ .r10) :
    (rf.set r v).get r = v := by
  cases r <;> simp_all [RegFile.get, RegFile.set]

/-- Reading a different register from the one written returns the original value. -/
theorem RegFile.get_set_diff (rf : RegFile) (rA rB : Reg) (v : Nat) (h : rA ≠ rB) :
    (rf.set rB v).get rA = rf.get rA := by
  cases rA <;> cases rB <;> simp_all [RegFile.get, RegFile.set]

/-! ## Machine state -/

/-- One internal call/return stack entry. Pushed by `.call_local`, popped by
    `.exit`; mirrors agave's `CallFrame`. Saves return PC, r10, and r6–r9 —
    r6–r9 are callee-saved in LLVM, so without restoring them on exit
    LLVM-emitted iterators get their loop pointer clobbered by sub-calls. -/
structure CallFrame where
  retPc : Nat
  savedR6 : Nat
  savedR7 : Nat
  savedR8 : Nat
  savedR9 : Nat
  savedR10 : Nat
  deriving Inhabited, Repr

/-- Typed VM-fault channel (audit L1). `ERR_*` sentinels live in `exitCode`,
    where a clean `exit` of the sentinel VALUE is indistinguishable from a
    fault (`sentinel_exit.so`: agave reports `UnknownError(InvalidError)` for
    the clean exit, distinct on chain). So the model carries the fault as a
    TYPED value here, set by every abort site alongside the sentinel; a clean
    `exit` never sets it. `exitCode` is unchanged (specs hold verbatim);
    `vmError` is authoritative for fault-vs-exit and feeds the M14 mapping. -/
inductive VmError
  | divideByZero
  | invalidPc
  | abort
  | accessViolation
  | unsupportedInstruction
  | callDepthExceeded
  | returnDataTooLarge
  | invalidLength
  | invalidAttribute
  | badSeeds
  | readonlyModified
  | invalidRealloc
  deriving Repr, DecidableEq, Inhabited

/-- sBPF machine state -/
structure State where
  regs : RegFile
  mem : Mem
  /-- Mapped regions. Accesses outside trap to `ERR_ACCESS_VIOLATION`;
      total `mem` is preserved underneath as a parallel bounds layer. -/
  regions : Memory.RegionTable
  /-- Index into the instruction array. -/
  pc : Nat
  /-- None if running, Some n if exited with code n. -/
  exitCode : Option Nat := none
  /-- Typed fault channel (L1): `some e` iff halted on a VM fault; a clean
      `exit` leaves it `none` even when r0 equals a sentinel. Set ALONGSIDE
      the `exitCode` sentinel (unchanged), so `exitCode` specs still hold. -/
  vmError : Option VmError := none
  /-- `sol_log_*` messages (one entry each). Observable from the runner;
      not owned by any SL assertion. -/
  log : Array ByteArray := #[]
  /-- Return-data buffer (`sol_set_return_data` / `sol_get_return_data`). -/
  returnData : ByteArray := ByteArray.empty
  /-- 32-byte program id that last called `sol_set_return_data`.
      Transaction-wide alongside `returnData` (agave inits the pair to
      `(Pubkey::default(), [])`, hence the 32-zero default), inherited/committed
      across CPI like `returnData`. Read out by `sol_get_return_data` (H7). -/
  returnDataProgId : ByteArray := ⟨Array.replicate 32 0⟩
  /-- Internal call/return stack. `.call_local` pushes a `CallFrame` (return PC,
      r10, r6–r9) then bumps `r10` by one V0 frame (0x1000 — `all_enabled` sets
      `enable_stack_frame_gaps = false`, num_frames = 1); `.exit` pops it
      (restoring all six fields) or terminates. Mirrors solana-sbpf V0. -/
  callStack : List CallFrame := []
  /-- Extra CU beyond the per-step "1 fuel per instruction" baseline, bumped by
      `.call syscall` per `syscallCu`. `SVM/Ffi.lean` reports
      `(cuBudget - fuelRemaining) + s.cuConsumed`. -/
  cuConsumed : Nat := 0
  /-- Total transaction CU budget (from `Runner.RunConfig` at `initState`).
      `sol_log_compute_units_` reports `cuBudget - cuConsumed` (saturating).
      `0` = unset/uncapped (still emits a `0 units remaining` message,
      matching agave on budget exhaustion). -/
  cuBudget : Nat := 0
  /-- Bump-allocator pointer for `sol_alloc_free_` (Tier-2 #6, program-local
      heap). Starts at `MM_HEAP_START`, grows upward; reset per CPI sub-state
      since agave allocates the heap fresh per invocation. -/
  heapNext : Nat := 0x300000000
  /-- 32-byte program-id currently executing. Used by `sol_invoke_signed{,_c}`
      to derive PDAs (hashes seeds ++ programId ++ "ProgramDerivedAddress").
      Set from `RunConfig.progIdBytes`, reset to the callee's id per CPI
      sub-state. Empty fails PDA derivation closed (safe default). -/
  progIdBytes : ByteArray := ByteArray.empty
  /-- Caller's RUNTIME-SET account privileges `(key, is_signer, is_writable)`,
      parsed from input at creation, immutable after. A program can overwrite
      the privilege byte in its own AccountInfo memory, but a CPI may only pass
      privileges the caller actually holds — so the runner clamps CPI privileges
      against this rather than the program-supplied bytes. Empty clamps every
      CPI signer/writable off unless PDA-derived. C5. -/
  origPrivs : List (ByteArray × Bool × Bool) := []
  /-- CPI invocation depth: 0 at top level, `caller + 1` per callee (set in
      `executeFnCpiWithFuel`). agave caps stack height at 5 (≤4 nested CPIs);
      CPI dispatch fails closed past that (M6). -/
  invokeDepth : Nat := 0
  deriving Inhabited

def State.running (s : State) : Prop := s.exitCode = none

/-! ## Helpers -/

/-- Resolve a source operand to its unsigned 64-bit value. -/
@[simp] def resolveSrc (rf : RegFile) (src : Src) : Nat :=
  match src with
  | .reg r => rf.get r
  | .imm v => toU64 v

/-! ## Runtime error codes

Used on unrecoverable errors (not an `exit`). Must be non-zero to distinguish
from success. -/

def ERR_DIVIDE_BY_ZERO : Nat := 0xFFFFFFFFFFFFFFFE
def ERR_INVALID_PC     : Nat := 0xFFFFFFFFFFFFFFFF
/-- `abort` / `sol_panic_`. Agave maps these to `ProgramFailedToComplete`;
    distinct non-zero code so callers can tell aborts from clean exits. -/
def ERR_ABORT          : Nat := 0xFFFFFFFFFFFFFFFD
/-- Out-of-region access (agave `EbpfError::AccessViolation`). Sentinel the
    harness maps to a `Failure` outcome. -/
def ERR_ACCESS_VIOLATION : Nat := 0xFFFFFFFFFFFFFFFC
/-- An instruction the model won't faithfully execute, so it refuses rather than
    fabricate a result (agave `UnsupportedInstruction` / unregistered syscall).
    Used by `.callx`, the proof-side CPI stub, unknown syscalls. Failing closed
    avoids proving an exit code false of the real VM on these paths. -/
def ERR_UNSUPPORTED_INSTRUCTION : Nat := 0xFFFFFFFFFFFFFFFA
/-- Call-depth limit exceeded (agave `CallDepthExceeded` at the 65th frame). -/
def ERR_CALL_DEPTH_EXCEEDED : Nat := 0xFFFFFFFFFFFFFFF9

/-- Max sBPF call depth (`MAX_CALL_DEPTH`); the 65th nested call aborts. -/
def MAX_CALL_DEPTH : Nat := 64

/-- `sol_set_return_data` with `len > MAX_RETURN_DATA` (agave `ReturnDataTooLarge`). -/
def ERR_RETURN_DATA_TOO_LARGE : Nat := 0xFFFFFFFFFFFFFFF8

/-- Over-length syscall input agave rejects (`InvalidLength`): `sol_big_mod_exp`
    >512 bytes, `sol_curve_multiscalar_mul` >512 points, etc. -/
def ERR_INVALID_LENGTH : Nat := 0xFFFFFFFFFFFFFFF7

/-- `SyscallError::InvalidAttribute`: unsupported curve id to a curve25519
    syscall under `abort_on_invalid_curve` (active under `all_enabled`). -/
def ERR_INVALID_ATTRIBUTE : Nat := 0xFFFFFFFFFFFFFFF6

/-- `SyscallError::BadSeeds`: PDA derivation with >`MAX_SEEDS` (16) seeds or a
    seed >32 bytes. Agave aborts rather than returning in-band. -/
def ERR_BAD_SEEDS : Nat := 0xFFFFFFFFFFFFFFF5

/-- CPI callee modified a read-only account's data/lamports/owner. Agave verifies
    every account after the sub-instruction, fails it
    (`ReadonlyDataModified`/...), and rolls back ALL callee modifications;
    `invoke` returns this in r0 and the caller resumes pre-CPI. We model the
    rollback exactly: discard the write-back, set r0 to this code. -/
def ERR_READONLY_MODIFIED : Nat := 0xFFFFFFFFFFFFFFF4

/-- CPI callee grew an account beyond `original_data_len +
    MAX_PERMITTED_DATA_INCREASE` (10240). Agave's re-serialization rejects it
    (`InvalidRealloc`) and rolls back; we model that exactly (caller mem
    unchanged, this code in r0). M6r. -/
def ERR_INVALID_REALLOC : Nat := 0xFFFFFFFFFFFFFFF3

/-- The `exitCode` sentinel each fault writes (wire keeps reporting it, so the
    diff-suite observables are unchanged). -/
def VmError.toSentinel : VmError → Nat
  | .divideByZero           => ERR_DIVIDE_BY_ZERO
  | .invalidPc              => ERR_INVALID_PC
  | .abort                  => ERR_ABORT
  | .accessViolation        => ERR_ACCESS_VIOLATION
  | .unsupportedInstruction => ERR_UNSUPPORTED_INSTRUCTION
  | .callDepthExceeded      => ERR_CALL_DEPTH_EXCEEDED
  | .returnDataTooLarge     => ERR_RETURN_DATA_TOO_LARGE
  | .invalidLength          => ERR_INVALID_LENGTH
  | .invalidAttribute       => ERR_INVALID_ATTRIBUTE
  | .badSeeds               => ERR_BAD_SEEDS
  | .readonlyModified       => ERR_READONLY_MODIFIED
  | .invalidRealloc         => ERR_INVALID_REALLOC

/-- `MAX_RETURN_DATA` (agave): a `sol_set_return_data` over 1024 bytes aborts. -/
def MAX_RETURN_DATA : Nat := 1024

/-! ## Checked syscall memory access (audit H6)

`step` region-checks `.ldx`/`.st`/`.stx`, but a syscall body touches `s.mem`
through the total `Nat → Nat` with no bounds layer — the H6 fail-open (any
address silently succeeds). These guards close it: each syscall slice
translation routes through `guardRead`/`guardWrite`, which consult the SAME
`RegionTable` as `step` and fault to `ERR_ACCESS_VIOLATION` (typed L1) on a
miss. Matches agave's `MemoryMapping::map` (whole range in one region, writable
for stores). agave short-circuits `len = 0` (`translate_slice_inner!`), so it's
always allowed; fixed-size translations (size ≥ 1) are always checked. -/

/-- Fault the state with an access violation. Mirrors the `step` ldx/st/stx miss
    branch: sets the sentinel exit code + typed fault channel (L1), all else
    untouched. -/
@[simp] def State.accessFault (s : State) : State :=
  { s with exitCode := some ERR_ACCESS_VIOLATION, vmError := some .accessViolation }

/-- Region-gated read guard: runs `k s` if `[addr, addr+len)` is in a mapped
    region (or `len = 0`, which agave never checks), else faults. -/
@[simp] def State.guardRead (s : State) (addr len : Nat) (k : State → State) : State :=
  if len = 0 ∨ s.regions.containsRange addr len = true then k s else s.accessFault

/-- Like `guardRead` but the range must be covered by a WRITABLE region
    (`translate_slice_mut` / `translate_type_mut`). -/
@[simp] def State.guardWrite (s : State) (addr len : Nat) (k : State → State) : State :=
  if len = 0 ∨ s.regions.containsWritable addr len = true then k s else s.accessFault

/-- Guard collapses to its continuation when the read range is covered. -/
theorem State.guardRead_pos (s : State) (addr len : Nat) (k : State → State)
    (h : len = 0 ∨ s.regions.containsRange addr len = true) :
    s.guardRead addr len k = k s := if_pos h

/-- Fault branch of `guardRead`. Rewriting with this (not
    `simp only [State.guardRead, if_neg h]`) keeps the 16-field `State` folded,
    which is what makes `guardSlices_eq` elaborate in ms not GBs. -/
theorem State.guardRead_neg (s : State) (addr len : Nat) (k : State → State)
    (h : ¬(len = 0 ∨ s.regions.containsRange addr len = true)) :
    s.guardRead addr len k = s.accessFault := if_neg h

theorem State.guardWrite_pos (s : State) (addr len : Nat) (k : State → State)
    (h : len = 0 ∨ s.regions.containsWritable addr len = true) :
    s.guardWrite addr len k = k s := if_pos h

/-- A guard preserves r10 in both branches when its continuation does. -/
theorem State.guardRead_r10 (s : State) (addr len : Nat) (k : State → State)
    (hk : (k s).regs.r10 = s.regs.r10) :
    (s.guardRead addr len k).regs.r10 = s.regs.r10 := by
  simp only [State.guardRead]; split
  · exact hk
  · rfl

theorem State.guardWrite_r10 (s : State) (addr len : Nat) (k : State → State)
    (hk : (k s).regs.r10 = s.regs.r10) :
    (s.guardWrite addr len k).regs.r10 = s.regs.r10 := by
  simp only [State.guardWrite]; split
  · exact hk
  · rfl

/-- Region-gated read guard for a `SliceDesc { ptr, len : u64 }[count]` array at
    `descsAddr`: walks the 16-byte descriptors, routing each `[ptr, ptr+len)`
    through `guardRead`. Faults on the first out-of-region slice; runs `k s`
    once all are covered. Mirrors the per-slice loop agave runs after
    translating the descriptor array (`for val in vals { translate_vm_slice }`
    in `SyscallHash`/`SyscallLogData`); the array itself is guarded by the
    caller. A `guardRead` miss never mutates `s`. -/
def State.guardSlices (s : State) (descsAddr count : Nat) (k : State → State) : State :=
  (List.range count).foldr
    (fun i (kont : State → State) (s' : State) =>
      s'.guardRead (Memory.readU64 s'.mem (descsAddr + i * 16))
        (Memory.readU64 s'.mem (descsAddr + i * 16 + 8)) kont)
    k s

/-- The descriptor walk is exactly `s.accessFault` (some slice out of region) or
    `k s` (reads never change `s`). Keystone the `Bounded` sweeps + fault lemmas
    reuse: collapses the recursive guard to a two-way case without unfolding the
    `foldr`. -/
theorem State.guardSlices_eq (s : State) (descsAddr count : Nat) (k : State → State) :
    s.guardSlices descsAddr count k = s.accessFault
      ∨ s.guardSlices descsAddr count k = k s := by
  simp only [State.guardSlices]
  generalize List.range count = l
  induction l with
  | nil => right; rfl
  | cons i t ih =>
    -- `rw`, NOT `simp only [List.foldr_cons]`: the latter builds congruence
    -- lemmas over the 16-field `State`, blowing elaboration to ~10GB.
    rw [List.foldr_cons]
    by_cases hc :
        Memory.readU64 s.mem (descsAddr + i * 16 + 8) = 0
          ∨ s.regions.containsRange (Memory.readU64 s.mem (descsAddr + i * 16))
              (Memory.readU64 s.mem (descsAddr + i * 16 + 8)) = true
    · rw [State.guardRead_pos _ _ _ _ hc]; exact ih
    · rw [State.guardRead_neg _ _ _ _ hc]; left; rfl

/-- A register predicate holding on `s.regs` and `(k s).regs` holds on a guarded
    read's result (fault keeps `s.regs`). The `Bounded` `regs`-bound closer. -/
theorem State.guardRead_regs_of_k {motive : RegFile → Prop} (s : State)
    (addr len : Nat) (k : State → State)
    (h0 : motive s.regs) (hk : motive (k s).regs) :
    motive (s.guardRead addr len k).regs := by
  simp only [State.guardRead]; split
  · exact hk
  · exact h0

/-- Descriptor-walk analog of `guardRead_regs_of_k`. -/
theorem State.guardSlices_regs_of_k {motive : RegFile → Prop} (s : State)
    (descsAddr count : Nat) (k : State → State)
    (h0 : motive s.regs) (hk : motive (k s).regs) :
    motive (s.guardSlices descsAddr count k).regs := by
  rcases s.guardSlices_eq descsAddr count k with h | h <;> rw [h]
  · exact h0
  · exact hk

/-- A guarded read preserves `mem` when its continuation does (fault never writes). -/
theorem State.guardRead_mem_eq_of_k (s : State) (addr len : Nat) (k : State → State)
    (hk : ∀ s', (k s').mem = s'.mem) :
    (s.guardRead addr len k).mem = s.mem := by
  simp only [State.guardRead]; split
  · exact hk s
  · rfl

/-- The walk only reads memory, so a `mem`-preserving continuation makes it
    `mem`-preserving. -/
theorem State.guardSlices_mem_eq_of_k (s : State) (descsAddr count : Nat)
    (k : State → State) (hk : ∀ s', (k s').mem = s'.mem) :
    (s.guardSlices descsAddr count k).mem = s.mem := by
  rcases s.guardSlices_eq descsAddr count k with h | h <;> rw [h]
  · rfl
  · exact hk s

/-- Generic field-projection collapse for `guardRead`: a projection `f` invariant
    under both a miss (`accessFault`) and the continuation is invariant under the
    guard. The field-agnostic core the syscall `preserves_*` sweeps reuse. -/
theorem State.guardRead_proj_eq_of_k {α} (f : State → α) (s : State)
    (addr len : Nat) (k : State → State)
    (hfault : f s.accessFault = f s) (hk : f (k s) = f s) :
    f (s.guardRead addr len k) = f s := by
  simp only [State.guardRead]; split
  · exact hk
  · exact hfault

/-- Descriptor-walk analog of `guardRead_proj_eq_of_k`. -/
theorem State.guardSlices_proj_eq_of_k {α} (f : State → α) (s : State)
    (descsAddr count : Nat) (k : State → State)
    (hfault : f s.accessFault = f s) (hk : f (k s) = f s) :
    f (s.guardSlices descsAddr count k) = f s := by
  rcases s.guardSlices_eq descsAddr count k with h | h <;> rw [h]
  · exact hfault
  · exact hk

/-- `guardWrite` analog of `guardRead_proj_eq_of_k`. -/
theorem State.guardWrite_proj_eq_of_k {α} (f : State → α) (s : State)
    (addr len : Nat) (k : State → State)
    (hfault : f s.accessFault = f s) (hk : f (k s) = f s) :
    f (s.guardWrite addr len k) = f s := by
  simp only [State.guardWrite]; split
  · exact hk
  · exact hfault

/-- `guardWrite` analog of `guardRead_regs_of_k`. -/
theorem State.guardWrite_regs_of_k {motive : RegFile → Prop} (s : State)
    (addr len : Nat) (k : State → State)
    (h0 : motive s.regs) (hk : motive (k s).regs) :
    motive (s.guardWrite addr len k).regs := by
  simp only [State.guardWrite]; split
  · exact hk
  · exact h0

/-- Per-byte mem bound surviving the fault state and the continuation survives
    the guard. The `Bounded` `mem_lt` closer for guarded mem-writing syscalls
    (the hash family writes a digest, so `mem` is bounded, not preserved). -/
theorem State.guardRead_mem_lt_of_k (s : State) (addr len : Nat) (k : State → State)
    (a : Nat) (h0 : s.mem a < 256) (hk : (k s).mem a < 256) :
    (s.guardRead addr len k).mem a < 256 := by
  simp only [State.guardRead]; split
  · exact hk
  · exact h0

/-- `guardWrite` analog of `guardRead_mem_lt_of_k`. -/
theorem State.guardWrite_mem_lt_of_k (s : State) (addr len : Nat) (k : State → State)
    (a : Nat) (h0 : s.mem a < 256) (hk : (k s).mem a < 256) :
    (s.guardWrite addr len k).mem a < 256 := by
  simp only [State.guardWrite]; split
  · exact hk
  · exact h0

/-- Descriptor-walk analog of `guardRead_mem_lt_of_k`. -/
theorem State.guardSlices_mem_lt_of_k (s : State) (descsAddr count : Nat)
    (k : State → State) (a : Nat) (h0 : s.mem a < 256) (hk : (k s).mem a < 256) :
    (s.guardSlices descsAddr count k).mem a < 256 := by
  rcases s.guardSlices_eq descsAddr count k with h | h <;> rw [h]
  · exact h0
  · exact hk

/-! ## Wrapping 64-bit arithmetic -/

@[simp] def wrapAdd (a b : Nat) : Nat := (a + b) % U64_MODULUS
@[simp] def wrapSub (a b : Nat) : Nat := (a + U64_MODULUS - b % U64_MODULUS) % U64_MODULUS
@[simp] def wrapMul (a b : Nat) : Nat := (a * b) % U64_MODULUS
@[simp] def wrapNeg (a : Nat) : Nat := (U64_MODULUS - a % U64_MODULUS) % U64_MODULUS

/-- No-overflow `wrapAdd` is ordinary addition. Exposes a lifted credit
    (`dst := wrapAdd dst amount`) as the clean `dst + amount`. -/
theorem wrapAdd_of_lt {a b : Nat} (h : a + b < 2 ^ 64) : wrapAdd a b = a + b := by
  simp only [wrapAdd, U64_MODULUS]
  exact Nat.mod_eq_of_lt h

/-- No-underflow `wrapSub` (with `a < 2^64`) is ordinary subtraction. Exposes a
    lifted debit (`src := wrapSub src amount`) as the clean `src - amount`. -/
theorem wrapSub_of_le {a b : Nat} (hle : b ≤ a) (ha : a < 2 ^ 64) :
    wrapSub a b = a - b := by
  simp only [wrapSub, U64_MODULUS]
  rw [Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega),
      show a + 2 ^ 64 - b = (a - b) + 2 ^ 64 by omega, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

/-- `toU64 1 = 1`. Lets a constant-`+1` credit clean to `v + 1`. -/
theorem toU64_one : toU64 1 = 1 := by decide

/-- No-overflow `+1` `wrapAdd` is ordinary `· + 1`. Constant-delta counterpart
    of `wrapAdd_of_lt`, used by the `counter += 1` balance-corollary codegen. -/
theorem wrapAdd_one_of_lt {a : Nat} (h : a + 1 < 2 ^ 64) :
    wrapAdd a (toU64 1) = a + 1 := by
  rw [toU64_one]; exact wrapAdd_of_lt h

def U32_MODULUS : Nat := 2 ^ 32

/-- Sign-extend a value reduced mod 2^32 into a 64-bit register. sBPF V0/V1
    sign-extends 32-bit ADD/SUB/MUL (`(x as i32).wrapping_op(y) as i64 as u64`;
    V2 zero-extends via `explicit_sign_extension_of_results`). C1. -/
@[simp] def signExtend32 (n : Nat) : Nat :=
  if n < 0x80000000 then n else n + (U64_MODULUS - U32_MODULUS)

-- ADD32/SUB32/MUL32 sign-extend their i32 result (V0/V1); the other 32-bit ALU
-- ops (OR/AND/XOR, shifts, MOV32, DIV32, MOD32, NEG32) zero-extend.
@[simp] def wrapAdd32 (a b : Nat) : Nat := signExtend32 ((a + b) % U32_MODULUS)
@[simp] def wrapSub32 (a b : Nat) : Nat := signExtend32 ((a + U32_MODULUS - b % U32_MODULUS) % U32_MODULUS)
@[simp] def wrapMul32 (a b : Nat) : Nat := signExtend32 ((a * b) % U32_MODULUS)
@[simp] def wrapNeg32 (a : Nat) : Nat := (U32_MODULUS - a % U32_MODULUS) % U32_MODULUS

-- C1 regression pins: V0 sign-extends 32-bit add/sub/mul into r[dst].
example : wrapSub32 0 1 = 0xFFFFFFFFFFFFFFFF := by decide          -- 0 - 1 underflows, all-ones
example : wrapAdd32 0 0x7FFFFFFF = 0x7FFFFFFF := by decide          -- bit 31 clear: unchanged
example : wrapAdd32 0 0x80000000 = 0xFFFFFFFF80000000 := by decide  -- bit 31 set: sign-extended
example : wrapMul32 0xFFFFFFFF 0xFFFFFFFF = 1 := by decide          -- (-1)*(-1) = 1

/-! ## Byte-region helpers for syscall bodies

Pull byte arrays out of memory and write them back. Live alongside `Mem` so
syscall-body modules don't depend on `Execute.lean`. -/

/-- Read `len` bytes from `mem` starting at `addr`. -/
def readBytes (mem : Memory.Mem) (addr len : Nat) : ByteArray :=
  ⟨(List.range len).foldl
    (fun acc i => acc.push (mem (addr + i) % 256).toUInt8) #[]⟩

/-- `readBytes`'s underlying `Array` is a map over `List.range len`. -/
theorem readBytes_data (mem : Memory.Mem) (addr len : Nat) :
    (readBytes mem addr len).data
      = ((List.range len).map (fun i => (mem (addr + i) % 256).toUInt8)).toArray := by
  show ((List.range len).foldl (fun acc i => acc.push (mem (addr + i) % 256).toUInt8) #[])
        = ((List.range len).map (fun i => (mem (addr + i) % 256).toUInt8)).toArray
  rw [List.foldl_push_eq_append]
  simp

/-- `readBytes` produces a `ByteArray` of size exactly `len`. -/
@[simp] theorem readBytes_size (mem : Memory.Mem) (addr len : Nat) :
    (readBytes mem addr len).size = len := by
  show (readBytes mem addr len).data.size = len
  rw [readBytes_data]
  simp [List.length_range]

/-- `readBytes` recovers `bs` when sizes match and each byte matches memory
    mod 256. Used by specs pulling a fixed-length blob under SL ownership. -/
theorem readBytes_eq_of_match (mem : Memory.Mem) (addr len : Nat) (bs : ByteArray)
    (hsize : bs.size = len)
    (hb : ∀ i, i < len → mem (addr + i) % 256 = (bs.get! i).toNat) :
    readBytes mem addr len = bs := by
  apply ByteArray.ext
  rw [readBytes_data]
  apply Array.ext
  · simp [List.length_range, hsize]
  · intro i hi1 _
    have hi : i < len := by
      have hi' : i < ((List.range len).map
          (fun i => (mem (addr + i) % 256).toUInt8)).toArray.size := hi1
      simpa [List.length_range] using hi'
    have hbsize : i < bs.size := by rw [hsize]; exact hi
    simp only [List.getElem_toArray, List.getElem_map, List.getElem_range]
    have hmem := hb i hi
    have h_get : bs.get! i = bs.data[i] := by
      show bs.data[i]! = bs.data[i]
      exact getElem!_pos bs.data i hbsize
    rw [hmem]
    show UInt8.ofNat (bs.get! i).toNat = bs.data[i]
    rw [UInt8.ofNat_toNat, h_get]


/-- Deref `n` 16-byte `SliceDesc { ptr, len : u64 }` descriptors at `descsAddr`
    and concatenate. Standard input shape for the hash family. -/
def readSlices (mem : Memory.Mem) (descsAddr n : Nat) : ByteArray :=
  (List.range n).foldl (fun acc i =>
    let descAddr := descsAddr + i * 16
    let ptr := Memory.readU64 mem descAddr
    let len := Memory.readU64 mem (descAddr + 8)
    acc ++ readBytes mem ptr len) ByteArray.empty

/-- Sum the `len` fields across `n` descriptors at `descsAddr`. Cheaper than
    `readSlices … |>.size`: skips dereferencing the slice bytes. -/
def sumSliceLens (mem : Memory.Mem) (descsAddr n : Nat) : Nat :=
  (List.range n).foldl (fun acc i =>
    let descAddr := descsAddr + i * 16
    acc + Memory.readU64 mem (descAddr + 8)) 0

/-- Per-slice hash-family cost. agave's
    `mem_op_base_cost.max(sha256_byte_cost.saturating_mul(len / 2))` applied per
    slice (NOT sum-of-lengths × byte_cost); the sum is added to base cost 85.
    `blueshift/sbpf/crates/runtime/src/syscalls/crypto.rs:83-86`. -/
def hashSliceCost (mem : Memory.Mem) (descsAddr n : Nat) : Nat :=
  (List.range n).foldl (fun acc i =>
    let descAddr := descsAddr + i * 16
    let len := Memory.readU64 mem (descAddr + 8)
    acc + Nat.max 10 (len / 2)) 0

/-- Write the first `len` bytes of `bs` to `out`, rest untouched. Writes
    byte-by-byte into the `Mem` overlay so reads take the O(1) HashMap path
    instead of walking a closure chain. -/
def writeBytes (mem : Memory.Mem) (out len : Nat) (bs : ByteArray) : Memory.Mem :=
  (List.range len).foldl
    (fun m i => Memory.writeU8 m (out + i) (bs.get! i).toNat) mem

/-- Reading `writeBytes` outside the written window is transparent. The
    fold-based body has no `if` to peel, so this replaces the old
    `unfold writeBytes; rw [if_neg ...]` pattern. -/
theorem writeBytes_read_outside (mem : Memory.Mem) (out len a : Nat) (bs : ByteArray)
    (h : a < out ∨ a ≥ out + len) :
    (writeBytes mem out len bs).read a = mem.read a := by
  unfold writeBytes
  induction len with
  | zero => simp [List.range_zero]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    unfold Memory.writeU8
    rw [Memory.Mem.read_put_other _ _ _ _ (by rcases h with h | h <;> omega)]
    apply ih
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)

/-- Reading `writeBytes` inside the window returns `bs.get! i`. Replaces the old
    `unfold writeBytes; rw [if_pos ...]`. (Sound because `bs.get!` < 256 matches
    the `val % 256` that `writeU8` stores.) -/
theorem writeBytes_read_inside (mem : Memory.Mem) (out len i : Nat) (bs : ByteArray)
    (hi : i < len) :
    (writeBytes mem out len bs).read (out + i) = (bs.get! i).toNat := by
  unfold writeBytes
  induction len with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    unfold Memory.writeU8
    by_cases h : i = n
    · subst h
      rw [Memory.Mem.read_put_self]
      have : (bs.get! i).toNat < 256 := (bs.get! i).toNat_lt
      omega
    · rw [Memory.Mem.read_put_other _ _ _ _ (by omega)]
      apply ih
      omega

/-- agave hash-syscall write envelope (sha256/sha512/keccak256/blake3): check the
    OUTPUT region FIRST (`translate_slice_mut`, agave's order), then the input
    descriptor array, then each slice; on success write `digest` and set
    `r0 := 0`. Any guard miss traps with a typed access violation.

    NOT `@[simp]`: the recursive `guardSlices` walk must stay folded so the
    blanket `Bounded`/`Execute` sweeps don't choke (the `sol_log_data` lesson);
    the field lemmas below close them folded, `regs_lt`/`mem_lt` via the
    dedicated closers. `@[irreducible]` so the `exact hashWrite_*` in those
    sweeps' `first` block fails by head-symbol instantly on non-hash leaves
    rather than whnf-unfolding (5 metavars) ~160s across the sweep; simp still
    unfolds via the equation lemma, the compiler still runs it. -/
@[irreducible] def State.hashWrite (s : State) (outPtr outLen inPtr inN : Nat)
    (digest : ByteArray) : State :=
  s.guardWrite outPtr outLen fun s =>
    s.guardRead inPtr (inN * 16) fun s =>
      s.guardSlices inPtr inN fun s =>
        { s with regs := s.regs.set .r0 0
                 mem  := writeBytes s.mem outPtr outLen digest }

/-- `hashWrite` only rewrites `regs` (r0) and `mem` (digest); every other field
    is preserved on both branches. `@[simp]` closes the sweeps folded (one set
    of lemmas covers all four hashes). -/
@[simp] theorem State.hashWrite_callStack (s : State)
    (outPtr outLen inPtr inN : Nat) (digest : ByteArray) :
    (s.hashWrite outPtr outLen inPtr inN digest).callStack = s.callStack := by
  simp only [State.hashWrite]
  refine State.guardWrite_proj_eq_of_k (·.callStack) s _ _ _ rfl ?_
  refine State.guardRead_proj_eq_of_k (·.callStack) s _ _ _ rfl ?_
  exact State.guardSlices_proj_eq_of_k (·.callStack) s _ _ _ rfl rfl

@[simp] theorem State.hashWrite_regions (s : State)
    (outPtr outLen inPtr inN : Nat) (digest : ByteArray) :
    (s.hashWrite outPtr outLen inPtr inN digest).regions = s.regions := by
  simp only [State.hashWrite]
  refine State.guardWrite_proj_eq_of_k (·.regions) s _ _ _ rfl ?_
  refine State.guardRead_proj_eq_of_k (·.regions) s _ _ _ rfl ?_
  exact State.guardSlices_proj_eq_of_k (·.regions) s _ _ _ rfl rfl

@[simp] theorem State.hashWrite_cuBudget (s : State)
    (outPtr outLen inPtr inN : Nat) (digest : ByteArray) :
    (s.hashWrite outPtr outLen inPtr inN digest).cuBudget = s.cuBudget := by
  simp only [State.hashWrite]
  refine State.guardWrite_proj_eq_of_k (·.cuBudget) s _ _ _ rfl ?_
  refine State.guardRead_proj_eq_of_k (·.cuBudget) s _ _ _ rfl ?_
  exact State.guardSlices_proj_eq_of_k (·.cuBudget) s _ _ _ rfl rfl

@[simp] theorem State.hashWrite_heapNext (s : State)
    (outPtr outLen inPtr inN : Nat) (digest : ByteArray) :
    (s.hashWrite outPtr outLen inPtr inN digest).heapNext = s.heapNext := by
  simp only [State.hashWrite]
  refine State.guardWrite_proj_eq_of_k (·.heapNext) s _ _ _ rfl ?_
  refine State.guardRead_proj_eq_of_k (·.heapNext) s _ _ _ rfl ?_
  exact State.guardSlices_proj_eq_of_k (·.heapNext) s _ _ _ rfl rfl

@[simp] theorem State.hashWrite_returnData (s : State)
    (outPtr outLen inPtr inN : Nat) (digest : ByteArray) :
    (s.hashWrite outPtr outLen inPtr inN digest).returnData = s.returnData := by
  simp only [State.hashWrite]
  refine State.guardWrite_proj_eq_of_k (·.returnData) s _ _ _ rfl ?_
  refine State.guardRead_proj_eq_of_k (·.returnData) s _ _ _ rfl ?_
  exact State.guardSlices_proj_eq_of_k (·.returnData) s _ _ _ rfl rfl

@[simp] theorem State.hashWrite_r10 (s : State)
    (outPtr outLen inPtr inN : Nat) (digest : ByteArray) :
    (s.hashWrite outPtr outLen inPtr inN digest).regs.r10 = s.regs.r10 := by
  simp only [State.hashWrite]
  refine State.guardWrite_proj_eq_of_k (·.regs.r10) s _ _ _ rfl ?_
  refine State.guardRead_proj_eq_of_k (·.regs.r10) s _ _ _ rfl ?_
  refine State.guardSlices_proj_eq_of_k (·.regs.r10) s _ _ _ rfl ?_
  exact RegFile.set_preserves_r10 s.regs .r0 0

/-- `hashWrite`'s `regs` is `s.regs` (faulted) or `s.regs.set .r0 0` (success);
    a predicate surviving both survives. The `Bounded` `regs_lt` hash closer. -/
theorem State.hashWrite_regs_of_k {motive : RegFile → Prop} (s : State)
    (outPtr outLen inPtr inN : Nat) (digest : ByteArray)
    (h0 : motive s.regs) (hk : motive (s.regs.set .r0 0)) :
    motive (s.hashWrite outPtr outLen inPtr inN digest).regs := by
  simp only [State.hashWrite]
  apply State.guardWrite_regs_of_k (motive := motive) (h0 := h0)
  apply State.guardRead_regs_of_k (motive := motive) (h0 := h0)
  apply State.guardSlices_regs_of_k (motive := motive) (h0 := h0)
  exact hk

/-- Commit an `Option ByteArray`: `some` writes to `*out` (sized `outSize`) +
    `r0 := 0`; `none` sets `r0 := 1`, mem unchanged. The 0/1 convention matches
    agave's `SyscallError`-to-u64 mapping (curve/pairing/big-mod-exp/poseidon/PDA).

    NOT `@[simp]` — unfolding across 44 syscall arms during
    `execSyscall_preserves_r10` blows up simp; the targeted
    `commitOptional_preserves_r10` below closes it in one rewrite instead. -/
def commitOptional (s : State) (out outSize : Nat)
    (result : Option ByteArray) : State :=
  match result with
  | some bs => { s with regs := s.regs.set .r0 0
                        mem  := writeBytes s.mem out outSize bs }
  | none    => { s with regs := s.regs.set .r0 1 }

/-- `commitOptional` preserves r10 in both arms. `@[simp]` so syscall arms ending
    in it discharge by one rewrite, no unfolding. -/
@[simp] theorem commitOptional_preserves_r10 (s : State) (out outSize : Nat)
    (result : Option ByteArray) :
    (commitOptional s out outSize result).regs.r10 = s.regs.r10 := by
  cases result <;> simp [commitOptional]

/-- `commitOptional` preserves the region table in both arms. `@[simp]` so the
    bounds invariant flows through any syscall ending in it. -/
@[simp] theorem commitOptional_preserves_regions (s : State) (out outSize : Nat)
    (result : Option ByteArray) :
    (commitOptional s out outSize result).regions = s.regions := by
  cases result <;> simp [commitOptional]

/-- `commitOptional` preserves `returnData` in both arms. `@[simp]` so specs
    owning `returnDataIs` can frame it through these syscalls. -/
@[simp] theorem commitOptional_preserves_returnData (s : State) (out outSize : Nat)
    (result : Option ByteArray) :
    (commitOptional s out outSize result).returnData = s.returnData := by
  cases result <;> simp [commitOptional]

/-- `commitOptional` preserves the call stack in both arms. `@[simp]` so specs
    owning `callStackIs` can frame it through these syscalls. -/
@[simp] theorem commitOptional_preserves_callStack (s : State) (out outSize : Nat)
    (result : Option ByteArray) :
    (commitOptional s out outSize result).callStack = s.callStack := by
  cases result <;> simp [commitOptional]

/-- Poseidon write envelope: like `hashWrite` but the body is `commitOptional`
    (poseidon returns an `Option`). Output region checked FIRST, then descriptor
    array, then each slice. `@[irreducible]` for the same `Bounded`-sweep
    head-symbol reason as `hashWrite`. -/
@[irreducible] def State.guardedCommit (s : State) (outPtr outLen inPtr inN : Nat)
    (result : Option ByteArray) : State :=
  s.guardWrite outPtr outLen fun s =>
    s.guardRead inPtr (inN * 16) fun s =>
      s.guardSlices inPtr inN fun s =>
        commitOptional s outPtr outLen result

/-- `guardedCommit` only rewrites `regs` (r0) and `mem` (the `some` write); every
    other field is preserved on both branches. `@[simp]` closes the
    `sol_poseidon` arm folded. -/
@[simp] theorem State.guardedCommit_callStack (s : State)
    (outPtr outLen inPtr inN : Nat) (result : Option ByteArray) :
    (s.guardedCommit outPtr outLen inPtr inN result).callStack = s.callStack := by
  simp only [State.guardedCommit]
  refine State.guardWrite_proj_eq_of_k (·.callStack) s _ _ _ rfl ?_
  refine State.guardRead_proj_eq_of_k (·.callStack) s _ _ _ rfl ?_
  refine State.guardSlices_proj_eq_of_k (·.callStack) s _ _ _ rfl ?_
  exact commitOptional_preserves_callStack s _ _ _

@[simp] theorem State.guardedCommit_regions (s : State)
    (outPtr outLen inPtr inN : Nat) (result : Option ByteArray) :
    (s.guardedCommit outPtr outLen inPtr inN result).regions = s.regions := by
  simp only [State.guardedCommit]
  refine State.guardWrite_proj_eq_of_k (·.regions) s _ _ _ rfl ?_
  refine State.guardRead_proj_eq_of_k (·.regions) s _ _ _ rfl ?_
  refine State.guardSlices_proj_eq_of_k (·.regions) s _ _ _ rfl ?_
  exact commitOptional_preserves_regions s _ _ _

@[simp] theorem State.guardedCommit_returnData (s : State)
    (outPtr outLen inPtr inN : Nat) (result : Option ByteArray) :
    (s.guardedCommit outPtr outLen inPtr inN result).returnData = s.returnData := by
  simp only [State.guardedCommit]
  refine State.guardWrite_proj_eq_of_k (·.returnData) s _ _ _ rfl ?_
  refine State.guardRead_proj_eq_of_k (·.returnData) s _ _ _ rfl ?_
  refine State.guardSlices_proj_eq_of_k (·.returnData) s _ _ _ rfl ?_
  exact commitOptional_preserves_returnData s _ _ _

@[simp] theorem State.guardedCommit_r10 (s : State)
    (outPtr outLen inPtr inN : Nat) (result : Option ByteArray) :
    (s.guardedCommit outPtr outLen inPtr inN result).regs.r10 = s.regs.r10 := by
  simp only [State.guardedCommit]
  refine State.guardWrite_proj_eq_of_k (·.regs.r10) s _ _ _ rfl ?_
  refine State.guardRead_proj_eq_of_k (·.regs.r10) s _ _ _ rfl ?_
  refine State.guardSlices_proj_eq_of_k (·.regs.r10) s _ _ _ rfl ?_
  exact commitOptional_preserves_r10 s _ _ _

@[simp] theorem State.guardedCommit_cuBudget (s : State)
    (outPtr outLen inPtr inN : Nat) (result : Option ByteArray) :
    (s.guardedCommit outPtr outLen inPtr inN result).cuBudget = s.cuBudget := by
  simp only [State.guardedCommit]
  refine State.guardWrite_proj_eq_of_k (·.cuBudget) s _ _ _ rfl ?_
  refine State.guardRead_proj_eq_of_k (·.cuBudget) s _ _ _ rfl ?_
  refine State.guardSlices_proj_eq_of_k (·.cuBudget) s _ _ _ rfl ?_
  cases result <;> rfl

@[simp] theorem State.guardedCommit_heapNext (s : State)
    (outPtr outLen inPtr inN : Nat) (result : Option ByteArray) :
    (s.guardedCommit outPtr outLen inPtr inN result).heapNext = s.heapNext := by
  simp only [State.guardedCommit]
  refine State.guardWrite_proj_eq_of_k (·.heapNext) s _ _ _ rfl ?_
  refine State.guardRead_proj_eq_of_k (·.heapNext) s _ _ _ rfl ?_
  refine State.guardSlices_proj_eq_of_k (·.heapNext) s _ _ _ rfl ?_
  cases result <;> rfl

/-- `guardedCommit`'s `regs` is `s.regs` (faulted) or `s.regs.set .r0 v`,
    `v ∈ {0,1}`; a predicate holding on all three survives. The `Bounded`
    `regs_lt` poseidon closer. -/
theorem State.guardedCommit_regs_of_k {motive : RegFile → Prop} (s : State)
    (outPtr outLen inPtr inN : Nat) (result : Option ByteArray)
    (h0 : motive s.regs) (hk0 : motive (s.regs.set .r0 0))
    (hk1 : motive (s.regs.set .r0 1)) :
    motive (s.guardedCommit outPtr outLen inPtr inN result).regs := by
  simp only [State.guardedCommit]
  apply State.guardWrite_regs_of_k (motive := motive) (h0 := h0)
  apply State.guardRead_regs_of_k (motive := motive) (h0 := h0)
  apply State.guardSlices_regs_of_k (motive := motive) (h0 := h0)
  cases result
  · exact hk1
  · exact hk0

end SVM.SBPF
