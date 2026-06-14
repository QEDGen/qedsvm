-- Machine state for sBPF execution: registers, call frames, top-level State,
-- runtime error codes, and the wrapping-arithmetic helpers.
--
-- Lifted out of Execute.lean so syscall-body modules (Sha256.lean,
-- Keccak256.lean, …) can spell `def exec : State → State` without an
-- import cycle through the dispatcher.

import SVM.SBPF.ISA
import SVM.SBPF.Memory

namespace SVM.SBPF

open Memory

/-! ## Register file as a concrete structure

Using named fields instead of a function `Reg → Nat` makes projections
trivially reducible by simp, avoiding the nested if-then-else chains that
cause timeouts in proofs. -/

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

/-- Get a register value -/
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

/-- Reading the register just written returns the written value (r0-r9 only). -/
theorem RegFile.get_set_self (rf : RegFile) (r : Reg) (v : Nat) (h : r ≠ .r10) :
    (rf.set r v).get r = v := by
  cases r <;> simp_all [RegFile.get, RegFile.set]

/-- Reading a different register from the one written returns the original value. -/
theorem RegFile.get_set_diff (rf : RegFile) (rA rB : Reg) (v : Nat) (h : rA ≠ rB) :
    (rf.set rB v).get rA = rf.get rA := by
  cases rA <;> cases rB <;> simp_all [RegFile.get, RegFile.set]

/-! ## Machine state -/

/-- One entry on the internal call/return stack. Pushed by
    `.call_local`, popped by `.exit`. Mirrors agave's `CallFrame`
    in solana-sbpf — saves the return PC, the frame pointer (r10),
    and the four caller-saved scratch registers (r6–r9) that LLVM
    treats as callee-saved across calls. Without restoring r6–r9
    on exit, LLVM-emitted iterators get their loop pointer
    clobbered by sub-calls. -/
structure CallFrame where
  retPc : Nat
  savedR6 : Nat
  savedR7 : Nat
  savedR8 : Nat
  savedR9 : Nat
  savedR10 : Nat
  deriving Inhabited, Repr

/-- Typed VM-fault channel (audit L1). The `ERR_*` sentinels (defined below) live
    in `exitCode : Option Nat`, where an `exit` of exactly the sentinel
    VALUE is indistinguishable from the fault — a spec phrased
    `exitCode = some ERR_X` is satisfiable by a pathological clean exit.
    The collision is observable on chain (the `sentinel_exit.so`
    experiment: agave reports `UnknownError(InvalidError)` for the clean
    exit, distinct from a real fault's error), so the model carries the
    fault as a TYPED value in `State.vmError`, set by every abort site
    alongside the sentinel; a clean `exit` never sets it. `exitCode`
    behavior is unchanged (all existing specs still hold verbatim);
    `vmError` is the authoritative channel for fault-vs-exit and the
    input to the cross-engine error-code mapping (M14). -/
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
  deriving Repr, DecidableEq, Inhabited

/-- sBPF machine state -/
structure State where
  /-- Register file -/
  regs : RegFile
  /-- Byte-addressable memory -/
  mem : Mem
  /-- Mapped regions (program, stack, heap, input). Memory accesses
      outside these regions trap to `ERR_ACCESS_VIOLATION`. Total `mem`
      is preserved underneath; the table is a parallel bounds layer. -/
  regions : Memory.RegionTable
  /-- Program counter: index into the instruction array -/
  pc : Nat
  /-- Exit status: None if running, Some n if exited with code n -/
  exitCode : Option Nat := none
  /-- Typed fault channel (audit L1): `some e` iff execution halted on a
      VM fault; a clean `exit` leaves it `none` even when r0 numerically
      equals a sentinel. Every abort site sets this ALONGSIDE the
      `exitCode` sentinel (which is unchanged, so specs phrased over
      `exitCode` still hold); `vmError` is what distinguishes the two. -/
  vmError : Option VmError := none
  /-- Side channel: messages written via `sol_log_*` syscalls.
      Each entry is one message. Observable from the runner; not owned
      by any separation-logic assertion. -/
  log : Array ByteArray := #[]
  /-- Side channel: return-data buffer set by `sol_set_return_data` and
      read by `sol_get_return_data`. -/
  returnData : ByteArray := ByteArray.empty
  /-- 32-byte program id of the program that last called
      `sol_set_return_data`. Transaction-wide alongside `returnData`
      (agave initializes the pair to `(Pubkey::default(), [])`, hence
      the 32-zero default), inherited/committed across CPI exactly like
      `returnData`. Written by `sol_get_return_data` into `*pubkey_out`
      (H7 — previously a fabricated 32-zero placeholder). -/
  returnDataProgId : ByteArray := ⟨Array.replicate 32 0⟩
  /-- Internal call / return stack. Each `.call_local` pushes a
      `CallFrame` capturing the return PC, current `r10`, and the
      callee-saved scratch registers r6–r9, then bumps `r10` by
      one V0 frame (0x1000 — agave 4.x with `all_enabled` features
      sets `enable_stack_frame_gaps = false`, so num_frames = 1).
      Each `.exit` either pops the frame (restoring all six fields)
      or, if empty, terminates the program. Mirrors agave's SBPF V0
      behavior in `solana-sbpf::Interpreter::push_frame` + `EXIT`. -/
  callStack : List CallFrame := []
  /-- Extra CU consumed beyond the per-step "1 fuel per instruction"
      baseline. Bumped by `.call syscall` according to
      `syscallCu` (mirrors agave's `SVMTransactionExecutionCost`).
      Top-level CU reporting in `SVM/Ffi.lean` is
      `(cuBudget - fuelRemaining) + s.cuConsumed`. -/
  cuConsumed : Nat := 0
  /-- Total transaction CU budget, threaded in from `Runner.RunConfig`
      at `initState` time. Used by `sol_log_compute_units_` to report
      `remaining = cuBudget - cuConsumed` (saturating to 0) — the
      agave-parity wording. `0` means "unset / uncapped" — log syscalls
      will still emit a `0 units remaining` message in that case,
      matching agave's behavior when the budget is exhausted. -/
  cuBudget : Nat := 0
  /-- Bump-allocator pointer for `sol_alloc_free_`. Starts at
      `MM_HEAP_START` (`0x300000000`) and grows upward as allocations
      happen. Tier-2 #6 — the BPF program-local heap. Reset to
      `MM_HEAP_START` on each CPI sub-state since agave allocates the
      heap fresh per invocation. -/
  heapNext : Nat := 0x300000000
  /-- 32-byte program-id of the program currently executing. Used
      by `sol_invoke_signed{,_c}` to derive PDAs from caller-supplied
      signer seeds (the derivation hashes seeds ++ programId ++
      "ProgramDerivedAddress"). Set to the top-level program's id by
      `Runner.initialState` from `RunConfig.progIdBytes`; reset to
      the callee's id when constructing each CPI sub-state. Empty
      (`ByteArray.empty`) means PDA derivation will fail closed —
      safe default for code paths that don't need signer seeds. -/
  progIdBytes : ByteArray := ByteArray.empty
  /-- Caller's RUNTIME-SET account privileges `(key, is_signer,
      is_writable)`, parsed from the serialized input when the state is
      created (and immutable thereafter). A program can overwrite the
      `is_signer`/`is_writable` byte in its own (writable) AccountInfo
      memory, but a CPI may only pass a callee privileges the caller
      actually holds — so the runner clamps CPI privileges against this
      table rather than trusting the program-supplied bytes. Empty means
      "no recorded privileges" (every CPI signer/writable clamps off
      unless PDA-derived). See docs/SOUNDNESS_AUDIT_* (C5). -/
  origPrivs : List (ByteArray × Bool × Bool) := []
  /-- CPI invocation depth of THIS state's program: 0 at top level,
      `caller + 1` for a CPI callee (set on the sub-state in
      `executeFnCpiWithFuel`). agave caps the instruction stack height
      at 5 (top level = height 1), i.e. at most 4 nested CPIs; the
      runner's CPI dispatch fails closed past that (M6). -/
  invokeDepth : Nat := 0
  deriving Inhabited

/-- Is the machine still running? -/
def State.running (s : State) : Prop := s.exitCode = none

/-! ## Helpers -/

/-- Resolve a source operand to its unsigned 64-bit value -/
@[simp] def resolveSrc (rf : RegFile) (src : Src) : Nat :=
  match src with
  | .reg r => rf.get r
  | .imm v => toU64 v

/-! ## Runtime error codes

These are used when the VM encounters an unrecoverable error (not a program
exit via `exit` instruction). They must be non-zero to distinguish from
success. -/

def ERR_DIVIDE_BY_ZERO : Nat := 0xFFFFFFFFFFFFFFFE
def ERR_INVALID_PC     : Nat := 0xFFFFFFFFFFFFFFFF
/-- Exit code for `abort` / `sol_panic_`. Solana's runtime maps these
    to `InstructionError::ProgramFailedToComplete`; we represent that
    as a distinct non-zero exit code so callers can distinguish program
    aborts from clean exits. -/
def ERR_ABORT          : Nat := 0xFFFFFFFFFFFFFFFD
/-- Exit code for an out-of-region memory access. Agave raises
    `EbpfError::AccessViolation` (a `MemoryError::AddressLoad` /
    `AddressStore` under the hood); we surface it as a sentinel exit
    code so the harness can map it to a `Failure` outcome. -/
def ERR_ACCESS_VIOLATION : Nat := 0xFFFFFFFFFFFFFFFC
/-- Exit code for an instruction the model does not faithfully execute
    and therefore refuses to run rather than fabricate a result. Agave
    raises `EbpfError::UnsupportedInstruction` (or `SyscallError` for an
    unregistered syscall). Used by `.callx` (indirect call: frame/vaddr
    semantics not modeled), the proof-side CPI stub, and unknown
    syscalls. Failing closed keeps the model from proving an exit code
    that is false of the real VM on these paths. -/
def ERR_UNSUPPORTED_INSTRUCTION : Nat := 0xFFFFFFFFFFFFFFFA
/-- Exit code for exceeding the sBPF call-depth limit. Agave raises
    `EbpfError::CallDepthExceeded` at the 65th nested frame. -/
def ERR_CALL_DEPTH_EXCEEDED : Nat := 0xFFFFFFFFFFFFFFF9

/-- Maximum sBPF call depth (`MAX_CALL_DEPTH` in solana-sbpf). The 65th
    nested `call`/`call_local` aborts with `CallDepthExceeded`. -/
def MAX_CALL_DEPTH : Nat := 64

/-- Exit code for `sol_set_return_data` with `len > MAX_RETURN_DATA`.
    Agave raises `SyscallError::ReturnDataTooLarge`. -/
def ERR_RETURN_DATA_TOO_LARGE : Nat := 0xFFFFFFFFFFFFFFF8

/-- Exit code for a syscall called with an over-length input that agave
    rejects (`SyscallError::InvalidLength`): `sol_big_mod_exp` over 512
    bytes, `sol_curve_multiscalar_mul` over 512 points, etc. -/
def ERR_INVALID_LENGTH : Nat := 0xFFFFFFFFFFFFFFF7

/-- Exit code for `SyscallError::InvalidAttribute`: an unsupported
    curve id passed to a curve25519 syscall when `abort_on_invalid_curve`
    is active (it is, under `FeatureSet::all_enabled`). -/
def ERR_INVALID_ATTRIBUTE : Nat := 0xFFFFFFFFFFFFFFF6

/-- Exit code for `SyscallError::BadSeeds`: a PDA derivation given more
    than `MAX_SEEDS` (16) seeds or a seed longer than 32 bytes. Agave
    aborts (`MaxSeedLengthExceeded`) rather than returning in-band. -/
def ERR_BAD_SEEDS : Nat := 0xFFFFFFFFFFFFFFF5

/-- Exit code for a CPI whose callee modified a NON-writable (read-only)
    account's data, lamports, or owner. agave verifies every account
    after a sub-instruction returns and fails the whole sub-instruction
    (`InstructionError::{ReadonlyDataModified,ReadonlyLamportChange,
    ExternalAccountDataModified,ModifiedProgramId}`), rolling back ALL of
    the callee's account modifications; the `invoke` syscall then returns
    this error in r0 and the caller resumes from its pre-CPI memory. We
    model that rollback exactly: on violation the runner discards the
    callee's write-back (caller mem unchanged) and sets r0 to this code. -/
def ERR_READONLY_MODIFIED : Nat := 0xFFFFFFFFFFFFFFF4

/-- The `exitCode` sentinel each fault writes (the wire keeps reporting
    this value, so the diff-suite observables are unchanged). -/
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

/-- `MAX_RETURN_DATA` (agave): a program may set at most 1024 bytes of
    return data; a larger `sol_set_return_data` aborts. -/
def MAX_RETURN_DATA : Nat := 1024

/-! ## Checked syscall memory access (audit H6)

`step` region-checks `.ldx`/`.st`/`.stx` against `s.regions`, but a
syscall body reads and writes `s.mem` through the total `Nat → Nat`
function with no bounds layer — so a syscall could touch any address and
silently succeed. That is the fail-open the audit flagged as H6
(`SVM/Syscalls/*` translate slices without consulting the region table).

These guards close it: each syscall that translates a `[addr, addr+len)`
slice routes through `guardRead` / `guardWrite`, which consult the SAME
`RegionTable` as `step` and fault to `ERR_ACCESS_VIOLATION` (typed
`vmError := some .accessViolation`, L1) on a miss. The check matches
agave's `MemoryMapping::map`: the whole range must fall inside one mapped
region (writable too, for stores). agave's `translate_slice_inner!`
short-circuits a zero-length access (`if len == 0 { return Ok(&[]) }` in
`solana-program-runtime::memory`), so `len = 0` is always allowed; a
fixed-size translation (`translate_type`, size ≥ 1) passes its constant
size and so is always checked. -/

/-- Fault the state with an access violation. Mirrors the `step`
    ldx/st/stx miss branch: sets the sentinel exit code and the typed
    fault channel (L1), leaving `mem`/`regs` and every other field
    untouched. -/
@[simp] def State.accessFault (s : State) : State :=
  { s with exitCode := some ERR_ACCESS_VIOLATION, vmError := some .accessViolation }

/-- Region-gated read guard for a syscall slice translation. Runs `k s`
    if `[addr, addr+len)` lies within a mapped region (or `len = 0`, which
    agave never checks), else faults with an access violation. -/
@[simp] def State.guardRead (s : State) (addr len : Nat) (k : State → State) : State :=
  if len = 0 ∨ s.regions.containsRange addr len = true then k s else s.accessFault

/-- Region-gated write guard: like `guardRead` but the range must be
    covered by a WRITABLE region (`translate_slice_mut` / `translate_type_mut`). -/
@[simp] def State.guardWrite (s : State) (addr len : Nat) (k : State → State) : State :=
  if len = 0 ∨ s.regions.containsWritable addr len = true then k s else s.accessFault

/-- The guard collapses to its continuation when the read range is
    covered. Lets a syscall spec, given its `rr` region requirement,
    rewrite `guardRead` away and reduce to the unguarded core. -/
theorem State.guardRead_pos (s : State) (addr len : Nat) (k : State → State)
    (h : len = 0 ∨ s.regions.containsRange addr len = true) :
    s.guardRead addr len k = k s := if_pos h

/-- The fault branch of `guardRead`: a non-empty out-of-region range collapses
    the guard to `accessFault`. The opaque counterpart of `guardRead_pos` —
    rewriting with this (rather than `simp only [State.guardRead, if_neg h]`)
    keeps the 16-field `State` record folded, which is what makes
    `guardSlices_eq` elaborate in milliseconds instead of exhausting memory. -/
theorem State.guardRead_neg (s : State) (addr len : Nat) (k : State → State)
    (h : ¬(len = 0 ∨ s.regions.containsRange addr len = true)) :
    s.guardRead addr len k = s.accessFault := if_neg h

theorem State.guardWrite_pos (s : State) (addr len : Nat) (k : State → State)
    (h : len = 0 ∨ s.regions.containsWritable addr len = true) :
    s.guardWrite addr len k = k s := if_pos h

/-- A guard never touches `regs` beyond what its continuation does, so the
    read-only frame pointer is preserved in both branches. -/
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

/-- Region-gated read guard for a `SliceDesc { ptr : u64, len : u64 }[count]`
    descriptor array at `descsAddr`. Walks the `count` 16-byte descriptors,
    reading each `(ptr, len)` from `s.mem`, and routes every slice read
    `[ptr, ptr+len)` through `guardRead`. Faults with an access violation on
    the first out-of-region slice; runs `k s` once every slice is covered.

    Mirrors the per-slice loop agave runs AFTER translating the descriptor
    array itself: `for val in vals { translate_vm_slice(val, ...)? }` in
    `SyscallHash` / `SyscallLogData` (`agave-syscalls-4.0.0-rc.0`). The
    descriptor array `[descsAddr, descsAddr + count*16)` is guarded
    separately by the caller (agave's `translate_slice::<VmSlice<u8>>` of
    the array precedes this loop). A `guardRead` miss never mutates `s`, so
    each descriptor is read against the same memory the caller saw. -/
def State.guardSlices (s : State) (descsAddr count : Nat) (k : State → State) : State :=
  (List.range count).foldr
    (fun i (kont : State → State) (s' : State) =>
      s'.guardRead (Memory.readU64 s'.mem (descsAddr + i * 16))
        (Memory.readU64 s'.mem (descsAddr + i * 16 + 8)) kont)
    k s

/-- The descriptor walk either faults (some slice out of region) or runs
    its continuation on the unmodified state — the reads never change `s`,
    so the success state is exactly `k s` and the fault state is exactly
    `s.accessFault`. This is the keystone the `Bounded` sweeps and the
    syscall fault lemmas reuse: it collapses the recursive guard to a
    two-way case without unfolding the `foldr`. -/
theorem State.guardSlices_eq (s : State) (descsAddr count : Nat) (k : State → State) :
    s.guardSlices descsAddr count k = s.accessFault
      ∨ s.guardSlices descsAddr count k = k s := by
  simp only [State.guardSlices]
  generalize List.range count = l
  induction l with
  | nil => right; rfl
  | cons i t ih =>
    -- `rw`, NOT `simp only [List.foldr_cons]`: the latter re-traverses the
    -- beta-reduced term and builds congruence lemmas over the 16-field `State`,
    -- blowing elaboration up to ~10GB. `rw` does the single keyed rewrite and
    -- leaves the goal in `s.guardRead …` form directly.
    rw [List.foldr_cons]
    by_cases hc :
        Memory.readU64 s.mem (descsAddr + i * 16 + 8) = 0
          ∨ s.regions.containsRange (Memory.readU64 s.mem (descsAddr + i * 16))
              (Memory.readU64 s.mem (descsAddr + i * 16 + 8)) = true
    · rw [State.guardRead_pos _ _ _ _ hc]; exact ih
    · rw [State.guardRead_neg _ _ _ _ hc]; left; rfl

/-- A register predicate that holds on `s.regs` and on the continuation's
    result holds on a guarded read's result (fault keeps `s.regs`; success is
    `(k s).regs`). Lets `Bounded` discharge a guarded syscall's `regs` bound by
    `apply`-ing the guard away and proving the two leaf states. -/
theorem State.guardRead_regs_of_k {motive : RegFile → Prop} (s : State)
    (addr len : Nat) (k : State → State)
    (h0 : motive s.regs) (hk : motive (k s).regs) :
    motive (s.guardRead addr len k).regs := by
  simp only [State.guardRead]; split
  · exact hk
  · exact h0

/-- The descriptor-walk analog of `guardRead_regs_of_k`: a register predicate
    surviving both leaves survives the whole walk. -/
theorem State.guardSlices_regs_of_k {motive : RegFile → Prop} (s : State)
    (descsAddr count : Nat) (k : State → State)
    (h0 : motive s.regs) (hk : motive (k s).regs) :
    motive (s.guardSlices descsAddr count k).regs := by
  rcases s.guardSlices_eq descsAddr count k with h | h <;> rw [h]
  · exact h0
  · exact hk

/-- A guarded read leaves `mem` exactly as its continuation does when the
    continuation itself preserves `mem` (the fault branch never writes). -/
theorem State.guardRead_mem_eq_of_k (s : State) (addr len : Nat) (k : State → State)
    (hk : ∀ s', (k s').mem = s'.mem) :
    (s.guardRead addr len k).mem = s.mem := by
  simp only [State.guardRead]; split
  · exact hk s
  · rfl

/-- The descriptor walk only reads memory, so a `mem`-preserving continuation
    makes the whole walk `mem`-preserving. -/
theorem State.guardSlices_mem_eq_of_k (s : State) (descsAddr count : Nat)
    (k : State → State) (hk : ∀ s', (k s').mem = s'.mem) :
    (s.guardSlices descsAddr count k).mem = s.mem := by
  rcases s.guardSlices_eq descsAddr count k with h | h <;> rw [h]
  · rfl
  · exact hk s

/-- Generic field-projection collapse for `guardRead`: any projection `f` that
    is invariant under both a guard miss (`accessFault`) and the continuation
    is invariant under the whole guard. The field-agnostic core the syscall
    `preserves_{callStack,regions,cuBudget,heapNext,returnData,r10}` sweeps use
    to close their guarded-syscall arms without unfolding `guardSlices`. -/
theorem State.guardRead_proj_eq_of_k {α} (f : State → α) (s : State)
    (addr len : Nat) (k : State → State)
    (hfault : f s.accessFault = f s) (hk : f (k s) = f s) :
    f (s.guardRead addr len k) = f s := by
  simp only [State.guardRead]; split
  · exact hk
  · exact hfault

/-- The descriptor-walk analog of `guardRead_proj_eq_of_k`: a projection
    invariant under a miss and the continuation is invariant under the walk. -/
theorem State.guardSlices_proj_eq_of_k {α} (f : State → α) (s : State)
    (descsAddr count : Nat) (k : State → State)
    (hfault : f s.accessFault = f s) (hk : f (k s) = f s) :
    f (s.guardSlices descsAddr count k) = f s := by
  rcases s.guardSlices_eq descsAddr count k with h | h <;> rw [h]
  · exact hfault
  · exact hk

/-- `guardWrite` analog of `guardRead_proj_eq_of_k` (the output-write guard the
    hash family checks first). -/
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

/-- Memory-bound propagation through a guard: a per-byte bound surviving both
    the fault state (`accessFault` keeps `s.mem`) and the continuation survives
    the whole guard. The bound counterpart of `guardRead_mem_eq_of_k`, used by
    the `Bounded` `mem_lt` sweep for guarded mem-writing syscalls (the hash
    family writes a digest, so its `mem` is NOT preserved — only bounded). -/
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

/-- The descriptor-walk analog: a per-byte mem bound surviving a miss and the
    continuation survives the whole walk. -/
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

/-- When the sum fits in 64 bits, `wrapAdd` is ordinary addition. Used
    to expose a lifted credit (`dst := wrapAdd dst amount`) as the clean
    `dst + amount` once a no-overflow guard is supplied. -/
theorem wrapAdd_of_lt {a b : Nat} (h : a + b < 2 ^ 64) : wrapAdd a b = a + b := by
  simp only [wrapAdd, U64_MODULUS]
  exact Nat.mod_eq_of_lt h

/-- When the subtrahend doesn't exceed the minuend (no underflow) and
    the minuend fits in 64 bits, `wrapSub` is ordinary subtraction. Used
    to expose a lifted debit (`src := wrapSub src amount`) as the clean
    `src - amount` once a sufficient-funds guard is supplied. -/
theorem wrapSub_of_le {a b : Nat} (hle : b ≤ a) (ha : a < 2 ^ 64) :
    wrapSub a b = a - b := by
  simp only [wrapSub, U64_MODULUS]
  rw [Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega),
      show a + 2 ^ 64 - b = (a - b) + 2 ^ 64 by omega, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

/-- `toU64 1` is the Nat literal `1` (the immediate `1` sign-extends to
    `1`). Lets a constant-`+1` credit (`cell := wrapAdd v (toU64 1)`) clean
    to `v + 1` the way `wrapAdd_of_lt` cleans a loaded-amount credit. -/
theorem toU64_one : toU64 1 = 1 := by decide

/-- When the sum fits in 64 bits, a `+1` `wrapAdd` is ordinary `· + 1`.
    The constant-delta counterpart of `wrapAdd_of_lt`, used by the
    balance-corollary codegen for `counter += 1` handlers. -/
theorem wrapAdd_one_of_lt {a : Nat} (h : a + 1 < 2 ^ 64) :
    wrapAdd a (toU64 1) = a + 1 := by
  rw [toU64_one]; exact wrapAdd_of_lt h

/-- 32-bit modulus for 32-bit ALU operations -/
def U32_MODULUS : Nat := 2 ^ 32

/-- Sign-extend a value already reduced mod 2^32 into a 64-bit register.
    For sBPF V0/V1 the 32-bit ADD/SUB/MUL results are sign-extended:
    solana-sbpf computes `(x as i32).wrapping_op(y) as i64 as u64`
    (`explicit_sign_extension_of_results` is V2-only, where it instead
    zero-extends). If bit 31 of `n` is set, the upper 32 bits become 1s.
    See docs/SOUNDNESS_AUDIT_* (C1). -/
@[simp] def signExtend32 (n : Nat) : Nat :=
  if n < 0x80000000 then n else n + (U64_MODULUS - U32_MODULUS)

-- ADD32 / SUB32 / MUL32 sign-extend their i32 result into the 64-bit
-- destination (V0/V1 semantics). The other 32-bit ALU ops (OR/AND/XOR,
-- shifts, MOV32, DIV32, MOD32, NEG32) zero-extend — see those arms.
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

Used by syscall bodies to pull byte arrays out of program memory and
write byte arrays back. Live alongside `Mem` so the syscall-body
modules don't have to depend on `Execute.lean`. -/

/-- Read `len` bytes from `mem` starting at `addr` into a `ByteArray`. -/
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

/-- `readBytes` recovers `bs` exactly when (a) sizes match and (b) each
    byte of `bs` matches the corresponding byte of memory mod 256.
    Used by syscall specs that pull a fixed-length blob (pubkey, hash,
    output buffer) out of caller memory under SL ownership. -/
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
    -- Goal: (mem (addr + i) % 256).toUInt8 = bs.data[i]
    have hmem := hb i hi
    -- hmem : mem (addr + i) % 256 = (bs.get! i).toNat
    have h_get : bs.get! i = bs.data[i] := by
      show bs.data[i]! = bs.data[i]
      exact getElem!_pos bs.data i hbsize
    rw [hmem]
    -- Goal: (bs.get! i).toNat.toUInt8 = bs.data[i]
    show UInt8.ofNat (bs.get! i).toNat = bs.data[i]
    rw [UInt8.ofNat_toNat, h_get]


/-- Read `n` 16-byte `SliceDesc { ptr: u64, len: u64 }` descriptors
    starting at `descsAddr`, deref each to its referenced bytes, and
    concatenate them. This is the standard input shape for the
    hash family (`sol_sha256` / `sol_sha512` / `sol_keccak256` /
    `sol_blake3` / `sol_poseidon`). -/
def readSlices (mem : Memory.Mem) (descsAddr n : Nat) : ByteArray :=
  (List.range n).foldl (fun acc i =>
    let descAddr := descsAddr + i * 16
    let ptr := Memory.readU64 mem descAddr
    let len := Memory.readU64 mem (descAddr + 8)
    acc ++ readBytes mem ptr len) ByteArray.empty

/-- Sum the `len` fields across `n` `SliceDesc { ptr, len }` descriptors
    starting at `descsAddr`. Cheaper than `readSlices …  |>.size` because
    it skips dereferencing the slice bytes. -/
def sumSliceLens (mem : Memory.Mem) (descsAddr n : Nat) : Nat :=
  (List.range n).foldl (fun acc i =>
    let descAddr := descsAddr + i * 16
    acc + Memory.readU64 mem (descAddr + 8)) 0

/-- Per-slice cost used by the hash family (sha256 / sha512 / keccak /
    blake3). Mirrors agave's
    `mem_op_base_cost.max(sha256_byte_cost.saturating_mul(len / 2))`
    applied to each slice individually — *not* a sum-of-lengths
    multiplied by byte_cost. Sum is then added to the syscall's
    base cost (85). See `blueshift/sbpf/crates/runtime/src/syscalls/crypto.rs:83-86`. -/
def hashSliceCost (mem : Memory.Mem) (descsAddr n : Nat) : Nat :=
  (List.range n).foldl (fun acc i =>
    let descAddr := descsAddr + i * 16
    let len := Memory.readU64 mem (descAddr + 8)
    acc + Nat.max 10 (len / 2)) 0

/-- Memory update that writes the first `len` bytes of `bs` to address
    `out`, leaving everything else untouched. Equivalent to the old
    inline `fun a => if a ≥ out ∧ a - out < len then bs.get! (a - out)
    else mem a` shape repeated across every crypto syscall body.

    Writes byte-by-byte into the `Mem` overlay so subsequent reads
    take the O(1) HashMap path instead of walking a closure chain. -/
def writeBytes (mem : Memory.Mem) (out len : Nat) (bs : ByteArray) : Memory.Mem :=
  (List.range len).foldl
    (fun m i => Memory.writeU8 m (out + i) (bs.get! i).toNat) mem

/-- Reading `writeBytes` at an address outside the written window is
    transparent. Replaces the old `unfold writeBytes; rw [if_neg ...]`
    pattern in `InstructionSpecs.lean` (proofs that the
    `Pda.createProgramAddress` write doesn't touch memory beyond
    `[r4V, r4V + 32)`). The new fold-based body has no `if` to peel,
    so this lemma takes its place. -/
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

/-- Reading `writeBytes` at an address inside the written window
    returns the corresponding byte from `bs`. Replaces the old
    `unfold writeBytes; rw [if_pos ...]` pattern — the new
    fold-based body has no `if` to peel.

    Requires `bs.get! j` to be < 256 (always true since `ByteArray.get!`
    returns `UInt8`), which is needed because the underlying
    `writeU8` stores `val % 256`. -/
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

/-- The agave hash-syscall write envelope (sha256 / sha512 / keccak256 /
    blake3): check the fixed-size OUTPUT region FIRST (`translate_slice_mut`,
    agave's order), then the input descriptor array, then each input slice; on
    success write `digest` to `[outPtr, outPtr+outLen)` and set `r0 := 0`. A
    guard miss at any layer traps with a typed access violation.

    Deliberately *not* `@[simp]`: the recursive `guardSlices` walk inside must
    stay folded so the blanket `Bounded`/`Execute` syscall sweeps don't choke
    on it (the `sol_log_data` lesson). The `@[simp]` field-preservation lemmas
    below close those sweeps with `hashWrite` folded; `regs_lt`/`mem_lt` use the
    dedicated `hashWrite_regs_of_k` / `hashWrite_mem_lt` closers.

    `@[irreducible]`: the `Bounded` `regs_lt`/`mem_lt` sweeps close the hash arms
    by an `exact hashWrite_{regs_of_k,mem_lt} …` inside a `first` block that is
    also tried (and must fail) on every other syscall's fall-through leaf.
    Without irreducibility, `exact` whnf-unfolds this `def` (5 metavars) against
    big non-hash goals to discover the head mismatch — ~160s across the sweep.
    Irreducible ⇒ the head stays `hashWrite`, so the match succeeds on hash arms
    and fails instantly elsewhere. simp still unfolds it via its equation lemma
    (the field lemmas below), and the compiler still runs it (diff tests). -/
@[irreducible] def State.hashWrite (s : State) (outPtr outLen inPtr inN : Nat)
    (digest : ByteArray) : State :=
  s.guardWrite outPtr outLen fun s =>
    s.guardRead inPtr (inN * 16) fun s =>
      s.guardSlices inPtr inN fun s =>
        { s with regs := s.regs.set .r0 0
                 mem  := writeBytes s.mem outPtr outLen digest }

/-- `hashWrite` only rewrites `regs` (to set `r0`) and `mem` (the digest write);
    every other `State` field is preserved on the fault branch (`accessFault`)
    and the success branch. `@[simp]` so the blanket sweeps close every hash arm
    with `hashWrite` left folded (one set of lemmas covers all four hashes). -/
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

/-- `hashWrite`'s `regs` is either `s.regs` (a guard faulted) or `s.regs.set .r0 0`
    (success) — a register predicate surviving both survives `hashWrite`. The
    `Bounded` `regs_lt` closer for the hash arms. -/
theorem State.hashWrite_regs_of_k {motive : RegFile → Prop} (s : State)
    (outPtr outLen inPtr inN : Nat) (digest : ByteArray)
    (h0 : motive s.regs) (hk : motive (s.regs.set .r0 0)) :
    motive (s.hashWrite outPtr outLen inPtr inN digest).regs := by
  simp only [State.hashWrite]
  apply State.guardWrite_regs_of_k (motive := motive) (h0 := h0)
  apply State.guardRead_regs_of_k (motive := motive) (h0 := h0)
  apply State.guardSlices_regs_of_k (motive := motive) (h0 := h0)
  exact hk

/-- Commit an `Option ByteArray` result to state: success writes the
    bytes to `*out` (sized `outSize`) and sets `r0 := 0`; failure sets
    `r0 := 1` and leaves memory unchanged. The 0/1 convention matches
    agave's `SyscallError`-to-u64 mapping used by the curve / pairing
    / big-mod-exp / poseidon / PDA syscalls.

    Deliberately *not* `@[simp]` — unfolding this across 44 syscall
    arms during `execSyscall_preserves_r10` blows up simp. Instead
    we ship the targeted `commitOptional_preserves_r10` lemma below;
    that single rewrite closes the r10-preservation goal for any
    syscall whose body ends in `commitOptional`. -/
def commitOptional (s : State) (out outSize : Nat)
    (result : Option ByteArray) : State :=
  match result with
  | some bs => { s with regs := s.regs.set .r0 0
                        mem  := writeBytes s.mem out outSize bs }
  | none    => { s with regs := s.regs.set .r0 1 }

/-- `commitOptional` preserves r10 in both arms. Marked `@[simp]` so
    syscall arms ending in `commitOptional s ...` discharge by a
    single rewrite without unfolding the whole function. -/
@[simp] theorem commitOptional_preserves_r10 (s : State) (out outSize : Nat)
    (result : Option ByteArray) :
    (commitOptional s out outSize result).regs.r10 = s.regs.r10 := by
  cases result <;> simp [commitOptional]

/-- `commitOptional` preserves the region table in both arms. Same
    shape as `commitOptional_preserves_r10` — marked `@[simp]` so the
    region-bounds invariant flows through any syscall ending in
    `commitOptional` (PDA, curve ops, big-mod-exp, poseidon, …). -/
@[simp] theorem commitOptional_preserves_regions (s : State) (out outSize : Nat)
    (result : Option ByteArray) :
    (commitOptional s out outSize result).regions = s.regions := by
  cases result <;> simp [commitOptional]

/-- `commitOptional` preserves the returnData buffer in both arms.
    Marked `@[simp]` so specs that own `returnDataIs` can frame the
    buffer through PDA / curve / poseidon / big-mod-exp syscalls. -/
@[simp] theorem commitOptional_preserves_returnData (s : State) (out outSize : Nat)
    (result : Option ByteArray) :
    (commitOptional s out outSize result).returnData = s.returnData := by
  cases result <;> simp [commitOptional]

/-- `commitOptional` preserves the call stack in both arms. Marked
    `@[simp]` so specs that own `callStackIs` can frame the stack
    through PDA / curve / poseidon / big-mod-exp syscalls. -/
@[simp] theorem commitOptional_preserves_callStack (s : State) (out outSize : Nat)
    (result : Option ByteArray) :
    (commitOptional s out outSize result).callStack = s.callStack := by
  cases result <;> simp [commitOptional]

end SVM.SBPF
