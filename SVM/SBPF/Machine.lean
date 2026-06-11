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
  /-- Side channel: messages written via `sol_log_*` syscalls.
      Each entry is one message. Observable from the runner; not owned
      by any separation-logic assertion. -/
  log : Array ByteArray := #[]
  /-- Side channel: return-data buffer set by `sol_set_return_data` and
      read by `sol_get_return_data`. -/
  returnData : ByteArray := ByteArray.empty
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

/-- `MAX_RETURN_DATA` (agave): a program may set at most 1024 bytes of
    return data; a larger `sol_set_return_data` aborts. -/
def MAX_RETURN_DATA : Nat := 1024

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
