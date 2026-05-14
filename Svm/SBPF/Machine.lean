-- Machine state for sBPF execution: registers, call frames, top-level State,
-- runtime error codes, and the wrapping-arithmetic helpers.
--
-- Lifted out of Execute.lean so syscall-body modules (Sha256.lean,
-- Keccak256.lean, …) can spell `def exec : State → State` without an
-- import cycle through the dispatcher.

import Svm.SBPF.ISA
import Svm.SBPF.Memory

namespace Svm.SBPF

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
theorem RegFile.get_set_diff (rf : RegFile) (r1 r2 : Reg) (v : Nat) (h : r1 ≠ r2) :
    (rf.set r2 v).get r1 = rf.get r1 := by
  cases r1 <;> cases r2 <;> simp_all [RegFile.get, RegFile.set]

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
      Top-level CU reporting in `Svm/Ffi.lean` is
      `(cuBudget - fuelRemaining) + s.cuConsumed`. -/
  cuConsumed : Nat := 0
  /-- Bump-allocator pointer for `sol_alloc_free_`. Starts at
      `MM_HEAP_START` (`0x300000000`) and grows upward as allocations
      happen. Tier-2 #6 — the BPF program-local heap. Reset to
      `MM_HEAP_START` on each CPI sub-state since agave allocates the
      heap fresh per invocation. -/
  heapNext : Nat := 0x300000000
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

/-! ## Wrapping 64-bit arithmetic -/

@[simp] def wrapAdd (a b : Nat) : Nat := (a + b) % U64_MODULUS
@[simp] def wrapSub (a b : Nat) : Nat := (a + U64_MODULUS - b % U64_MODULUS) % U64_MODULUS
@[simp] def wrapMul (a b : Nat) : Nat := (a * b) % U64_MODULUS
@[simp] def wrapNeg (a : Nat) : Nat := (U64_MODULUS - a % U64_MODULUS) % U64_MODULUS

/-- 32-bit modulus for 32-bit ALU operations -/
def U32_MODULUS : Nat := 2 ^ 32

@[simp] def wrapAdd32 (a b : Nat) : Nat := (a + b) % U32_MODULUS
@[simp] def wrapSub32 (a b : Nat) : Nat := (a + U32_MODULUS - b % U32_MODULUS) % U32_MODULUS
@[simp] def wrapMul32 (a b : Nat) : Nat := (a * b) % U32_MODULUS
@[simp] def wrapNeg32 (a : Nat) : Nat := (U32_MODULUS - a % U32_MODULUS) % U32_MODULUS

/-! ## Byte-region helpers for syscall bodies

Used by syscall bodies to pull byte arrays out of program memory and
write byte arrays back. Live alongside `Mem` so the syscall-body
modules don't have to depend on `Execute.lean`. -/

/-- Read `len` bytes from `mem` starting at `addr` into a `ByteArray`. -/
def readBytes (mem : Memory.Mem) (addr len : Nat) : ByteArray :=
  ⟨(List.range len).foldl
    (fun acc i => acc.push (mem (addr + i) % 256).toUInt8) #[]⟩

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
    `out`, leaving everything else untouched. Equivalent to the
    inline `fun a => if a ≥ out ∧ a - out < len then bs.get! (a - out)
    else mem a` shape repeated across every crypto syscall body. -/
def writeBytes (mem : Memory.Mem) (out len : Nat) (bs : ByteArray) : Memory.Mem :=
  fun a =>
    if a ≥ out ∧ a - out < len then (bs.get! (a - out)).toNat
    else mem a

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

end Svm.SBPF
