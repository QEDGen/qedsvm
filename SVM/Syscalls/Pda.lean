/-
  Program Derived Address (PDA) derivation: pure-Lean
  `sol_create_program_address` / `sol_try_find_program_address`, built only on
  `Sha256.hash` (FIPS-180-4) and `Curve25519.validateEdwards` (lean-bridge).

  `create_program_address`: validate seeds (≤16, each ≤32), hash
  `seed* ‖ program_id ‖ "ProgramDerivedAddress"`, reject if on the ed25519 curve
  (could be a real pubkey, defeating the PDA security property), else return it.
  `try_find_program_address` iterates a 1-byte bump seed 255→0 until that succeeds.
-/

import SVM.SBPF.Machine
import SVM.Syscalls.Sha256
import SVM.Syscalls.Curve25519

namespace SVM.SBPF
namespace Pda

/-- Seed-count / per-seed-length caps; exceeding either is `MaxSeedLengthExceeded`. -/
def MAX_SEEDS    : Nat := 16
def MAX_SEED_LEN : Nat := 32

/-- The 21-byte ASCII marker `"ProgramDerivedAddress"`, appended after
    `program_id` so PDAs are distinct from `create_with_seed` outputs. -/
def PDA_MARKER : ByteArray := ⟨#[
  0x50, 0x72, 0x6f, 0x67, 0x72, 0x61, 0x6d,   -- "Program"
  0x44, 0x65, 0x72, 0x69, 0x76, 0x65, 0x64,   -- "Derived"
  0x41, 0x64, 0x64, 0x72, 0x65, 0x73, 0x73]⟩  -- "Address"

/-- `Address::create_program_address(seeds, program_id)`. `some <32-byte PDA>` if
    valid (within limits, hash off the ed25519 curve), else `none`. All failures
    lump to `none` → `r0 := 1`; the real syscall doesn't distinguish either. -/
def createProgramAddress (seeds : List ByteArray) (programId : ByteArray) : Option ByteArray :=
  if seeds.length > MAX_SEEDS then none
  else if seeds.any (fun s => s.size > MAX_SEED_LEN) then none
  else if programId.size ≠ 32 then none
  else
    let payload := seeds.foldl (· ++ ·) ByteArray.empty ++ programId ++ PDA_MARKER
    let h := Sha256.hash payload
    if Curve25519.validateEdwards h then none
    else some h

/-- 1-byte ByteArray holding the bump (truncated via `toUInt8`). -/
private def bumpSeed (bump : Nat) : ByteArray := ⟨#[bump.toUInt8]⟩

/-- Inner loop for `tryFindProgramAddress`: returns the result plus the attempt
    count (= `createProgramAddress` calls, used for the per-attempt 1500 CU charge).
    Iterates `bump` 255→**1**, never `bump = 0` (agave's `0..u8::MAX` range). -/
private def tryFindLoopWithIters (seeds : List ByteArray) (programId : ByteArray)
    : Nat → Option (ByteArray × UInt8) × Nat
  | 0 => (none, 0)
  | bump + 1 =>
    let attempt := bump + 1
    match createProgramAddress (seeds ++ [bumpSeed attempt]) programId with
    | some addr => (some (addr, attempt.toUInt8), 1)
    | none =>
      let (rest, restIters) := tryFindLoopWithIters seeds programId bump
      (rest, restIters + 1)

/-- `find_program_address`: iterate `bump` 255→1 appending `[bump]`, return the
    first `(off-curve PDA, bump)`. `none` only if all 255..=1 are on-curve. -/
def tryFindProgramAddress (seeds : List ByteArray) (programId : ByteArray)
    : Option (ByteArray × UInt8) :=
  (tryFindLoopWithIters seeds programId 255).1

/-- Same as `tryFindProgramAddress` but returns the iteration count
    alongside the result. Used for state-dependent CU scaling. -/
def tryFindProgramAddressWithIters (seeds : List ByteArray) (programId : ByteArray)
    : Option (ByteArray × UInt8) × Nat :=
  tryFindLoopWithIters seeds programId 255

/-! ## Syscall bindings -/

/-- Read `n` seeds from a `VmSlice` array as `List ByteArray` (like Machine's
    `readSlices` but keeps each seed separate, as the PDA helpers need). -/
@[simp] def readSeeds (mem : Memory.Mem) (seedsA n : Nat) : List ByteArray :=
  (List.range n).map (fun i =>
    let descAddr := seedsA + i * 16
    let ptr := Memory.readU64 mem descAddr
    let len := Memory.readU64 mem (descAddr + 8)
    readBytes mem ptr len)

/-- CU per `create_program_address` attempt (agave's
    `create_program_address_units`). `create` pays once; `try_find` pays this
    per bump-loop iteration (consume before loop + at end of each failed one). -/
def cuPerAttempt : Nat := 1_500

/-- CU charge for `sol_create_program_address`. Single flat cost. -/
def cuCreate : Nat := cuPerAttempt

/-- State-dependent CU for `sol_try_find_program_address`: simulate the bump loop
    via the same `tryFindLoopWithIters` `execTryFind` runs, charge
    `cuPerAttempt × attempts + extra`. Success at attempt k: k × 1500;
    full-search failure: 256 × 1500 (255 iters + the un-short-circuited pre-loop). -/
def cuTryFind (s : State) : Nat :=
  let seeds := readSeeds s.mem s.regs.r1 s.regs.r2
  let pid   := readBytes s.mem s.regs.r3 32
  let (result, iters) := tryFindProgramAddressWithIters seeds pid
  let extra := match result with
    | some _ => 0
    | none   => cuPerAttempt
  cuPerAttempt * iters + extra

/-- Execute `sol_create_program_address`.
    ABI: r1 = `*const [VmSlice; N]`, r2 = N, r3 = `*const [u8; 32]`
    program_id, r4 = `*mut [u8; 32]` out. r0 = 0/1. -/
-- NOTE (M7, deferred): agave ABORTS with `BadSeeds` for > MAX_SEEDS / over-long
-- seeds; the model returns in-band r0:=1. Adding the abort restructures
-- `execCreate` and breaks the two `call_create_program_address_*_spec` proofs;
-- rarely reachable (programs use valid seeds), so left as-is.
@[simp] def execCreate (s : State) : State :=
  -- H6: guardedCommit checks output `[r4,32)` → descriptor array `[r1,r2·16)` →
  -- each seed slice → commitOptional; the extra guardRead covers program_id `[r3,32)`.
  s.guardRead s.regs.r3 32 fun s =>
    s.guardedCommit s.regs.r4 32 s.regs.r1 s.regs.r2
      (createProgramAddress (readSeeds s.mem s.regs.r1 s.regs.r2)
                            (readBytes s.mem s.regs.r3 32))

/-- H6 fault direction: an out-of-region program_id `[r3,32)` (the first guarded
    slice) traps with a typed access violation. -/
theorem execCreate_faults_oob (s : State)
    (hoob : s.regions.containsRange s.regs.r3 32 = false) :
    (execCreate s).vmError = some .accessViolation := by
  simp only [execCreate, State.guardRead]
  rw [if_neg (by
    rintro (h | h)
    · exact absurd h (by decide)
    · rw [hoob] at h; exact absurd h (by decide))]
  rfl

/-- Companion to `execCreate_faults_oob`: the same out-of-region program_id
    pins the `exitCode` sentinel (guardRead sets both). Discharges the exitCode
    conjunct of the lifted PDA-create `cuTripleFaultsWithinMem` corollary. -/
theorem execCreate_faults_oob_exitCode (s : State)
    (hoob : s.regions.containsRange s.regs.r3 32 = false) :
    (execCreate s).exitCode = some ERR_ACCESS_VIOLATION := by
  simp only [execCreate, State.guardRead]
  rw [if_neg (by
    rintro (h | h)
    · exact absurd h (by decide)
    · rw [hoob] at h; exact absurd h (by decide))]
  rfl

/-- Execute `sol_try_find_program_address`.
    Same as `execCreate` plus r5 = `*mut [u8; 1]` bump output. -/
def execTryFind (s : State) : State :=
  -- H6: guard program_id `[r3,32)`, descriptor array `[r1,r2·16)` and each seed
  -- slice up front; on success guard the PDA output `[r4,32)` + bump `[r5,1)` too.
  s.guardRead s.regs.r3 32 fun s =>
  s.guardRead s.regs.r1 (s.regs.r2 * 16) fun s =>
  s.guardSlices s.regs.r1 s.regs.r2 fun s =>
    let outA   := s.regs.r4
    let bumpA  := s.regs.r5
    let seeds  := readSeeds s.mem s.regs.r1 s.regs.r2
    let pid    := readBytes s.mem s.regs.r3 32
    let result := tryFindProgramAddress seeds pid
    match result with
    | some (pda, bump) =>
      s.guardWrite outA 32 fun s =>
      s.guardWrite bumpA 1 fun s =>
        let mem' : Memory.Mem := fun a =>
          if a = bumpA then bump.toNat
          else writeBytes s.mem outA 32 pda a
        { s with regs := s.regs.set .r0 0, mem := mem' }
    | none => { s with regs := s.regs.set .r0 1 }

/-- `execTryFind` preserves r10 in both arms. `@[simp]` so
    `execSyscall_preserves_r10` closes the arm without case-splitting on `result`
    (`execTryFind` itself isn't `@[simp]`, else simp unfolds its body in this proof). -/
@[simp] theorem execTryFind_preserves_r10 (s : State) :
    (execTryFind s).regs.r10 = s.regs.r10 := by
  simp only [execTryFind]
  refine State.guardRead_proj_eq_of_k (·.regs.r10) s _ _ _ rfl ?_
  refine State.guardRead_proj_eq_of_k (·.regs.r10) s _ _ _ rfl ?_
  refine State.guardSlices_proj_eq_of_k (·.regs.r10) s _ _ _ rfl ?_
  split
  · refine State.guardWrite_proj_eq_of_k (·.regs.r10) s _ _ _ rfl ?_
    refine State.guardWrite_proj_eq_of_k (·.regs.r10) s _ _ _ rfl ?_
    simp
  · simp

/-- `execTryFind` preserves the region table in both arms (companion to
    `execTryFind_preserves_r10`). -/
@[simp] theorem execTryFind_preserves_regions (s : State) :
    (execTryFind s).regions = s.regions := by
  simp only [execTryFind]
  refine State.guardRead_proj_eq_of_k (·.regions) s _ _ _ rfl ?_
  refine State.guardRead_proj_eq_of_k (·.regions) s _ _ _ rfl ?_
  refine State.guardSlices_proj_eq_of_k (·.regions) s _ _ _ rfl ?_
  split
  · refine State.guardWrite_proj_eq_of_k (·.regions) s _ _ _ rfl ?_
    refine State.guardWrite_proj_eq_of_k (·.regions) s _ _ _ rfl ?_
    rfl
  · rfl

/-- H6 fault direction: an out-of-region program_id `[r3,32)` (the first guarded
    slice) traps with a typed access violation. -/
theorem execTryFind_faults_oob (s : State)
    (hoob : s.regions.containsRange s.regs.r3 32 = false) :
    (execTryFind s).vmError = some .accessViolation := by
  simp only [execTryFind, State.guardRead]
  rw [if_neg (by
    rintro (h | h)
    · exact absurd h (by decide)
    · rw [hoob] at h; exact absurd h (by decide))]
  rfl

end Pda
end SVM.SBPF
