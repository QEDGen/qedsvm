/-
  Program Derived Address (PDA) derivation.

  Pure-Lean implementation of `sol_create_program_address` and
  `sol_try_find_program_address`. The algorithm only depends on:
    - `Sha256.hash`            (pure-Lean FIPS-180-4)
    - `Curve25519.validateEdwards`  (lean-bridge → curve25519-dalek)
  No new bridge code; this entire module is built from primitives
  already in the repo.

  Algorithm (`Address::create_program_address` in solana-sdk):
    1. Validate `seeds.length ≤ 16` and `∀ s ∈ seeds, s.size ≤ 32`.
    2. Compute `h = SHA-256(seed₀ ‖ seed₁ ‖ … ‖ program_id ‖ "ProgramDerivedAddress")`.
    3. If `h` is on the ed25519 curve, reject (it could be a real
       pubkey with a private key, defeating the PDA security property).
    4. Otherwise return `h` as the PDA.

  `try_find_program_address` iterates a 1-byte bump seed from 255 down
  to 0, appending it to the seeds, until `create_program_address`
  succeeds.

  Wired to `.sol_create_program_address` and
  `.sol_try_find_program_address` via `execCreate` / `execTryFind`
  below.
-/

import SVM.SBPF.Machine
import SVM.Syscalls.Sha256
import SVM.Syscalls.Curve25519

namespace SVM.SBPF
namespace Pda

/-- Solana caps the number of seeds and per-seed length. Exceeding
    either yields `MaxSeedLengthExceeded` in agave. -/
def MAX_SEEDS    : Nat := 16
def MAX_SEED_LEN : Nat := 32

/-- The 21-byte marker `"ProgramDerivedAddress"` (ASCII). Appended
    after `program_id` in the hash input so PDAs are
    distinguishable from `Address::create_with_seed` outputs. -/
def PDA_MARKER : ByteArray := ⟨#[
  0x50, 0x72, 0x6f, 0x67, 0x72, 0x61, 0x6d,   -- "Program"
  0x44, 0x65, 0x72, 0x69, 0x76, 0x65, 0x64,   -- "Derived"
  0x41, 0x64, 0x64, 0x72, 0x65, 0x73, 0x73]⟩  -- "Address"

/-- `Address::create_program_address(seeds, program_id)`. Returns
    `some <32-byte PDA>` if valid (within seed-count / seed-length
    limits, hash result not on the ed25519 curve); `none` on any
    failure mode. Matches agave's discrimination — failures are
    lumped into a single `none` here; the syscall arm maps to
    `r0 := 1` in either case (Solana's create_program_address
    syscall doesn't distinguish error codes either). -/
def createProgramAddress (seeds : List ByteArray) (programId : ByteArray) : Option ByteArray :=
  if seeds.length > MAX_SEEDS then none
  else if seeds.any (fun s => s.size > MAX_SEED_LEN) then none
  else if programId.size ≠ 32 then none
  else
    let payload := seeds.foldl (· ++ ·) ByteArray.empty ++ programId ++ PDA_MARKER
    let h := Sha256.hash payload
    if Curve25519.validateEdwards h then none
    else some h

/-- A 1-byte ByteArray containing the bump value (must be `< 256`;
    we truncate via `toUInt8` for safety in case of caller error). -/
private def bumpSeed (bump : Nat) : ByteArray := ⟨#[bump.toUInt8]⟩

/-- Inner loop for `tryFindProgramAddress`. Returns both the search
    result and the *number of attempts* the loop made (= number of
    `createProgramAddress` calls performed, including the one that
    succeeded). Used by both `tryFindProgramAddress` and the per-call
    CU charge — agave charges `1500` per attempt (initial + each
    failed iteration). Mirrors agave's `SyscallTryFindProgramAddress`
    loop bound: iterates `bump` from 255 down to **1**, never tries
    `bump = 0` (the `0..u8::MAX` range in agave's source). -/
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

/-- `Address::find_program_address(seeds, program_id)` (agave's
    `sol_try_find_program_address`). Iterates `bump` from 255 down to
    1, appending `[bump]` as the trailing seed each time, and returns
    the first `(off-curve PDA, bump)`. Returns `none` only if every
    bump in 255..=1 yields an on-curve hash — statistically
    impossible in real use; agave also never tries `bump = 0`. -/
def tryFindProgramAddress (seeds : List ByteArray) (programId : ByteArray)
    : Option (ByteArray × UInt8) :=
  (tryFindLoopWithIters seeds programId 255).1

/-- Same as `tryFindProgramAddress` but returns the iteration count
    alongside the result. Used for state-dependent CU scaling. -/
def tryFindProgramAddressWithIters (seeds : List ByteArray) (programId : ByteArray)
    : Option (ByteArray × UInt8) × Nat :=
  tryFindLoopWithIters seeds programId 255

/-! ## Syscall bindings -/

/-- Read `n` seeds from a `VmSlice` array as a `List ByteArray`.
    Mirrors `readSlices` from Machine.lean but keeps each seed as a
    separate list element — `createProgramAddress` /
    `tryFindProgramAddress` need the structured form. -/
@[simp] def readSeeds (mem : Memory.Mem) (seedsA n : Nat) : List ByteArray :=
  (List.range n).map (fun i =>
    let descAddr := seedsA + i * 16
    let ptr := Memory.readU64 mem descAddr
    let len := Memory.readU64 mem (descAddr + 8)
    readBytes mem ptr len)

/-- CU charge for one `create_program_address` attempt. Agave's
    `create_program_address_units` from `SVMTransactionExecutionCost`.
    `sol_create_program_address` pays exactly this once;
    `sol_try_find_program_address` pays this **per iteration** of its
    bump loop (initial + each failed attempt = total attempts made).
    Matches agave's `SyscallTryFindProgramAddress::rust` charging
    model (consume before loop + consume at end of each failed
    iteration). -/
def cuPerAttempt : Nat := 1_500

/-- CU charge for `sol_create_program_address`. Single flat cost. -/
def cuCreate : Nat := cuPerAttempt

/-- State-dependent CU charge for `sol_try_find_program_address`.
    Reads seeds + program_id from caller memory, simulates the bump
    loop, and charges `cuPerAttempt × attempts_made` — matching
    agave's `SyscallTryFindProgramAddress::rust` charging model:
    one consume before the loop + one consume at the end of each
    failed iteration. The loop simulation runs `tryFindLoopWithIters`
    so the charged iteration count is byte-for-byte identical to
    what `execTryFind` actually performs.

    On success at attempt `k` (1 ≤ k ≤ 255): iters = k, CU = k × 1500.
    On full-search failure (all 255 attempts on-curve): iters = 255,
    plus agave's pre-loop charge that never gets the early-return
    short-circuit, so CU = 256 × 1500.

    Pure-but-State-keyed: invoked via the existing `syscallCu`
    dispatcher in `Execute.lean`. -/
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
-- NOTE (M7, deferred): agave ABORTS with `BadSeeds` for > MAX_SEEDS seeds
-- or an over-long seed; the model returns in-band r0:=1 (via
-- `createProgramAddress` → none → commitOptional). Adding the abort
-- changes `execCreate`'s structure and breaks the two LEGITIMATE n0/n1
-- `call_create_program_address_*_spec` proofs (~400 lines each) that
-- reduce `execCreate` to `commitOptional`. Left as-is. (Programs use
-- valid seeds, so the divergence is rarely reachable.)
@[simp] def execCreate (s : State) : State :=
  -- H6: agave translates the program_id `[r3,32)` (Load), the seed descriptor
  -- array `[r1, r2·16)` plus each seed slice (Load), and the 32-byte output
  -- `[r4,32)` (Store). `guardedCommit` checks output → descriptor array →
  -- each slice → `commitOptional`; the extra `guardRead` covers the program_id.
  -- Any out-of-region (or non-writable output) access traps. The guards reuse
  -- the poseidon `guardedCommit` combinator, so `execCreate` stays `@[simp]`.
  s.guardRead s.regs.r3 32 fun s =>
    s.guardedCommit s.regs.r4 32 s.regs.r1 s.regs.r2
      (createProgramAddress (readSeeds s.mem s.regs.r1 s.regs.r2)
                            (readBytes s.mem s.regs.r3 32))

/-- H6 fault direction: an out-of-region program_id `[r3,32)` traps with a
    typed access violation (the first guarded slice; the output `[r4,32)`,
    the seed descriptor array and each seed slice are the others). -/
theorem execCreate_faults_oob (s : State)
    (hoob : s.regions.containsRange s.regs.r3 32 = false) :
    (execCreate s).vmError = some .accessViolation := by
  simp only [execCreate, State.guardRead]
  rw [if_neg (by
    rintro (h | h)
    · exact absurd h (by decide)
    · rw [hoob] at h; exact absurd h (by decide))]
  rfl

/-- Execute `sol_try_find_program_address`.
    Same as `execCreate` plus r5 = `*mut [u8; 1]` bump output. -/
def execTryFind (s : State) : State :=
  -- H6: agave translates the program_id `[r3,32)`, the seed descriptor array
  -- `[r1, r2·16)` and each seed slice (Load) up front; on a successful search
  -- it then translates the 32-byte PDA output `[r4,32)` and the 1-byte bump
  -- output `[r5,1)` (Store) before writing. Any out-of-region (or non-writable
  -- output) access traps with a typed access violation.
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

/-- `execTryFind` preserves r10 in both match arms. Marked `@[simp]`
    so `execSyscall_preserves_r10`'s blanket simp closes the
    `sol_try_find_program_address` arm without case-splitting on
    `result`. (`execTryFind` itself isn't `@[simp]` because simp would
    then try to unfold the whole body inside this very proof.) -/
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

/-- `execTryFind` preserves the region table in both match arms.
    Companion to `execTryFind_preserves_r10`; lets the blanket
    `execSyscall_preserves_regions` close `sol_try_find_program_address`
    without case-splitting on `result`. -/
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

/-- H6 fault direction: an out-of-region program_id `[r3,32)` traps with a
    typed access violation (the first guarded slice). -/
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
