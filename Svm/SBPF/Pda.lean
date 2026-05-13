/-
  Program Derived Address (PDA) derivation.

  Pure-Lean implementation of `sol_create_program_address` and
  `sol_try_find_program_address`. The algorithm only depends on:
    - `Sha256.hash`            (pure-Lean FIPS-180-4)
    - `Curve25519.validateEdwards`  (rust-bridge → curve25519-dalek)
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

import Svm.SBPF.Machine
import Svm.SBPF.Sha256
import Svm.SBPF.Curve25519

namespace Svm.SBPF
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

/-- Inner loop for `tryFindProgramAddress`. Recurses on `fuel` (an
    explicit bound for structural recursion). Each iteration appends
    `[bump]` as an extra seed and calls `createProgramAddress`. The
    first off-curve result wins; if all 256 bumps fail, returns
    `none` (statistically impossible in real use). -/
private def tryFindLoop (seeds : List ByteArray) (programId : ByteArray)
    : Nat → Nat → Option (ByteArray × UInt8)
  | 0, _ => none
  | _ + 1, 0 =>
    match createProgramAddress (seeds ++ [bumpSeed 0]) programId with
    | some addr => some (addr, 0)
    | none => none
  | fuel + 1, bump + 1 =>
    match createProgramAddress (seeds ++ [bumpSeed (bump + 1)]) programId with
    | some addr => some (addr, (bump + 1).toUInt8)
    | none => tryFindLoop seeds programId fuel bump

/-- `Address::find_program_address(seeds, program_id)` (agave's
    `sol_try_find_program_address`). Iterates `bump` from 255 down to
    0, appending `[bump]` as the trailing seed each time, and returns
    the first `(off-curve PDA, bump)`. Returns `none` only if every
    bump yields an on-curve hash — statistically impossible. -/
def tryFindProgramAddress (seeds : List ByteArray) (programId : ByteArray)
    : Option (ByteArray × UInt8) :=
  tryFindLoop seeds programId 256 255

/-! ## Syscall bindings -/

/-- CU charge for both PDA syscalls. `try_find` is charged once per
    iteration in agave; we currently approximate by charging the
    single-attempt cost. -/
def cu : Nat := 1_500

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

/-- Execute `sol_create_program_address`.
    ABI: r1 = `*const [VmSlice; N]`, r2 = N, r3 = `*const [u8; 32]`
    program_id, r4 = `*mut [u8; 32]` out. r0 = 0/1. -/
@[simp] def execCreate (s : State) : State :=
  let seeds  := readSeeds s.mem s.regs.r1 s.regs.r2
  let pid    := readBytes s.mem s.regs.r3 32
  let result := createProgramAddress seeds pid
  commitOptional s s.regs.r4 32 result

/-- Execute `sol_try_find_program_address`.
    Same as `execCreate` plus r5 = `*mut [u8; 1]` bump output. The
    extra bump byte means we hand-roll the commit rather than reuse
    `commitOptional`. -/
def execTryFind (s : State) : State :=
  let outA   := s.regs.r4
  let bumpA  := s.regs.r5
  let seeds  := readSeeds s.mem s.regs.r1 s.regs.r2
  let pid    := readBytes s.mem s.regs.r3 32
  let result := tryFindProgramAddress seeds pid
  match result with
  | some (pda, bump) =>
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
  split <;> simp

end Pda
end Svm.SBPF
