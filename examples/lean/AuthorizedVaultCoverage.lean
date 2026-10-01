/- Universal termination and result coverage for the pinned 66-instruction
   V3 vault, under the declared two-record [41, 0] memory layout.
   This uses one common input snapshot, not a coverage assumption or a list
   of path-specific preconditions supplied by the caller. -/
import Generated.Sbpfv3VaultAuthorizedTransition
import SVM.SBPF.Tactic.SL

namespace Examples.AuthorizedVaultCoverage

open SVM.SBPF SVM.SBPF.Memory SVM.Solana.Abstract
open Examples.Sbpfv3VaultAuthorizedTransition

set_option maxRecDepth 65536
set_option maxHeartbeats 60000000

structure Inputs where
  r0 : Nat
  base : Nat
  r2 : Nat
  owner0 : Nat
  owner1 : Nat
  owner2 : Nat
  owner3 : Nat
  total : Nat
  bump : Nat
  instructionLength : Nat
  writable : Nat
  executable : Nat
  signer : Nat
  program0 : Nat
  programOwner0 : Nat
  r3 : Nat
  program1 : Nat
  programOwner1 : Nat
  program2 : Nat
  programOwner2 : Nat
  program3 : Nat
  programOwner3 : Nat
  authority0 : Nat
  authority1 : Nat
  authority2 : Nat
  authority3 : Nat
  discriminator : Nat
  amount : Nat
  r4 : Nat

/-- Machine-word bounds; register values and byte guards need no extra bound. -/
structure Bounded (i : Inputs) : Prop where
  instructionLength_lt : i.instructionLength < 2 ^ 64
  program0_lt : i.program0 < 2 ^ 64
  programOwner0_lt : i.programOwner0 < 2 ^ 64
  program1_lt : i.program1 < 2 ^ 64
  programOwner1_lt : i.programOwner1 < 2 ^ 64
  program2_lt : i.program2 < 2 ^ 64
  programOwner2_lt : i.programOwner2 < 2 ^ 64
  program3_lt : i.program3 < 2 ^ 64
  programOwner3_lt : i.programOwner3 < 2 ^ 64
  authority0_lt : i.authority0 < 2 ^ 64
  owner0_lt : i.owner0 < 2 ^ 64
  authority1_lt : i.authority1 < 2 ^ 64
  owner1_lt : i.owner1 < 2 ^ 64
  authority2_lt : i.authority2 < 2 ^ 64
  owner2_lt : i.owner2 < 2 ^ 64
  authority3_lt : i.authority3 < 2 ^ 64
  owner3_lt : i.owner3 < 2 ^ 64
  discriminator_lt : i.discriminator < 2 ^ 64
  amount_lt : i.amount < 2 ^ 64
  total_lt : i.total < 2 ^ 64

/-- All instructions, including every rejection branch and the shared exit. -/
def program : Array Insn := #[
  .mov64 .r0 (.imm (6)),
  .ldx .dword .r2 .r1 0,
  .jne .r2 (.imm (2)) 63,
  .ldx .byte .r2 .r1 8,
  .jne .r2 (.imm (255)) 63,
  .ldx .dword .r2 .r1 88,
  .jne .r2 (.imm (41)) 63,
  .ldx .byte .r2 .r1 10392,
  .jne .r2 (.imm (255)) 63,
  .ldx .dword .r2 .r1 10472,
  .jne .r2 (.imm (0)) 63,
  .mov64 .r0 (.imm (7)),
  .ldx .dword .r2 .r1 20728,
  .jne .r2 (.imm (16)) 63,
  .mov64 .r0 (.imm (8)),
  .ldx .byte .r2 .r1 10,
  .jne .r2 (.imm (1)) 63,
  .ldx .byte .r2 .r1 11,
  .jne .r2 (.imm (0)) 63,
  .mov64 .r0 (.imm (5)),
  .ldx .byte .r2 .r1 10393,
  .jne .r2 (.imm (1)) 63,
  .mov64 .r0 (.imm (4)),
  .ldx .dword .r2 .r1 20752,
  .ldx .dword .r3 .r1 48,
  .jne .r3 (.reg .r2) 63,
  .ldx .dword .r2 .r1 20760,
  .ldx .dword .r3 .r1 56,
  .jne .r3 (.reg .r2) 63,
  .ldx .dword .r2 .r1 20768,
  .ldx .dword .r3 .r1 64,
  .jne .r3 (.reg .r2) 63,
  .ldx .dword .r2 .r1 20776,
  .ldx .dword .r3 .r1 72,
  .jne .r3 (.reg .r2) 63,
  .ldx .dword .r2 .r1 10400,
  .ldx .dword .r3 .r1 96,
  .jne .r3 (.reg .r2) 63,
  .ldx .dword .r2 .r1 10408,
  .ldx .dword .r3 .r1 104,
  .jne .r3 (.reg .r2) 63,
  .ldx .dword .r2 .r1 10416,
  .ldx .dword .r3 .r1 112,
  .jne .r3 (.reg .r2) 63,
  .ldx .dword .r2 .r1 10424,
  .ldx .dword .r3 .r1 120,
  .jne .r3 (.reg .r2) 63,
  .mov64 .r0 (.imm (2)),
  .ldx .dword .r2 .r1 20736,
  .jne .r2 (.imm (1)) 63,
  .ldx .dword .r3 .r1 20744,
  .jeq .r3 (.imm (0)) 62,
  .ldx .dword .r4 .r1 128,
  .mov64 .r2 (.reg .r4),
  .add64 .r2 (.reg .r3),
  .mov64 .r3 (.imm (1)),
  .jlt .r2 (.reg .r4) 58,
  .mov64 .r3 (.imm (0)),
  .jeq .r3 (.imm (1)) 64,
  .stx .dword .r1 128 .r2,
  .mov64 .r0 (.imm (0)),
  .ja 63,
  .mov64 .r0 (.imm (1)),
  .exit,
  .mov64 .r0 (.imm (3)),
  .ja 63
  ]

/-- Byte pins use the same native_decide trust boundary as generated lifts.
    The symbolic termination theorem below uses only standard axioms. -/
theorem complete_decode :
    Decode.decodeProgram Examples.Lifted.Sbpfv3VaultAuthorizedSuccess.Sbpfv3VaultAuthorizedSuccessText [] .v3
      = some program := by native_decide

theorem complete_elf :
    (Elf.loadV3 Examples.Lifted.Sbpfv3VaultAuthorizedSuccess.Sbpfv3VaultAuthorizedSuccessElf).map (·.textBytes)
      = some Examples.Lifted.Sbpfv3VaultAuthorizedSuccess.Sbpfv3VaultAuthorizedSuccessText := by native_decide

def fetch := Runner.fetchFromArray program

/-- Fixed metadata encodes exactly two non-duplicate records, with lengths
    41 and 0. Other cells are arbitrary bounded input words/bytes. -/
def inputPre (i : Inputs) : Assertion :=
  (.r0 ↦ᵣ i.r0) **
  (.r1 ↦ᵣ i.base) **
  (.r2 ↦ᵣ i.r2) **
  (.r3 ↦ᵣ i.r3) **
  (.r4 ↦ᵣ i.r4) **
  (effectiveAddr i.base 0 ↦U64 2) **
  (effectiveAddr i.base 8 ↦ₘ 255) **
  (effectiveAddr i.base 10 ↦ₘ i.writable) **
  (effectiveAddr i.base 11 ↦ₘ i.executable) **
  (effectiveAddr i.base 48 ↦U64 i.programOwner0) **
  (effectiveAddr i.base 56 ↦U64 i.programOwner1) **
  (effectiveAddr i.base 64 ↦U64 i.programOwner2) **
  (effectiveAddr i.base 72 ↦U64 i.programOwner3) **
  (effectiveAddr i.base 88 ↦U64 41) **
  (effectiveAddr i.base 96 ↦U64 i.owner0) **
  (effectiveAddr i.base 104 ↦U64 i.owner1) **
  (effectiveAddr i.base 112 ↦U64 i.owner2) **
  (effectiveAddr i.base 120 ↦U64 i.owner3) **
  (effectiveAddr i.base 128 ↦U64 i.total) **
  (effectiveAddr i.base 136 ↦ₘ i.bump) **
  (effectiveAddr i.base 10392 ↦ₘ 255) **
  (effectiveAddr i.base 10393 ↦ₘ i.signer) **
  (effectiveAddr i.base 10400 ↦U64 i.authority0) **
  (effectiveAddr i.base 10408 ↦U64 i.authority1) **
  (effectiveAddr i.base 10416 ↦U64 i.authority2) **
  (effectiveAddr i.base 10424 ↦U64 i.authority3) **
  (effectiveAddr i.base 10472 ↦U64 0) **
  (effectiveAddr i.base 20728 ↦U64 i.instructionLength) **
  (effectiveAddr i.base 20736 ↦U64 i.discriminator) **
  (effectiveAddr i.base 20744 ↦U64 i.amount) **
  (effectiveAddr i.base 20752 ↦U64 i.program0) **
  (effectiveAddr i.base 20760 ↦U64 i.program1) **
  (effectiveAddr i.base 20768 ↦U64 i.program2) **
  (effectiveAddr i.base 20776 ↦U64 i.program3) **
  callStackIs []

def accessRanges : List (Nat × Nat) :=
  [(0, 8), (8, 1), (10, 1), (11, 1), (48, 8), (56, 8), (64, 8), (72, 8), (88, 8), (96, 8), (104, 8), (112, 8), (120, 8), (128, 8), (10392, 1), (10393, 1), (10400, 8), (10408, 8), (10416, 8), (10424, 8), (10472, 8), (20728, 8), (20736, 8), (20744, 8), (20752, 8), (20760, 8), (20768, 8), (20776, 8)]

/-- Readable regions for all possible loads, and writable total. -/
def Regions (i : Inputs) (rt : RegionTable) : Prop :=
  (∀ off size, (off, size) ∈ accessRanges → rt.containsRange (effectiveAddr i.base off) size = true) ∧
    rt.containsWritable (effectiveAddr i.base 128) 8 = true

def vaultPost (i : Inputs) (total : Nat) : Assertion :=
  codecCoarse (i.base + 96)
    [(0, .pubkey ⟨i.owner0, i.owner1, i.owner2, i.owner3⟩),
     (32, .u64 total), (40, .byte i.bump)]

def Terminates (i : Inputs) (s : State) (code total : Nat) : Prop :=
  ∃ k, k ≤ 64 ∧
    (executeFn fetch s k).exitCode = some code ∧
    (executeFn fetch s k).cuConsumed ≤ s.cuConsumed + 64 ∧
    (vaultPost i total).holdsFor (executeFn fetch s k)

section
open Lean Lean.Meta Lean.Elab.Tactic Lean.Elab.Term SVM.SBPF.SLBlockIter

/-- Proof-producing projection of a common separating snapshot. Uses the
    existing SL permutation builder, then drops the unused compatible frame. -/
elab "coverage_project " ht:term : tactic => withMainContext do
  let h ← elabTermAndSynthesize ht none
  let g ← getMainGoal
  let source := (← inferType h).getAppArgs[0]!
  let state := (← inferType h).getAppArgs[1]!
  let target := (← g.getType).getAppArgs[0]!
  let src := flattenSepConj source
  let tgt := flattenSepConj target
  let some (iff?, frame, _) ← buildPermuteIff src tgt
    | throwError "coverage_project: target is not part of the common snapshot"
  let mut proof := h
  if let some iff ← buildRightFoldIff source then
    let lift ← mkAppOptM ``holdsFor_iff_pointwise #[none, none, some state, some iff]
    proof ← mkAppM ``Iff.mp #[lift, proof]
  if let some iff := iff? then
    let lift ← mkAppOptM ``holdsFor_iff_pointwise #[none, none, some state, some iff]
    proof ← mkAppM ``Iff.mp #[lift, proof]
  if !frame.isEmpty then
    let f ← rebuildSepConj frame
    let grouped ← mkAppM ``sepConj #[target, f]
    if let some iff ← buildRightFoldIff grouped then
      let lift ← mkAppOptM ``holdsFor_iff_pointwise #[none, none, some state, some iff]
      proof ← mkAppM ``Iff.mpr #[lift, proof]
    proof ← mkAppM ``holdsFor_sepConj_left #[proof]
  else if let some iff ← buildRightFoldIff target then
    let lift ← mkAppOptM ``holdsFor_iff_pointwise #[none, none, some state, some iff]
    proof ← mkAppM ``Iff.mpr #[lift, proof]
  g.assign proof
end

private theorem fetch_union {cr1 cr2 : CodeReq}
    (h1 : cr1.SatisfiedBy fetch) (h2 : cr2.SatisfiedBy fetch) :
    (cr1.union cr2).SatisfiedBy fetch := by
  intro pc insn h
  unfold CodeReq.union at h
  cases he : cr1 pc with
  | none => simp only [he] at h; exact h2 pc insn h
  | some v => simp only [he, Option.some.injEq] at h; subst v; exact h1 pc insn he

/-- Discharge finite region requirements from the declared readable ranges. -/
elab "coverage_regions " hr:term : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| repeat' constructor))
  Lean.Elab.Tactic.evalTactic (← `(tactic| all_goals first
    | exact ($hr).2
    | exact ($hr).1 0 8 (by decide)
    | exact ($hr).1 8 1 (by decide)
    | exact ($hr).1 10 1 (by decide)
    | exact ($hr).1 11 1 (by decide)
    | exact ($hr).1 48 8 (by decide)
    | exact ($hr).1 56 8 (by decide)
    | exact ($hr).1 64 8 (by decide)
    | exact ($hr).1 72 8 (by decide)
    | exact ($hr).1 88 8 (by decide)
    | exact ($hr).1 96 8 (by decide)
    | exact ($hr).1 104 8 (by decide)
    | exact ($hr).1 112 8 (by decide)
    | exact ($hr).1 120 8 (by decide)
    | exact ($hr).1 128 8 (by decide)
    | exact ($hr).1 10392 1 (by decide)
    | exact ($hr).1 10393 1 (by decide)
    | exact ($hr).1 10400 8 (by decide)
    | exact ($hr).1 10408 8 (by decide)
    | exact ($hr).1 10416 8 (by decide)
    | exact ($hr).1 10424 8 (by decide)
    | exact ($hr).1 10472 8 (by decide)
    | exact ($hr).1 20728 8 (by decide)
    | exact ($hr).1 20736 8 (by decide)
    | exact ($hr).1 20744 8 (by decide)
    | exact ($hr).1 20752 8 (by decide)
    | exact ($hr).1 20760 8 (by decide)
    | exact ($hr).1 20768 8 (by decide)
    | exact ($hr).1 20776 8 (by decide)))

private def paths (i : Inputs) (hb : Bounded i) :=
  sbpfv3_vault_authorized_transition
    i.r0 i.base 2 i.r2 255
    41 255 i.owner0 i.owner1 i.owner2
    i.owner3 i.total i.bump 0 i.instructionLength
    i.writable i.executable i.signer i.program0 i.programOwner0
    i.r3 i.program1 i.programOwner1 i.program2 i.programOwner2
    i.program3 i.programOwner3 i.authority0 i.authority1 i.authority2
    i.authority3 i.discriminator i.amount i.r4
    (by decide)
    (by decide)
    (by decide)
    (hb.instructionLength_lt)
    (hb.program0_lt)
    (hb.programOwner0_lt)
    (hb.program1_lt)
    (hb.programOwner1_lt)
    (hb.program2_lt)
    (hb.programOwner2_lt)
    (hb.program3_lt)
    (hb.programOwner3_lt)
    (hb.authority0_lt)
    (hb.owner0_lt)
    (hb.authority1_lt)
    (hb.owner1_lt)
    (hb.authority2_lt)
    (hb.owner2_lt)
    (hb.authority3_lt)
    (hb.owner3_lt)
    (hb.discriminator_lt)
    (hb.amount_lt)
    (hb.total_lt)

theorem noOverflow_of_not_wrapped (i : Inputs) (hb : Bounded i)
    (h : ¬ wrapAdd i.total i.amount < i.total) : i.total + i.amount < 2 ^ 64 := by
  have ht := hb.total_lt
  have ha := hb.amount_lt
  simp only [wrapAdd, U64_MODULUS] at h
  omega

private theorem case_short_instruction (i : Inputs) (hb : Bounded i) (s : State)
    (hin : (inputPre i).holdsFor s) (hr : Regions i s.regions)
    (hpc : s.pc = 0) (hex : s.exitCode = none) (hbud : s.cuConsumed + 64 ≤ s.cuBudget)
    (hg0 : 2 = toU64 2)
    (hg1 : 255 % 256 = toU64 255)
    (hg2 : 41 = toU64 41)
    (hg3 : 255 % 256 = toU64 255)
    (hg4 : 0 = toU64 0)
    (hg5 : i.instructionLength ≠ toU64 16)
    : Terminates i s 7 i.total := by
  have hp := (paths i hb).2.2.2.2.2.2.2.2.1 hg0 hg1 hg2 hg3 hg4 hg5
  unfold AsmRefinesTransitionPath at hp
  obtain ⟨k, hk, hc, hcu, hpost⟩ := hp emp pcFree_emp fetch (by
    repeat' apply fetch_union
    all_goals rw [CodeReq.SatisfiedBy_singleton]; rfl) s (by
      simp only [inputPre] at hin
      simp only [codecsPre, codecCoarse, FieldVal.coarse, pubkeyIs, Nat.add_assoc,
        sepConj_emp_right_eq] at hin ⊢
      coverage_project hin) hpc hex (by omega) (by
        coverage_regions hr)
  refine ⟨k, by omega, hc, by omega, ?_⟩
  simp only [vaultPost, codecsPost, codecCoarse, FieldVal.coarse, pubkeyIs, Nat.add_assoc,
    sepConj_emp_right_eq] at hpost ⊢
  coverage_project hpost

private theorem case_readonly (i : Inputs) (hb : Bounded i) (s : State)
    (hin : (inputPre i).holdsFor s) (hr : Regions i s.regions)
    (hpc : s.pc = 0) (hex : s.exitCode = none) (hbud : s.cuConsumed + 64 ≤ s.cuBudget)
    (hg0 : 2 = toU64 2)
    (hg1 : 255 % 256 = toU64 255)
    (hg2 : 41 = toU64 41)
    (hg3 : 255 % 256 = toU64 255)
    (hg4 : 0 = toU64 0)
    (hg5 : i.instructionLength = toU64 16)
    (hg6 : i.writable % 256 ≠ toU64 1)
    : Terminates i s 8 i.total := by
  have hp := (paths i hb).2.2.2.2.2.2.2.1 hg0 hg1 hg2 hg3 hg4 hg5 hg6
  unfold AsmRefinesTransitionPath at hp
  obtain ⟨k, hk, hc, hcu, hpost⟩ := hp emp pcFree_emp fetch (by
    repeat' apply fetch_union
    all_goals rw [CodeReq.SatisfiedBy_singleton]; rfl) s (by
      simp only [inputPre] at hin
      simp only [codecsPre, codecCoarse, FieldVal.coarse, pubkeyIs, Nat.add_assoc,
        sepConj_emp_right_eq] at hin ⊢
      coverage_project hin) hpc hex (by omega) (by
        coverage_regions hr)
  refine ⟨k, by omega, hc, by omega, ?_⟩
  simp only [vaultPost, codecsPost, codecCoarse, FieldVal.coarse, pubkeyIs, Nat.add_assoc,
    sepConj_emp_right_eq] at hpost ⊢
  coverage_project hpost

private theorem case_executable (i : Inputs) (hb : Bounded i) (s : State)
    (hin : (inputPre i).holdsFor s) (hr : Regions i s.regions)
    (hpc : s.pc = 0) (hex : s.exitCode = none) (hbud : s.cuConsumed + 64 ≤ s.cuBudget)
    (hg0 : 2 = toU64 2)
    (hg1 : 255 % 256 = toU64 255)
    (hg2 : 41 = toU64 41)
    (hg3 : 255 % 256 = toU64 255)
    (hg4 : 0 = toU64 0)
    (hg5 : i.instructionLength = toU64 16)
    (hg6 : i.writable % 256 = toU64 1)
    (hg7 : i.executable % 256 ≠ toU64 0)
    : Terminates i s 8 i.total := by
  have hp := (paths i hb).2.1 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7
  unfold AsmRefinesTransitionPath at hp
  obtain ⟨k, hk, hc, hcu, hpost⟩ := hp emp pcFree_emp fetch (by
    repeat' apply fetch_union
    all_goals rw [CodeReq.SatisfiedBy_singleton]; rfl) s (by
      simp only [inputPre] at hin
      simp only [codecsPre, codecCoarse, FieldVal.coarse, pubkeyIs, Nat.add_assoc,
        sepConj_emp_right_eq] at hin ⊢
      coverage_project hin) hpc hex (by omega) (by
        coverage_regions hr)
  refine ⟨k, by omega, hc, by omega, ?_⟩
  simp only [vaultPost, codecsPost, codecCoarse, FieldVal.coarse, pubkeyIs, Nat.add_assoc,
    sepConj_emp_right_eq] at hpost ⊢
  coverage_project hpost

private theorem case_missing_signer (i : Inputs) (hb : Bounded i) (s : State)
    (hin : (inputPre i).holdsFor s) (hr : Regions i s.regions)
    (hpc : s.pc = 0) (hex : s.exitCode = none) (hbud : s.cuConsumed + 64 ≤ s.cuBudget)
    (hg0 : 2 = toU64 2)
    (hg1 : 255 % 256 = toU64 255)
    (hg2 : 41 = toU64 41)
    (hg3 : 255 % 256 = toU64 255)
    (hg4 : 0 = toU64 0)
    (hg5 : i.instructionLength = toU64 16)
    (hg6 : i.writable % 256 = toU64 1)
    (hg7 : i.executable % 256 = toU64 0)
    (hg8 : i.signer % 256 ≠ toU64 1)
    : Terminates i s 5 i.total := by
  have hp := (paths i hb).2.2.2.2.1 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8
  unfold AsmRefinesTransitionPath at hp
  obtain ⟨k, hk, hc, hcu, hpost⟩ := hp emp pcFree_emp fetch (by
    repeat' apply fetch_union
    all_goals rw [CodeReq.SatisfiedBy_singleton]; rfl) s (by
      simp only [inputPre] at hin
      simp only [codecsPre, codecCoarse, FieldVal.coarse, pubkeyIs, Nat.add_assoc,
        sepConj_emp_right_eq] at hin ⊢
      coverage_project hin) hpc hex (by omega) (by
        coverage_regions hr)
  refine ⟨k, by omega, hc, by omega, ?_⟩
  simp only [vaultPost, codecsPost, codecCoarse, FieldVal.coarse, pubkeyIs, Nat.add_assoc,
    sepConj_emp_right_eq] at hpost ⊢
  coverage_project hpost

private theorem case_wrong_program_owner_0 (i : Inputs) (hb : Bounded i) (s : State)
    (hin : (inputPre i).holdsFor s) (hr : Regions i s.regions)
    (hpc : s.pc = 0) (hex : s.exitCode = none) (hbud : s.cuConsumed + 64 ≤ s.cuBudget)
    (hg0 : 2 = toU64 2)
    (hg1 : 255 % 256 = toU64 255)
    (hg2 : 41 = toU64 41)
    (hg3 : 255 % 256 = toU64 255)
    (hg4 : 0 = toU64 0)
    (hg5 : i.instructionLength = toU64 16)
    (hg6 : i.writable % 256 = toU64 1)
    (hg7 : i.executable % 256 = toU64 0)
    (hg8 : i.signer % 256 = toU64 1)
    (hg9 : i.programOwner0 ≠ i.program0)
    : Terminates i s 4 i.total := by
  have hp := (paths i hb).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9
  unfold AsmRefinesTransitionPath at hp
  obtain ⟨k, hk, hc, hcu, hpost⟩ := hp emp pcFree_emp fetch (by
    repeat' apply fetch_union
    all_goals rw [CodeReq.SatisfiedBy_singleton]; rfl) s (by
      simp only [inputPre] at hin
      simp only [codecsPre, codecCoarse, FieldVal.coarse, pubkeyIs, Nat.add_assoc,
        sepConj_emp_right_eq] at hin ⊢
      coverage_project hin) hpc hex (by omega) (by
        coverage_regions hr)
  refine ⟨k, by omega, hc, by omega, ?_⟩
  simp only [vaultPost, codecsPost, codecCoarse, FieldVal.coarse, pubkeyIs, Nat.add_assoc,
    sepConj_emp_right_eq] at hpost ⊢
  coverage_project hpost

private theorem case_wrong_program_owner_1 (i : Inputs) (hb : Bounded i) (s : State)
    (hin : (inputPre i).holdsFor s) (hr : Regions i s.regions)
    (hpc : s.pc = 0) (hex : s.exitCode = none) (hbud : s.cuConsumed + 64 ≤ s.cuBudget)
    (hg0 : 2 = toU64 2)
    (hg1 : 255 % 256 = toU64 255)
    (hg2 : 41 = toU64 41)
    (hg3 : 255 % 256 = toU64 255)
    (hg4 : 0 = toU64 0)
    (hg5 : i.instructionLength = toU64 16)
    (hg6 : i.writable % 256 = toU64 1)
    (hg7 : i.executable % 256 = toU64 0)
    (hg8 : i.signer % 256 = toU64 1)
    (hg9 : i.programOwner0 = i.program0)
    (hg10 : i.programOwner1 ≠ i.program1)
    : Terminates i s 4 i.total := by
  have hp := (paths i hb).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10
  unfold AsmRefinesTransitionPath at hp
  obtain ⟨k, hk, hc, hcu, hpost⟩ := hp emp pcFree_emp fetch (by
    repeat' apply fetch_union
    all_goals rw [CodeReq.SatisfiedBy_singleton]; rfl) s (by
      simp only [inputPre] at hin
      simp only [codecsPre, codecCoarse, FieldVal.coarse, pubkeyIs, Nat.add_assoc,
        sepConj_emp_right_eq] at hin ⊢
      coverage_project hin) hpc hex (by omega) (by
        coverage_regions hr)
  refine ⟨k, by omega, hc, by omega, ?_⟩
  simp only [vaultPost, codecsPost, codecCoarse, FieldVal.coarse, pubkeyIs, Nat.add_assoc,
    sepConj_emp_right_eq] at hpost ⊢
  coverage_project hpost

private theorem case_wrong_program_owner_2 (i : Inputs) (hb : Bounded i) (s : State)
    (hin : (inputPre i).holdsFor s) (hr : Regions i s.regions)
    (hpc : s.pc = 0) (hex : s.exitCode = none) (hbud : s.cuConsumed + 64 ≤ s.cuBudget)
    (hg0 : 2 = toU64 2)
    (hg1 : 255 % 256 = toU64 255)
    (hg2 : 41 = toU64 41)
    (hg3 : 255 % 256 = toU64 255)
    (hg4 : 0 = toU64 0)
    (hg5 : i.instructionLength = toU64 16)
    (hg6 : i.writable % 256 = toU64 1)
    (hg7 : i.executable % 256 = toU64 0)
    (hg8 : i.signer % 256 = toU64 1)
    (hg9 : i.programOwner0 = i.program0)
    (hg10 : i.programOwner1 = i.program1)
    (hg11 : i.programOwner2 ≠ i.program2)
    : Terminates i s 4 i.total := by
  have hp := (paths i hb).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11
  unfold AsmRefinesTransitionPath at hp
  obtain ⟨k, hk, hc, hcu, hpost⟩ := hp emp pcFree_emp fetch (by
    repeat' apply fetch_union
    all_goals rw [CodeReq.SatisfiedBy_singleton]; rfl) s (by
      simp only [inputPre] at hin
      simp only [codecsPre, codecCoarse, FieldVal.coarse, pubkeyIs, Nat.add_assoc,
        sepConj_emp_right_eq] at hin ⊢
      coverage_project hin) hpc hex (by omega) (by
        coverage_regions hr)
  refine ⟨k, by omega, hc, by omega, ?_⟩
  simp only [vaultPost, codecsPost, codecCoarse, FieldVal.coarse, pubkeyIs, Nat.add_assoc,
    sepConj_emp_right_eq] at hpost ⊢
  coverage_project hpost

private theorem case_wrong_program_owner_3 (i : Inputs) (hb : Bounded i) (s : State)
    (hin : (inputPre i).holdsFor s) (hr : Regions i s.regions)
    (hpc : s.pc = 0) (hex : s.exitCode = none) (hbud : s.cuConsumed + 64 ≤ s.cuBudget)
    (hg0 : 2 = toU64 2)
    (hg1 : 255 % 256 = toU64 255)
    (hg2 : 41 = toU64 41)
    (hg3 : 255 % 256 = toU64 255)
    (hg4 : 0 = toU64 0)
    (hg5 : i.instructionLength = toU64 16)
    (hg6 : i.writable % 256 = toU64 1)
    (hg7 : i.executable % 256 = toU64 0)
    (hg8 : i.signer % 256 = toU64 1)
    (hg9 : i.programOwner0 = i.program0)
    (hg10 : i.programOwner1 = i.program1)
    (hg11 : i.programOwner2 = i.program2)
    (hg12 : i.programOwner3 ≠ i.program3)
    : Terminates i s 4 i.total := by
  have hp := (paths i hb).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12
  unfold AsmRefinesTransitionPath at hp
  obtain ⟨k, hk, hc, hcu, hpost⟩ := hp emp pcFree_emp fetch (by
    repeat' apply fetch_union
    all_goals rw [CodeReq.SatisfiedBy_singleton]; rfl) s (by
      simp only [inputPre] at hin
      simp only [codecsPre, codecCoarse, FieldVal.coarse, pubkeyIs, Nat.add_assoc,
        sepConj_emp_right_eq] at hin ⊢
      coverage_project hin) hpc hex (by omega) (by
        coverage_regions hr)
  refine ⟨k, by omega, hc, by omega, ?_⟩
  simp only [vaultPost, codecsPost, codecCoarse, FieldVal.coarse, pubkeyIs, Nat.add_assoc,
    sepConj_emp_right_eq] at hpost ⊢
  coverage_project hpost

private theorem case_wrong_owner_0 (i : Inputs) (hb : Bounded i) (s : State)
    (hin : (inputPre i).holdsFor s) (hr : Regions i s.regions)
    (hpc : s.pc = 0) (hex : s.exitCode = none) (hbud : s.cuConsumed + 64 ≤ s.cuBudget)
    (hg0 : 2 = toU64 2)
    (hg1 : 255 % 256 = toU64 255)
    (hg2 : 41 = toU64 41)
    (hg3 : 255 % 256 = toU64 255)
    (hg4 : 0 = toU64 0)
    (hg5 : i.instructionLength = toU64 16)
    (hg6 : i.writable % 256 = toU64 1)
    (hg7 : i.executable % 256 = toU64 0)
    (hg8 : i.signer % 256 = toU64 1)
    (hg9 : i.programOwner0 = i.program0)
    (hg10 : i.programOwner1 = i.program1)
    (hg11 : i.programOwner2 = i.program2)
    (hg12 : i.programOwner3 = i.program3)
    (hg13 : i.owner0 ≠ i.authority0)
    : Terminates i s 4 i.total := by
  have hp := (paths i hb).2.2.2.2.2.2.2.2.2.2.2.2.1 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13
  unfold AsmRefinesTransitionPath at hp
  obtain ⟨k, hk, hc, hcu, hpost⟩ := hp emp pcFree_emp fetch (by
    repeat' apply fetch_union
    all_goals rw [CodeReq.SatisfiedBy_singleton]; rfl) s (by
      simp only [inputPre] at hin
      simp only [codecsPre, codecCoarse, FieldVal.coarse, pubkeyIs, Nat.add_assoc,
        sepConj_emp_right_eq] at hin ⊢
      coverage_project hin) hpc hex (by omega) (by
        coverage_regions hr)
  refine ⟨k, by omega, hc, by omega, ?_⟩
  simp only [vaultPost, codecsPost, codecCoarse, FieldVal.coarse, pubkeyIs, Nat.add_assoc,
    sepConj_emp_right_eq] at hpost ⊢
  coverage_project hpost

private theorem case_wrong_owner_1 (i : Inputs) (hb : Bounded i) (s : State)
    (hin : (inputPre i).holdsFor s) (hr : Regions i s.regions)
    (hpc : s.pc = 0) (hex : s.exitCode = none) (hbud : s.cuConsumed + 64 ≤ s.cuBudget)
    (hg0 : 2 = toU64 2)
    (hg1 : 255 % 256 = toU64 255)
    (hg2 : 41 = toU64 41)
    (hg3 : 255 % 256 = toU64 255)
    (hg4 : 0 = toU64 0)
    (hg5 : i.instructionLength = toU64 16)
    (hg6 : i.writable % 256 = toU64 1)
    (hg7 : i.executable % 256 = toU64 0)
    (hg8 : i.signer % 256 = toU64 1)
    (hg9 : i.programOwner0 = i.program0)
    (hg10 : i.programOwner1 = i.program1)
    (hg11 : i.programOwner2 = i.program2)
    (hg12 : i.programOwner3 = i.program3)
    (hg13 : i.owner0 = i.authority0)
    (hg14 : i.owner1 ≠ i.authority1)
    : Terminates i s 4 i.total := by
  have hp := (paths i hb).2.2.2.2.2.2.2.2.2.2.2.2.2.1 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14
  unfold AsmRefinesTransitionPath at hp
  obtain ⟨k, hk, hc, hcu, hpost⟩ := hp emp pcFree_emp fetch (by
    repeat' apply fetch_union
    all_goals rw [CodeReq.SatisfiedBy_singleton]; rfl) s (by
      simp only [inputPre] at hin
      simp only [codecsPre, codecCoarse, FieldVal.coarse, pubkeyIs, Nat.add_assoc,
        sepConj_emp_right_eq] at hin ⊢
      coverage_project hin) hpc hex (by omega) (by
        coverage_regions hr)
  refine ⟨k, by omega, hc, by omega, ?_⟩
  simp only [vaultPost, codecsPost, codecCoarse, FieldVal.coarse, pubkeyIs, Nat.add_assoc,
    sepConj_emp_right_eq] at hpost ⊢
  coverage_project hpost

private theorem case_wrong_owner_2 (i : Inputs) (hb : Bounded i) (s : State)
    (hin : (inputPre i).holdsFor s) (hr : Regions i s.regions)
    (hpc : s.pc = 0) (hex : s.exitCode = none) (hbud : s.cuConsumed + 64 ≤ s.cuBudget)
    (hg0 : 2 = toU64 2)
    (hg1 : 255 % 256 = toU64 255)
    (hg2 : 41 = toU64 41)
    (hg3 : 255 % 256 = toU64 255)
    (hg4 : 0 = toU64 0)
    (hg5 : i.instructionLength = toU64 16)
    (hg6 : i.writable % 256 = toU64 1)
    (hg7 : i.executable % 256 = toU64 0)
    (hg8 : i.signer % 256 = toU64 1)
    (hg9 : i.programOwner0 = i.program0)
    (hg10 : i.programOwner1 = i.program1)
    (hg11 : i.programOwner2 = i.program2)
    (hg12 : i.programOwner3 = i.program3)
    (hg13 : i.owner0 = i.authority0)
    (hg14 : i.owner1 = i.authority1)
    (hg15 : i.owner2 ≠ i.authority2)
    : Terminates i s 4 i.total := by
  have hp := (paths i hb).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15
  unfold AsmRefinesTransitionPath at hp
  obtain ⟨k, hk, hc, hcu, hpost⟩ := hp emp pcFree_emp fetch (by
    repeat' apply fetch_union
    all_goals rw [CodeReq.SatisfiedBy_singleton]; rfl) s (by
      simp only [inputPre] at hin
      simp only [codecsPre, codecCoarse, FieldVal.coarse, pubkeyIs, Nat.add_assoc,
        sepConj_emp_right_eq] at hin ⊢
      coverage_project hin) hpc hex (by omega) (by
        coverage_regions hr)
  refine ⟨k, by omega, hc, by omega, ?_⟩
  simp only [vaultPost, codecsPost, codecCoarse, FieldVal.coarse, pubkeyIs, Nat.add_assoc,
    sepConj_emp_right_eq] at hpost ⊢
  coverage_project hpost

private theorem case_wrong_owner_3 (i : Inputs) (hb : Bounded i) (s : State)
    (hin : (inputPre i).holdsFor s) (hr : Regions i s.regions)
    (hpc : s.pc = 0) (hex : s.exitCode = none) (hbud : s.cuConsumed + 64 ≤ s.cuBudget)
    (hg0 : 2 = toU64 2)
    (hg1 : 255 % 256 = toU64 255)
    (hg2 : 41 = toU64 41)
    (hg3 : 255 % 256 = toU64 255)
    (hg4 : 0 = toU64 0)
    (hg5 : i.instructionLength = toU64 16)
    (hg6 : i.writable % 256 = toU64 1)
    (hg7 : i.executable % 256 = toU64 0)
    (hg8 : i.signer % 256 = toU64 1)
    (hg9 : i.programOwner0 = i.program0)
    (hg10 : i.programOwner1 = i.program1)
    (hg11 : i.programOwner2 = i.program2)
    (hg12 : i.programOwner3 = i.program3)
    (hg13 : i.owner0 = i.authority0)
    (hg14 : i.owner1 = i.authority1)
    (hg15 : i.owner2 = i.authority2)
    (hg16 : i.owner3 ≠ i.authority3)
    : Terminates i s 4 i.total := by
  have hp := (paths i hb).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16
  unfold AsmRefinesTransitionPath at hp
  obtain ⟨k, hk, hc, hcu, hpost⟩ := hp emp pcFree_emp fetch (by
    repeat' apply fetch_union
    all_goals rw [CodeReq.SatisfiedBy_singleton]; rfl) s (by
      simp only [inputPre] at hin
      simp only [codecsPre, codecCoarse, FieldVal.coarse, pubkeyIs, Nat.add_assoc,
        sepConj_emp_right_eq] at hin ⊢
      coverage_project hin) hpc hex (by omega) (by
        coverage_regions hr)
  refine ⟨k, by omega, hc, by omega, ?_⟩
  simp only [vaultPost, codecsPost, codecCoarse, FieldVal.coarse, pubkeyIs, Nat.add_assoc,
    sepConj_emp_right_eq] at hpost ⊢
  coverage_project hpost

private theorem case_unknown (i : Inputs) (hb : Bounded i) (s : State)
    (hin : (inputPre i).holdsFor s) (hr : Regions i s.regions)
    (hpc : s.pc = 0) (hex : s.exitCode = none) (hbud : s.cuConsumed + 64 ≤ s.cuBudget)
    (hg0 : 2 = toU64 2)
    (hg1 : 255 % 256 = toU64 255)
    (hg2 : 41 = toU64 41)
    (hg3 : 255 % 256 = toU64 255)
    (hg4 : 0 = toU64 0)
    (hg5 : i.instructionLength = toU64 16)
    (hg6 : i.writable % 256 = toU64 1)
    (hg7 : i.executable % 256 = toU64 0)
    (hg8 : i.signer % 256 = toU64 1)
    (hg9 : i.programOwner0 = i.program0)
    (hg10 : i.programOwner1 = i.program1)
    (hg11 : i.programOwner2 = i.program2)
    (hg12 : i.programOwner3 = i.program3)
    (hg13 : i.owner0 = i.authority0)
    (hg14 : i.owner1 = i.authority1)
    (hg15 : i.owner2 = i.authority2)
    (hg16 : i.owner3 = i.authority3)
    (hg17 : i.discriminator ≠ toU64 1)
    : Terminates i s 2 i.total := by
  have hp := (paths i hb).2.2.2.2.2.2.2.2.2.2.2.1 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17
  unfold AsmRefinesTransitionPath at hp
  obtain ⟨k, hk, hc, hcu, hpost⟩ := hp emp pcFree_emp fetch (by
    repeat' apply fetch_union
    all_goals rw [CodeReq.SatisfiedBy_singleton]; rfl) s (by
      simp only [inputPre] at hin
      simp only [codecsPre, codecCoarse, FieldVal.coarse, pubkeyIs, Nat.add_assoc,
        sepConj_emp_right_eq] at hin ⊢
      coverage_project hin) hpc hex (by omega) (by
        coverage_regions hr)
  refine ⟨k, by omega, hc, by omega, ?_⟩
  simp only [vaultPost, codecsPost, codecCoarse, FieldVal.coarse, pubkeyIs, Nat.add_assoc,
    sepConj_emp_right_eq] at hpost ⊢
  coverage_project hpost

private theorem case_zero (i : Inputs) (hb : Bounded i) (s : State)
    (hin : (inputPre i).holdsFor s) (hr : Regions i s.regions)
    (hpc : s.pc = 0) (hex : s.exitCode = none) (hbud : s.cuConsumed + 64 ≤ s.cuBudget)
    (hg0 : 2 = toU64 2)
    (hg1 : 255 % 256 = toU64 255)
    (hg2 : 41 = toU64 41)
    (hg3 : 255 % 256 = toU64 255)
    (hg4 : 0 = toU64 0)
    (hg5 : i.instructionLength = toU64 16)
    (hg6 : i.writable % 256 = toU64 1)
    (hg7 : i.executable % 256 = toU64 0)
    (hg8 : i.signer % 256 = toU64 1)
    (hg9 : i.programOwner0 = i.program0)
    (hg10 : i.programOwner1 = i.program1)
    (hg11 : i.programOwner2 = i.program2)
    (hg12 : i.programOwner3 = i.program3)
    (hg13 : i.owner0 = i.authority0)
    (hg14 : i.owner1 = i.authority1)
    (hg15 : i.owner2 = i.authority2)
    (hg16 : i.owner3 = i.authority3)
    (hg17 : i.discriminator = toU64 1)
    (hg18 : i.amount = toU64 0)
    : Terminates i s 1 i.total := by
  have hp := (paths i hb).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18
  unfold AsmRefinesTransitionPath at hp
  obtain ⟨k, hk, hc, hcu, hpost⟩ := hp emp pcFree_emp fetch (by
    repeat' apply fetch_union
    all_goals rw [CodeReq.SatisfiedBy_singleton]; rfl) s (by
      simp only [inputPre] at hin
      simp only [codecsPre, codecCoarse, FieldVal.coarse, pubkeyIs, Nat.add_assoc,
        sepConj_emp_right_eq] at hin ⊢
      coverage_project hin) hpc hex (by omega) (by
        coverage_regions hr)
  refine ⟨k, by omega, hc, by omega, ?_⟩
  simp only [vaultPost, codecsPost, codecCoarse, FieldVal.coarse, pubkeyIs, Nat.add_assoc,
    sepConj_emp_right_eq] at hpost ⊢
  coverage_project hpost

private theorem case_overflow (i : Inputs) (hb : Bounded i) (s : State)
    (hin : (inputPre i).holdsFor s) (hr : Regions i s.regions)
    (hpc : s.pc = 0) (hex : s.exitCode = none) (hbud : s.cuConsumed + 64 ≤ s.cuBudget)
    (hg0 : 2 = toU64 2)
    (hg1 : 255 % 256 = toU64 255)
    (hg2 : 41 = toU64 41)
    (hg3 : 255 % 256 = toU64 255)
    (hg4 : 0 = toU64 0)
    (hg5 : i.instructionLength = toU64 16)
    (hg6 : i.writable % 256 = toU64 1)
    (hg7 : i.executable % 256 = toU64 0)
    (hg8 : i.signer % 256 = toU64 1)
    (hg9 : i.programOwner0 = i.program0)
    (hg10 : i.programOwner1 = i.program1)
    (hg11 : i.programOwner2 = i.program2)
    (hg12 : i.programOwner3 = i.program3)
    (hg13 : i.owner0 = i.authority0)
    (hg14 : i.owner1 = i.authority1)
    (hg15 : i.owner2 = i.authority2)
    (hg16 : i.owner3 = i.authority3)
    (hg17 : i.discriminator = toU64 1)
    (hg18 : i.amount ≠ toU64 0)
    (hg19 : wrapAdd i.total i.amount < i.total)
    (hg20 : toU64 1 = toU64 1)
    : Terminates i s 3 i.total := by
  have hp := (paths i hb).2.2.2.2.2.2.1 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20
  unfold AsmRefinesTransitionPath at hp
  obtain ⟨k, hk, hc, hcu, hpost⟩ := hp emp pcFree_emp fetch (by
    repeat' apply fetch_union
    all_goals rw [CodeReq.SatisfiedBy_singleton]; rfl) s (by
      simp only [inputPre] at hin
      simp only [codecsPre, codecCoarse, FieldVal.coarse, pubkeyIs, Nat.add_assoc,
        sepConj_emp_right_eq] at hin ⊢
      coverage_project hin) hpc hex (by omega) (by
        coverage_regions hr)
  refine ⟨k, by omega, hc, by omega, ?_⟩
  simp only [vaultPost, codecsPost, codecCoarse, FieldVal.coarse, pubkeyIs, Nat.add_assoc,
    sepConj_emp_right_eq] at hpost ⊢
  coverage_project hpost

private theorem case_success (i : Inputs) (hb : Bounded i) (s : State)
    (hin : (inputPre i).holdsFor s) (hr : Regions i s.regions)
    (hpc : s.pc = 0) (hex : s.exitCode = none) (hbud : s.cuConsumed + 64 ≤ s.cuBudget)
    (hg0 : 2 = toU64 2)
    (hg1 : 255 % 256 = toU64 255)
    (hg2 : 41 = toU64 41)
    (hg3 : 255 % 256 = toU64 255)
    (hg4 : 0 = toU64 0)
    (hg5 : i.instructionLength = toU64 16)
    (hg6 : i.writable % 256 = toU64 1)
    (hg7 : i.executable % 256 = toU64 0)
    (hg8 : i.signer % 256 = toU64 1)
    (hg9 : i.programOwner0 = i.program0)
    (hg10 : i.programOwner1 = i.program1)
    (hg11 : i.programOwner2 = i.program2)
    (hg12 : i.programOwner3 = i.program3)
    (hg13 : i.owner0 = i.authority0)
    (hg14 : i.owner1 = i.authority1)
    (hg15 : i.owner2 = i.authority2)
    (hg16 : i.owner3 = i.authority3)
    (hg17 : i.discriminator = toU64 1)
    (hg18 : i.amount ≠ toU64 0)
    (hg19 : ¬ wrapAdd i.total i.amount < i.total)
    (hg20 : toU64 0 ≠ toU64 1)
    (hg21 : i.total + i.amount < 2 ^ 64)
    : Terminates i s 0 (i.total + i.amount) := by
  have hp := (paths i hb).2.2.2.2.2.2.2.2.2.2.1 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21
  unfold AsmRefinesTransitionPath at hp
  obtain ⟨k, hk, hc, hcu, hpost⟩ := hp emp pcFree_emp fetch (by
    repeat' apply fetch_union
    all_goals rw [CodeReq.SatisfiedBy_singleton]; rfl) s (by
      simp only [inputPre] at hin
      simp only [codecsPre, codecCoarse, FieldVal.coarse, pubkeyIs, Nat.add_assoc,
        sepConj_emp_right_eq] at hin ⊢
      coverage_project hin) hpc hex (by omega) (by
        coverage_regions hr)
  refine ⟨k, by omega, hc, by omega, ?_⟩
  simp only [vaultPost, codecsPost, codecCoarse, FieldVal.coarse, pubkeyIs, Nat.add_assoc,
    sepConj_emp_right_eq] at hpost ⊢
  coverage_project hpost

/-- Return-code classifier follows the checks in bytecode order. -/
def resultCode (i : Inputs) : Nat :=
  if i.instructionLength = toU64 16 then
    if i.writable % 256 = toU64 1 then
      if i.executable % 256 = toU64 0 then
        if i.signer % 256 = toU64 1 then
          if i.programOwner0 = i.program0 then
            if i.programOwner1 = i.program1 then
              if i.programOwner2 = i.program2 then
                if i.programOwner3 = i.program3 then
                  if i.owner0 = i.authority0 then
                    if i.owner1 = i.authority1 then
                      if i.owner2 = i.authority2 then
                        if i.owner3 = i.authority3 then
                          if i.discriminator = toU64 1 then
                            if i.amount ≠ toU64 0 then
                              if ¬ wrapAdd i.total i.amount < i.total then
                                0
                              else 3
                            else 1
                          else 2
                        else 4
                      else 4
                    else 4
                  else 4
                else 4
              else 4
            else 4
          else 4
        else 5
      else 8
    else 8
  else 7

/-- Every declared-layout snapshot reaches success or a specified rejection
    within 64 steps/CU, preserving owner and bump and updating total only on
    success. No path-coverage premise is required. -/
theorem all_inputs_terminate (i : Inputs) (hb : Bounded i) (s : State)
    (hin : (inputPre i).holdsFor s) (hr : Regions i s.regions)
    (hpc : s.pc = 0) (hex : s.exitCode = none) (hbud : s.cuConsumed + 64 ≤ s.cuBudget)
    : Terminates i s (resultCode i)
        (if resultCode i = 0 then i.total + i.amount else i.total) := by
  by_cases h0 : i.instructionLength = toU64 16
  ·
    by_cases h1 : i.writable % 256 = toU64 1
    ·
      by_cases h2 : i.executable % 256 = toU64 0
      ·
        by_cases h3 : i.signer % 256 = toU64 1
        ·
          by_cases h4 : i.programOwner0 = i.program0
          ·
            by_cases h5 : i.programOwner1 = i.program1
            ·
              by_cases h6 : i.programOwner2 = i.program2
              ·
                by_cases h7 : i.programOwner3 = i.program3
                ·
                  by_cases h8 : i.owner0 = i.authority0
                  ·
                    by_cases h9 : i.owner1 = i.authority1
                    ·
                      by_cases h10 : i.owner2 = i.authority2
                      ·
                        by_cases h11 : i.owner3 = i.authority3
                        ·
                          by_cases h12 : i.discriminator = toU64 1
                          ·
                            by_cases h13 : i.amount ≠ toU64 0
                            ·
                              by_cases h14 : ¬ wrapAdd i.total i.amount < i.total
                              ·
                                simpa only [resultCode, if_pos h0, if_pos h1, if_pos h2, if_pos h3, if_pos h4, if_pos h5, if_pos h6, if_pos h7, if_pos h8, if_pos h9, if_pos h10, if_pos h11, if_pos h12, if_pos h13, if_pos h14, ite_true, ite_false, Nat.succ_ne_zero, eq_self] using
                                  (case_success i hb s hin hr hpc hex hbud (by decide) (by decide) (by decide) (by decide) (by decide) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 (by decide) (noOverflow_of_not_wrapped i hb h14))
                              · simpa only [resultCode, if_pos h0, if_pos h1, if_pos h2, if_pos h3, if_pos h4, if_pos h5, if_pos h6, if_pos h7, if_pos h8, if_pos h9, if_pos h10, if_pos h11, if_pos h12, if_pos h13, if_neg h14, ite_true, ite_false, Nat.succ_ne_zero, eq_self] using
                                  (case_overflow i hb s hin hr hpc hex hbud (by decide) (by decide) (by decide) (by decide) (by decide) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 (Classical.not_not.mp h14) (by decide))
                            · simpa only [resultCode, if_pos h0, if_pos h1, if_pos h2, if_pos h3, if_pos h4, if_pos h5, if_pos h6, if_pos h7, if_pos h8, if_pos h9, if_pos h10, if_pos h11, if_pos h12, if_neg h13, ite_true, ite_false, Nat.succ_ne_zero, eq_self] using
                                (case_zero i hb s hin hr hpc hex hbud (by decide) (by decide) (by decide) (by decide) (by decide) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 (Classical.not_not.mp h13))
                          · simpa only [resultCode, if_pos h0, if_pos h1, if_pos h2, if_pos h3, if_pos h4, if_pos h5, if_pos h6, if_pos h7, if_pos h8, if_pos h9, if_pos h10, if_pos h11, if_neg h12, ite_true, ite_false, Nat.succ_ne_zero, eq_self] using
                              (case_unknown i hb s hin hr hpc hex hbud (by decide) (by decide) (by decide) (by decide) (by decide) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12)
                        · simpa only [resultCode, if_pos h0, if_pos h1, if_pos h2, if_pos h3, if_pos h4, if_pos h5, if_pos h6, if_pos h7, if_pos h8, if_pos h9, if_pos h10, if_neg h11, ite_true, ite_false, Nat.succ_ne_zero, eq_self] using
                            (case_wrong_owner_3 i hb s hin hr hpc hex hbud (by decide) (by decide) (by decide) (by decide) (by decide) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11)
                      · simpa only [resultCode, if_pos h0, if_pos h1, if_pos h2, if_pos h3, if_pos h4, if_pos h5, if_pos h6, if_pos h7, if_pos h8, if_pos h9, if_neg h10, ite_true, ite_false, Nat.succ_ne_zero, eq_self] using
                          (case_wrong_owner_2 i hb s hin hr hpc hex hbud (by decide) (by decide) (by decide) (by decide) (by decide) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
                    · simpa only [resultCode, if_pos h0, if_pos h1, if_pos h2, if_pos h3, if_pos h4, if_pos h5, if_pos h6, if_pos h7, if_pos h8, if_neg h9, ite_true, ite_false, Nat.succ_ne_zero, eq_self] using
                        (case_wrong_owner_1 i hb s hin hr hpc hex hbud (by decide) (by decide) (by decide) (by decide) (by decide) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9)
                  · simpa only [resultCode, if_pos h0, if_pos h1, if_pos h2, if_pos h3, if_pos h4, if_pos h5, if_pos h6, if_pos h7, if_neg h8, ite_true, ite_false, Nat.succ_ne_zero, eq_self] using
                      (case_wrong_owner_0 i hb s hin hr hpc hex hbud (by decide) (by decide) (by decide) (by decide) (by decide) h0 h1 h2 h3 h4 h5 h6 h7 h8)
                · simpa only [resultCode, if_pos h0, if_pos h1, if_pos h2, if_pos h3, if_pos h4, if_pos h5, if_pos h6, if_neg h7, ite_true, ite_false, Nat.succ_ne_zero, eq_self] using
                    (case_wrong_program_owner_3 i hb s hin hr hpc hex hbud (by decide) (by decide) (by decide) (by decide) (by decide) h0 h1 h2 h3 h4 h5 h6 h7)
              · simpa only [resultCode, if_pos h0, if_pos h1, if_pos h2, if_pos h3, if_pos h4, if_pos h5, if_neg h6, ite_true, ite_false, Nat.succ_ne_zero, eq_self] using
                  (case_wrong_program_owner_2 i hb s hin hr hpc hex hbud (by decide) (by decide) (by decide) (by decide) (by decide) h0 h1 h2 h3 h4 h5 h6)
            · simpa only [resultCode, if_pos h0, if_pos h1, if_pos h2, if_pos h3, if_pos h4, if_neg h5, ite_true, ite_false, Nat.succ_ne_zero, eq_self] using
                (case_wrong_program_owner_1 i hb s hin hr hpc hex hbud (by decide) (by decide) (by decide) (by decide) (by decide) h0 h1 h2 h3 h4 h5)
          · simpa only [resultCode, if_pos h0, if_pos h1, if_pos h2, if_pos h3, if_neg h4, ite_true, ite_false, Nat.succ_ne_zero, eq_self] using
              (case_wrong_program_owner_0 i hb s hin hr hpc hex hbud (by decide) (by decide) (by decide) (by decide) (by decide) h0 h1 h2 h3 h4)
        · simpa only [resultCode, if_pos h0, if_pos h1, if_pos h2, if_neg h3, ite_true, ite_false, Nat.succ_ne_zero, eq_self] using
            (case_missing_signer i hb s hin hr hpc hex hbud (by decide) (by decide) (by decide) (by decide) (by decide) h0 h1 h2 h3)
      · simpa only [resultCode, if_pos h0, if_pos h1, if_neg h2, ite_true, ite_false, Nat.succ_ne_zero, eq_self] using
          (case_executable i hb s hin hr hpc hex hbud (by decide) (by decide) (by decide) (by decide) (by decide) h0 h1 h2)
    · simpa only [resultCode, if_pos h0, if_neg h1, ite_true, ite_false, Nat.succ_ne_zero, eq_self] using
        (case_readonly i hb s hin hr hpc hex hbud (by decide) (by decide) (by decide) (by decide) (by decide) h0 h1)
  · simpa only [resultCode, if_neg h0, ite_true, ite_false, Nat.succ_ne_zero, eq_self] using
      (case_short_instruction i hb s hin hr hpc hex hbud (by decide) (by decide) (by decide) (by decide) (by decide)  h0)
end Examples.AuthorizedVaultCoverage
