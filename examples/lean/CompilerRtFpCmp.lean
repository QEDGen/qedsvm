/-
  Layer 3b artifact #3: Hoare triple over the **greater-than happy
  path** of the compiler-rt IEEE-754 double-precision compare callee
  at bytes 0x185F8-0x186F0 of `qedsvm-rs/tests/fixtures/p_token.so`
  (release `p-token@v1.0.0-rc.1`).

  The callee implements `__cmpdf2`-like semantics over raw u64
  operands interpreted as IEEE-754 doubles. It computes a 2-bit
  enum `r3 ∈ {0, 1, 2, 3}` where:

  - `r3 = 0` ↦ A < B (less)
  - `r3 = 1` ↦ A = B (equal)
  - `r3 = 2` ↦ A > B (greater)
  - `r3 = 3` ↦ unordered (NaN involved)

  then dereferences a 4-entry lookup table at `.data.rel.ro` offset
  0x19378 (after `r3 * 8` indexing) and returns the loaded f64 in r0.

  This artifact covers the `r3 = 2` path: A and B are both positive
  non-NaN with A strictly greater than B. Under those preconditions
  all 9 of the callee's branches collapse via if-rewrite — no
  `sl_branch` required. See `docs/next-session-plan.md` (post-N+1
  handoff) for the rationale: the magic-match if-collapse trick from
  `PTokenValidationPrelude` extends to runtime-data-driven branches
  whenever the precondition determines the outcome. The original
  handoff assumed branches comparing operand values needed
  `sl_branch`; in fact `sl_branch` is only needed when the proof has
  to characterize *both* arms of a branch.

  **PC numbering.** The Lean model treats `lddw` as a single PC slot
  (see `SVM/SBPF/Execute.lean:189-190`: `pc' := s.pc + 1` regardless
  of `lddw`). Real sBPF bytecode lays `lddw` out as two 8-byte slots.
  The PCs in this file use the abstract/Lean numbering, not byte
  offsets — for the 3 `lddw` insns at byte offsets 0x18600, 0x18620,
  0x186d0, the abstract PCs are 1, 4, 25 (not 1, 5, 27 as
  `disasm-to-lean` would emit).

  Methodology unknowns retired by this artifact:

  - **If-collapse on runtime-data-driven branches.** Six conditional
    jumps and (skipped) `ja`s all reduce to deterministic exit PCs
    once preconditions fix branch decisions.
  - **`lddw` in the middle of a block.** Three `lddw` insns at PCs 1,
    4, 25 — needs abstract PC numbering (above).
  - **`and64_reg`, `or64_reg`, `lsh64_imm` over arbitrary operands.**
    Bit-vector simplifications via `Nat.and_two_pow_sub_one_of_lt_two_pow`
    and `Nat.or_lt_two_pow`.
  - **Skipped PCs in the chain CR.** `jsge` at abstract PC 15 jumps
    to abstract PC 21, leaving PCs 16-20 unreachable on this path.
    The chain CR has 23 entries; the consumer (N+3 glue artifact)
    bridges to the full 29-entry callee CR by inclusion.

  Sibling triples for `r3 ∈ {0, 1, 3}` are mechanical follow-ons —
  same chain shape, different collapse outcomes at `jsge` (PC 15),
  `jeq` (PC 22), and the upstream NaN / zero guards.
-/

import SVM.SBPF.InstructionSpecs
import SVM.SBPF.Tactic.SL
import SVM.SBPF.Macros

namespace Examples.CompilerRtFpCmp

open SVM.SBPF
open Memory

/-! ## Bit-pattern literals -/

/-- IEEE-754 sign-bit-clear mask: bits 0..62 set, bit 63 clear.
    Equal to `2^63 - 1`. -/
def signClearMask : Nat := 0x7FFFFFFFFFFFFFFF

/-- IEEE-754 double-precision positive-infinity bit pattern. NaN bit
    patterns have `bits & signClearMask > infBitPattern`. -/
def infBitPattern : Nat := 0x7FF0000000000000

/-- Base address of the 4-entry f64 lookup table in `.data.rel.ro`. -/
def lookupTableBase : Nat := 0x19378

/-- Offset into the lookup table for the `r3 = 2` (greater-than)
    case — `r3 * 8 = 16`. -/
def gtOffset : Nat := 16

/-- Offset into the lookup table for the `r3 = 0` (less-than) case —
    `r3 * 8 = 0`. -/
def ltOffset : Nat := 0

/-! ## CodeReq for the executed path

    23 entries in chain order, abstract PCs. Skipped PCs 16-20 are
    not included; the `jsge` at PC 15 jumps to PC 21. -/

def fpCmpGtPathCr (base : Nat) : CodeReq :=
  ((((((((((((((((((((((CodeReq.singleton (base +  0) (.mov64 .r3 (.imm 3))).union
        (CodeReq.singleton (base +  1) (.lddw .r0 signClearMask))).union
        (CodeReq.singleton (base +  2) (.mov64 .r4 (.reg .r1)))).union
        (CodeReq.singleton (base +  3) (.and64 .r4 (.reg .r0)))).union
        (CodeReq.singleton (base +  4) (.lddw .r6 infBitPattern))).union
        (CodeReq.singleton (base +  5) (.jgt .r4 (.reg .r6) (base + 24)))).union
        (CodeReq.singleton (base +  6) (.mov64 .r5 (.reg .r2)))).union
        (CodeReq.singleton (base +  7) (.and64 .r5 (.reg .r0)))).union
        (CodeReq.singleton (base +  8) (.jgt .r5 (.reg .r6) (base + 24)))).union
        (CodeReq.singleton (base +  9) (.or64 .r5 (.reg .r4)))).union
        (CodeReq.singleton (base + 10) (.jeq .r5 (.imm 0) (base + 17)))).union
        (CodeReq.singleton (base + 11) (.mov64 .r3 (.reg .r2)))).union
        (CodeReq.singleton (base + 12) (.and64 .r3 (.reg .r1)))).union
        (CodeReq.singleton (base + 13) (.jsle .r3 (.imm (-1)) (base + 19)))).union
        (CodeReq.singleton (base + 14) (.mov64 .r3 (.imm 0)))).union
        (CodeReq.singleton (base + 15) (.jsge .r1 (.reg .r2) (base + 21)))).union
        (CodeReq.singleton (base + 21) (.mov64 .r3 (.imm 1)))).union
        (CodeReq.singleton (base + 22) (.jeq .r1 (.reg .r2) (base + 24)))).union
        (CodeReq.singleton (base + 23) (.mov64 .r3 (.imm 2)))).union
        (CodeReq.singleton (base + 24) (.lsh64 .r3 (.imm 3)))).union
        (CodeReq.singleton (base + 25) (.lddw .r1 lookupTableBase))).union
        (CodeReq.singleton (base + 26) (.add64 .r1 (.reg .r3)))).union
        (CodeReq.singleton (base + 27) (.ldx .dword .r0 .r1 0))

theorem fp_cmp_gt_path_spec
    (base : Nat)
    (A B : Nat)
    (initR0 initR3 initR4 initR5 initR6 cmpTableGt : Nat)
    (hA_sign : A < 2 ^ 63)
    (hB_sign : B < 2 ^ 63)
    (hA_notNaN : A ≤ infBitPattern)
    (hB_notNaN : B ≤ infBitPattern)
    (hAB_gt : A > B)
    (hTable_lt : cmpTableGt < 2 ^ 64) :
    cuTripleWithinMem 23 0 base (base + 28) (fpCmpGtPathCr base)
      ((.r3 ↦ᵣ initR3) ** (.r0 ↦ᵣ initR0) ** (.r4 ↦ᵣ initR4) **
        (.r1 ↦ᵣ A) ** (.r6 ↦ᵣ initR6) ** (.r5 ↦ᵣ initR5) **
        (.r2 ↦ᵣ B) **
        (effectiveAddr (lookupTableBase + gtOffset) 0 ↦U64 cmpTableGt))
      ((.r3 ↦ᵣ gtOffset) ** (.r0 ↦ᵣ cmpTableGt) ** (.r4 ↦ᵣ A) **
        (.r1 ↦ᵣ lookupTableBase + gtOffset) **
        (.r6 ↦ᵣ infBitPattern) ** (.r5 ↦ᵣ B ||| A) **
        (.r2 ↦ᵣ B) **
        (effectiveAddr (lookupTableBase + gtOffset) 0 ↦U64 cmpTableGt))
      (fun rt => rt.containsRange
        (effectiveAddr (lookupTableBase + gtOffset) 0) 8 = true) := by
  -- Bit-vector simplifications used throughout. `A < 2^63` lets us
  -- collapse `A &&& signClearMask = A` (clearing the already-zero sign
  -- bit is a no-op), and similarly for B. The `% U64_MODULUS` factors
  -- vanish because everything stays under 2^63.
  have h_U64_eq : U64_MODULUS = 2 ^ 64 := rfl
  have hA_mask : (A &&& signClearMask) % U64_MODULUS = A := by
    have h1 : A &&& signClearMask = A :=
      Nat.and_two_pow_sub_one_of_lt_two_pow hA_sign
    rw [h1, h_U64_eq, Nat.mod_eq_of_lt (by omega : A < 2 ^ 64)]
  have hB_mask : (B &&& signClearMask) % U64_MODULUS = B := by
    have h1 : B &&& signClearMask = B :=
      Nat.and_two_pow_sub_one_of_lt_two_pow hB_sign
    rw [h1, h_U64_eq, Nat.mod_eq_of_lt (by omega : B < 2 ^ 64)]
  have hBA_or_lt : (B ||| A) < 2 ^ 63 := Nat.or_lt_two_pow hB_sign hA_sign
  have hBA_or_mod : (B ||| A) % U64_MODULUS = B ||| A := by
    rw [h_U64_eq]; exact Nat.mod_eq_of_lt (by omega : B ||| A < 2 ^ 64)
  have hBA_or_ne_zero : (B ||| A) ≠ 0 := by
    have hA_pos : 0 < A := by omega
    have h_le : A ≤ B ||| A := Nat.right_le_or
    omega
  have hBA_and_lt : (B &&& A) < 2 ^ 63 := by
    have h : B &&& A ≤ B := Nat.and_le_left
    omega
  have hBA_and_mod : (B &&& A) % U64_MODULUS = B &&& A := by
    rw [h_U64_eq]; exact Nat.mod_eq_of_lt (by omega : B &&& A < 2 ^ 64)
  have hBA_and_signed : toSigned64 (B &&& A) = ↑(B &&& A) := by
    unfold toSigned64; simp; intro hc; omega
  -- Helper: `toU64` of a Nat-coerced-to-Int is the Nat itself
  -- (when < 2^64). Used to undo the elaborator's `↑n : Int` coercion
  -- in spec posts coming from `lddw` / `and64` / `or64`.
  have h_toU64_natCast (n : Nat) (hn : n < 2 ^ 64) :
      toU64 ((↑n : Int)) = n := by
    unfold toU64
    rw [Int.emod_eq_of_lt (by omega : (0 : Int) ≤ ↑n) (by exact_mod_cast hn)]
    exact Int.toNat_natCast n
  have h_toU64_signClear : toU64 ((↑signClearMask : Int)) = signClearMask :=
    h_toU64_natCast signClearMask (by unfold signClearMask; decide)
  have h_toU64_inf : toU64 ((↑infBitPattern : Int)) = infBitPattern :=
    h_toU64_natCast infBitPattern (by unfold infBitPattern; decide)
  have h_toU64_table : toU64 ((↑lookupTableBase : Int)) = lookupTableBase :=
    h_toU64_natCast lookupTableBase (by unfold lookupTableBase; decide)
  have h_toU64_neg1 : toU64 (-1 : Int) = 2 ^ 64 - 1 := by
    unfold toU64; decide
  have h_signed_neg1 : toSigned64 (2 ^ 64 - 1) = -1 := by
    unfold toSigned64 U64_MODULUS; decide
  have h_signed_A : toSigned64 A = ↑A := by
    unfold toSigned64; simp; intro hc; omega
  have h_signed_B : toSigned64 B = ↑B := by
    unfold toSigned64; simp; intro hc; omega
  -- Concrete values for the lsh + add computation at PCs 24, 26.
  have h_lsh3 : (toU64 2 <<< (toU64 3 % 64)) % U64_MODULUS = gtOffset := by
    unfold gtOffset toU64 U64_MODULUS; decide
  have h_wrap_add : wrapAdd lookupTableBase gtOffset
                    = lookupTableBase + gtOffset := by
    unfold wrapAdd lookupTableBase gtOffset U64_MODULUS
    decide
  -- Specs in chain order, base-shifted PCs.
  have h0  := mov64_imm_spec .r3 3 initR3 (base + 0) (by decide)
  have h1  := lddw_spec .r0 signClearMask initR0 (base + 1) (by decide)
  have h2  := mov64_reg_spec .r4 .r1 initR4 A (base + 2) (by decide)
  have h3  := and64_reg_spec .r4 .r0 A (toU64 signClearMask) (base + 3) (by decide)
  have h4  := lddw_spec .r6 infBitPattern initR6 (base + 4) (by decide)
  have h5  := jgt_reg_spec .r4 .r6
              ((A &&& toU64 signClearMask) % U64_MODULUS)
              (toU64 infBitPattern) (base + 5) (base + 24)
  have h6  := mov64_reg_spec .r5 .r2 initR5 B (base + 6) (by decide)
  have h7  := and64_reg_spec .r5 .r0 B (toU64 signClearMask) (base + 7) (by decide)
  have h8  := jgt_reg_spec .r5 .r6
              ((B &&& toU64 signClearMask) % U64_MODULUS)
              (toU64 infBitPattern) (base + 8) (base + 24)
  have h9  := or64_reg_spec .r5 .r4
              ((B &&& toU64 signClearMask) % U64_MODULUS)
              ((A &&& toU64 signClearMask) % U64_MODULUS) (base + 9) (by decide)
  have h10 := jeq_imm_spec .r5 0
              ((((B &&& toU64 signClearMask) % U64_MODULUS) |||
                ((A &&& toU64 signClearMask) % U64_MODULUS)) % U64_MODULUS)
              (base + 10) (base + 17)
  have h11 := mov64_reg_spec .r3 .r2 (toU64 3) B (base + 11) (by decide)
  have h12 := and64_reg_spec .r3 .r1 B A (base + 12) (by decide)
  have h13 := jsle_imm_spec .r3 (-1) ((B &&& A) % U64_MODULUS) (base + 13) (base + 19)
  have h14 := mov64_imm_spec .r3 0 ((B &&& A) % U64_MODULUS) (base + 14) (by decide)
  have h15 := jsge_reg_spec .r1 .r2 A B (base + 15) (base + 21)
  have h21 := mov64_imm_spec .r3 1 (toU64 0) (base + 21) (by decide)
  have h22 := jeq_reg_spec .r1 .r2 A B (base + 22) (base + 24)
  have h23 := mov64_imm_spec .r3 2 (toU64 1) (base + 23) (by decide)
  have h24 := lsh64_imm_spec .r3 3 (toU64 2) (base + 24) (by decide)
  have h25 := lddw_spec .r1 lookupTableBase A (base + 25) (by decide)
  have h26 := add64_reg_spec .r1 .r3 (toU64 lookupTableBase)
              ((toU64 2 <<< (toU64 3 % 64)) % U64_MODULUS) (base + 26) (by decide)
  have h27 := ldxdw_spec .r0 .r1 0
              signClearMask
              (lookupTableBase + gtOffset)
              cmpTableGt (base + 27) (by decide) hTable_lt
  -- Collapse the conditional-jump exit PCs.
  -- PC base+5: jgt r4 r6 doesn't fire because (A &&& mask) = A ≤ infBitPattern.
  rw [show (if ((A &&& toU64 signClearMask) % U64_MODULUS) >
            toU64 infBitPattern then (base + 24) else (base + 5) + 1)
            = (base + 6) from by
        rw [h_toU64_signClear, hA_mask, h_toU64_inf]
        have : ¬ A > infBitPattern := by omega
        simp [this]] at h5
  -- PC base+8: same for B.
  rw [show (if ((B &&& toU64 signClearMask) % U64_MODULUS) >
            toU64 infBitPattern then (base + 24) else (base + 8) + 1)
            = (base + 9) from by
        rw [h_toU64_signClear, hB_mask, h_toU64_inf]
        have : ¬ B > infBitPattern := by omega
        simp [this]] at h8
  -- PC base+10: jeq r5 0 doesn't fire because (B ||| A) ≠ 0.
  rw [show (if ((((B &&& toU64 signClearMask) % U64_MODULUS) |||
                ((A &&& toU64 signClearMask) % U64_MODULUS)) % U64_MODULUS) =
            toU64 0 then (base + 17) else (base + 10) + 1) = (base + 11) from by
        rw [h_toU64_signClear, hA_mask, hB_mask, hBA_or_mod]
        simp [hBA_or_ne_zero]] at h10
  -- PC base+13: jsle r3 -1 doesn't fire (B & A < 2^63 so toSigned ≥ 0).
  rw [show (if toSigned64 ((B &&& A) % U64_MODULUS) ≤
            toSigned64 (toU64 (-1)) then (base + 19) else (base + 13) + 1)
            = (base + 14) from by
        rw [hBA_and_mod, h_toU64_neg1, h_signed_neg1, hBA_and_signed]
        have : ¬ ((↑(B &&& A) : Int) ≤ -1) := by
          have : 0 ≤ (↑(B &&& A) : Int) := by exact_mod_cast Nat.zero_le _
          omega
        simp [this]] at h13
  -- PC base+15: jsge r1 r2 fires (A > B → toSigned A ≥ toSigned B).
  rw [show (if toSigned64 A ≥ toSigned64 B then (base + 21) else (base + 15) + 1)
            = (base + 21) from by
        rw [h_signed_A, h_signed_B]
        have : (↑A : Int) ≥ ↑B := by exact_mod_cast Nat.le_of_lt hAB_gt
        simp [this]] at h15
  -- PC base+22: jeq r1 r2 doesn't fire (A > B → A ≠ B).
  rw [show (if A = B then (base + 24) else (base + 22) + 1) = (base + 23) from by
        have : A ≠ B := by omega
        simp [this]] at h22
  -- Simplify each spec's post-state expressions so the chain atoms
  -- match the goal's clean form (toU64 ↑X → X; bit ops mod-collapsed;
  -- lsh + wrapAdd folded to concrete addresses).
  simp only [h_toU64_signClear, h_toU64_inf, h_toU64_table,
             hA_mask, hB_mask, hBA_or_mod, hBA_and_mod, h_lsh3,
             h_wrap_add]
    at h1 h3 h4 h5 h7 h8 h9 h10 h12 h13 h14 h24 h25 h26 h27
  -- Compose. sl_block_iter handles the register-atom reshuffling.
  unfold fpCmpGtPathCr
  sl_block_iter [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
                 h11, h12, h13, h14, h15, h21, h22, h23, h24, h25,
                 h26, h27]

/-! ## LT-path artifact (sibling of fp_cmp_gt_path_spec)

    The LT path executes the same callee body but takes the
    `jsge r1 r2` fall-through at PC 15 (because A < B → not A ≥ B),
    then the unconditional `ja base+24` at PC 16. PCs 17-23 are
    unreachable on this path. Final classification: r3 = 0 (LT),
    r0 loaded from lookup table at `lookupTableBase + ltOffset` =
    `lookupTableBase`.

    Required by p-token Transfer's third call: the call asks "is
    initR6 (an f64 amount) ≤ maxI64AsDouble?" — the happy path needs
    a NON-positive cmp result (r0 ≤ 0 signed) so the post-call
    `jsgt r0, 0` doesn't fire and the converted i64 stays bound to
    r1. The LT path delivers that. -/

def fpCmpLtPathCr (base : Nat) : CodeReq :=
  ((((((((((((((((((((CodeReq.singleton (base +  0) (.mov64 .r3 (.imm 3))).union
        (CodeReq.singleton (base +  1) (.lddw .r0 signClearMask))).union
        (CodeReq.singleton (base +  2) (.mov64 .r4 (.reg .r1)))).union
        (CodeReq.singleton (base +  3) (.and64 .r4 (.reg .r0)))).union
        (CodeReq.singleton (base +  4) (.lddw .r6 infBitPattern))).union
        (CodeReq.singleton (base +  5) (.jgt .r4 (.reg .r6) (base + 24)))).union
        (CodeReq.singleton (base +  6) (.mov64 .r5 (.reg .r2)))).union
        (CodeReq.singleton (base +  7) (.and64 .r5 (.reg .r0)))).union
        (CodeReq.singleton (base +  8) (.jgt .r5 (.reg .r6) (base + 24)))).union
        (CodeReq.singleton (base +  9) (.or64 .r5 (.reg .r4)))).union
        (CodeReq.singleton (base + 10) (.jeq .r5 (.imm 0) (base + 17)))).union
        (CodeReq.singleton (base + 11) (.mov64 .r3 (.reg .r2)))).union
        (CodeReq.singleton (base + 12) (.and64 .r3 (.reg .r1)))).union
        (CodeReq.singleton (base + 13) (.jsle .r3 (.imm (-1)) (base + 19)))).union
        (CodeReq.singleton (base + 14) (.mov64 .r3 (.imm 0)))).union
        (CodeReq.singleton (base + 15) (.jsge .r1 (.reg .r2) (base + 21)))).union
        (CodeReq.singleton (base + 16) (.ja (base + 24)))).union
        (CodeReq.singleton (base + 24) (.lsh64 .r3 (.imm 3)))).union
        (CodeReq.singleton (base + 25) (.lddw .r1 lookupTableBase))).union
        (CodeReq.singleton (base + 26) (.add64 .r1 (.reg .r3)))).union
        (CodeReq.singleton (base + 27) (.ldx .dword .r0 .r1 0))

theorem fp_cmp_lt_path_spec
    (base : Nat)
    (A B : Nat)
    (initR0 initR3 initR4 initR5 initR6 cmpTableLt : Nat)
    (hA_sign : A < 2 ^ 63)
    (hB_sign : B < 2 ^ 63)
    (hA_notNaN : A ≤ infBitPattern)
    (hB_notNaN : B ≤ infBitPattern)
    (hAB_lt : A < B)
    (hTable_lt : cmpTableLt < 2 ^ 64) :
    cuTripleWithinMem 21 0 base (base + 28) (fpCmpLtPathCr base)
      ((.r3 ↦ᵣ initR3) ** (.r0 ↦ᵣ initR0) ** (.r4 ↦ᵣ initR4) **
        (.r1 ↦ᵣ A) ** (.r6 ↦ᵣ initR6) ** (.r5 ↦ᵣ initR5) **
        (.r2 ↦ᵣ B) **
        (effectiveAddr (lookupTableBase + ltOffset) 0 ↦U64 cmpTableLt))
      ((.r3 ↦ᵣ ltOffset) ** (.r0 ↦ᵣ cmpTableLt) ** (.r4 ↦ᵣ A) **
        (.r1 ↦ᵣ lookupTableBase + ltOffset) **
        (.r6 ↦ᵣ infBitPattern) ** (.r5 ↦ᵣ B ||| A) **
        (.r2 ↦ᵣ B) **
        (effectiveAddr (lookupTableBase + ltOffset) 0 ↦U64 cmpTableLt))
      (fun rt => rt.containsRange
        (effectiveAddr (lookupTableBase + ltOffset) 0) 8 = true) := by
  -- Bit-vector simplifications — same as GT path.
  have h_U64_eq : U64_MODULUS = 2 ^ 64 := rfl
  have hA_mask : (A &&& signClearMask) % U64_MODULUS = A := by
    have h1 : A &&& signClearMask = A :=
      Nat.and_two_pow_sub_one_of_lt_two_pow hA_sign
    rw [h1, h_U64_eq, Nat.mod_eq_of_lt (by omega : A < 2 ^ 64)]
  have hB_mask : (B &&& signClearMask) % U64_MODULUS = B := by
    have h1 : B &&& signClearMask = B :=
      Nat.and_two_pow_sub_one_of_lt_two_pow hB_sign
    rw [h1, h_U64_eq, Nat.mod_eq_of_lt (by omega : B < 2 ^ 64)]
  have hBA_or_lt : (B ||| A) < 2 ^ 63 := Nat.or_lt_two_pow hB_sign hA_sign
  have hBA_or_mod : (B ||| A) % U64_MODULUS = B ||| A := by
    rw [h_U64_eq]; exact Nat.mod_eq_of_lt (by omega : B ||| A < 2 ^ 64)
  -- LT case: A < B and both ≥ 0 → B > 0. We need B ||| A ≠ 0.
  -- Case split on A = 0 to avoid needing OR-commutativity lemmas.
  have hBA_or_ne_zero : (B ||| A) ≠ 0 := by
    have hB_pos : 0 < B := by omega
    by_cases hA_zero : A = 0
    · -- A = 0: B ||| 0 = B (by simp), and B > 0.
      rw [hA_zero]
      intro h; simp at h; omega
    · -- A > 0: Nat.right_le_or gives A ≤ B ||| A, so B|A ≥ A > 0.
      have hA_pos : 0 < A := Nat.pos_of_ne_zero hA_zero
      have h_le : A ≤ B ||| A := Nat.right_le_or
      omega
  have hBA_and_lt : (B &&& A) < 2 ^ 63 := by
    have h : B &&& A ≤ B := Nat.and_le_left
    omega
  have hBA_and_mod : (B &&& A) % U64_MODULUS = B &&& A := by
    rw [h_U64_eq]; exact Nat.mod_eq_of_lt (by omega : B &&& A < 2 ^ 64)
  have hBA_and_signed : toSigned64 (B &&& A) = ↑(B &&& A) := by
    unfold toSigned64; simp; intro hc; omega
  have h_toU64_natCast (n : Nat) (hn : n < 2 ^ 64) :
      toU64 ((↑n : Int)) = n := by
    unfold toU64
    rw [Int.emod_eq_of_lt (by omega : (0 : Int) ≤ ↑n) (by exact_mod_cast hn)]
    exact Int.toNat_natCast n
  have h_toU64_signClear : toU64 ((↑signClearMask : Int)) = signClearMask :=
    h_toU64_natCast signClearMask (by unfold signClearMask; decide)
  have h_toU64_inf : toU64 ((↑infBitPattern : Int)) = infBitPattern :=
    h_toU64_natCast infBitPattern (by unfold infBitPattern; decide)
  have h_toU64_table : toU64 ((↑lookupTableBase : Int)) = lookupTableBase :=
    h_toU64_natCast lookupTableBase (by unfold lookupTableBase; decide)
  have h_toU64_neg1 : toU64 (-1 : Int) = 2 ^ 64 - 1 := by
    unfold toU64; decide
  have h_signed_neg1 : toSigned64 (2 ^ 64 - 1) = -1 := by
    unfold toSigned64 U64_MODULUS; decide
  have h_signed_A : toSigned64 A = ↑A := by
    unfold toSigned64; simp; intro hc; omega
  have h_signed_B : toSigned64 B = ↑B := by
    unfold toSigned64; simp; intro hc; omega
  -- LT-path-specific: r3 = 0 at PC 24, so lsh3 gives ltOffset = 0.
  have h_lsh3_lt : (toU64 0 <<< (toU64 3 % 64)) % U64_MODULUS = ltOffset := by
    unfold ltOffset toU64 U64_MODULUS; decide
  have h_wrap_add_lt : wrapAdd lookupTableBase ltOffset
                      = lookupTableBase + ltOffset := by
    unfold wrapAdd lookupTableBase ltOffset U64_MODULUS
    decide
  -- Specs in chain order — same as GT through PC 15, then PC 16 ja,
  -- then PCs 24-27.
  have h0  := mov64_imm_spec .r3 3 initR3 (base + 0) (by decide)
  have h1  := lddw_spec .r0 signClearMask initR0 (base + 1) (by decide)
  have h2  := mov64_reg_spec .r4 .r1 initR4 A (base + 2) (by decide)
  have h3  := and64_reg_spec .r4 .r0 A (toU64 signClearMask) (base + 3) (by decide)
  have h4  := lddw_spec .r6 infBitPattern initR6 (base + 4) (by decide)
  have h5  := jgt_reg_spec .r4 .r6
              ((A &&& toU64 signClearMask) % U64_MODULUS)
              (toU64 infBitPattern) (base + 5) (base + 24)
  have h6  := mov64_reg_spec .r5 .r2 initR5 B (base + 6) (by decide)
  have h7  := and64_reg_spec .r5 .r0 B (toU64 signClearMask) (base + 7) (by decide)
  have h8  := jgt_reg_spec .r5 .r6
              ((B &&& toU64 signClearMask) % U64_MODULUS)
              (toU64 infBitPattern) (base + 8) (base + 24)
  have h9  := or64_reg_spec .r5 .r4
              ((B &&& toU64 signClearMask) % U64_MODULUS)
              ((A &&& toU64 signClearMask) % U64_MODULUS) (base + 9) (by decide)
  have h10 := jeq_imm_spec .r5 0
              ((((B &&& toU64 signClearMask) % U64_MODULUS) |||
                ((A &&& toU64 signClearMask) % U64_MODULUS)) % U64_MODULUS)
              (base + 10) (base + 17)
  have h11 := mov64_reg_spec .r3 .r2 (toU64 3) B (base + 11) (by decide)
  have h12 := and64_reg_spec .r3 .r1 B A (base + 12) (by decide)
  have h13 := jsle_imm_spec .r3 (-1) ((B &&& A) % U64_MODULUS) (base + 13) (base + 19)
  have h14 := mov64_imm_spec .r3 0 ((B &&& A) % U64_MODULUS) (base + 14) (by decide)
  have h15 := jsge_reg_spec .r1 .r2 A B (base + 15) (base + 21)
  have h16 := ja_spec (base + 24) (base + 16)
  have h24 := lsh64_imm_spec .r3 3 (toU64 0) (base + 24) (by decide)
  have h25 := lddw_spec .r1 lookupTableBase A (base + 25) (by decide)
  have h26 := add64_reg_spec .r1 .r3 (toU64 lookupTableBase)
              ((toU64 0 <<< (toU64 3 % 64)) % U64_MODULUS) (base + 26) (by decide)
  have h27 := ldxdw_spec .r0 .r1 0
              signClearMask
              (lookupTableBase + ltOffset)
              cmpTableLt (base + 27) (by decide) hTable_lt
  -- Collapse the conditional-jump exit PCs.
  -- PC base+5: jgt r4 r6 doesn't fire (A non-NaN).
  rw [show (if ((A &&& toU64 signClearMask) % U64_MODULUS) >
            toU64 infBitPattern then (base + 24) else (base + 5) + 1)
            = (base + 6) from by
        rw [h_toU64_signClear, hA_mask, h_toU64_inf]
        have : ¬ A > infBitPattern := by omega
        simp [this]] at h5
  -- PC base+8: same for B.
  rw [show (if ((B &&& toU64 signClearMask) % U64_MODULUS) >
            toU64 infBitPattern then (base + 24) else (base + 8) + 1)
            = (base + 9) from by
        rw [h_toU64_signClear, hB_mask, h_toU64_inf]
        have : ¬ B > infBitPattern := by omega
        simp [this]] at h8
  -- PC base+10: jeq r5 0 doesn't fire (B ||| A ≠ 0 since B > 0).
  rw [show (if ((((B &&& toU64 signClearMask) % U64_MODULUS) |||
                ((A &&& toU64 signClearMask) % U64_MODULUS)) % U64_MODULUS) =
            toU64 0 then (base + 17) else (base + 10) + 1) = (base + 11) from by
        rw [h_toU64_signClear, hA_mask, hB_mask, hBA_or_mod]
        simp [hBA_or_ne_zero]] at h10
  -- PC base+13: jsle r3 -1 doesn't fire (B & A < 2^63).
  rw [show (if toSigned64 ((B &&& A) % U64_MODULUS) ≤
            toSigned64 (toU64 (-1)) then (base + 19) else (base + 13) + 1)
            = (base + 14) from by
        rw [hBA_and_mod, h_toU64_neg1, h_signed_neg1, hBA_and_signed]
        have : ¬ ((↑(B &&& A) : Int) ≤ -1) := by
          have : 0 ≤ (↑(B &&& A) : Int) := by exact_mod_cast Nat.zero_le _
          omega
        simp [this]] at h13
  -- PC base+15: jsge r1 r2 does NOT fire (A < B → not A ≥ B).
  rw [show (if toSigned64 A ≥ toSigned64 B then (base + 21) else (base + 15) + 1)
            = (base + 16) from by
        rw [h_signed_A, h_signed_B]
        have : ¬ ((↑A : Int) ≥ ↑B) := by
          have h : (↑A : Int) < ↑B := by exact_mod_cast hAB_lt
          omega
        simp [this]] at h15
  -- PC base+16: ja (base+24) — unconditional, no collapse needed.
  -- Simplify each spec's post-state expressions.
  simp only [h_toU64_signClear, h_toU64_inf, h_toU64_table,
             hA_mask, hB_mask, hBA_or_mod, hBA_and_mod, h_lsh3_lt,
             h_wrap_add_lt]
    at h1 h3 h4 h5 h7 h8 h9 h10 h12 h13 h14 h24 h25 h26 h27
  -- Compose. sl_block_iter handles the register-atom reshuffling.
  unfold fpCmpLtPathCr
  sl_block_iter [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
                 h11, h12, h13, h14, h15, h16, h24, h25, h26, h27]

end Examples.CompilerRtFpCmp
