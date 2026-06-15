/-
  Layer 3b artifact #3: Hoare triple over the GT happy path of the compiler-rt
  IEEE-754 double-compare callee (bytes 0x185F8-0x186F0, p-token@v1.0.0-rc.1).

  Callee: `__cmpdf2`-like — computes r3 ∈ {0=LT,1=EQ,2=GT,3=NaN} then loads
  `lookupTable[r3*8]` into r0. This file covers r3=2 (A > B, both positive non-NaN);
  all 9 branches collapse via if-rewrite, no `sl_branch` needed.

  PC numbering: abstract (lddw = 1 slot). `lddw` insns at byte-offsets 0x18600,
  0x18620, 0x186d0 map to abstract PCs 1, 4, 25 (not 1, 5, 27 from byte counts).

  Sibling triples for {0,1,3} are mechanical follow-ons with different collapses
  at jsge (PC 15) / jeq (PC 22) / NaN guards.
-/

import SVM.SBPF.InstructionSpecs
import SVM.SBPF.Tactic.SL
import SVM.SBPF.Macros

namespace Examples.CompilerRtFpCmp

open SVM.SBPF
open Memory

/-! ## Bit-pattern literals -/

/-- IEEE-754 sign-bit-clear mask (`2^63 - 1`). -/
def signClearMask : Nat := 0x7FFFFFFFFFFFFFFF

/-- IEEE-754 double +infinity pattern. NaN: `bits & signClearMask > infBitPattern`. -/
def infBitPattern : Nat := 0x7FF0000000000000

/-- Base address of the 4-entry f64 lookup table in `.data.rel.ro`. -/
def lookupTableBase : Nat := 0x19378

/-- Lookup table offset for r3=2 (GT): `r3 * 8 = 16`. -/
def gtOffset : Nat := 16

/-- Lookup table offset for r3=0 (LT): `r3 * 8 = 0`. -/
def ltOffset : Nat := 0

/-! ## CodeReq for the GT-path (23 entries, abstract PCs; PCs 16-20 skipped via jsge→21). -/

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
  -- `A < 2^63` → `A &&& signClearMask = A` (sign bit already zero); same for B.
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
  -- Undo elaborator's `↑n : Int` coercion in lddw/and64/or64 spec posts.
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
  -- lsh3 + wrapAdd at PCs 24/26 fold to concrete addresses.
  have h_lsh3 : (toU64 2 <<< (toU64 3 % 64)) % U64_MODULUS = gtOffset := by
    unfold gtOffset toU64 U64_MODULUS; decide
  have h_wrap_add : wrapAdd lookupTableBase gtOffset
                    = lookupTableBase + gtOffset := by
    unfold wrapAdd lookupTableBase gtOffset U64_MODULUS
    decide
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
  -- Collapse conditional jumps: each rw pins the non-taken/taken PC.
  -- PC base+5: A ≤ infBitPattern → jgt not taken.
  rw [show (if ((A &&& toU64 signClearMask) % U64_MODULUS) >
            toU64 infBitPattern then (base + 24) else (base + 5) + 1)
            = (base + 6) from by
        rw [h_toU64_signClear, hA_mask, h_toU64_inf]
        have : ¬ A > infBitPattern := by omega
        simp [this]] at h5
  -- PC base+8: B non-NaN → jgt not taken.
  rw [show (if ((B &&& toU64 signClearMask) % U64_MODULUS) >
            toU64 infBitPattern then (base + 24) else (base + 8) + 1)
            = (base + 9) from by
        rw [h_toU64_signClear, hB_mask, h_toU64_inf]
        have : ¬ B > infBitPattern := by omega
        simp [this]] at h8
  -- PC base+10: B ||| A ≠ 0 → jeq not taken.
  rw [show (if ((((B &&& toU64 signClearMask) % U64_MODULUS) |||
                ((A &&& toU64 signClearMask) % U64_MODULUS)) % U64_MODULUS) =
            toU64 0 then (base + 17) else (base + 10) + 1) = (base + 11) from by
        rw [h_toU64_signClear, hA_mask, hB_mask, hBA_or_mod]
        simp [hBA_or_ne_zero]] at h10
  -- PC base+13: B & A < 2^63 → jsle not taken.
  rw [show (if toSigned64 ((B &&& A) % U64_MODULUS) ≤
            toSigned64 (toU64 (-1)) then (base + 19) else (base + 13) + 1)
            = (base + 14) from by
        rw [hBA_and_mod, h_toU64_neg1, h_signed_neg1, hBA_and_signed]
        have : ¬ ((↑(B &&& A) : Int) ≤ -1) := by
          have : 0 ≤ (↑(B &&& A) : Int) := by exact_mod_cast Nat.zero_le _
          omega
        simp [this]] at h13
  -- PC base+15: A > B → jsge fires.
  rw [show (if toSigned64 A ≥ toSigned64 B then (base + 21) else (base + 15) + 1)
            = (base + 21) from by
        rw [h_signed_A, h_signed_B]
        have : (↑A : Int) ≥ ↑B := by exact_mod_cast Nat.le_of_lt hAB_gt
        simp [this]] at h15
  -- PC base+22: A ≠ B → jeq not taken.
  rw [show (if A = B then (base + 24) else (base + 22) + 1) = (base + 23) from by
        have : A ≠ B := by omega
        simp [this]] at h22
  -- Simplify post-states (toU64 ↑X → X; mod-collapse; lsh + wrapAdd folded).
  simp only [h_toU64_signClear, h_toU64_inf, h_toU64_table,
             hA_mask, hB_mask, hBA_or_mod, hBA_and_mod, h_lsh3,
             h_wrap_add]
    at h1 h3 h4 h5 h7 h8 h9 h10 h12 h13 h14 h24 h25 h26 h27
  unfold fpCmpGtPathCr
  sl_block_iter [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
                 h11, h12, h13, h14, h15, h21, h22, h23, h24, h25,
                 h26, h27]

/-! ## LT-path artifact

LT path: jsge fall-through at PC 15 (A < B), ja at PC 16 → PC 24; PCs 17-23 skipped.
Result: r3=0, r0 from `lookupTableBase + ltOffset`. Required by Transfer's third call:
the happy path needs `toSigned64 cmpTableLt ≤ 0` so the post-call `jsgt` doesn't fire. -/

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
  -- Same bit-vector simplifications as GT path.
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
  -- A < B, both ≥ 0 → B > 0 → B ||| A ≠ 0. Case-split on A=0 avoids OR-commutativity.
  have hBA_or_ne_zero : (B ||| A) ≠ 0 := by
    have hB_pos : 0 < B := by omega
    by_cases hA_zero : A = 0
    ·
      rw [hA_zero]
      intro h; simp at h; omega
    ·
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
  -- LT: r3=0 at PC 24 → lsh3=ltOffset=0.
  have h_lsh3_lt : (toU64 0 <<< (toU64 3 % 64)) % U64_MODULUS = ltOffset := by
    unfold ltOffset toU64 U64_MODULUS; decide
  have h_wrap_add_lt : wrapAdd lookupTableBase ltOffset
                      = lookupTableBase + ltOffset := by
    unfold wrapAdd lookupTableBase ltOffset U64_MODULUS
    decide
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
  -- Collapse conditional jumps (LT path).
  -- PC base+5: A non-NaN → jgt not taken.
  rw [show (if ((A &&& toU64 signClearMask) % U64_MODULUS) >
            toU64 infBitPattern then (base + 24) else (base + 5) + 1)
            = (base + 6) from by
        rw [h_toU64_signClear, hA_mask, h_toU64_inf]
        have : ¬ A > infBitPattern := by omega
        simp [this]] at h5
  -- PC base+8: B non-NaN → jgt not taken.
  rw [show (if ((B &&& toU64 signClearMask) % U64_MODULUS) >
            toU64 infBitPattern then (base + 24) else (base + 8) + 1)
            = (base + 9) from by
        rw [h_toU64_signClear, hB_mask, h_toU64_inf]
        have : ¬ B > infBitPattern := by omega
        simp [this]] at h8
  -- PC base+10: B ||| A ≠ 0 → jeq not taken.
  rw [show (if ((((B &&& toU64 signClearMask) % U64_MODULUS) |||
                ((A &&& toU64 signClearMask) % U64_MODULUS)) % U64_MODULUS) =
            toU64 0 then (base + 17) else (base + 10) + 1) = (base + 11) from by
        rw [h_toU64_signClear, hA_mask, hB_mask, hBA_or_mod]
        simp [hBA_or_ne_zero]] at h10
  -- PC base+13: B & A < 2^63 → jsle not taken.
  rw [show (if toSigned64 ((B &&& A) % U64_MODULUS) ≤
            toSigned64 (toU64 (-1)) then (base + 19) else (base + 13) + 1)
            = (base + 14) from by
        rw [hBA_and_mod, h_toU64_neg1, h_signed_neg1, hBA_and_signed]
        have : ¬ ((↑(B &&& A) : Int) ≤ -1) := by
          have : 0 ≤ (↑(B &&& A) : Int) := by exact_mod_cast Nat.zero_le _
          omega
        simp [this]] at h13
  -- PC base+15: A < B → jsge falls through.
  rw [show (if toSigned64 A ≥ toSigned64 B then (base + 21) else (base + 15) + 1)
            = (base + 16) from by
        rw [h_signed_A, h_signed_B]
        have : ¬ ((↑A : Int) ≥ ↑B) := by
          have h : (↑A : Int) < ↑B := by exact_mod_cast hAB_lt
          omega
        simp [this]] at h15
  -- PC base+16: ja (base+24) unconditional; simplify post-states.
  simp only [h_toU64_signClear, h_toU64_inf, h_toU64_table,
             hA_mask, hB_mask, hBA_or_mod, hBA_and_mod, h_lsh3_lt,
             h_wrap_add_lt]
    at h1 h3 h4 h5 h7 h8 h9 h10 h12 h13 h14 h24 h25 h26 h27
  unfold fpCmpLtPathCr
  sl_block_iter [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
                 h11, h12, h13, h14, h15, h16, h24, h25, h26, h27]

end Examples.CompilerRtFpCmp
