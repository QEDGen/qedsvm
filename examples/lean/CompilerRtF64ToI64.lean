/-
  Layer 3b artifact #5 (N+4): Hoare triple over the **in-range happy
  path** of the compiler-rt f64→i64 conversion callee at bytes
  0x18EE0-0x18F90 of `qedsvm-rs/tests/fixtures/p_token.so` (release
  `p-token@v1.0.0-rc.1`).

  The callee converts an f64 bit pattern `r1` to its corresponding
  integer value in `r0`:

  - **In-range path** (`oneFp ≤ r1 < twoToSixtyFour_Fp`, finite
    positive normal f64 ≥ 1.0): extracts mantissa, sets hidden bit,
    shifts by (62 - exponent) — this artifact.
  - Below 1.0: returns 0.
  - Above 2^64 finite: returns -1.
  - NaN: returns -1.

  Pinocchio's downstream call (at byte 0x7720) passes the f64 result
  from the FP-compare callee (`fp_cmp_gt_path_spec`) into this one.
  For the "greater than" path of the FP-compare, the returned f64 is
  the lookup-table entry — typically `1.0` (bit pattern 0x3FF0...),
  which falls in the in-range domain proved here.

  **Path layout (abstract PCs).** 15 instructions executed, then `ja`
  to exit at PC 18. PCs 15-17 are unreachable on this path.

  - PC 0: `mov64 r0, 0` (initialize default return)
  - PC 1: `lddw r2, 0x3FF0000000000000` (= `oneFp`, IEEE 1.0)
  - PC 2: `jlt r1, r2, exit` — doesn't fire (r1 ≥ oneFp)
  - PC 3: `lddw r2, 0x43F0000000000000` (= `twoToSixtyFour_Fp`, IEEE 2^64)
  - PC 4: `jge r1, r2, PC 15` — doesn't fire (r1 < twoToSixtyFour_Fp)
  - PC 5-13: bit manipulation extracting integer value
  - PC 14: `ja +4` → PC 18 (exit)

  Like `CompilerRtFpCmp`, parameterized over `base : Nat` so it can
  be glued at any callee PC.
-/

import Svm.SBPF.InstructionSpecs
import Svm.SBPF.SLTactic
import Svm.SBPF.Macros

namespace Examples.CompilerRtF64ToI64

open Svm.SBPF
open Memory

/-- IEEE-754 f64 bit pattern for `+1.0`. Lower bound of the in-range
    domain — values below this would have triggered the early `jlt`
    return-zero path. -/
def oneFp : Nat := 0x3FF0000000000000

/-- IEEE-754 f64 bit pattern for `+2^64`. Upper bound (exclusive) of
    the in-range domain — values at or above this trigger the
    overflow path (returns -1 unless NaN). -/
def twoToSixtyFour_Fp : Nat := 0x43F0000000000000

/-- Bit-63 mask, equal to `2^63 = toU64 (-0x8000000000000000 : Int)`.
    Used to set the IEEE-754 hidden mantissa bit when reconstructing
    the integer. -/
def signBit : Nat := 0x8000000000000000

/-- The integer value computed by the in-range bit-manipulation
    sequence (PCs 5-13). Form matches the abstract chain output —
    `% 64` / `% U64_MODULUS` factors and the literal `11 % 64`
    appear as-is from the spec template; downstream consumers can
    simplify under `Nat.mod_mod_of_dvd` (64 ∣ 2^64) and concrete
    computation as needed. -/
def f64ToI64Result (r1 : Nat) : Nat :=
  let after_lsh11   := (r1 <<< (11 % 64)) % U64_MODULUS
  let with_hidden   := (after_lsh11 ||| signBit) % U64_MODULUS
  let exp           := r1 >>> (52 % 64)
  let shift_amount  := (wrapSub 0x3E exp &&& 63) % U64_MODULUS
  with_hidden >>> (shift_amount % 64)

/-! ## CodeReq for the in-range happy path

    15 entries at PCs base..base+14, in chain order. PCs base+15..17
    are NOT included; the `ja` at base+14 jumps over them. -/

def f64ToI64InRangeCr (base : Nat) : CodeReq :=
  ((((((((((((((CodeReq.singleton (base +  0) (.mov64 .r0 (.imm 0))).union
        (CodeReq.singleton (base +  1) (.lddw .r2 oneFp))).union
        (CodeReq.singleton (base +  2) (.jlt .r1 (.reg .r2) (base + 18)))).union
        (CodeReq.singleton (base +  3) (.lddw .r2 twoToSixtyFour_Fp))).union
        (CodeReq.singleton (base +  4) (.jge .r1 (.reg .r2) (base + 15)))).union
        (CodeReq.singleton (base +  5) (.mov64 .r0 (.reg .r1)))).union
        (CodeReq.singleton (base +  6) (.lsh64 .r0 (.imm 0xb)))).union
        (CodeReq.singleton (base +  7) (.lddw .r2 (-0x8000000000000000)))).union
        (CodeReq.singleton (base +  8) (.or64 .r0 (.reg .r2)))).union
        (CodeReq.singleton (base +  9) (.rsh64 .r1 (.imm 0x34)))).union
        (CodeReq.singleton (base + 10) (.mov64 .r2 (.imm 0x3e)))).union
        (CodeReq.singleton (base + 11) (.sub64 .r2 (.reg .r1)))).union
        (CodeReq.singleton (base + 12) (.and64 .r2 (.imm 0x3f)))).union
        (CodeReq.singleton (base + 13) (.rsh64 .r0 (.reg .r2)))).union
        (CodeReq.singleton (base + 14) (.ja (base + 18)))

theorem f64_to_i64_in_range_spec
    (base : Nat)
    (r1 : Nat)
    (initR0 initR2 : Nat)
    (h_lb : r1 ≥ oneFp)
    (h_ub : r1 < twoToSixtyFour_Fp) :
    cuTripleWithin 15 base (base + 18) (f64ToI64InRangeCr base)
      ((.r0 ↦ᵣ initR0) ** (.r2 ↦ᵣ initR2) ** (.r1 ↦ᵣ r1))
      ((.r0 ↦ᵣ f64ToI64Result r1) **
        (.r2 ↦ᵣ (wrapSub 0x3E (r1 >>> (52 % 64)) &&& 63) % U64_MODULUS) **
        (.r1 ↦ᵣ r1 >>> (52 % 64))) := by
  -- Helpers for `toU64` undoing on coerced Nats.
  have h_U64_eq : U64_MODULUS = 2 ^ 64 := rfl
  have h_toU64_natCast (n : Nat) (hn : n < 2 ^ 64) :
      toU64 ((↑n : Int)) = n := by
    unfold toU64
    rw [Int.emod_eq_of_lt (by omega : (0 : Int) ≤ ↑n) (by exact_mod_cast hn)]
    exact Int.toNat_natCast n
  have h_toU64_oneFp : toU64 ((↑oneFp : Int)) = oneFp :=
    h_toU64_natCast oneFp (by unfold oneFp; decide)
  have h_toU64_64Fp : toU64 ((↑twoToSixtyFour_Fp : Int)) = twoToSixtyFour_Fp :=
    h_toU64_natCast twoToSixtyFour_Fp (by unfold twoToSixtyFour_Fp; decide)
  have h_toU64_signBit : toU64 (-0x8000000000000000 : Int) = signBit := by
    unfold signBit toU64; decide
  have h_toU64_0x3E : toU64 (0x3e : Int) = 0x3E := by unfold toU64; decide
  have h_toU64_0x3f : toU64 (0x3f : Int) = 0x3F := by unfold toU64; decide
  have h_toU64_0xb : toU64 (0xb : Int) = 0xb := by unfold toU64; decide
  have h_toU64_0x34 : toU64 (0x34 : Int) = 0x34 := by unfold toU64; decide
  -- Specs in chain order.
  have h0  := mov64_imm_spec .r0 0 initR0 (base + 0) (by decide)
  have h1  := lddw_spec .r2 oneFp initR2 (base + 1) (by decide)
  have h2  := jlt_reg_spec .r1 .r2 r1 (toU64 oneFp) (base + 2) (base + 18)
  have h3  := lddw_spec .r2 twoToSixtyFour_Fp (toU64 oneFp) (base + 3) (by decide)
  have h4  := jge_reg_spec .r1 .r2 r1 (toU64 twoToSixtyFour_Fp)
              (base + 4) (base + 15)
  have h5  := mov64_reg_spec .r0 .r1 (toU64 0) r1 (base + 5) (by decide)
  have h6  := lsh64_imm_spec .r0 0xb r1 (base + 6) (by decide)
  have h7  := lddw_spec .r2 (-0x8000000000000000) (toU64 twoToSixtyFour_Fp)
              (base + 7) (by decide)
  have h8  := or64_reg_spec .r0 .r2 ((r1 <<< (toU64 0xb % 64)) % U64_MODULUS)
              (toU64 (-0x8000000000000000 : Int)) (base + 8) (by decide)
  have h9  := rsh64_imm_spec .r1 0x34 r1 (base + 9) (by decide)
  have h10 := mov64_imm_spec .r2 0x3e (toU64 (-0x8000000000000000 : Int))
              (base + 10) (by decide)
  have h11 := sub64_reg_spec .r2 .r1 (toU64 0x3e) (r1 >>> (toU64 0x34 % 64))
              (base + 11) (by decide)
  have h12 := and64_imm_spec .r2 0x3f
              (wrapSub (toU64 0x3e) (r1 >>> (toU64 0x34 % 64)))
              (base + 12) (by decide)
  have h13 := rsh64_reg_spec .r0 .r2
              (((r1 <<< (toU64 0xb % 64)) % U64_MODULUS ||| toU64 (-0x8000000000000000 : Int))
                % U64_MODULUS)
              ((wrapSub (toU64 0x3e) (r1 >>> (toU64 0x34 % 64)) &&& toU64 0x3f)
                % U64_MODULUS)
              (base + 13) (by decide)
  have h14 := ja_spec (base + 18) (base + 14)
  -- Collapse the two conditional jumps under the precondition that
  -- r1 is in the in-range domain.
  rw [show (if r1 < toU64 oneFp then (base + 18) else (base + 2) + 1)
            = (base + 3) from by
        rw [h_toU64_oneFp]
        have : ¬ (r1 < oneFp) := by omega
        simp [this]] at h2
  rw [show (if r1 ≥ toU64 twoToSixtyFour_Fp then (base + 15) else (base + 4) + 1)
            = (base + 5) from by
        rw [h_toU64_64Fp]
        have : ¬ (r1 ≥ twoToSixtyFour_Fp) := by omega
        simp [this]] at h4
  -- Simplify the chain hypotheses so their state atoms have a
  -- canonical form matching the goal's postcondition.
  simp only [h_toU64_oneFp, h_toU64_64Fp, h_toU64_signBit,
             h_toU64_0x3E, h_toU64_0x3f, h_toU64_0xb, h_toU64_0x34]
    at h1 h3 h6 h7 h8 h9 h10 h11 h12 h13
  -- Compose.
  unfold f64ToI64InRangeCr
  unfold f64ToI64Result
  sl_block_iter [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
                 h11, h12, h13, h14]

end Examples.CompilerRtF64ToI64
