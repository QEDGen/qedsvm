/-
  Layer 3b artifact #7 (N+6): **Extension of the two-call glue**
  through the post-call linear+branch+stxdw slice at bytes
  0x7728-0x7750 (synthetic PCs 8..11), stopping just before the
  third `call_local`.

  Chain (adds 4 components to N+5's two-call glue):

  - `p_token_transfer_arm_two_calls_spec` — the existing 6-component
    glue, used here as a single chain component.
  - `jslt r7, 0x0, target=10` at synthetic PC 8. Under
    `cmpTableGt < 2^63` (sign bit of r7 = 0), this doesn't fire and
    collapses to PC 9. (The taken branch — `r7 < 0 signed`, i.e.,
    the FP-cmp returned a "less than" or NaN sentinel — would skip
    the stxdw; this artifact commits to the happy path.)
  - `stxdw [r10 - 0x828], r0` at PC 9. Writes `f64ToI64Result initR6`
    to the stack slot that the original setup zeroed (overwriting
    `toU64 0` with the f64→i64 conversion result).
  - `mov64 r1, r6` at PC 10. r1 := initR6 (input to the next call).
  - `lddw r2, 0x43efffffffffffff` at PC 11. r2 := an f64 constant
    (= largest representable double less than 2^63) — second
    argument to the upcoming third `call_local`.

  Triple advances PC 0 → 12. Total CU = 48 + 1 + 1 + 1 + 1 = 52.

  **New precondition vs N+5:** `cmpTableGt < 2 ^ 63` (tighter than
  the existing `< 2 ^ 64`). This is the sign-bit-clear guarantee
  needed to collapse the `jslt`. For pinocchio's actual `cmpTableGt`
  = `0x3FF0000000000000` (IEEE 1.0), this is satisfied trivially.

  Methodology: this is the smaller scope of two N+6 options listed
  in the post-N+5 handoff. The larger option (also prove the third
  callee triple + glue it in) is N+7 / N+8.
-/

import PTokenTransferArmTwoCalls
import Svm.SBPF.InstructionSpecs
import Svm.SBPF.SLTactic
import Svm.SBPF.Macros

namespace Examples.PTokenTransferArmTwoCallsExt

open Svm.SBPF
open Memory
open Examples.PTokenTransferArmSetup (stackSlotOff)
open Examples.CompilerRtFpCmp
  (signClearMask infBitPattern lookupTableBase gtOffset)
open Examples.CompilerRtF64ToI64
  (f64ToI64Result oneFp twoToSixtyFour_Fp signBit)
open Examples.PTokenTransferArmTwoCalls
  (transferArmTwoCallsCr calleeEntry2 callerContPc2)

/-- f64 constant loaded at synthetic PC 11 (byte 0x7740). Hex
    `0x43efffffffffffff` is the largest representable double less
    than 2^63 — the "max value the next callee will accept without
    overflow" constant. -/
def maxI64AsDouble : Nat := 0x43EFFFFFFFFFFFFF

/-- PC right after the upcoming third `call_local` (which isn't
    included in this artifact). Whatever this is in the next session
    is fine — this artifact's exit PC is the literal PC value 12. -/
def afterPreCall3Pc : Nat := 12

def transferArmTwoCallsExtCr : CodeReq :=
  (((transferArmTwoCallsCr.union
      (CodeReq.singleton 8 (.jslt .r7 (.imm 0) 10))).union
      (CodeReq.singleton 9 (.stx .dword .r10 stackSlotOff .r0))).union
      (CodeReq.singleton 10 (.mov64 .r1 (.reg .r6)))).union
      (CodeReq.singleton 11 (.lddw .r2 maxI64AsDouble))

theorem p_token_transfer_arm_two_calls_ext_spec
    (initR0 initR1 initR2 initR3 initR4 initR5 initR6 : Nat)
    (initR7 initR8 initR9 initR10 : Nat)
    (oldStackVal cmpTableGt : Nat)
    (h_initR6_sign  : initR6 < 2 ^ 63)
    (h_initR6_notNaN : initR6 ≤ infBitPattern)
    (h_initR6_lb    : initR6 ≥ oneFp)
    (h_initR6_ub    : initR6 < twoToSixtyFour_Fp)
    (h_cmpTable_pos : cmpTableGt < 2 ^ 63) :
    cuTripleWithinMem 52 0 afterPreCall3Pc transferArmTwoCallsExtCr
      ((.r1 ↦ᵣ initR1) ** (.r10 ↦ᵣ initR10) **
        (effectiveAddr initR10 stackSlotOff ↦U64 oldStackVal) **
        (.r6 ↦ᵣ initR6) ** (.r2 ↦ᵣ initR2) **
        (.r7 ↦ᵣ initR7) ** (.r8 ↦ᵣ initR8) ** (.r9 ↦ᵣ initR9) **
        callStackIs [] **
        (.r3 ↦ᵣ initR3) ** (.r0 ↦ᵣ initR0) ** (.r4 ↦ᵣ initR4) **
        (.r5 ↦ᵣ initR5) **
        (effectiveAddr (lookupTableBase + gtOffset) 0 ↦U64 cmpTableGt))
      ((.r1 ↦ᵣ initR6) ** (.r10 ↦ᵣ initR10) **
        (effectiveAddr initR10 stackSlotOff ↦U64 f64ToI64Result initR6) **
        (.r6 ↦ᵣ initR6) ** (.r2 ↦ᵣ toU64 ((↑maxI64AsDouble : Int))) **
        (.r7 ↦ᵣ cmpTableGt) ** (.r8 ↦ᵣ initR8) ** (.r9 ↦ᵣ initR9) **
        callStackIs [] **
        (.r3 ↦ᵣ gtOffset) ** (.r0 ↦ᵣ f64ToI64Result initR6) **
        (.r4 ↦ᵣ initR6) **
        (.r5 ↦ᵣ toU64 0 ||| initR6) **
        (effectiveAddr (lookupTableBase + gtOffset) 0 ↦U64 cmpTableGt))
      (fun rt =>
        (rt.containsWritable (effectiveAddr initR10 stackSlotOff) 8 = true ∧
          rt.containsRange
            (effectiveAddr (lookupTableBase + gtOffset) 0) 8 = true) ∧
        rt.containsWritable (effectiveAddr initR10 stackSlotOff) 8 = true) := by
  -- Use the existing N+5 two-call glue as a single component.
  have h_cmp_lt_64 : cmpTableGt < 2 ^ 64 := by
    have h63 : (2 : Nat) ^ 63 < 2 ^ 64 := by decide
    omega
  have h_glue2 := Examples.PTokenTransferArmTwoCalls.p_token_transfer_arm_two_calls_spec
    initR0 initR1 initR2 initR3 initR4 initR5 initR6
    initR7 initR8 initR9 initR10
    oldStackVal cmpTableGt
    h_initR6_sign h_initR6_notNaN h_initR6_lb h_initR6_ub
    h_cmp_lt_64
  -- jslt r7, 0 at PC 8: r7 = cmpTableGt < 2^63, so toSigned64 r7 ≥ 0,
  -- not < 0 signed → branch doesn't fire.
  have h_jslt := jslt_imm_spec .r7 0 cmpTableGt 8 10
  have h_signed_cmpTable : toSigned64 cmpTableGt = ↑cmpTableGt := by
    unfold toSigned64
    have h_lt : cmpTableGt < U64_MODULUS / 2 := by
      show cmpTableGt < 2 ^ 63
      exact h_cmpTable_pos
    exact if_pos h_lt
  have h_toU64_0 : toU64 (0 : Int) = 0 := by unfold toU64; decide
  have h_signed_0 : toSigned64 0 = 0 := by
    unfold toSigned64
    have h_lt : (0 : Nat) < U64_MODULUS / 2 := by decide
    rw [if_pos h_lt]; rfl
  rw [show (if toSigned64 cmpTableGt < toSigned64 (toU64 0)
            then (10 : Nat) else 8 + 1) = 9 from by
        rw [h_signed_cmpTable, h_toU64_0, h_signed_0]
        have h_nonneg : (0 : Int) ≤ ↑cmpTableGt := by
          exact_mod_cast Nat.zero_le _
        have h_not : ¬ ((↑cmpTableGt : Int) < 0) := by omega
        simp [h_not]] at h_jslt
  -- stxdw at PC 9: writes r0 (= f64ToI64Result initR6) to stack slot.
  -- The previous mem atom value was toU64 0 (from N+5's exit state).
  have h_stxdw := stxdw_spec .r10 .r0 stackSlotOff initR10
    (f64ToI64Result initR6) (toU64 0) 9
  -- mov64 r1, r6 at PC 10. vOld of r1 = initR6 >>> (52 % 64) (from N+5).
  have h_mov_r1 := mov64_reg_spec .r1 .r6
    (initR6 >>> (52 % 64)) initR6 10 (by decide)
  -- lddw r2, maxI64AsDouble at PC 11. vOld of r2 = the wrapSub thing from N+5.
  have h_lddw := lddw_spec .r2 maxI64AsDouble
    ((wrapSub 0x3E (initR6 >>> (52 % 64)) &&& 63) % U64_MODULUS) 11 (by decide)
  unfold transferArmTwoCallsExtCr afterPreCall3Pc
  show cuTripleWithinMem (48 + 1 + 1 + 1 + 1) 0 (11 + 1) _ _ _ _
  sl_block_iter [h_glue2, h_jslt, h_stxdw, h_mov_r1, h_lddw]

end Examples.PTokenTransferArmTwoCallsExt
