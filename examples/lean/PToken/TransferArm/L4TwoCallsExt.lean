/-
  L3b N+6 extension: two-call glue + post-call jslt/stxdw/mov/lddw (bytes 0x7728-0x7750).

  Adds 4 insns to N+5: jslt-NT (cmpTableGt<2^63 → sign-bit=0), stxdw stack slot,
  mov r1←r6, lddw r2←maxI64AsDouble. 52 CU, pc → 12.
  New precondition: `cmpTableGt < 2^63` (sign-bit-clear for jslt collapse).
-/

import PToken.TransferArm.L3TwoCalls
import SVM.SBPF.InstructionSpecs
import SVM.SBPF.Tactic.SL
import SVM.SBPF.Macros

namespace Examples.PTokenTransferArmTwoCallsExt

open SVM.SBPF
open Memory
open Examples.PTokenTransferArmSetup (stackSlotOff)
open Examples.CompilerRtFpCmp
  (signClearMask infBitPattern lookupTableBase gtOffset)
open Examples.CompilerRtF64ToI64
  (f64ToI64Result oneFp twoToSixtyFour_Fp signBit)
open Examples.PTokenTransferArmTwoCalls
  (transferArmTwoCallsCr calleeEntry2 callerContPc2)

/-- Largest f64 < 2^63 (`0x43efffffffffffff`); loaded by lddw at PC 11. -/
def maxI64AsDouble : Nat := 0x43EFFFFFFFFFFFFF

/-- Exit PC of this artifact (literal 12; third call_local is not included here). -/
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
    cuTripleWithinMem 52 0 0 afterPreCall3Pc transferArmTwoCallsExtCr
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
  have h_cmp_lt_64 : cmpTableGt < 2 ^ 64 := by
    have h63 : (2 : Nat) ^ 63 < 2 ^ 64 := by decide
    omega
  have h_glue2 := Examples.PTokenTransferArmTwoCalls.p_token_transfer_arm_two_calls_spec
    initR0 initR1 initR2 initR3 initR4 initR5 initR6
    initR7 initR8 initR9 initR10
    oldStackVal cmpTableGt
    h_initR6_sign h_initR6_notNaN h_initR6_lb h_initR6_ub
    h_cmp_lt_64
  -- jslt collapse: cmpTableGt < 2^63 → toSigned64 r7 ≥ 0, branch NT.
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
  have h_stxdw := stxdw_spec .r10 .r0 stackSlotOff initR10
    (f64ToI64Result initR6) (toU64 0) 9
  have h_mov_r1 := mov64_reg_spec .r1 .r6
    (initR6 >>> (52 % 64)) initR6 10 (by decide)
  have h_lddw := lddw_spec .r2 maxI64AsDouble
    ((wrapSub 0x3E (initR6 >>> (52 % 64)) &&& 63) % U64_MODULUS) 11 (by decide)
  unfold transferArmTwoCallsExtCr afterPreCall3Pc
  show cuTripleWithinMem (48 + 1 + 1 + 1 + 1) 0 0 (11 + 1) _ _ _ _
  sl_block_iter [h_glue2, h_jslt, h_stxdw, h_mov_r1, h_lddw]

end Examples.PTokenTransferArmTwoCallsExt
