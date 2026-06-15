/-
  Layer 3b #8: 75 CU triple (PC 0→13). Third call_local (FP-cmp LT path, callee@PC300).
  LT path: checks initR6 < maxI64AsDouble so jsgt r0,0 at 0x7760 falls through.
  Added precondition vs TwoCallsExt: initR6 < toU64 (maxI64AsDouble : Int).
-/

import PToken.TransferArm.L4TwoCallsExt
import CompilerRtFpCmp
import SVM.SBPF.InstructionSpecs
import SVM.SBPF.Tactic.SL
import SVM.SBPF.Macros

namespace Examples.PTokenTransferArmThirdCall

open SVM.SBPF
open Memory
open Examples.PTokenTransferArmSetup (stackSlotOff)
open Examples.CompilerRtFpCmp
  (fpCmpLtPathCr lookupTableBase ltOffset gtOffset signClearMask infBitPattern)
open Examples.CompilerRtF64ToI64
  (f64ToI64Result oneFp twoToSixtyFour_Fp)
open Examples.PTokenTransferArmTwoCallsExt
  (transferArmTwoCallsExtCr afterPreCall3Pc maxI64AsDouble)

def calleeEntry3 : Nat := 300
def callerContPc3 : Nat := 13

def transferArmThirdCallCr : CodeReq :=
  (((transferArmTwoCallsExtCr.union
      (CodeReq.singleton 12 (.call_local calleeEntry3))).union
      (fpCmpLtPathCr calleeEntry3)).union
      (CodeReq.singleton (calleeEntry3 + 28) .exit))

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
theorem p_token_transfer_arm_third_call_spec
    (initR0 initR1 initR2 initR3 initR4 initR5 initR6 : Nat)
    (initR7 initR8 initR9 initR10 : Nat)
    (oldStackVal cmpTableGt cmpTableLt : Nat)
    (h_initR6_sign  : initR6 < 2 ^ 63)
    (h_initR6_notNaN : initR6 ≤ infBitPattern)
    (h_initR6_lb    : initR6 ≥ oneFp)
    (h_initR6_ub    : initR6 < twoToSixtyFour_Fp)
    (h_initR6_lt_maxI64 :
        initR6 < toU64 ((↑maxI64AsDouble : Int)))
    (h_cmpTable_pos : cmpTableGt < 2 ^ 63)
    (h_cmpTableLt_ub : cmpTableLt < 2 ^ 64) :
    cuTripleWithinMem (52 + 1 + 21 + 1) 0 0 callerContPc3
      transferArmThirdCallCr
      ((.r1 ↦ᵣ initR1) ** (.r10 ↦ᵣ initR10) **
        (effectiveAddr initR10 stackSlotOff ↦U64 oldStackVal) **
        (.r6 ↦ᵣ initR6) ** (.r2 ↦ᵣ initR2) **
        (.r7 ↦ᵣ initR7) ** (.r8 ↦ᵣ initR8) ** (.r9 ↦ᵣ initR9) **
        callStackIs [] **
        (.r3 ↦ᵣ initR3) ** (.r0 ↦ᵣ initR0) ** (.r4 ↦ᵣ initR4) **
        (.r5 ↦ᵣ initR5) **
        (effectiveAddr (lookupTableBase + gtOffset) 0 ↦U64 cmpTableGt) **
        (effectiveAddr (lookupTableBase + ltOffset) 0 ↦U64 cmpTableLt))
      ((.r1 ↦ᵣ lookupTableBase + ltOffset) ** (.r10 ↦ᵣ initR10) **
        (effectiveAddr initR10 stackSlotOff ↦U64 f64ToI64Result initR6) **
        (.r6 ↦ᵣ initR6) **
        (.r2 ↦ᵣ toU64 ((↑maxI64AsDouble : Int))) **
        (.r7 ↦ᵣ cmpTableGt) ** (.r8 ↦ᵣ initR8) ** (.r9 ↦ᵣ initR9) **
        callStackIs [] **
        (.r3 ↦ᵣ ltOffset) ** (.r0 ↦ᵣ cmpTableLt) ** (.r4 ↦ᵣ initR6) **
        (.r5 ↦ᵣ toU64 ((↑maxI64AsDouble : Int)) ||| initR6) **
        (effectiveAddr (lookupTableBase + gtOffset) 0 ↦U64 cmpTableGt) **
        (effectiveAddr (lookupTableBase + ltOffset) 0 ↦U64 cmpTableLt))
      (fun rt =>
        ((rt.containsWritable (effectiveAddr initR10 stackSlotOff) 8 = true ∧
          rt.containsRange
            (effectiveAddr (lookupTableBase + gtOffset) 0) 8 = true) ∧
         rt.containsWritable (effectiveAddr initR10 stackSlotOff) 8 = true) ∧
        rt.containsRange
          (effectiveAddr (lookupTableBase + ltOffset) 0) 8 = true) := by
  have h_two_calls_ext :=
    Examples.PTokenTransferArmTwoCallsExt.p_token_transfer_arm_two_calls_ext_spec
      initR0 initR1 initR2 initR3 initR4 initR5 initR6
      initR7 initR8 initR9 initR10
      oldStackVal cmpTableGt
      h_initR6_sign h_initR6_notNaN h_initR6_lb h_initR6_ub
      h_cmpTable_pos
  have h_call3 := call_local_spec calleeEntry3 [] initR6 cmpTableGt
    initR8 initR9 initR10 12
  -- Third callee LT path: A=initR6, B=toU64(maxI64AsDouble), from TwoCallsExt post.
  have hB_sign : toU64 ((↑maxI64AsDouble : Int)) < 2 ^ 63 := by
    unfold maxI64AsDouble toU64; decide
  have hB_notNaN : toU64 ((↑maxI64AsDouble : Int)) ≤ infBitPattern := by
    unfold maxI64AsDouble toU64 infBitPattern; decide
  have h_callee3 := Examples.CompilerRtFpCmp.fp_cmp_lt_path_spec
    calleeEntry3 initR6 (toU64 ((↑maxI64AsDouble : Int)))
    (f64ToI64Result initR6) gtOffset initR6 (toU64 0 ||| initR6) initR6
    cmpTableLt
    h_initR6_sign hB_sign h_initR6_notNaN hB_notNaN
    h_initR6_lt_maxI64 h_cmpTableLt_ub
  have h_exit3 := exit_pops_spec
    ⟨callerContPc3, initR6, cmpTableGt, initR8, initR9, initR10⟩
    [] infBitPattern cmpTableGt initR8 initR9 (initR10 + 0x1000)
    (calleeEntry3 + 28)
  unfold transferArmThirdCallCr
  sl_block_iter [h_two_calls_ext, h_call3, h_callee3, h_exit3]

end Examples.PTokenTransferArmThirdCall
