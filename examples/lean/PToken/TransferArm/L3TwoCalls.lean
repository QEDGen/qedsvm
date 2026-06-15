/-
  Layer 3b #6: 48 CU two-call glue triple (PC 0→8).
  Extends the one-call glue with a second call_local (f64→i64 callee at synthetic PC 200).
  6 components: setup + call1 + callee1 + mov×2 + call2 + callee2 + exit_pops.
  Added precondition vs N+3: initR6 ∈ [oneFp, twoToSixtyFour_Fp) (f64→i64 in-range domain).
-/

import PToken.TransferArm.L2Bytecode
import CompilerRtF64ToI64
import SVM.SBPF.InstructionSpecs
import SVM.SBPF.Tactic.SL
import SVM.SBPF.Macros

namespace Examples.PTokenTransferArmTwoCalls

open SVM.SBPF
open Memory
open Examples.PTokenTransferArmSetup (transferArmSetupCr stackSlotOff)
open Examples.CompilerRtFpCmp
  (fpCmpGtPathCr signClearMask infBitPattern lookupTableBase gtOffset)
open Examples.CompilerRtF64ToI64
  (f64ToI64InRangeCr f64ToI64Result oneFp twoToSixtyFour_Fp signBit)
open Examples.PTokenTransferArm (transferArmCr calleeEntry callerContPc)

def calleeEntry2 : Nat := 200
def callerContPc2 : Nat := 8

def transferArmTwoCallsCr : CodeReq :=
  (((((transferArmCr.union
        (CodeReq.singleton 5 (.mov64 .r7 (.reg .r0)))).union
        (CodeReq.singleton 6 (.mov64 .r1 (.reg .r6)))).union
        (CodeReq.singleton 7 (.call_local calleeEntry2))).union
        (f64ToI64InRangeCr calleeEntry2)).union
        (CodeReq.singleton (calleeEntry2 + 18) .exit))

theorem p_token_transfer_arm_two_calls_spec
    (initR0 initR1 initR2 initR3 initR4 initR5 initR6 : Nat)
    (initR7 initR8 initR9 initR10 : Nat)
    (oldStackVal cmpTableGt : Nat)
    (h_initR6_sign  : initR6 < 2 ^ 63)
    (h_initR6_notNaN : initR6 ≤ infBitPattern)
    (h_initR6_lb    : initR6 ≥ oneFp)
    (h_initR6_ub    : initR6 < twoToSixtyFour_Fp)
    (hTable_lt      : cmpTableGt < 2 ^ 64) :
    cuTripleWithinMem 48 0 0 callerContPc2 transferArmTwoCallsCr
      ((.r1 ↦ᵣ initR1) ** (.r10 ↦ᵣ initR10) **
        (effectiveAddr initR10 stackSlotOff ↦U64 oldStackVal) **
        (.r6 ↦ᵣ initR6) ** (.r2 ↦ᵣ initR2) **
        (.r7 ↦ᵣ initR7) ** (.r8 ↦ᵣ initR8) ** (.r9 ↦ᵣ initR9) **
        callStackIs [] **
        (.r3 ↦ᵣ initR3) ** (.r0 ↦ᵣ initR0) ** (.r4 ↦ᵣ initR4) **
        (.r5 ↦ᵣ initR5) **
        (effectiveAddr (lookupTableBase + gtOffset) 0 ↦U64 cmpTableGt))
      ((.r1 ↦ᵣ initR6 >>> (52 % 64)) ** (.r10 ↦ᵣ initR10) **
        (effectiveAddr initR10 stackSlotOff ↦U64 toU64 0) **
        (.r6 ↦ᵣ initR6) **
        (.r2 ↦ᵣ (wrapSub 0x3E (initR6 >>> (52 % 64)) &&& 63) % U64_MODULUS) **
        (.r7 ↦ᵣ cmpTableGt) ** (.r8 ↦ᵣ initR8) ** (.r9 ↦ᵣ initR9) **
        callStackIs [] **
        (.r3 ↦ᵣ gtOffset) ** (.r0 ↦ᵣ f64ToI64Result initR6) **
        (.r4 ↦ᵣ initR6) **
        (.r5 ↦ᵣ toU64 0 ||| initR6) **
        (effectiveAddr (lookupTableBase + gtOffset) 0 ↦U64 cmpTableGt))
      (fun rt =>
        rt.containsWritable (effectiveAddr initR10 stackSlotOff) 8 = true ∧
        rt.containsRange
          (effectiveAddr (lookupTableBase + gtOffset) 0) 8 = true) := by
  -- N+3 glue needs `> 0`; derive it from `≥ oneFp`.
  have h_initR6_pos : initR6 > 0 := by
    have h_oneFp_pos : (0 : Nat) < oneFp := by unfold oneFp; decide
    omega
  have h_glue1 := Examples.PTokenTransferArm.p_token_transfer_arm_spec
    initR0 initR1 initR2 initR3 initR4 initR5 initR6
    initR7 initR8 initR9 initR10
    oldStackVal cmpTableGt
    h_initR6_sign h_initR6_notNaN h_initR6_pos hTable_lt
  have h_mov_r7 := mov64_reg_spec .r7 .r0 initR7 cmpTableGt 5 (by decide)
  have h_mov_r1 := mov64_reg_spec .r1 .r6
    (lookupTableBase + gtOffset) initR6 6 (by decide)
  have h_call2 := call_local_spec calleeEntry2 [] initR6 cmpTableGt
    initR8 initR9 initR10 7
  -- r1=initR6 (just set), r0=cmpTableGt, r2=toU64 0 (setup, untouched).
  have h_callee2 := Examples.CompilerRtF64ToI64.f64_to_i64_in_range_spec
    calleeEntry2 initR6 cmpTableGt (toU64 0) h_initR6_lb h_initR6_ub
  have h_exit2 := exit_pops_spec
    ⟨callerContPc2, initR6, cmpTableGt, initR8, initR9, initR10⟩
    [] initR6 cmpTableGt initR8 initR9 (initR10 + 0x1000)
    (calleeEntry2 + 18)
  unfold transferArmTwoCallsCr
  sl_block_iter [h_glue1, h_mov_r7, h_mov_r1, h_call2, h_callee2, h_exit2]

end Examples.PTokenTransferArmTwoCalls
