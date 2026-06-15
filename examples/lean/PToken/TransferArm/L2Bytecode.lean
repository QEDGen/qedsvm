/-
  L3b N+3 glue: setup → call_local → FP-cmp callee → exit_pops.

  Threads `callStackIs` through a real cross-procedure composition for the first time.
  Synthetic PC layout (100 = calleeEntry); real pinocchio: setup@0x76e8, callee@0x185F8.
-/

import PToken.TransferArm.L1Setup
import CompilerRtFpCmp
import SVM.SBPF.InstructionSpecs
import SVM.SBPF.Tactic.SL
import SVM.SBPF.Macros

namespace Examples.PTokenTransferArm

open SVM.SBPF
open Memory
open Examples.PTokenTransferArmSetup (transferArmSetupCr stackSlotOff)
open Examples.CompilerRtFpCmp
  (fpCmpGtPathCr signClearMask infBitPattern lookupTableBase gtOffset)

/-- Synthetic callee base PC (real pinocchio: 0x185F8 = absolute PC 12603). -/
def calleeEntry : Nat := 100

/-- Caller continuation: return address for exit_pops. -/
def callerContPc : Nat := 5

/-- CodeReq: setup ∪ call_local ∪ callee_body ∪ exit. -/
def transferArmCr : CodeReq :=
  (((transferArmSetupCr.union
      (CodeReq.singleton 4 (.call_local calleeEntry))).union
      (fpCmpGtPathCr calleeEntry)).union
      (CodeReq.singleton (calleeEntry + 28) .exit))

theorem p_token_transfer_arm_spec
    (initR0 initR1 initR2 initR3 initR4 initR5 initR6 : Nat)
    (initR7 initR8 initR9 initR10 : Nat)
    (oldStackVal cmpTableGt : Nat)
    (h_initR6_sign  : initR6 < 2 ^ 63)
    (h_initR6_notNaN : initR6 ≤ infBitPattern)
    (h_initR6_pos   : initR6 > 0)
    (hTable_lt      : cmpTableGt < 2 ^ 64) :
    cuTripleWithinMem 29 0 0 callerContPc transferArmCr
      ((.r1 ↦ᵣ initR1) ** (.r10 ↦ᵣ initR10) **
        (effectiveAddr initR10 stackSlotOff ↦U64 oldStackVal) **
        (.r6 ↦ᵣ initR6) ** (.r2 ↦ᵣ initR2) **
        (.r7 ↦ᵣ initR7) ** (.r8 ↦ᵣ initR8) ** (.r9 ↦ᵣ initR9) **
        callStackIs [] **
        (.r3 ↦ᵣ initR3) ** (.r0 ↦ᵣ initR0) ** (.r4 ↦ᵣ initR4) **
        (.r5 ↦ᵣ initR5) **
        (effectiveAddr (lookupTableBase + gtOffset) 0 ↦U64 cmpTableGt))
      ((.r1 ↦ᵣ lookupTableBase + gtOffset) ** (.r10 ↦ᵣ initR10) **
        (effectiveAddr initR10 stackSlotOff ↦U64 toU64 0) **
        (.r6 ↦ᵣ initR6) ** (.r2 ↦ᵣ toU64 0) **
        (.r7 ↦ᵣ initR7) ** (.r8 ↦ᵣ initR8) ** (.r9 ↦ᵣ initR9) **
        callStackIs [] **
        (.r3 ↦ᵣ gtOffset) ** (.r0 ↦ᵣ cmpTableGt) ** (.r4 ↦ᵣ initR6) **
        (.r5 ↦ᵣ toU64 0 ||| initR6) **
        (effectiveAddr (lookupTableBase + gtOffset) 0 ↦U64 cmpTableGt))
      (fun rt =>
        rt.containsWritable (effectiveAddr initR10 stackSlotOff) 8 = true ∧
        rt.containsRange
          (effectiveAddr (lookupTableBase + gtOffset) 0) 8 = true) := by
  have h_setup := Examples.PTokenTransferArmSetup.p_token_transfer_arm_setup_spec
    initR1 initR2 initR6 initR10 oldStackVal
  have h_call := call_local_spec calleeEntry [] initR6 initR7 initR8 initR9
    initR10 4
  -- Callee entry: A=initR6 (after setup), B=0.
  have hB_sign : (toU64 0) < 2 ^ 63 := by unfold toU64; decide
  have hB_notNaN : (toU64 0) ≤ infBitPattern := by
    unfold toU64 infBitPattern; decide
  have h_callee := Examples.CompilerRtFpCmp.fp_cmp_gt_path_spec
    calleeEntry initR6 (toU64 0)
    initR0 initR3 initR4 initR5 initR6 cmpTableGt
    h_initR6_sign hB_sign h_initR6_notNaN hB_notNaN h_initR6_pos hTable_lt
  have h_exit := exit_pops_spec
    ⟨callerContPc, initR6, initR7, initR8, initR9, initR10⟩
    [] infBitPattern initR7 initR8 initR9 (initR10 + 0x1000)
    (calleeEntry + 28)
  unfold transferArmCr
  sl_block_iter [h_setup, h_call, h_callee, h_exit]

end Examples.PTokenTransferArm
