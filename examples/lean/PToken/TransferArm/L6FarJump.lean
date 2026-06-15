/-
  L3b N+8: 4-insn post-call cleanup (bytes 0x7758-0x7770, p-token@v1.0.0-rc.1).

  Adds to ThirdCall: mov r1←-1 (FP-overflow sentinel), jsgt-NT (cmpTableLt≤0 signed),
  ldxdw r1←stack (restores f64ToI64Result), mov r4←r9. 79 CU total, pc → 17.
  New precondition: `toSigned64 cmpTableLt ≤ 0` (jsgt collapse).
-/

import PToken.TransferArm.L5ThirdCall
import SVM.SBPF.InstructionSpecs
import SVM.SBPF.Tactic.SL
import SVM.SBPF.Macros

namespace Examples.PTokenTransferArmFarJump

open SVM.SBPF
open Memory
open Examples.PTokenTransferArmSetup (stackSlotOff)
open Examples.CompilerRtFpCmp
  (lookupTableBase ltOffset gtOffset signClearMask infBitPattern)
open Examples.CompilerRtF64ToI64
  (f64ToI64Result oneFp twoToSixtyFour_Fp)
open Examples.PTokenTransferArmTwoCallsExt (maxI64AsDouble)
open Examples.PTokenTransferArmThirdCall
  (transferArmThirdCallCr callerContPc3 calleeEntry3)

/-- Exit PC of this arm (far-jump at PC 17 is handled by the next arm). -/
def beforeFarJumpPc : Nat := 17

/-- CodeReq: `transferArmThirdCallCr` + 4-insn cleanup at PCs 13..16. -/
def transferArmFarJumpCr : CodeReq :=
  (((transferArmThirdCallCr.union
      (CodeReq.singleton 13 (.mov64 .r1 (.imm (-1))))).union
      (CodeReq.singleton 14 (.jsgt .r0 (.imm 0) 16))).union
      (CodeReq.singleton 15 (.ldx .dword .r1 .r10 stackSlotOff))).union
      (CodeReq.singleton 16 (.mov64 .r4 (.reg .r9)))

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
theorem p_token_transfer_arm_far_jump_spec
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
    (h_cmpTableLt_ub : cmpTableLt < 2 ^ 64)
    (h_cmpTableLt_le_zero : toSigned64 cmpTableLt ≤ 0) :
    cuTripleWithinMem (75 + 4) 0 0 beforeFarJumpPc
      transferArmFarJumpCr
      ((.r1 ↦ᵣ initR1) ** (.r10 ↦ᵣ initR10) **
        (effectiveAddr initR10 stackSlotOff ↦U64 oldStackVal) **
        (.r6 ↦ᵣ initR6) ** (.r2 ↦ᵣ initR2) **
        (.r7 ↦ᵣ initR7) ** (.r8 ↦ᵣ initR8) ** (.r9 ↦ᵣ initR9) **
        callStackIs [] **
        (.r3 ↦ᵣ initR3) ** (.r0 ↦ᵣ initR0) ** (.r4 ↦ᵣ initR4) **
        (.r5 ↦ᵣ initR5) **
        (effectiveAddr (lookupTableBase + gtOffset) 0 ↦U64 cmpTableGt) **
        (effectiveAddr (lookupTableBase + ltOffset) 0 ↦U64 cmpTableLt))
      ((.r1 ↦ᵣ f64ToI64Result initR6) ** (.r10 ↦ᵣ initR10) **
        (effectiveAddr initR10 stackSlotOff ↦U64 f64ToI64Result initR6) **
        (.r6 ↦ᵣ initR6) **
        (.r2 ↦ᵣ toU64 ((↑maxI64AsDouble : Int))) **
        (.r7 ↦ᵣ cmpTableGt) ** (.r8 ↦ᵣ initR8) ** (.r9 ↦ᵣ initR9) **
        callStackIs [] **
        (.r3 ↦ᵣ ltOffset) ** (.r0 ↦ᵣ cmpTableLt) ** (.r4 ↦ᵣ initR9) **
        (.r5 ↦ᵣ toU64 ((↑maxI64AsDouble : Int)) ||| initR6) **
        (effectiveAddr (lookupTableBase + gtOffset) 0 ↦U64 cmpTableGt) **
        (effectiveAddr (lookupTableBase + ltOffset) 0 ↦U64 cmpTableLt))
      (fun rt =>
        (((rt.containsWritable (effectiveAddr initR10 stackSlotOff) 8 = true ∧
            rt.containsRange
              (effectiveAddr (lookupTableBase + gtOffset) 0) 8 = true) ∧
           rt.containsWritable (effectiveAddr initR10 stackSlotOff) 8 = true) ∧
          rt.containsRange
            (effectiveAddr (lookupTableBase + ltOffset) 0) 8 = true) ∧
        rt.containsRange (effectiveAddr initR10 stackSlotOff) 8 = true) := by
  have h_third_call :=
    Examples.PTokenTransferArmThirdCall.p_token_transfer_arm_third_call_spec
      initR0 initR1 initR2 initR3 initR4 initR5 initR6
      initR7 initR8 initR9 initR10
      oldStackVal cmpTableGt cmpTableLt
      h_initR6_sign h_initR6_notNaN h_initR6_lb h_initR6_ub
      h_initR6_lt_maxI64 h_cmpTable_pos h_cmpTableLt_ub
  have h_mov_sentinel := mov64_imm_spec .r1 (-1)
    (lookupTableBase + ltOffset) 13 (by decide)
  -- jsgt collapse: cmpTableLt≤0 signed → branch NT, falls to PC 15.
  have h_jsgt := jsgt_imm_spec .r0 0 cmpTableLt 14 16
  have h_toU64_0 : toU64 (0 : Int) = 0 := by unfold toU64; decide
  have h_signed_0 : toSigned64 0 = 0 := by
    unfold toSigned64
    have h_lt : (0 : Nat) < U64_MODULUS / 2 := by decide
    rw [if_pos h_lt]; rfl
  rw [show (if toSigned64 cmpTableLt > toSigned64 (toU64 0)
            then (16 : Nat) else 14 + 1) = 15 from by
        rw [h_toU64_0, h_signed_0]
        have h_not : ¬ (toSigned64 cmpTableLt > (0 : Int)) := by
          omega
        simp [h_not]] at h_jsgt
  -- f64ToI64Result < 2^64: it's `_ % U64_MODULUS >>> shift`, both bounded.
  have h_f64_ub : f64ToI64Result initR6 < 2 ^ 64 := by
    unfold f64ToI64Result
    have h_mod : ∀ n : Nat, n % U64_MODULUS < 2 ^ 64 := by
      intro n
      show n % U64_MODULUS < U64_MODULUS
      exact Nat.mod_lt _ (by decide)
    have h_shr_bound : ∀ a b : Nat, a < 2 ^ 64 → a >>> b < 2 ^ 64 := by
      intro a b ha
      exact Nat.lt_of_le_of_lt (Nat.shiftRight_le a b) ha
    exact h_shr_bound _ _ (h_mod _)
  have h_ldxdw := ldxdw_spec .r1 .r10 stackSlotOff
    (toU64 ((-1) : Int)) initR10 (f64ToI64Result initR6) 15
    (by decide) h_f64_ub
  have h_mov_r4 := mov64_reg_spec .r4 .r9 initR6 initR9 16 (by decide)
  unfold transferArmFarJumpCr beforeFarJumpPc
  show cuTripleWithinMem (75 + 1 + 1 + 1 + 1) 0 0 (16 + 1) _ _ _ _
  sl_block_iter [h_third_call, h_mov_sentinel, h_jsgt, h_ldxdw, h_mov_r4]

end Examples.PTokenTransferArmFarJump
