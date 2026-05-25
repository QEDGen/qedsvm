/-
  Layer 3b artifact #9 (N+8): the 4-instruction **post-call cleanup**
  between the third `call_local` exit (PC 13) and the far-jump
  (PC 17). Bytes 0x7758-0x7770 of
  `qedsvm-rs/tests/fixtures/p_token.so` (release
  `p-token@v1.0.0-rc.1`).

  Chain (adds 4 components to ThirdCall's 75-CU run through PC 13):

  - `mov64 r1, -0x1` at PC 13 — sentinel "FP-overflow returned" value
    bound to r1. Overwritten in two insns; only matters if the
    subsequent `jsgt` *takes* the branch, which the happy path
    arranges not to do.
  - `jsgt r0, 0x0, +0x1` at PC 14. After ThirdCall, r0 = cmpTableLt.
    Happy path needs `toSigned64 cmpTableLt ≤ 0` so the branch
    doesn't fire and we fall through to PC 15. The taken branch
    would skip the ldxdw, leaving the sentinel r1 = -1 bound — the
    "FP comparison says amount > maxI64AsDouble" error path that
    pinocchio bubbles up to its caller.
  - `ldxdw r1, [r10 - 0x828]` at PC 15. Restores the converted i64
    from the stack slot that L4TwoCallsExt stored at PC 9. After
    this, r1 = f64ToI64Result initR6 — the actual transfer amount
    expressed as an integer.
  - `mov64 r4, r9` at PC 16. Stages r9 (an accounts-array pointer
    held since the prelude) into r4 ahead of the far-jump.

  Triple advances PC 0 → 17. Total CU = 75 + 4 = **79 CU**.

  Re: ROADMAP wording. The roadmap says "1 CU remaining" before this
  arm. That framing was based on mollusk's measured 76-CU final
  total, but L1-L5's 75 CU was only the FP-validation prelude — the
  post-call cleanup (this arm, 4 CU) and the account-mutation block
  reached via the far-jump (~50 insns, several syscalls) still add
  real CU. The actual "remaining" CU at end of L5 is much more than
  1; the 76-CU mollusk number reflects the *total* program CU, not
  the CU-after-L5.

  New precondition vs ThirdCall: `toSigned64 cmpTableLt ≤ 0`. The
  LT-path callee returns r0 from the lookup table at
  `lookupTableBase + ltOffset`; for pinocchio's actual table, that
  value's high bit is set (= negative signed), so the jsgt falls
  through. The explicit precondition makes the dependence visible.

  Followup: PTokenTransferArmAccountMutation.lean (L7) covers the
  far-jump at PC 17 to byte 0x9068 plus the account-mutation block
  that actually shifts the token balances.
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

/-- PC right after the last instruction in this arm; the far-jump
    at PC 17 is the next arm's responsibility. -/
def beforeFarJumpPc : Nat := 17

/-- Combined CodeReq: extends `transferArmThirdCallCr` (which ends at
    PC 13) with the 4-insn post-call cleanup at PCs 13..16. -/
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
  -- Use ThirdCall as a single chain component.
  have h_third_call :=
    Examples.PTokenTransferArmThirdCall.p_token_transfer_arm_third_call_spec
      initR0 initR1 initR2 initR3 initR4 initR5 initR6
      initR7 initR8 initR9 initR10
      oldStackVal cmpTableGt cmpTableLt
      h_initR6_sign h_initR6_notNaN h_initR6_lb h_initR6_ub
      h_initR6_lt_maxI64 h_cmpTable_pos h_cmpTableLt_ub
  -- mov64 r1, -1 at PC 13. vOld of r1 = lookupTableBase + ltOffset
  -- (from ThirdCall's post).
  have h_mov_sentinel := mov64_imm_spec .r1 (-1)
    (lookupTableBase + ltOffset) 13 (by decide)
  -- jsgt r0, 0, target=16 at PC 14. Under h_cmpTableLt_le_zero, the
  -- branch doesn't fire and PC collapses to 15.
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
  -- ldxdw r1, [r10 - 0x828] at PC 15. v = f64ToI64Result initR6
  -- (written to the slot by L4TwoCallsExt's stxdw at PC 9, preserved
  -- through L5's callee body and exit). vOldDst of r1 = toU64 (-1)
  -- (from h_mov_sentinel).
  have h_f64_ub : f64ToI64Result initR6 < 2 ^ 64 := by
    unfold f64ToI64Result
    -- Final form is `with_hidden >>> shift_amount`. `with_hidden < 2^64`
    -- since it's `_ % U64_MODULUS`. Right shift of a value < 2^64 is
    -- also < 2^64.
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
  -- mov64 r4, r9 at PC 16. vOld of r4 = initR6 (from ThirdCall's post).
  have h_mov_r4 := mov64_reg_spec .r4 .r9 initR6 initR9 16 (by decide)
  unfold transferArmFarJumpCr beforeFarJumpPc
  show cuTripleWithinMem (75 + 1 + 1 + 1 + 1) 0 0 (16 + 1) _ _ _ _
  sl_block_iter [h_third_call, h_mov_sentinel, h_jsgt, h_ldxdw, h_mov_r4]

end Examples.PTokenTransferArmFarJump
