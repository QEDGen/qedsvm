/-
  Layer 3b artifact #8 (N+7): the third `call_local` into the
  compiler-rt FP-cmp callee — but this time via the **LT path**
  (`A < B`), not the GT path that the first call used.

  Why LT here: after the second call (f64→i64) writes the converted
  value to the stack, the third call asks "is the original f64
  amount ≤ maxI64AsDouble (the largest representable signed i64 as
  a double)?" The happy path needs `r0 ≤ 0` signed after the call
  so the subsequent `jsgt r0, 0` at byte 0x7760 falls through and
  the converted i64 stays bound to r1 (rather than being replaced
  by the `-1` error sentinel). `r0 ≤ 0` signed comes from a LT or
  EQ classification. This artifact commits to the strict LT case;
  EQ would be a sibling lemma.

  Chain (adds 3 components to TwoCallsExt's 52-CU glue):

    - `p_token_transfer_arm_two_calls_ext_spec` — the existing 52-CU
      chain through PC 12. Used as a single component.
    - `call_local 300` at PC 12 — third call site.
    - `fp_cmp_lt_path_spec` at base 300 — the third callee body,
      taking the LT path (= same `fpCmpGtPathCr` code, different
      classification, different sentinel slot).
    - `exit_pops_spec` at PC 328 — pops the frame, restores
      r6..r10, returns to caller-continuation PC 13.

  Triple advances PC 0 → 13. Total CU = 52 + 1 + 21 + 1 = 75.

  New precondition vs TwoCallsExt: `initR6 < toU64 (↑maxI64AsDouble : Int)`
  — the LT-path condition. For pinocchio's actual usage this is
  satisfied for any in-range Transfer amount (amounts ≤ 2^63 - 1 as
  signed i64).

  Followup: PTokenTransferArmFarJump.lean covers the 11-insn post-call
  slice through the `ja +0x422` to byte 0x9068 (the account-mutation
  block entry).
-/

import PTokenTransferArmTwoCallsExt
import CompilerRtFpCmp
import Svm.SBPF.InstructionSpecs
import Svm.SBPF.SLTactic
import Svm.SBPF.Macros

namespace Examples.PTokenTransferArmThirdCall

open Svm.SBPF
open Memory
open Examples.PTokenTransferArmSetup (stackSlotOff)
open Examples.CompilerRtFpCmp
  (fpCmpLtPathCr lookupTableBase ltOffset gtOffset signClearMask infBitPattern)
open Examples.CompilerRtF64ToI64
  (f64ToI64Result oneFp twoToSixtyFour_Fp)
open Examples.PTokenTransferArmTwoCallsExt
  (transferArmTwoCallsExtCr afterPreCall3Pc maxI64AsDouble)

/-- Synthetic base PC for the third callee body. -/
def calleeEntry3 : Nat := 300

/-- PC of the caller's instruction right after the third
    `call_local` — where the third `exit_pops` returns to. -/
def callerContPc3 : Nat := 13

/-- Combined CodeReq: extends `transferArmTwoCallsExtCr` (which
    ends at PC 12) with the third call_local, the LT-path callee
    body, and the callee's exit. -/
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
    cuTripleWithinMem (52 + 1 + 21 + 1) 0 callerContPc3
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
  -- Use TwoCallsExt as a single chain component.
  have h_two_calls_ext :=
    Examples.PTokenTransferArmTwoCallsExt.p_token_transfer_arm_two_calls_ext_spec
      initR0 initR1 initR2 initR3 initR4 initR5 initR6
      initR7 initR8 initR9 initR10
      oldStackVal cmpTableGt
      h_initR6_sign h_initR6_notNaN h_initR6_lb h_initR6_ub
      h_cmpTable_pos
  -- Third call_local at PC 12. Pre-state (from TwoCallsExt's post):
  -- r6 = initR6, r7 = cmpTableGt, r8 = initR8, r9 = initR9, r10 = initR10.
  have h_call3 := call_local_spec calleeEntry3 [] initR6 cmpTableGt
    initR8 initR9 initR10 12
  -- Third callee body — LT path. Inputs from TwoCallsExt's post:
  -- A := r1's value = initR6, B := r2's value = toU64 (↑maxI64AsDouble : Int).
  -- Callee's view of its own initial r0/r3/r4/r5 = the caller's post r0/r3/r4/r5.
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
  -- Third exit_pops at PC calleeEntry3 + 28 = 328.
  -- Frame to pop: retPc = 13, savedR6..R10 = the caller's pre-call values
  -- (r6 = initR6, r7 = cmpTableGt, r8 = initR8, r9 = initR9, r10 = initR10).
  -- Current (in-callee) r6 = infBitPattern (set by fp_cmp body); r7..r9
  -- untouched; r10 = initR10 + 0x1000 (bumped by call_local).
  have h_exit3 := exit_pops_spec
    ⟨callerContPc3, initR6, cmpTableGt, initR8, initR9, initR10⟩
    [] infBitPattern cmpTableGt initR8 initR9 (initR10 + 0x1000)
    (calleeEntry3 + 28)
  unfold transferArmThirdCallCr
  sl_block_iter [h_two_calls_ext, h_call3, h_callee3, h_exit3]

end Examples.PTokenTransferArmThirdCall
