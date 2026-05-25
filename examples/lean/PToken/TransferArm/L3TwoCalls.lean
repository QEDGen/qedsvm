/-
  Layer 3b artifact #6 (N+5): **Two-call glue triple** extending
  `PTokenTransferArm.lean` with the second `call_local` to the
  f64→i64 conversion callee. Demonstrates that the glue chain
  composes incrementally — adding new call sites is mechanical once
  the per-callee triples are in hand.

  **Chain (6 component triples):**

  1. `p_token_transfer_arm_spec` — the existing one-call glue
     (PCs 0..4 setup + call_local + callee body at base=100 +
     exit_pops returning to PC 5).
  2. `mov64 r7, r0` at PC 5 (save FP-cmp result to r7).
  3. `mov64 r1, r6` at PC 6 (set up next call's input).
  4. `call_local 200` at PC 7 (jump to f64→i64 callee at synthetic
     base PC 200).
  5. `f64_to_i64_in_range_spec 200` — the f64→i64 callee body at
     base=200 (PCs 200..214, advancing PC 200 → 218 via the `ja`).
  6. `exit_pops` at PC 218, returning to caller's PC 8.

  Triple advances PC 0 → 8. Total CU = 29 + 1 + 1 + 1 + 15 + 1 = 48.

  **Key precondition added vs N+3 glue:**
  `initR6 ∈ [oneFp, twoToSixtyFour_Fp)`. The f64→i64 callee's
  in-range domain. The earlier N+3 preconditions
  (`initR6 < 2^63`, `≤ infBitPattern`, `> 0`) remain — though
  `≥ oneFp` already subsumes `> 0` since `oneFp > 0`. Kept all
  for clarity; the proof never uses the redundant ones from N+3 that
  don't matter for N+5's added structure.

  **Methodology:** the chain composes via one `sl_block_iter` call
  with 6 component triples. No new framework support needed past
  N+3's additions (`pcFree_callStackIs`, omega fallback in
  `sl_disjoint_codereq`). Validates the N+4 cost projection: each
  subsequent glue extension is ~½ day with the established patterns.
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

/-- Synthetic base PC for the second callee (f64→i64). -/
def calleeEntry2 : Nat := 200

/-- PC of the caller's instruction right after the second
    `call_local` — where the second `exit_pops` will return to. -/
def callerContPc2 : Nat := 8

/-- Combined CodeReq: extends `transferArmCr` with the second
    call's worth of insns (2 movs + `call_local` + callee body +
    `exit`). -/
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
    cuTripleWithinMem 48 0 callerContPc2 transferArmTwoCallsCr
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
  -- Use the existing N+3 glue as a single component.
  -- The N+3 glue needs a `> 0` precondition; derive it from `≥ oneFp`.
  have h_initR6_pos : initR6 > 0 := by
    have h_oneFp_pos : (0 : Nat) < oneFp := by unfold oneFp; decide
    omega
  have h_glue1 := Examples.PTokenTransferArm.p_token_transfer_arm_spec
    initR0 initR1 initR2 initR3 initR4 initR5 initR6
    initR7 initR8 initR9 initR10
    oldStackVal cmpTableGt
    h_initR6_sign h_initR6_notNaN h_initR6_pos hTable_lt
  -- Linear inserts at PCs 5, 6.
  have h_mov_r7 := mov64_reg_spec .r7 .r0 initR7 cmpTableGt 5 (by decide)
  have h_mov_r1 := mov64_reg_spec .r1 .r6
    (lookupTableBase + gtOffset) initR6 6 (by decide)
  -- Second call_local at PC 7, target = calleeEntry2.
  -- At call time: r6 = initR6, r7 = cmpTableGt (just set), r8/r9/r10 = restored,
  -- callStack = [] (popped by first exit_pops).
  have h_call2 := call_local_spec calleeEntry2 [] initR6 cmpTableGt
    initR8 initR9 initR10 7
  -- Second callee body. Input r1 = initR6 (just set). r0 at entry =
  -- cmpTableGt (not touched by movs or call_local). r2 at entry =
  -- toU64 0 (set by setup, untouched since).
  have h_callee2 := Examples.CompilerRtF64ToI64.f64_to_i64_in_range_spec
    calleeEntry2 initR6 cmpTableGt (toU64 0) h_initR6_lb h_initR6_ub
  -- Second exit_pops at PC calleeEntry2 + 18 = 218, retPc = callerContPc2 = 8.
  -- Callee body doesn't touch r6..r10 (it only writes r0, r1, r2),
  -- so r6 = initR6, r7 = cmpTableGt (saved into frame), r8 = initR8,
  -- r9 = initR9, r10 = initR10 + 0x1000.
  have h_exit2 := exit_pops_spec
    ⟨callerContPc2, initR6, cmpTableGt, initR8, initR9, initR10⟩
    [] initR6 cmpTableGt initR8 initR9 (initR10 + 0x1000)
    (calleeEntry2 + 18)
  unfold transferArmTwoCallsCr
  sl_block_iter [h_glue1, h_mov_r7, h_mov_r1, h_call2, h_callee2, h_exit2]

end Examples.PTokenTransferArmTwoCalls
