/-
  AsmRefinesFieldUpdate asm-refines theorem for a multi-field NON-token account.
  MECHANICALLY EMITTED by qedlift from the Codama IDL account layout +
  the lift's atoms. The lift owns the updated `u64` field; the account
  codec is reshaped coarse→fine via the layout-general `account_agg`
  (`codecCoarse_eq_fine`) and the untouched fields are framed.
-/

import SVM.SBPF.Tactic.SL
import SVM.SBPF.Tactic.Discharge
import SVM.Solana.Abstract.Refinement
import Generated.VaultBlobTracedLifted

namespace Examples.VaultBlobRefinement
open SVM SVM.SBPF SVM.SBPF.Memory

set_option maxHeartbeats 800000 in
theorem refines_asm
    (cr : CodeReq) (rr : Memory.RegionTable → Prop)
    (baseAddr oldMemD_0 vR2Old vR0Old fb1 : Nat)
    (fg0 : ByteArray)
    (lift : cuTripleWithinMem 4 0 0 4 cr
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 32 ↦U64 oldMemD_0) **
      (.r2 ↦ᵣ vR2Old) **
      (.r0 ↦ᵣ vR0Old))
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 32 ↦U64 oldMemD_0 + 1) **
      (.r2 ↦ᵣ wrapAdd oldMemD_0 (toU64 1)) **
      (.r0 ↦ᵣ toU64 0)) rr) :
    SVM.Solana.Abstract.AsmRefinesFieldUpdate cr 4 0 0 4 rr baseAddr
      [(0, .blob [.gap fg0]), (32, .u64 oldMemD_0), (40, .byte fb1)]
      [(0, .blob [.gap fg0]), (32, .u64 (oldMemD_0 + 1)), (40, .byte fb1)]
      ((.r1 ↦ᵣ baseAddr) **
      (.r2 ↦ᵣ vR2Old) **
      (.r0 ↦ᵣ vR0Old))
      ((.r1 ↦ᵣ baseAddr) **
      (.r2 ↦ᵣ wrapAdd oldMemD_0 (toU64 1)) **
      (.r0 ↦ᵣ toU64 0)) := by
  unfold SVM.Solana.Abstract.AsmRefinesFieldUpdate
  rw [codecCoarse_eq_fine baseAddr
        [(0, .blob [.gap fg0]), (32, .u64 oldMemD_0), (40, .byte fb1)]
        (by simp [codecValid, FieldVal.fineValid, segsValid, FieldSeg.valid]),
      codecCoarse_eq_fine baseAddr
        [(0, .blob [.gap fg0]), (32, .u64 (oldMemD_0 + 1)), (40, .byte fb1)]
        (by simp [codecValid, FieldVal.fineValid, segsValid, FieldSeg.valid])]
  simp only [codecFine, FieldVal.fine, segsSL, FieldSeg.sl, sepConj_emp_right_eq, Nat.add_zero]
  have framed := cuTripleWithinMem_frame_right
    ( (effectiveAddr baseAddr 0 ↦Bytes fg0) **
      (effectiveAddr baseAddr 40 ↦ₘ fb1) )
    (by sl_pcfree) lift
  sl_exact framed

/-- qedgen `ensures`-shape, mechanically discharged: the mutated `u64`
    field (offset 32) shifts by 1. Pairs with `refines_asm`
    (which says the bytecode realises this field-list transition); together
    they discharge qedgen's `accessor post = accessor pre ± k` over the
    decoded field list via the layout-general accessor projection. -/
theorem ensures
    (oldMemD_0 fb1 : Nat)
    (fg0 : ByteArray) :
    u64FieldAt 32 [(0, .blob [.gap fg0]), (32, .u64 (oldMemD_0 + 1)), (40, .byte fb1)]
      = u64FieldAt 32 [(0, .blob [.gap fg0]), (32, .u64 oldMemD_0), (40, .byte fb1)] + 1 := by
  qedsvm_discharge

end Examples.VaultBlobRefinement
