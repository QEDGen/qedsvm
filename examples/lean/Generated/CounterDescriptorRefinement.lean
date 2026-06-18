/-
  AsmRefinesFieldUpdate asm-refines theorem, SPEC-DRIVEN. Emitted by qedlift
  from a qedspec-shaped refinement descriptor (account Counter, handler increment,
  mutated field counter), NOT from the hardcoded `refine_registry`. The
  field offsets come from the IDL (the shape substrate), not the descriptor.
  The lift owns the updated `u64` field; the account codec is reshaped
  coarse→fine via the layout-general `account_agg` (`codecCoarse_eq_fine`)
  and the untouched fields (if any) are framed. See docs/DEVEX_QEDSPEC_GAP.md.
-/

import SVM.SBPF.Tactic.SL
import SVM.SBPF.Tactic.Discharge
import SVM.Solana.Abstract.Refinement
import Generated.CounterDescriptorTracedLifted

namespace Examples.CounterDescriptorRefinement
open SVM SVM.SBPF SVM.SBPF.Memory

set_option maxHeartbeats 800000 in
theorem refines_asm
    (cr : CodeReq) (rr : Memory.RegionTable → Prop)
    (baseAddr oldMemD_0 vR2Old vR0Old : Nat)
    (lift : cuTripleWithinMem 4 0 0 4 cr
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 oldMemD_0) **
      (.r2 ↦ᵣ vR2Old) **
      (.r0 ↦ᵣ vR0Old))
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 oldMemD_0 + 1) **
      (.r2 ↦ᵣ wrapAdd oldMemD_0 (toU64 1)) **
      (.r0 ↦ᵣ toU64 0)) rr) :
    SVM.Solana.Abstract.AsmRefinesFieldUpdate cr 4 0 0 4 rr baseAddr
      [(0, .u64 oldMemD_0)]
      [(0, .u64 (oldMemD_0 + 1))]
      ((.r1 ↦ᵣ baseAddr) **
      (.r2 ↦ᵣ vR2Old) **
      (.r0 ↦ᵣ vR0Old))
      ((.r1 ↦ᵣ baseAddr) **
      (.r2 ↦ᵣ wrapAdd oldMemD_0 (toU64 1)) **
      (.r0 ↦ᵣ toU64 0)) := by
  unfold SVM.Solana.Abstract.AsmRefinesFieldUpdate
  rw [codecCoarse_eq_fine baseAddr
        [(0, .u64 oldMemD_0)]
        (by simp [codecValid, FieldVal.fineValid]),
      codecCoarse_eq_fine baseAddr
        [(0, .u64 (oldMemD_0 + 1))]
        (by simp [codecValid, FieldVal.fineValid])]
  simp only [codecFine, FieldVal.fine, sepConj_emp_right_eq, Nat.add_zero]
  sl_exact lift

/-- qedgen `ensures`-shape, mechanically discharged: the mutated `u64`
    field (offset 0) shifts by 1. Pairs with `refines_asm`
    (which says the bytecode realises this field-list transition); together
    they discharge qedgen's `accessor post = accessor pre ± k` over the
    decoded field list via the layout-general accessor projection. -/
theorem ensures
    (oldMemD_0 : Nat) :
    u64FieldAt 0 [(0, .u64 (oldMemD_0 + 1))]
      = u64FieldAt 0 [(0, .u64 oldMemD_0)] + 1 := by
  qedsvm_discharge

end Examples.CounterDescriptorRefinement
