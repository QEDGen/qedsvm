/-
Axiom audit gate (soundness CI): `lake build Examples` fails if any flagship
theorem acquires an axiom outside {propext, Classical.choice, Quot.sound}.
On failure, either a proof regressed to sorry/native_decide, or a new axiom
legitimately belongs — add it to the per-theorem allow-list with justification.
-/
import Lean
import SVM.SBPF.Bounded
import Generated.PTokenTransferTracedLifted
import PToken.TransferRefinement
import PToken.TransferArm.FullHappyPath
import Generated.VaultRefinement
import Generated.CounterRefinement
import Generated.AbortCallerLifted

open Lean Elab Command

/-- The classical axioms every theorem is allowed to depend on. -/
private def stdAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- `#assert_std_axioms foo` fails elaboration unless `foo` depends only on the
    standard classical axioms. The soundness gate for flagship theorems. -/
elab "#assert_std_axioms " id:ident : command => do
  let cName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axs ← liftCoreM <| collectAxioms cName
  let bad := axs.filter (fun a => !stdAxioms.contains a)
  unless bad.isEmpty do
    throwError "AXIOM AUDIT FAILED: '{cName}' depends on non-standard axioms: {bad.toList}"

#assert_std_axioms Examples.Lifted.PTokenTransfer.PTokenTransfer_lifted_spec
#assert_std_axioms Examples.Lifted.PTokenTransfer.PTokenTransfer_balance_correct
#assert_std_axioms Examples.PTokenTransferRefinement.refines_asm
#assert_std_axioms Examples.PTokenTransferFullHappyPath.p_token_transfer_full_happy_path_spec
#assert_std_axioms Examples.PTokenTransferFullHappyPath.p_token_transfer_full_happy_path_terminates
#assert_std_axioms Examples.VaultRefinement.refines_asm
#assert_std_axioms Examples.VaultRefinement.ensures
#assert_std_axioms Examples.CounterRefinement.refines_asm
#assert_std_axioms Examples.CounterRefinement.ensures

-- Phase 7 sub-item 3 (emitter half): the typed-fault corollary and its running
-- prefix must stay axiom-clean (no sorry/native_decide leaking into the
-- abort-path proof — the disjointness is `decide`, the prefix `sl_block_auto`).
#assert_std_axioms Examples.Lifted.AbortCaller.AbortCaller_lifted_spec
#assert_std_axioms Examples.Lifted.AbortCaller.AbortCaller_fault_correct

-- StateBounded invariant (audit L5 + L3): must remain decide-only, never sorry/native_decide.
-- step_bounded = per-insn preservation (incl. r10 discipline); executeFn_bounded = multi-step
-- closure; initialState_bounded = runner base case; mem_byte_canonical = L3 fence.
#assert_std_axioms SVM.SBPF.step_bounded
#assert_std_axioms SVM.SBPF.executeFn_bounded
#assert_std_axioms SVM.SBPF.initialState_bounded
#assert_std_axioms SVM.SBPF.mem_byte_canonical
