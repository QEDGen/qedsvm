/-
Axiom audit gate (soundness CI).

This module is part of the `Examples` lake target, so `lake build Examples`
fails if any flagship theorem acquires an axiom outside the standard classical
set (`propext`, `Classical.choice`, `Quot.sound`). That includes `sorryAx`
(introduced by `sorry`), the `native_decide` per-theorem trust axioms, and the
`SVM.SBPF.CryptoTrust` crypto shape axioms: none of those may appear in the
end-to-end theorems the project advertises as machine-checked.

If a build fails here, EITHER a proof regressed to `sorry`/`native_decide`,
OR a new axiom legitimately belongs in the theorem — in which case add it to
the per-theorem allow-list argument, with justification, deliberately.
-/
import Lean
import Generated.PTokenTransferTracedLifted
import PToken.TransferRefinement
import PToken.TransferArm.FullHappyPath
import Generated.VaultRefinement
import Generated.CounterRefinement

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
