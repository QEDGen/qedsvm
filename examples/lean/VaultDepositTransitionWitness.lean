/- Concrete branch witnesses for the source-built V3 vault transition.
   The bundle must admit an overflowing input as well as a successful credit.
   These check actual named total/amount values, not just a footprint witness. -/
import Generated.Sbpfv3VaultDepositTransition

namespace Examples.VaultDepositTransitionWitness

open SVM.SBPF Examples.Sbpfv3VaultDepositTransition

-- Registers and untouched owner limbs are arbitrary here; input addresses
-- and the IDL-bound discriminator, amount and vault total are concrete.
private def overflowBundle := sbpfv3_vault_deposit_transition
  0 17179869184 1 0 1 0 (2 ^ 64 - 1) 0 0 0 0 0 0
  (by decide) (by decide) (by decide)

def overflow_rejection :=
  overflowBundle.1 (by decide) (by decide) (by decide) (by decide)

private def successBundle := sbpfv3_vault_deposit_transition
  0 17179869184 1 0 7 0 9 0 0 0 0 0 0
  (by decide) (by decide) (by decide)

def success_credit :=
  successBundle.2.1 (by decide) (by decide) (by decide) (by decide) (by decide)

private def zeroBundle := sbpfv3_vault_deposit_transition
  0 17179869184 1 0 0 0 9 0 0 0 0 0 0
  (by decide) (by decide) (by decide)

def zero_rejection :=
  zeroBundle.2.2.2 (by decide) (by decide)

private def unknownBundle := sbpfv3_vault_deposit_transition
  0 17179869184 9 0 7 0 9 0 0 0 0 0 0
  (by decide) (by decide) (by decide)

def unknown_rejection :=
  unknownBundle.2.2.1 (by decide)

end Examples.VaultDepositTransitionWitness
