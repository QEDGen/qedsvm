/- Concrete witnesses that each captured branch has satisfiable guards.
   Metadata values reflect the runtime input cases in diff_mollusk.rs.
   These instantiate selected-path proofs, without asserting exhaustive coverage. -/
import Generated.Sbpfv3VaultAuthorizedTransition

namespace Examples.AuthorizedVaultTransitionWitness

open SVM.SBPF Examples.Sbpfv3VaultAuthorizedTransition

private def duplicateBundle := sbpfv3_vault_authorized_transition
  0 17179869184 2 0 255 41 0
  3834029160418063669 3834029160418063669 3834029160418063669 3834029160418063669 9 53 0
  16 1 0 1 705 705 0
  0 0 0 0 0 0 3834029160418063669
  3834029160418063669 3834029160418063669 3834029160418063669 1 7 0
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide)

def duplicate :=
  duplicateBundle.1 (by decide) (by decide) (by decide) (by decide)

private def long_instructionBundle := sbpfv3_vault_authorized_transition
  0 17179869184 2 0 255 41 255
  3834029160418063669 3834029160418063669 3834029160418063669 3834029160418063669 9 53 0
  17 1 0 1 705 705 0
  0 0 0 0 0 0 3834029160418063669
  3834029160418063669 3834029160418063669 3834029160418063669 1 7 0
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide)

def long_instruction :=
  long_instructionBundle.2.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private def missing_accountBundle := sbpfv3_vault_authorized_transition
  0 17179869184 1 0 255 41 255
  3834029160418063669 3834029160418063669 3834029160418063669 3834029160418063669 9 53 0
  16 1 0 1 705 705 0
  0 0 0 0 0 0 3834029160418063669
  3834029160418063669 3834029160418063669 3834029160418063669 1 7 0
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide)

def missing_account :=
  missing_accountBundle.2.2.2.1 (by decide)

private def missing_signerBundle := sbpfv3_vault_authorized_transition
  0 17179869184 2 0 255 41 255
  3834029160418063669 3834029160418063669 3834029160418063669 3834029160418063669 9 53 0
  16 1 0 0 705 705 0
  0 0 0 0 0 0 3834029160418063669
  3834029160418063669 3834029160418063669 3834029160418063669 1 7 0
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide)

def missing_signer :=
  missing_signerBundle.2.2.2.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private def overflowBundle := sbpfv3_vault_authorized_transition
  0 17179869184 2 0 255 41 255
  3834029160418063669 3834029160418063669 3834029160418063669 3834029160418063669 (2 ^ 64 - 1) 53 0
  16 1 0 1 705 705 0
  0 0 0 0 0 0 3834029160418063669
  3834029160418063669 3834029160418063669 3834029160418063669 1 1 0
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide)

def overflow :=
  overflowBundle.2.2.2.2.2.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private def readonlyBundle := sbpfv3_vault_authorized_transition
  0 17179869184 2 0 255 41 255
  3834029160418063669 3834029160418063669 3834029160418063669 3834029160418063669 9 53 0
  16 0 0 1 705 705 0
  0 0 0 0 0 0 3834029160418063669
  3834029160418063669 3834029160418063669 3834029160418063669 1 7 0
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide)

def readonly :=
  readonlyBundle.2.2.2.2.2.2.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private def short_instructionBundle := sbpfv3_vault_authorized_transition
  0 17179869184 2 0 255 41 255
  3834029160418063669 3834029160418063669 3834029160418063669 3834029160418063669 9 53 0
  8 1 0 1 705 705 0
  0 0 0 0 0 0 3834029160418063669
  3834029160418063669 3834029160418063669 3834029160418063669 1 7 0
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide)

def short_instruction :=
  short_instructionBundle.2.2.2.2.2.2.2.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private def short_vaultBundle := sbpfv3_vault_authorized_transition
  0 17179869184 2 0 255 40 255
  3834029160418063669 3834029160418063669 3834029160418063669 3834029160418063669 9 53 0
  16 1 0 1 705 705 0
  0 0 0 0 0 0 3834029160418063669
  3834029160418063669 3834029160418063669 3834029160418063669 1 7 0
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide)

def short_vault :=
  short_vaultBundle.2.2.2.2.2.2.2.2.2.1 (by decide) (by decide) (by decide)

private def successBundle := sbpfv3_vault_authorized_transition
  0 17179869184 2 0 255 41 255
  3834029160418063669 3834029160418063669 3834029160418063669 3834029160418063669 9 53 0
  16 1 0 1 705 705 0
  0 0 0 0 0 0 3834029160418063669
  3834029160418063669 3834029160418063669 3834029160418063669 1 7 0
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide)

def success :=
  successBundle.2.2.2.2.2.2.2.2.2.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private def unknownBundle := sbpfv3_vault_authorized_transition
  0 17179869184 2 0 255 41 255
  3834029160418063669 3834029160418063669 3834029160418063669 3834029160418063669 9 53 0
  16 1 0 1 705 705 0
  0 0 0 0 0 0 3834029160418063669
  3834029160418063669 3834029160418063669 3834029160418063669 9 7 0
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide)

def unknown :=
  unknownBundle.2.2.2.2.2.2.2.2.2.2.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private def wrong_owner_0Bundle := sbpfv3_vault_authorized_transition
  0 17179869184 2 0 255 41 255
  3834029160418063668 3834029160418063669 3834029160418063669 3834029160418063669 9 53 0
  16 1 0 1 705 705 0
  0 0 0 0 0 0 3834029160418063669
  3834029160418063669 3834029160418063669 3834029160418063669 1 7 0
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide)

def wrong_owner_0 :=
  wrong_owner_0Bundle.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private def wrong_owner_1Bundle := sbpfv3_vault_authorized_transition
  0 17179869184 2 0 255 41 255
  3834029160418063669 3834029160418063668 3834029160418063669 3834029160418063669 9 53 0
  16 1 0 1 705 705 0
  0 0 0 0 0 0 3834029160418063669
  3834029160418063669 3834029160418063669 3834029160418063669 1 7 0
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide)

def wrong_owner_1 :=
  wrong_owner_1Bundle.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private def wrong_owner_2Bundle := sbpfv3_vault_authorized_transition
  0 17179869184 2 0 255 41 255
  3834029160418063669 3834029160418063669 3834029160418063668 3834029160418063669 9 53 0
  16 1 0 1 705 705 0
  0 0 0 0 0 0 3834029160418063669
  3834029160418063669 3834029160418063669 3834029160418063669 1 7 0
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide)

def wrong_owner_2 :=
  wrong_owner_2Bundle.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private def wrong_owner_3Bundle := sbpfv3_vault_authorized_transition
  0 17179869184 2 0 255 41 255
  3834029160418063669 3834029160418063669 3834029160418063669 3834029160418063668 9 53 0
  16 1 0 1 705 705 0
  0 0 0 0 0 0 3834029160418063669
  3834029160418063669 3834029160418063669 3834029160418063669 1 7 0
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide)

def wrong_owner_3 :=
  wrong_owner_3Bundle.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private def wrong_program_owner_0Bundle := sbpfv3_vault_authorized_transition
  0 17179869184 2 0 255 41 255
  3834029160418063669 3834029160418063669 3834029160418063669 3834029160418063669 9 53 0
  16 1 0 1 705 704 0
  0 0 0 0 0 0 3834029160418063669
  3834029160418063669 3834029160418063669 3834029160418063669 1 7 0
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide)

def wrong_program_owner_0 :=
  wrong_program_owner_0Bundle.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private def wrong_program_owner_1Bundle := sbpfv3_vault_authorized_transition
  0 17179869184 2 0 255 41 255
  3834029160418063669 3834029160418063669 3834029160418063669 3834029160418063669 9 53 0
  16 1 0 1 705 705 0
  0 1 0 0 0 0 3834029160418063669
  3834029160418063669 3834029160418063669 3834029160418063669 1 7 0
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide)

def wrong_program_owner_1 :=
  wrong_program_owner_1Bundle.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private def wrong_program_owner_2Bundle := sbpfv3_vault_authorized_transition
  0 17179869184 2 0 255 41 255
  3834029160418063669 3834029160418063669 3834029160418063669 3834029160418063669 9 53 0
  16 1 0 1 705 705 0
  0 0 0 1 0 0 3834029160418063669
  3834029160418063669 3834029160418063669 3834029160418063669 1 7 0
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide)

def wrong_program_owner_2 :=
  wrong_program_owner_2Bundle.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private def wrong_program_owner_3Bundle := sbpfv3_vault_authorized_transition
  0 17179869184 2 0 255 41 255
  3834029160418063669 3834029160418063669 3834029160418063669 3834029160418063669 9 53 0
  16 1 0 1 705 705 0
  0 0 0 0 0 1 3834029160418063669
  3834029160418063669 3834029160418063669 3834029160418063669 1 7 0
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide)

def wrong_program_owner_3 :=
  wrong_program_owner_3Bundle.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private def zeroBundle := sbpfv3_vault_authorized_transition
  0 17179869184 2 0 255 41 255
  3834029160418063669 3834029160418063669 3834029160418063669 3834029160418063669 9 53 0
  16 1 0 1 705 705 0
  0 0 0 0 0 0 3834029160418063669
  3834029160418063669 3834029160418063669 3834029160418063669 1 0 0
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide)

def zero :=
  zeroBundle.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private def executableBundle := sbpfv3_vault_authorized_transition
  0 17179869184 2 0 255 41 255
  3834029160418063669 3834029160418063669 3834029160418063669 3834029160418063669 9 53 0
  16 1 1 1 705 705 0
  0 0 0 0 0 0 3834029160418063669
  3834029160418063669 3834029160418063669 3834029160418063669 1 7 0
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide)

def executable :=
  executableBundle.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private def nonempty_authorityBundle := sbpfv3_vault_authorized_transition
  0 17179869184 2 0 255 41 255
  3834029160418063669 3834029160418063669 3834029160418063669 3834029160418063669 9 53 1
  16 1 0 1 705 705 0
  0 0 0 0 0 0 3834029160418063669
  3834029160418063669 3834029160418063669 3834029160418063669 1 7 0
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide)

def nonempty_authority :=
  nonempty_authorityBundle.2.2.2.2.2.1 (by decide) (by decide) (by decide) (by decide) (by decide)

end Examples.AuthorizedVaultTransitionWitness
