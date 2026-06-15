/-
  The SPL token account as a layout-general `FieldVal` field list: convergence
  onto the `account_agg` route (QEDGen/qedsvm#25).

  `tokenAcctBalance` (mint@0, owner@32, amount@64, rest@72) is shown equal to the
  coarse codec of its field list, so a token obligation is a field-list obligation
  and `u64FieldAt` reads `amount` directly — no bespoke `TokenAccount` record on
  the path. SPL layout is fixed, so the `amount` discharge `ensures` is a library
  fact, not a per-lift emission.
-/

import SVM.SBPF.Tactic.Discharge
import SVM.Solana.TokenAccountCodec

namespace SVM.Solana

open SVM.SBPF SVM.Pubkey

/-- The SPL token account as a `FieldVal` field list (the `account_agg` example
    in `SVM/SBPF/AccountCodec.lean`): mint@0, owner@32, amount@64, tail `.blob`@72. -/
def tokenFields (mint owner : SVM.Pubkey) (amount : Nat) (rest : ByteArray) :
    List (Nat × FieldVal) :=
  [(0, .pubkey mint), (32, .pubkey owner), (64, .u64 amount), (72, .blob [.gap rest])]

/-- **Convergence keystone.** The byte-level token predicate is the coarse codec
    of its field list, so `AsmRefinesTokenTransfer` is a field-list obligation
    and the accessor projection applies. -/
theorem tokenAcctBalance_codec (ata : Nat) (mint owner : SVM.Pubkey) (amount : Nat) (rest : ByteArray) :
    tokenAcctBalance ata mint owner amount rest
      = codecCoarse ata (tokenFields mint owner amount rest) := by
  simp [tokenAcctBalance, tokenFields, MINT_OFF, OWNER_OFF, AMOUNT_OFF, REST_OFF,
        codecCoarse, FieldVal.coarse, segsBytes, FieldSeg.bytes,
        sepConj_emp_right_eq]

/-- The accessor reads the `amount` field (offset 64) of a token field list. -/
@[simp] theorem u64FieldAt_tokenFields (mint owner : SVM.Pubkey) (amount : Nat) (rest : ByteArray) :
    u64FieldAt 64 (tokenFields mint owner amount rest) = amount := by
  simp [u64FieldAt, tokenFields]

/-- qedgen `ensures_axiom_0`: `amount` debit (from_balance post = pre - amount). -/
theorem token_ensures_debit (mint owner : SVM.Pubkey) (balance amount : Nat) (rest : ByteArray) :
    u64FieldAt 64 (tokenFields mint owner (balance - amount) rest)
      = u64FieldAt 64 (tokenFields mint owner balance rest) - amount := by
  qedsvm_discharge

/-- qedgen `ensures_axiom_1`: `amount` credit (to_balance post = pre + amount). -/
theorem token_ensures_credit (mint owner : SVM.Pubkey) (balance amount : Nat) (rest : ByteArray) :
    u64FieldAt 64 (tokenFields mint owner (balance + amount) rest)
      = u64FieldAt 64 (tokenFields mint owner balance rest) + amount := by
  qedsvm_discharge

end SVM.Solana
