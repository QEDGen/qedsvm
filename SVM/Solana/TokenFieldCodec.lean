/-
  The SPL token account as a layout-general `FieldVal` field list — the
  convergence of the bespoke token codec onto the `account_agg` route
  (QEDGen/qedsvm#25, "converge the abstract-coupled codecs").

  `tokenAcctBalance` (the byte-level SPL predicate: mint@0, owner@32,
  amount@64, rest@72) is shown equal to the coarse codec of its field list.
  So a token obligation is a field-list obligation, and the discharge
  accessor projection (`u64FieldAt`) reads the `amount` field directly —
  the same route the layout-general vault/counter lifts use, with no
  bespoke `TokenAccount` record on the path.

  Unlike a per-program account, the SPL layout is fixed, so the discharge
  `ensures` for the `amount` field is a single library fact rather than a
  per-lift emission.
-/

import SVM.SBPF.Tactic.Discharge
import SVM.Solana.TokenAccountCodec

namespace SVM.Solana

open SVM.SBPF SVM.Pubkey

/-- The SPL token account as a `FieldVal` field list (the `account_agg`
    example in `SVM/SBPF/AccountCodec.lean`): mint@0, owner@32, amount@64,
    and the opaque tail as a `.blob` at 72. -/
def tokenFields (mint owner : SVM.Pubkey) (amount : Nat) (rest : ByteArray) :
    List (Nat × FieldVal) :=
  [(0, .pubkey mint), (32, .pubkey owner), (64, .u64 amount), (72, .blob [.gap rest])]

/-- **Convergence keystone.** The byte-level token account predicate is the
    coarse codec of its field list. So `AsmRefinesTokenTransfer` is a
    field-list obligation, and the accessor projection applies. -/
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

/-- qedgen `ensures_axiom_0`: a debit of the `amount` field
    (`from_balance post = from_balance pre - amount`), discharged. -/
theorem token_ensures_debit (mint owner : SVM.Pubkey) (balance amount : Nat) (rest : ByteArray) :
    u64FieldAt 64 (tokenFields mint owner (balance - amount) rest)
      = u64FieldAt 64 (tokenFields mint owner balance rest) - amount := by
  qedsvm_discharge

/-- qedgen `ensures_axiom_1`: a credit of the `amount` field
    (`to_balance post = to_balance pre + amount`), discharged. -/
theorem token_ensures_credit (mint owner : SVM.Pubkey) (balance amount : Nat) (rest : ByteArray) :
    u64FieldAt 64 (tokenFields mint owner (balance + amount) rest)
      = u64FieldAt 64 (tokenFields mint owner balance rest) + amount := by
  qedsvm_discharge

end SVM.Solana
