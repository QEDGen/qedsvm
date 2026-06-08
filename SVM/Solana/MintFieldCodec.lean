/-
  The SPL Token *mint* account as a layout-general `FieldVal` field list —
  the mint-side convergence of the bespoke codec onto the `account_agg`
  route (QEDGen/qedsvm#25, "converge the abstract-coupled codecs"). Sibling
  of `TokenFieldCodec.lean`, for the MintTo / Burn intrinsics.

  `mintAcctSupply` (the byte-level SPL mint predicate: mint_authority@0,
  supply@36, rest@44) is shown equal to the coarse codec of its field list.
  So a mint obligation is a field-list obligation, and the discharge
  accessor projection (`u64FieldAt`) reads the `supply` field directly — the
  same route the layout-general vault/counter lifts use, with no bespoke
  `Mint` record on the path.

  Unlike a per-program account, the SPL layout is fixed, so the discharge
  `ensures` for the `supply` field is a single library fact rather than a
  per-lift emission.
-/

import SVM.SBPF.Tactic.Discharge
import SVM.Solana.MintAccountCodec

namespace SVM.Solana

open SVM.SBPF

/-- The SPL mint account as a `FieldVal` field list: the `COption<Pubkey>`
    mint_authority as an opaque `.blob` at 0, the `supply` `.u64` at 36, and
    the decimals / is_initialized / freeze_authority tail as a `.blob` at 44.
    `supply` is mid-struct (offset 36), so unlike the token `amount` it is
    not a trailing field — the field-list route handles it uniformly. -/
def mintFields (preAuth : ByteArray) (supply : Nat) (rest : ByteArray) :
    List (Nat × FieldVal) :=
  [(0, .blob [.gap preAuth]), (36, .u64 supply), (44, .blob [.gap rest])]

/-- **Convergence keystone.** The byte-level mint predicate is the coarse
    codec of its field list. So `AsmRefinesTokenMintTo` / `AsmRefinesTokenBurn`
    are field-list obligations, and the accessor projection applies. -/
theorem mintSupply_codec (base : Nat) (preAuth : ByteArray) (supply : Nat) (rest : ByteArray) :
    mintAcctSupply base preAuth supply rest
      = codecCoarse base (mintFields preAuth supply rest) := by
  simp [mintAcctSupply, mintFields, MINT_AUTH_OFF, SUPPLY_OFF, MINT_REST_OFF,
        codecCoarse, FieldVal.coarse, segsBytes, FieldSeg.bytes,
        sepConj_emp_right_eq]

/-- The accessor reads the `supply` field (offset 36) of a mint field list. -/
@[simp] theorem u64FieldAt_mintFields (preAuth : ByteArray) (supply : Nat) (rest : ByteArray) :
    u64FieldAt 36 (mintFields preAuth supply rest) = supply := by
  simp [u64FieldAt, mintFields]

/-- qedgen `ensures`: a credit of the `supply` field
    (`supply post = supply pre + amount`) — the MintTo case, discharged. -/
theorem mint_ensures_credit (preAuth : ByteArray) (supply amount : Nat) (rest : ByteArray) :
    u64FieldAt 36 (mintFields preAuth (supply + amount) rest)
      = u64FieldAt 36 (mintFields preAuth supply rest) + amount := by
  qedsvm_discharge

/-- qedgen `ensures`: a debit of the `supply` field
    (`supply post = supply pre - amount`) — the Burn case, discharged. -/
theorem mint_ensures_debit (preAuth : ByteArray) (supply amount : Nat) (rest : ByteArray) :
    u64FieldAt 36 (mintFields preAuth (supply - amount) rest)
      = u64FieldAt 36 (mintFields preAuth supply rest) - amount := by
  qedsvm_discharge

end SVM.Solana
