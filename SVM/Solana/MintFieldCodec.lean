/-
  The SPL mint account as a layout-general `FieldVal` field list: the mint-side
  convergence onto the `account_agg` route (QEDGen/qedsvm#25). For MintTo / Burn.

  `mintAcctSupply` (mint_authority@0, supply@36, rest@44) is shown equal to the
  coarse codec of its field list, so a mint obligation is a field-list obligation
  and `u64FieldAt` reads `supply` directly — no bespoke `Mint` record on the path.
  SPL layout is fixed, so the `supply` discharge `ensures` is a library fact, not
  a per-lift emission.
-/

import SVM.SBPF.Tactic.Discharge
import SVM.Solana.MintAccountCodec

namespace SVM.Solana

open SVM.SBPF

/-- The SPL mint as a `FieldVal` field list: mint_authority `.blob`@0,
    supply `.u64`@36, decimals/is_init/freeze tail `.blob`@44. `supply` is
    mid-struct, not trailing — the field-list route handles it uniformly. -/
def mintFields (preAuth : ByteArray) (supply : Nat) (rest : ByteArray) :
    List (Nat × FieldVal) :=
  [(0, .blob [.gap preAuth]), (36, .u64 supply), (44, .blob [.gap rest])]

/-- **Convergence keystone.** The byte-level mint predicate is the coarse codec
    of its field list, so `AsmRefinesTokenMintTo`/`AsmRefinesTokenBurn` are
    field-list obligations and the accessor projection applies. -/
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

/-- qedgen `ensures`: `supply` credit (post = pre + amount), MintTo. -/
theorem mint_ensures_credit (preAuth : ByteArray) (supply amount : Nat) (rest : ByteArray) :
    u64FieldAt 36 (mintFields preAuth (supply + amount) rest)
      = u64FieldAt 36 (mintFields preAuth supply rest) + amount := by
  qedsvm_discharge

/-- qedgen `ensures`: `supply` debit (post = pre - amount), Burn. -/
theorem mint_ensures_debit (preAuth : ByteArray) (supply amount : Nat) (rest : ByteArray) :
    u64FieldAt 36 (mintFields preAuth (supply - amount) rest)
      = u64FieldAt 36 (mintFields preAuth supply rest) - amount := by
  qedsvm_discharge

end SVM.Solana
