/-
  Discharge PoC: qedgen's parametric `ensures_axiom` shape drops out of a
  lift's layout-general field-list obligation.

  qedgen states a state-mutation contract parametrically, over an opaque
  `State` and an accessor `State → Nat`
  (QEDGen/solana-skills: crates/qedgen/data/proofs/spl/Token.lean):

      axiom ensures_axiom_0 {State} [Inhabited State]
        (pre post : State) (amount : Nat) (from_balance : State → Nat) :
        (from_balance post) = (from_balance pre) - amount

  The `qedsvm_discharge` direction (QEDGen/qedsvm#24) is to PROVE that
  obligation against pinned bytecode instead of axiomatising it. This file
  validates the keystone of that direction: the accessor projection.

  Instantiate `State` as the decoded field list the lift emits (the
  `List (Nat × FieldVal)` that `AsmRefinesFieldUpdate` carries, after the
  `account_agg` byte<->field reshape — keystone #2, already proven), and
  `from_balance` as a `u64` field lookup. Then qedgen's
  `accessor post = accessor pre ± amount` is a pure projection on the
  pre/post field lists. The byte realization is the lift's reshape; this is
  the accessor read on top — and it needs NO raw `readU64`/`Mem` bridge,
  because the field-list route sidesteps it.
-/

import SVM.SBPF.AccountCodec

namespace Examples.DischargePoC

open SVM.SBPF SVM.Pubkey

/-- qedgen's `from_balance : State → Nat`, instantiated: read the `u64`
    field at byte offset `off` from a decoded account. Here `State` is the
    field list the lift produces; `from_balance := u64FieldAt off`. -/
def u64FieldAt (off : Nat) : List (Nat × FieldVal) → Nat
  | [] => 0
  | (o, .u64 v) :: rest => if o = off then v else u64FieldAt off rest
  | _ :: rest => u64FieldAt off rest

/-! ## Vault: `total post = total pre + 1`

A real `AsmRefinesFieldUpdate` instance. The pre/post field lists are
exactly `VaultRefinement`'s (`examples/lean/Generated/VaultRefinement.lean`,
`{owner:Pubkey@0, total:u64@32, bump:u8@40}`). qedgen's ensures-shape for
the `+1` update drops out by a field lookup. -/
theorem vault_total_ensures (o0 o1 o2 o3 total bump : Nat) :
    u64FieldAt 32 [(0, .pubkey ⟨o0,o1,o2,o3⟩), (32, .u64 (total + 1)), (40, .byte bump)]
      = u64FieldAt 32 [(0, .pubkey ⟨o0,o1,o2,o3⟩), (32, .u64 total), (40, .byte bump)] + 1 := by
  simp [u64FieldAt]

/-! ## Token transfer: qedgen's actual `ensures_axiom_0` / `ensures_axiom_1`

    ensures_axiom_0 : from_balance post = from_balance pre - amount
    ensures_axiom_1 : to_balance   post = to_balance   pre + amount

on the SPL token account's `amount` field (offset 64), with the opaque
`rest` region as a `.blob` (exactly the layout-general shape the vault-blob
codegen now emits). -/
theorem transfer_ensures_0
    (mLo mHi oLo oHi fromAmt amount : Nat) (rest : List FieldSeg) :
    u64FieldAt 64 [(0,.pubkey ⟨mLo,mHi,0,0⟩),(32,.pubkey ⟨oLo,oHi,0,0⟩),(64,.u64 (fromAmt - amount)),(72,.blob rest)]
      = u64FieldAt 64 [(0,.pubkey ⟨mLo,mHi,0,0⟩),(32,.pubkey ⟨oLo,oHi,0,0⟩),(64,.u64 fromAmt),(72,.blob rest)] - amount := by
  simp [u64FieldAt]

theorem transfer_ensures_1
    (mLo mHi oLo oHi toAmt amount : Nat) (rest : List FieldSeg) :
    u64FieldAt 64 [(0,.pubkey ⟨mLo,mHi,0,0⟩),(32,.pubkey ⟨oLo,oHi,0,0⟩),(64,.u64 (toAmt + amount)),(72,.blob rest)]
      = u64FieldAt 64 [(0,.pubkey ⟨mLo,mHi,0,0⟩),(32,.pubkey ⟨oLo,oHi,0,0⟩),(64,.u64 toAmt),(72,.blob rest)] + amount := by
  simp [u64FieldAt]

end Examples.DischargePoC
