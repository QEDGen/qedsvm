/-
  Abstract Solana state for spec-to-asm refinement.

  Pilot scope (TokenTransfer-only): the abstract heap is a partial map
  `Pubkey → Option TokenAccount`. No signers, no instruction data, no
  return data, no CU — those land when the second intrinsic
  (`RequireSigner`, `Cpi`, ...) demands them, not preemptively.

  Two-layer architecture (Direction-A MIR, qedgen issue #66):
    * This is the ABSTRACT side. Reasoning lives over decoded token
      accounts, not over byte ranges in `SVM.SBPF.Memory.Mem`.
    * The CONCRETE side is the existing sBPF `PartialState` in
      `SVM/SBPF/SepLogic.lean`.
    * The bridge is `SVM/Solana/Abstract/Refinement.lean` (TBD): an
      abstraction relation φ that says "this abstract account matches
      these concrete bytes at this layout offset."

  Extension protocol: add fields here only when an in-flight pilot
  needs them. Each new field adds clauses to the SL `Disjoint` /
  `CompatibleWith` / `union` definitions in `Abstract/SepLogic.lean`.
-/

import SVM.Pubkey

namespace SVM.Solana.Abstract

open SVM.Pubkey

/-! ## TokenAccount — decoded SPL Token v4 account

The byte-level Pack codec lives in `SVM.Solana.TokenAccount` as the
predicate `tokenAcctBalance`; this record is the abstract-side
counterpart. Refinement obligation (Task 8): bytes at the layout-given
offset decode to this record.

`rest` carries the opaque 93-byte tail (delegate / state / is_native /
delegated_amount / close_authority) as a single flow-through field.
The mint / owner / amount triple is what Transfer-class theorems
mutate; everything else passes through unchanged. -/

structure TokenAccount where
  mint   : Pubkey
  owner  : Pubkey
  amount : Nat
  rest   : ByteArray
  deriving Inhabited

namespace TokenAccount

/-- Adjust the `amount` field, preserving everything else. -/
def withAmount (t : TokenAccount) (a : Nat) : TokenAccount :=
  { t with amount := a }

@[simp] theorem withAmount_amount (t : TokenAccount) (a : Nat) :
    (t.withAmount a).amount = a := rfl
@[simp] theorem withAmount_mint (t : TokenAccount) (a : Nat) :
    (t.withAmount a).mint = t.mint := rfl
@[simp] theorem withAmount_owner (t : TokenAccount) (a : Nat) :
    (t.withAmount a).owner = t.owner := rfl
@[simp] theorem withAmount_rest (t : TokenAccount) (a : Nat) :
    (t.withAmount a).rest = t.rest := rfl

end TokenAccount

/-! ## AbstractState — the partial heap of decoded accounts

Single field today; grows as later pilots demand new resources
(`signers : Finset Pubkey`, `ixData : ByteArray`, `returnData`,
`cuRemaining`, `cpiLog`). -/

structure AbstractState where
  accounts : Pubkey → Option TokenAccount
  deriving Inhabited

namespace AbstractState

/-- The empty abstract state owns no accounts. -/
def empty : AbstractState :=
  { accounts := fun _ => none }

@[simp] theorem empty_accounts (k : Pubkey) :
    empty.accounts k = none := rfl

/-- Read the account at `key`, if any. Definitionally equal to
    `s.accounts key`; the named accessor is useful for `simp` rewriting. -/
@[inline] def get (s : AbstractState) (key : Pubkey) : Option TokenAccount :=
  s.accounts key

/-- Install `t` at `key`, leaving every other key unchanged. -/
def set (s : AbstractState) (key : Pubkey) (t : TokenAccount) : AbstractState :=
  { accounts := fun k => if k = key then some t else s.accounts k }

@[simp] theorem set_get_eq (s : AbstractState) (key : Pubkey) (t : TokenAccount) :
    (s.set key t).get key = some t := by
  unfold set get; simp

@[simp] theorem set_get_of_ne (s : AbstractState) {key key' : Pubkey}
    (t : TokenAccount) (h : key' ≠ key) :
    (s.set key t).get key' = s.get key' := by
  unfold set get; simp [h]

/-- Field-level `.accounts` variant of `set_get_eq`, useful when proofs
    pattern-match on the raw field rather than going through `.get`. -/
@[simp] theorem set_accounts_eq (s : AbstractState) (key : Pubkey) (t : TokenAccount) :
    (s.set key t).accounts key = some t := by
  unfold set; simp

@[simp] theorem set_accounts_of_ne (s : AbstractState) {key key' : Pubkey}
    (t : TokenAccount) (h : key' ≠ key) :
    (s.set key t).accounts key' = s.accounts key' := by
  unfold set; simp [h]

/-- Apply `f` to the account at `key`, if it exists. No-op if absent.
    The Transfer balance shift lands here:
    `s.update from (·.withAmount (preA - x))`. -/
def update (s : AbstractState) (key : Pubkey) (f : TokenAccount → TokenAccount) :
    AbstractState :=
  match s.get key with
  | some t => s.set key (f t)
  | none   => s

@[simp] theorem update_get_eq (s : AbstractState) (key : Pubkey)
    (f : TokenAccount → TokenAccount) (t : TokenAccount) (h : s.get key = some t) :
    (s.update key f).get key = some (f t) := by
  unfold update; rw [h]; exact set_get_eq s key (f t)

@[simp] theorem update_get_of_ne (s : AbstractState) {key key' : Pubkey}
    (f : TokenAccount → TokenAccount) (h : key' ≠ key) :
    (s.update key f).get key' = s.get key' := by
  unfold update
  cases hk : s.get key with
  | some t => exact set_get_of_ne s (f t) h
  | none   => rfl

end AbstractState
end SVM.Solana.Abstract
