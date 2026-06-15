/-
  Bridge between the abstract `TokenAccount` record and the byte-level SL
  predicate `tokenAcctBalance`.

  No executable encode/decode: the refinement bridge works at the predicate
  level, not via bit-level transcoding. This file lifts the per-field predicate
  to one keyed on the abstract record, plus rewriting lemmas under field updates.
  A new field-mutating intrinsic adds a sibling unfolding lemma here.
-/

import SVM.Solana.TokenAccount
import SVM.Solana.Abstract.State

namespace SVM.Solana

open SVM.SBPF
open SVM.Solana.Abstract

/-- Record-keyed view of `tokenAcctBalance`: the SL atom for a
    full SPL Token v4 account at byte address `ata`, with contents
    matching the abstract record `t`. -/
def tokenAcctBalanceOf (ata : Nat) (t : Abstract.TokenAccount) : Assertion :=
  tokenAcctBalance ata t.mint t.owner t.amount t.rest

/-- Definitional unfold for `simp` chains. -/
@[simp] theorem tokenAcctBalanceOf_eq (ata : Nat) (t : Abstract.TokenAccount) :
    tokenAcctBalanceOf ata t =
      tokenAcctBalance ata t.mint t.owner t.amount t.rest := rfl

/-- Load-bearing: a `withAmount` shift rewrites the SL atom to the new amount
    (mint/owner/rest unchanged); the refinement bridge applies it to convert the
    abstract TokenTransfer post-state to the asm-side predicate. -/
@[simp] theorem tokenAcctBalanceOf_withAmount
    (ata : Nat) (t : Abstract.TokenAccount) (a : Nat) :
    tokenAcctBalanceOf ata (t.withAmount a) =
      tokenAcctBalance ata t.mint t.owner a t.rest := by
  unfold tokenAcctBalanceOf Abstract.TokenAccount.withAmount
  rfl

end SVM.Solana
