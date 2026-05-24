/-
  Bridge between the abstract `TokenAccount` record (decoded form,
  defined in `Svm/Solana/Abstract/State.lean`) and the byte-level SL
  predicate `tokenAcctBalance` (defined in `Svm/Solana/TokenAccount.lean`).

  No executable encode / decode functions — the refinement bridge
  (`Svm/Solana/Abstract/Refinement.lean`, Task 7) works at the
  predicate level, not via bit-level transcoding. This file just lifts
  the per-field predicate to one keyed on the abstract record, plus
  rewriting lemmas under field updates.

  Adding a new field-mutating intrinsic later (e.g., a `SetMint`
  variant for delegate operations) means adding a sibling unfolding
  lemma here: `tokenAcctBalanceOf ata (t.withMint m') = …`.
-/

import Svm.Solana.TokenAccount
import Svm.Solana.Abstract.State

namespace Svm.Solana

open Svm.SBPF
open Svm.Solana.Abstract

/-- Record-keyed view of `tokenAcctBalance`: the SL atom for a
    full SPL Token v4 account at byte address `ata`, with contents
    matching the abstract record `t`. -/
def tokenAcctBalanceOf (ata : Nat) (t : Abstract.TokenAccount) : Assertion :=
  tokenAcctBalance ata t.mint t.owner t.amount t.rest

/-- Definitional unfold for `simp` chains. -/
@[simp] theorem tokenAcctBalanceOf_eq (ata : Nat) (t : Abstract.TokenAccount) :
    tokenAcctBalanceOf ata t =
      tokenAcctBalance ata t.mint t.owner t.amount t.rest := rfl

/-- A `withAmount` shift on the abstract record rewrites the SL atom
    to one with the new amount, mint/owner/rest unchanged. This is the
    load-bearing lemma the refinement bridge applies to convert the
    abstract TokenTransfer's post-state to the asm-side predicate. -/
@[simp] theorem tokenAcctBalanceOf_withAmount
    (ata : Nat) (t : Abstract.TokenAccount) (a : Nat) :
    tokenAcctBalanceOf ata (t.withAmount a) =
      tokenAcctBalance ata t.mint t.owner a t.rest := by
  unfold tokenAcctBalanceOf Abstract.TokenAccount.withAmount
  rfl

end Svm.Solana
