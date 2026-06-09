/-
  Domain vocabulary for abstract Solana triples.

  Layer 0 of the readability stack — thin projections over
  `AbstractState` that let consumer-facing theorems name what they're
  saying ("balance shift", "valid transfer") instead of unfolding to
  `accountIs k t ** accountIs k' t'`.

  These are thin projections over `AbstractState` (token balance, owner,
  mint, well-formedness) — the domain vocabulary consumer-facing theorems
  name their pre/post-conditions with.
-/

import SVM.Solana.Abstract.State

namespace SVM.Solana.Abstract

open SVM.Pubkey

/-! ## Domain projections -/

namespace AbstractState

/-- Token balance at `a`, or `0` if no account exists. The `getD 0`
    convention matches user mental model: an uninitialised ATA "holds
    zero tokens". Use `hasAccount` to distinguish "absent" from
    "present with balance 0". -/
@[inline] def balance (s : AbstractState) (a : Pubkey) : Nat :=
  ((s.get a).map (·.amount)).getD 0

/-- Owner of the account at `a`, if any. -/
@[inline] def owner (s : AbstractState) (a : Pubkey) : Option Pubkey :=
  (s.get a).map (·.owner)

/-- Mint of the account at `a`, if any. -/
@[inline] def mint (s : AbstractState) (a : Pubkey) : Option Pubkey :=
  (s.get a).map (·.mint)

/-- Whether the state owns an account at `a`. -/
@[inline] def hasAccount (s : AbstractState) (a : Pubkey) : Prop :=
  s.get a ≠ none

end AbstractState

/-! ## Well-formedness predicates -/

/-- Preconditions for a successful SPL Token `Transfer`:
    distinct accounts, both initialised, source has enough balance,
    and the destination won't overflow u64. -/
def validTransfer (s : AbstractState) (src dst : Pubkey) (amount : Nat) : Prop :=
  src ≠ dst
    ∧ s.hasAccount src
    ∧ s.hasAccount dst
    ∧ amount ≤ s.balance src
    ∧ s.balance dst + amount < 2 ^ 64

end SVM.Solana.Abstract
