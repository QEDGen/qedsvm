/-
  Domain vocabulary for abstract Solana triples.

  Layer 0 of the readability stack — thin projections over
  `AbstractState` that let consumer-facing theorems name what they're
  saying ("balance shift", "valid transfer") instead of unfolding to
  `accountIs k t ** accountIs k' t'`.

  The SL-shaped `tokenTransfer_spec` in `Triples.lean` is the *internal*
  proof obligation; `tokenTransfer_correct` below is the *external*
  statement consumers cite. Both denote the same thing; the latter is
  the form a Solana engineer reads.
-/

import SVM.Solana.Mir

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

/-! ## Consumer-facing correctness theorem

The same content as `tokenTransfer_spec`, but stated in domain
vocabulary — what a token-program author reads when they want to know
"what did we prove?". The SL-flavoured form is left as the internal
helper. -/

/-- `tokenTransfer src dst amount` is correct: under `validTransfer`,
    it moves `amount` units of balance from `src` to `dst`, preserves
    owner and mint on both, and touches no other account. -/
theorem tokenTransfer_correct
    (s : AbstractState) (src dst : Pubkey) (amount : Nat)
    (h : validTransfer s src dst amount) :
    ∃ s', runMir [.tokenTransfer src dst amount] s = .ok s'
      ∧ s'.balance src = s.balance src - amount
      ∧ s'.balance dst = s.balance dst + amount
      ∧ s'.owner src = s.owner src
      ∧ s'.owner dst = s.owner dst
      ∧ s'.mint  src = s.mint  src
      ∧ s'.mint  dst = s.mint  dst
      ∧ ∀ k, k ≠ src → k ≠ dst → s'.get k = s.get k := by
  obtain ⟨h_ne, h_src_ex, h_dst_ex, h_funds, h_overflow⟩ := h
  -- Materialise the token records behind `hasAccount` witnesses.
  obtain ⟨tSrc, h_src_eq⟩ : ∃ t, s.get src = some t := by
    cases h : s.get src with
    | none   => exact absurd h h_src_ex
    | some t => exact ⟨t, rfl⟩
  obtain ⟨tDst, h_dst_eq⟩ : ∃ t, s.get dst = some t := by
    cases h : s.get dst with
    | none   => exact absurd h h_dst_ex
    | some t => exact ⟨t, rfl⟩
  -- Rephrase the validTransfer guards in terms of record fields.
  have h_bal_src : s.balance src = tSrc.amount := by
    simp [AbstractState.balance, h_src_eq]
  have h_bal_dst : s.balance dst = tDst.amount := by
    simp [AbstractState.balance, h_dst_eq]
  have h_funds'    : amount ≤ tSrc.amount := h_bal_src ▸ h_funds
  have h_overflow' : tDst.amount + amount < 2 ^ 64 := h_bal_dst ▸ h_overflow
  -- Construct the post-state explicitly: src loses, then dst gains.
  let s1 := s.set src (tSrc.withAmount (tSrc.amount - amount))
  let s' := s1.set dst (tDst.withAmount (tDst.amount + amount))
  refine ⟨s', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- runMir reaches s'.
  · rw [runMir_singleton]
    show runStep (.tokenTransfer src dst amount) s = .ok s'
    have h_no_funds    : ¬ (amount > tSrc.amount)        := by omega
    have h_no_overflow : ¬ (tDst.amount + amount ≥ 2 ^ 64) := by omega
    simp only [runStep, h_src_eq, h_dst_eq,
               if_neg h_ne, if_neg h_no_funds, if_neg h_no_overflow]
    rfl
  -- balance src decreased by amount.
  · show s'.balance src = s.balance src - amount
    have h1 : s'.get src = some (tSrc.withAmount (tSrc.amount - amount)) := by
      show (s1.set dst _).get src = _
      rw [AbstractState.set_get_of_ne _ _ h_ne]
      exact AbstractState.set_get_eq _ _ _
    simp [AbstractState.balance, h1, h_src_eq]
  -- balance dst increased by amount.
  · show s'.balance dst = s.balance dst + amount
    have h1 : s'.get dst = some (tDst.withAmount (tDst.amount + amount)) :=
      AbstractState.set_get_eq _ _ _
    simp [AbstractState.balance, h1, h_dst_eq]
  -- owner src preserved.
  · show s'.owner src = s.owner src
    have h1 : s'.get src = some (tSrc.withAmount (tSrc.amount - amount)) := by
      show (s1.set dst _).get src = _
      rw [AbstractState.set_get_of_ne _ _ h_ne]
      exact AbstractState.set_get_eq _ _ _
    simp [AbstractState.owner, h1, h_src_eq]
  -- owner dst preserved.
  · show s'.owner dst = s.owner dst
    have h1 : s'.get dst = some (tDst.withAmount (tDst.amount + amount)) :=
      AbstractState.set_get_eq _ _ _
    simp [AbstractState.owner, h1, h_dst_eq]
  -- mint src preserved.
  · show s'.mint src = s.mint src
    have h1 : s'.get src = some (tSrc.withAmount (tSrc.amount - amount)) := by
      show (s1.set dst _).get src = _
      rw [AbstractState.set_get_of_ne _ _ h_ne]
      exact AbstractState.set_get_eq _ _ _
    simp [AbstractState.mint, h1, h_src_eq]
  -- mint dst preserved.
  · show s'.mint dst = s.mint dst
    have h1 : s'.get dst = some (tDst.withAmount (tDst.amount + amount)) :=
      AbstractState.set_get_eq _ _ _
    simp [AbstractState.mint, h1, h_dst_eq]
  -- Untouched keys flow through.
  · intro k h_k_src h_k_dst
    show s'.get k = s.get k
    rw [AbstractState.set_get_of_ne _ _ h_k_dst,
        AbstractState.set_get_of_ne _ _ h_k_src]

end SVM.Solana.Abstract
