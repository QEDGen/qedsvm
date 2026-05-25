/-
  Abstract Hoare triples over `runMir`.

  Pilot scope: one triple, `tokenTransfer_spec`, for the single-stmt
  MIR program `[.tokenTransfer src dst amount]`. Composition of
  multiple statements into a longer triple (via an SL frame rule
  analogous to `sl_block_iter`) is a later task — for the pilot the
  refinement bridge consumes this atomic triple directly.

  Triple shape: total-correctness with a success obligation. Given a
  pre-state satisfying `P`, the program runs to `.ok s'` and the
  post-state `s'` satisfies `Q`. The frame is captured by `holdsFor`:
  the input state may own accounts beyond those `P` mentions; those
  are untouched (proven case-by-case in the post-state CompatibleWith
  reconstruction). A separate frame-rule theorem will state this
  cleanly once composition becomes relevant.
-/

import SVM.Solana.Mir
import SVM.Solana.Abstract.SepLogic

namespace SVM.Solana.Abstract

open SVM.Pubkey

/-- Abstract Hoare triple. Partial-correctness: if `P.holdsFor s` then
    `runMir prog s` succeeds and the result satisfies `Q.holdsFor`. -/
def absTriple (prog : List MirStmt) (P Q : AbsAssertion) : Prop :=
  ∀ s, P.holdsFor s → ∃ s', runMir prog s = .ok s' ∧ Q.holdsFor s'

/-! ## tokenTransfer spec — the load-bearing pilot theorem -/

/-- The abstract spec for `tokenTransfer src dst amount`: the source
    account's `amount` field decreases by `amount`, the destination's
    increases by `amount`, and `mint`/`owner`/`rest` flow through on
    both via `TokenAccount.withAmount`.

    Preconditions:
    * `h_funds` — source has enough balance (`amount ≤ tSrc.amount`).
    * `h_noOverflow` — destination won't overflow u64.

    `src ≠ dst` is **not** an explicit precondition — it's derived
    inside the proof from the SL `Disjoint` of the two singleton
    atoms in the pre-state assertion. -/
theorem tokenTransfer_spec
    (src dst : Pubkey) (tSrc tDst : TokenAccount) (amount : Nat)
    (h_funds      : amount ≤ tSrc.amount)
    (h_noOverflow : tDst.amount + amount < 2 ^ 64) :
    absTriple [.tokenTransfer src dst amount]
      ((src ↦ₐ tSrc) ** (dst ↦ₐ tDst))
      ((src ↦ₐ tSrc.withAmount (tSrc.amount - amount)) **
       (dst ↦ₐ tDst.withAmount (tDst.amount + amount))) := by
  intro s hP
  obtain ⟨_, hC, h1, h2, hDisj, hUnion, hP1, hP2⟩ := hP
  subst hP1; subst hP2
  -- src ≠ dst follows from Disjoint at key = src.
  have h_ne : src ≠ dst := by
    intro h_eq; subst h_eq
    rcases hDisj.accounts src with hN | hN <;>
      · rw [PartialAbstractState.singletonAccount_accounts_self] at hN
        cases hN
  -- Lookup src / dst values in the full state via CompatibleWith.
  have h_s_src : s.accounts src = some tSrc := by
    refine hC.accounts src tSrc ?_
    rw [← hUnion]
    exact PartialAbstractState.union_accounts_of_left_some
      PartialAbstractState.singletonAccount_accounts_self
  have h_s_dst : s.accounts dst = some tDst := by
    refine hC.accounts dst tDst ?_
    rw [← hUnion,
        PartialAbstractState.union_accounts_of_left_none
          (PartialAbstractState.singletonAccount_accounts_other (Ne.symm h_ne))]
    exact PartialAbstractState.singletonAccount_accounts_self
  -- `.get` views of the lookups, for unfolding into `runStep`'s match.
  have h_get_src : s.get src = some tSrc := h_s_src
  have h_get_dst : s.get dst = some tDst := h_s_dst
  -- Witness the post-state explicitly.
  refine ⟨(s.set src (tSrc.withAmount (tSrc.amount - amount))).set
            dst (tDst.withAmount (tDst.amount + amount)), ?_, ?_⟩
  · -- runMir reaches the constructed post-state.
    rw [runMir_singleton]
    simp only [runStep, h_get_src, h_get_dst,
               if_neg h_ne,
               if_neg (Nat.not_lt.mpr h_funds),
               if_neg (Nat.not_le.mpr h_noOverflow)]
  · -- Post-condition holdsFor the constructed state.
    refine ⟨(PartialAbstractState.singletonAccount src
              (tSrc.withAmount (tSrc.amount - amount))).union
            (PartialAbstractState.singletonAccount dst
              (tDst.withAmount (tDst.amount + amount))), ?_, ?_⟩
    · -- CompatibleWith the post-state: every owned key matches.
      constructor
      intro k t hk
      by_cases h_k_src : k = src
      · subst h_k_src
        rw [PartialAbstractState.union_accounts_of_left_some
              PartialAbstractState.singletonAccount_accounts_self] at hk
        have h_eq : t = tSrc.withAmount (tSrc.amount - amount) := by
          injection hk with h; exact h.symm
        subst h_eq
        rw [AbstractState.set_accounts_of_ne _ _ h_ne,
            AbstractState.set_accounts_eq]
      · by_cases h_k_dst : k = dst
        · subst h_k_dst
          rw [PartialAbstractState.union_accounts_of_left_none
                (PartialAbstractState.singletonAccount_accounts_other (Ne.symm h_ne)),
              PartialAbstractState.singletonAccount_accounts_self] at hk
          have h_eq : t = tDst.withAmount (tDst.amount + amount) := by
            injection hk with h; exact h.symm
          subst h_eq
          rw [AbstractState.set_accounts_eq]
        · exfalso
          rw [PartialAbstractState.union_accounts_of_left_none
                (PartialAbstractState.singletonAccount_accounts_other h_k_src),
              PartialAbstractState.singletonAccount_accounts_other h_k_dst] at hk
          cases hk
    · -- The assertion holds on the constructed partial state.
      refine ⟨PartialAbstractState.singletonAccount src
                (tSrc.withAmount (tSrc.amount - amount)),
              PartialAbstractState.singletonAccount dst
                (tDst.withAmount (tDst.amount + amount)),
              singletonAccount_Disjoint_of_ne _ _ h_ne,
              rfl, rfl, rfl⟩

end SVM.Solana.Abstract
