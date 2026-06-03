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
      refine ⟨fun k t hk => ?_, fun k m hk => ?_, fun k cc hk => ?_⟩
      · -- accounts clause
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
      · -- mints clause: the post partial state (two token singletons) owns no mints.
        rw [PartialAbstractState.union_mints_of_left_none
              (PartialAbstractState.singletonAccount_mints k),
            PartialAbstractState.singletonAccount_mints] at hk
        exact absurd hk (by simp)
      · -- counters clause: the post partial state owns no counters.
        rw [PartialAbstractState.union_counters_of_left_none
              (PartialAbstractState.singletonAccount_counters k),
            PartialAbstractState.singletonAccount_counters] at hk
        exact absurd hk (by simp)
    · -- The assertion holds on the constructed partial state.
      refine ⟨PartialAbstractState.singletonAccount src
                (tSrc.withAmount (tSrc.amount - amount)),
              PartialAbstractState.singletonAccount dst
                (tDst.withAmount (tDst.amount + amount)),
              singletonAccount_Disjoint_of_ne _ _ h_ne,
              rfl, rfl, rfl⟩

/-! ## tokenMintTo spec -/

/-- The abstract spec for `tokenMintTo mint dest amount`: the mint's
    `supply` and the destination's `amount` each increase by `amount`;
    `preAuth`/`rest` and `mint`/`owner`/`rest` flow through. Preconditions
    rule out u64 overflow of either field. -/
theorem tokenMintTo_spec
    (mint dest : Pubkey) (m : Mint) (tDest : TokenAccount) (amount : Nat)
    (h_noOvSupply : m.supply + amount < 2 ^ 64)
    (h_noOvDest   : tDest.amount + amount < 2 ^ 64) :
    absTriple [.tokenMintTo mint dest amount]
      ((mint ↦ₘ m) ** (dest ↦ₐ tDest))
      ((mint ↦ₘ m.withSupply (m.supply + amount)) **
       (dest ↦ₐ tDest.withAmount (tDest.amount + amount))) := by
  intro s hP
  obtain ⟨_, hC, h1, h2, hDisj, hUnion, hP1, hP2⟩ := hP
  subst hP1; subst hP2
  have h_s_mint : s.mints mint = some m := by
    refine hC.mints mint m ?_
    rw [← hUnion]
    exact PartialAbstractState.union_mints_of_left_some
      PartialAbstractState.singletonMint_mints_self
  have h_s_dest : s.accounts dest = some tDest := by
    refine hC.accounts dest tDest ?_
    rw [← hUnion,
        PartialAbstractState.union_accounts_of_left_none
          (PartialAbstractState.singletonMint_accounts dest)]
    exact PartialAbstractState.singletonAccount_accounts_self
  have h_getMint : s.getMint mint = some m := h_s_mint
  have h_get_dest : s.get dest = some tDest := h_s_dest
  refine ⟨(s.setMint mint (m.withSupply (m.supply + amount))).set
            dest (tDest.withAmount (tDest.amount + amount)), ?_, ?_⟩
  · rw [runMir_singleton]
    simp only [runStep, h_getMint, h_get_dest,
               if_neg (Nat.not_le.mpr h_noOvSupply),
               if_neg (Nat.not_le.mpr h_noOvDest)]
  · refine ⟨(PartialAbstractState.singletonMint mint
              (m.withSupply (m.supply + amount))).union
            (PartialAbstractState.singletonAccount dest
              (tDest.withAmount (tDest.amount + amount))), ?_, ?_⟩
    · refine ⟨fun k t hk => ?_, fun k mm hk => ?_, fun k cc hk => ?_⟩
      · -- accounts clause: only `dest` is owned (the mint singleton owns no accounts).
        rw [PartialAbstractState.union_accounts_of_left_none
              (PartialAbstractState.singletonMint_accounts k)] at hk
        by_cases h_k_dest : k = dest
        · subst h_k_dest
          rw [PartialAbstractState.singletonAccount_accounts_self] at hk
          have h_eq : t = tDest.withAmount (tDest.amount + amount) := by
            injection hk with h; exact h.symm
          subst h_eq
          rw [AbstractState.set_accounts_eq]
        · exfalso
          rw [PartialAbstractState.singletonAccount_accounts_other h_k_dest] at hk
          cases hk
      · -- mints clause: only `mint` is owned (left singleton).
        by_cases h_k_mint : k = mint
        · subst h_k_mint
          rw [PartialAbstractState.union_mints_of_left_some
                PartialAbstractState.singletonMint_mints_self] at hk
          have h_eq : mm = m.withSupply (m.supply + amount) := by
            injection hk with h; exact h.symm
          subst h_eq
          rw [AbstractState.set_mints, AbstractState.setMint_mints_eq]
        · exfalso
          rw [PartialAbstractState.union_mints_of_left_none
                (PartialAbstractState.singletonMint_mints_other h_k_mint),
              PartialAbstractState.singletonAccount_mints] at hk
          cases hk
      · -- counters clause: the post partial state owns no counters.
        rw [PartialAbstractState.union_counters_of_left_none
              (PartialAbstractState.singletonMint_counters k),
            PartialAbstractState.singletonAccount_counters] at hk
        exact absurd hk (by simp)
    · refine ⟨PartialAbstractState.singletonMint mint
                (m.withSupply (m.supply + amount)),
              PartialAbstractState.singletonAccount dest
                (tDest.withAmount (tDest.amount + amount)),
              (singletonAccount_Disjoint_singletonMint _ _).symm,
              rfl, rfl, rfl⟩

/-! ## tokenBurn spec -/

/-- The abstract spec for `tokenBurn account mint amount`: the account's
    `amount` and the mint's `supply` each decrease by `amount`.
    Precondition `h_funds` rules out an under-funded burn. -/
theorem tokenBurn_spec
    (account mint : Pubkey) (tAcc : TokenAccount) (m : Mint) (amount : Nat)
    (h_funds : amount ≤ tAcc.amount) :
    absTriple [.tokenBurn account mint amount]
      ((account ↦ₐ tAcc) ** (mint ↦ₘ m))
      ((account ↦ₐ tAcc.withAmount (tAcc.amount - amount)) **
       (mint ↦ₘ m.withSupply (m.supply - amount))) := by
  intro s hP
  obtain ⟨_, hC, h1, h2, hDisj, hUnion, hP1, hP2⟩ := hP
  subst hP1; subst hP2
  have h_s_acc : s.accounts account = some tAcc := by
    refine hC.accounts account tAcc ?_
    rw [← hUnion]
    exact PartialAbstractState.union_accounts_of_left_some
      PartialAbstractState.singletonAccount_accounts_self
  have h_s_mint : s.mints mint = some m := by
    refine hC.mints mint m ?_
    rw [← hUnion,
        PartialAbstractState.union_mints_of_left_none
          (PartialAbstractState.singletonAccount_mints mint)]
    exact PartialAbstractState.singletonMint_mints_self
  have h_get_acc : s.get account = some tAcc := h_s_acc
  have h_getMint : s.getMint mint = some m := h_s_mint
  refine ⟨(s.set account (tAcc.withAmount (tAcc.amount - amount))).setMint
            mint (m.withSupply (m.supply - amount)), ?_, ?_⟩
  · rw [runMir_singleton]
    simp only [runStep, h_get_acc, h_getMint, if_neg (Nat.not_lt.mpr h_funds)]
  · refine ⟨(PartialAbstractState.singletonAccount account
              (tAcc.withAmount (tAcc.amount - amount))).union
            (PartialAbstractState.singletonMint mint
              (m.withSupply (m.supply - amount))), ?_, ?_⟩
    · refine ⟨fun k t hk => ?_, fun k mm hk => ?_, fun k cc hk => ?_⟩
      · -- accounts clause: only `account` is owned (left singleton).
        by_cases h_k_acc : k = account
        · subst h_k_acc
          rw [PartialAbstractState.union_accounts_of_left_some
                PartialAbstractState.singletonAccount_accounts_self] at hk
          have h_eq : t = tAcc.withAmount (tAcc.amount - amount) := by
            injection hk with h; exact h.symm
          subst h_eq
          rw [AbstractState.setMint_accounts, AbstractState.set_accounts_eq]
        · exfalso
          rw [PartialAbstractState.union_accounts_of_left_none
                (PartialAbstractState.singletonAccount_accounts_other h_k_acc),
              PartialAbstractState.singletonMint_accounts] at hk
          cases hk
      · -- mints clause: only `mint` is owned (right singleton).
        rw [PartialAbstractState.union_mints_of_left_none
              (PartialAbstractState.singletonAccount_mints k)] at hk
        by_cases h_k_mint : k = mint
        · subst h_k_mint
          rw [PartialAbstractState.singletonMint_mints_self] at hk
          have h_eq : mm = m.withSupply (m.supply - amount) := by
            injection hk with h; exact h.symm
          subst h_eq
          rw [AbstractState.setMint_mints_eq]
        · exfalso
          rw [PartialAbstractState.singletonMint_mints_other h_k_mint] at hk
          cases hk
      · -- counters clause: the post partial state owns no counters.
        rw [PartialAbstractState.union_counters_of_left_none
              (PartialAbstractState.singletonAccount_counters k),
            PartialAbstractState.singletonMint_counters] at hk
        exact absurd hk (by simp)
    · refine ⟨PartialAbstractState.singletonAccount account
                (tAcc.withAmount (tAcc.amount - amount)),
              PartialAbstractState.singletonMint mint
                (m.withSupply (m.supply - amount)),
              singletonAccount_Disjoint_singletonMint _ _,
              rfl, rfl, rfl⟩

/-! ## counterIncrement spec — the first non-token intrinsic -/

/-- The abstract spec for `counterIncrement key`: the counter account's
    `counter` field increases by one. Single account, single field, only
    an overflow precondition — strictly simpler than the token specs (no
    `src ≠ dst` disjointness, no second account). Validates that the
    abstract-triple machinery is layout-general, not token-shaped. -/
theorem counterIncrement_spec
    (key : Pubkey) (c : CounterAccount)
    (h_noOverflow : c.counter + 1 < 2 ^ 64) :
    absTriple [.counterIncrement key]
      (key ↦cnt c)
      (key ↦cnt c.withCounter (c.counter + 1)) := by
  intro s hP
  obtain ⟨ph, hC, hph⟩ := hP
  subst hph
  -- The single owned counter agrees with the full state.
  have h_s : s.counters key = some c :=
    hC.counters key c PartialAbstractState.singletonCounter_counters_self
  have h_get : s.getCounter key = some c := h_s
  refine ⟨s.setCounter key (c.withCounter (c.counter + 1)), ?_, ?_⟩
  · -- runMir reaches the constructed post-state.
    rw [runMir_singleton]
    simp only [runStep, h_get, if_neg (Nat.not_le.mpr h_noOverflow)]
  · -- Post-condition holdsFor the constructed state.
    refine ⟨PartialAbstractState.singletonCounter key
              (c.withCounter (c.counter + 1)), ?_, rfl⟩
    refine ⟨fun k t hk => ?_, fun k m hk => ?_, fun k cc hk => ?_⟩
    · -- accounts clause: the post partial state owns no accounts.
      rw [PartialAbstractState.singletonCounter_accounts] at hk
      exact absurd hk (by simp)
    · -- mints clause: the post partial state owns no mints.
      rw [PartialAbstractState.singletonCounter_mints] at hk
      exact absurd hk (by simp)
    · -- counters clause: only `key` is owned.
      by_cases h_k : k = key
      · subst h_k
        rw [PartialAbstractState.singletonCounter_counters_self] at hk
        have h_eq : cc = c.withCounter (c.counter + 1) := by
          injection hk with h; exact h.symm
        subst h_eq
        exact AbstractState.setCounter_counters_eq _ _ _
      · exfalso
        rw [PartialAbstractState.singletonCounter_counters_other h_k] at hk
        cases hk

end SVM.Solana.Abstract
