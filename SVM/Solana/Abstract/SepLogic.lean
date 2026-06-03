/-
  Separation logic over `AbstractState` — the abstract analog of
  `SVM/SBPF/SepLogic.lean`.

  Ownership granularity: **one resource per account**, keyed by Pubkey.
  A `PartialAbstractState` owns some subset of accounts; the predicate
  `accountIs k t` asserts ownership of the single account at key `k`
  with decoded contents `t`. The separating conjunction `P ** Q` holds
  when the partial state splits into two disjoint pieces (no shared
  Pubkey) with `P` and `Q` holding on each.

  Whole-account (vs field-level) ownership is the right call for the
  pilot:
    * Refinement obligation is `bytes-at-layout-offset ↔ decoded
      TokenAccount`, naturally whole-record.
    * Transfer-class effects mutate `amount` while `mint`/`owner`/`rest`
      flow through unchanged — the abstract triple binds the
      `withAmount` shift on the *whole* record without per-field
      decomposition.
    * Field-level atoms are a future refinement when a user-spec needs
      to express e.g. "this transfer touches `amount` and `delegate`
      but not `owner`" — out of pilot scope.

  Single-field `PartialAbstractState` keeps the Disjoint/union/lemma
  surface tiny. Adding a future resource (signers, ixData, …) follows
  the same extension protocol as `SVM/SBPF/SepLogic.lean`: add a field,
  a singleton, one clause to Disjoint / CompatibleWith / union, and
  the per-resource simp lemmas.
-/

import SVM.Solana.Abstract.State

namespace SVM.Solana.Abstract

open SVM.Pubkey

/-! ## PartialAbstractState — partial ownership of accounts -/

/-- A partial view of an `AbstractState`. `some t` at key `k` means we
    own the account at `k` and assert its decoded contents equal `t`;
    `none` means we don't own that account. -/
structure PartialAbstractState where
  accounts : Pubkey → Option TokenAccount
  mints    : Pubkey → Option Mint
  counters : Pubkey → Option CounterAccount
  deriving Inhabited

namespace PartialAbstractState

/-- The empty partial state owns no accounts. -/
def empty : PartialAbstractState :=
  { accounts := fun _ => none, mints := fun _ => none, counters := fun _ => none }

/-- Partial state owning exactly the token account at `key` with contents `t`. -/
def singletonAccount (key : Pubkey) (t : TokenAccount) : PartialAbstractState :=
  { accounts := fun k => if k = key then some t else none, mints := fun _ => none,
    counters := fun _ => none }

/-- Partial state owning exactly the mint at `key` with contents `m`. -/
def singletonMint (key : Pubkey) (m : Mint) : PartialAbstractState :=
  { accounts := fun _ => none, mints := fun k => if k = key then some m else none,
    counters := fun _ => none }

/-- Partial state owning exactly the counter at `key` with contents `c`. -/
def singletonCounter (key : Pubkey) (c : CounterAccount) : PartialAbstractState :=
  { accounts := fun _ => none, mints := fun _ => none,
    counters := fun k => if k = key then some c else none }

/-- Two partial states are disjoint if they never both own the same
    account, mint, or counter. One clause per resource. -/
structure Disjoint (h1 h2 : PartialAbstractState) : Prop where
  accounts : ∀ k, h1.accounts k = none ∨ h2.accounts k = none
  mints    : ∀ k, h1.mints k = none ∨ h2.mints k = none
  counters : ∀ k, h1.counters k = none ∨ h2.counters k = none

/-- Left-biased union of two partial states. -/
def union (h1 h2 : PartialAbstractState) : PartialAbstractState where
  accounts := fun k =>
    match h1.accounts k with
    | some t => some t
    | none   => h2.accounts k
  mints := fun k =>
    match h1.mints k with
    | some m => some m
    | none   => h2.mints k
  counters := fun k =>
    match h1.counters k with
    | some c => some c
    | none   => h2.counters k

/-- A partial state is compatible with a full `AbstractState` if every
    owned account/mint/counter agrees with the full state. -/
structure CompatibleWith (h : PartialAbstractState) (s : AbstractState) : Prop where
  accounts : ∀ k t, h.accounts k = some t → s.accounts k = some t
  mints    : ∀ k m, h.mints k = some m → s.mints k = some m
  counters : ∀ k c, h.counters k = some c → s.counters k = some c

/-! ## Disjoint lemmas -/

theorem Disjoint.symm {h1 h2 : PartialAbstractState} (hd : h1.Disjoint h2) :
    h2.Disjoint h1 :=
  { accounts := fun k => (hd.accounts k).symm,
    mints    := fun k => (hd.mints k).symm,
    counters := fun k => (hd.counters k).symm }

/-! ## Singleton projection lemmas -/

@[simp] theorem singletonAccount_accounts_self {key : Pubkey} {t : TokenAccount} :
    (singletonAccount key t).accounts key = some t := by
  unfold singletonAccount; simp

@[simp] theorem singletonAccount_accounts_other
    {key key' : Pubkey} {t : TokenAccount} (h : key' ≠ key) :
    (singletonAccount key t).accounts key' = none := by
  unfold singletonAccount; simp [h]

@[simp] theorem singletonAccount_mints {key : Pubkey} {t : TokenAccount} (k : Pubkey) :
    (singletonAccount key t).mints k = none := rfl

@[simp] theorem singletonMint_mints_self {key : Pubkey} {m : Mint} :
    (singletonMint key m).mints key = some m := by
  unfold singletonMint; simp

@[simp] theorem singletonMint_mints_other
    {key key' : Pubkey} {m : Mint} (h : key' ≠ key) :
    (singletonMint key m).mints key' = none := by
  unfold singletonMint; simp [h]

@[simp] theorem singletonMint_accounts {key : Pubkey} {m : Mint} (k : Pubkey) :
    (singletonMint key m).accounts k = none := rfl

@[simp] theorem singletonAccount_counters {key : Pubkey} {t : TokenAccount} (k : Pubkey) :
    (singletonAccount key t).counters k = none := rfl

@[simp] theorem singletonMint_counters {key : Pubkey} {m : Mint} (k : Pubkey) :
    (singletonMint key m).counters k = none := rfl

@[simp] theorem singletonCounter_counters_self {key : Pubkey} {c : CounterAccount} :
    (singletonCounter key c).counters key = some c := by
  unfold singletonCounter; simp

@[simp] theorem singletonCounter_counters_other
    {key key' : Pubkey} {c : CounterAccount} (h : key' ≠ key) :
    (singletonCounter key c).counters key' = none := by
  unfold singletonCounter; simp [h]

@[simp] theorem singletonCounter_accounts {key : Pubkey} {c : CounterAccount} (k : Pubkey) :
    (singletonCounter key c).accounts k = none := rfl

@[simp] theorem singletonCounter_mints {key : Pubkey} {c : CounterAccount} (k : Pubkey) :
    (singletonCounter key c).mints k = none := rfl

@[simp] theorem empty_accounts (k : Pubkey) :
    empty.accounts k = none := rfl

@[simp] theorem empty_mints (k : Pubkey) :
    empty.mints k = none := rfl

@[simp] theorem empty_counters (k : Pubkey) :
    empty.counters k = none := rfl

/-! ## Union lemmas -/

theorem union_accounts_of_left_none {h1 h2 : PartialAbstractState} {k : Pubkey}
    (h : h1.accounts k = none) : (h1.union h2).accounts k = h2.accounts k := by
  show (match h1.accounts k with | some t => some t | none => h2.accounts k) =
       h2.accounts k
  rw [h]

theorem union_accounts_of_left_some {h1 h2 : PartialAbstractState}
    {k : Pubkey} {t : TokenAccount}
    (h : h1.accounts k = some t) : (h1.union h2).accounts k = some t := by
  show (match h1.accounts k with | some t => some t | none => h2.accounts k) =
       some t
  rw [h]

@[simp] theorem union_accounts_eq_match (h1 h2 : PartialAbstractState) :
    ∀ k, (h1.union h2).accounts k =
      (match h1.accounts k with | some t => some t | none => h2.accounts k) :=
  fun _ => rfl

theorem union_accounts_eq_none_iff {h1 h2 : PartialAbstractState} {k : Pubkey} :
    (h1.union h2).accounts k = none ↔
      h1.accounts k = none ∧ h2.accounts k = none := by
  show (match h1.accounts k with | some t => some t | none => h2.accounts k) =
       none ↔ _
  cases h1.accounts k
  · cases h2.accounts k <;> simp
  · simp

/-! ### Mint-clause union lemmas (mirror the account-clause ones) -/

@[simp] theorem union_mints_eq_match (h1 h2 : PartialAbstractState) :
    ∀ k, (h1.union h2).mints k =
      (match h1.mints k with | some m => some m | none => h2.mints k) :=
  fun _ => rfl

theorem union_mints_of_left_none {h1 h2 : PartialAbstractState} {k : Pubkey}
    (h : h1.mints k = none) : (h1.union h2).mints k = h2.mints k := by
  show (match h1.mints k with | some m => some m | none => h2.mints k) =
       h2.mints k
  rw [h]

theorem union_mints_of_left_some {h1 h2 : PartialAbstractState}
    {k : Pubkey} {m : Mint}
    (h : h1.mints k = some m) : (h1.union h2).mints k = some m := by
  show (match h1.mints k with | some m => some m | none => h2.mints k) =
       some m
  rw [h]

theorem union_mints_eq_none_iff {h1 h2 : PartialAbstractState} {k : Pubkey} :
    (h1.union h2).mints k = none ↔
      h1.mints k = none ∧ h2.mints k = none := by
  show (match h1.mints k with | some m => some m | none => h2.mints k) =
       none ↔ _
  cases h1.mints k
  · cases h2.mints k <;> simp
  · simp

/-! ### Counter-clause union lemmas (mirror the account-clause ones) -/

@[simp] theorem union_counters_eq_match (h1 h2 : PartialAbstractState) :
    ∀ k, (h1.union h2).counters k =
      (match h1.counters k with | some c => some c | none => h2.counters k) :=
  fun _ => rfl

theorem union_counters_of_left_none {h1 h2 : PartialAbstractState} {k : Pubkey}
    (h : h1.counters k = none) : (h1.union h2).counters k = h2.counters k := by
  show (match h1.counters k with | some c => some c | none => h2.counters k) =
       h2.counters k
  rw [h]

theorem union_counters_of_left_some {h1 h2 : PartialAbstractState}
    {k : Pubkey} {c : CounterAccount}
    (h : h1.counters k = some c) : (h1.union h2).counters k = some c := by
  show (match h1.counters k with | some c => some c | none => h2.counters k) =
       some c
  rw [h]

theorem union_counters_eq_none_iff {h1 h2 : PartialAbstractState} {k : Pubkey} :
    (h1.union h2).counters k = none ↔
      h1.counters k = none ∧ h2.counters k = none := by
  show (match h1.counters k with | some c => some c | none => h2.counters k) =
       none ↔ _
  cases h1.counters k
  · cases h2.counters k <;> simp
  · simp

theorem union_empty_left {h : PartialAbstractState} : empty.union h = h := by
  cases h; rfl

theorem union_empty_right {h : PartialAbstractState} : h.union empty = h := by
  obtain ⟨accs, mnts, cnts⟩ := h
  show PartialAbstractState.mk _ _ _ = _
  simp only [PartialAbstractState.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;>
    · funext k
      first | cases accs k <;> rfl | cases mnts k <;> rfl | cases cnts k <;> rfl

theorem union_comm_of_disjoint {h1 h2 : PartialAbstractState}
    (hd : h1.Disjoint h2) : h1.union h2 = h2.union h1 := by
  show PartialAbstractState.mk _ _ _ = PartialAbstractState.mk _ _ _
  simp only [PartialAbstractState.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext k
    rcases hd.accounts k with h | h
    · rw [h]; cases h2.accounts k <;> rfl
    · rw [h]; cases h1.accounts k <;> rfl
  · funext k
    rcases hd.mints k with h | h
    · rw [h]; cases h2.mints k <;> rfl
    · rw [h]; cases h1.mints k <;> rfl
  · funext k
    rcases hd.counters k with h | h
    · rw [h]; cases h2.counters k <;> rfl
    · rw [h]; cases h1.counters k <;> rfl

theorem union_assoc {h1 h2 h3 : PartialAbstractState} :
    h1.union (h2.union h3) = (h1.union h2).union h3 := by
  obtain ⟨a1, m1, c1⟩ := h1
  obtain ⟨a2, m2, c2⟩ := h2
  obtain ⟨a3, m3, c3⟩ := h3
  show PartialAbstractState.mk _ _ _ = PartialAbstractState.mk _ _ _
  simp only [PartialAbstractState.mk.injEq, union]
  refine ⟨?_, ?_, ?_⟩
  · funext k; cases a1 k <;> cases a2 k <;> cases a3 k <;> rfl
  · funext k; cases m1 k <;> cases m2 k <;> cases m3 k <;> rfl
  · funext k; cases c1 k <;> cases c2 k <;> cases c3 k <;> rfl

/-! ## Empty-disjointness -/

theorem Disjoint_empty_left {h : PartialAbstractState} : empty.Disjoint h :=
  { accounts := fun _ => Or.inl rfl, mints := fun _ => Or.inl rfl,
    counters := fun _ => Or.inl rfl }

theorem Disjoint_empty_right {h : PartialAbstractState} : h.Disjoint empty :=
  Disjoint_empty_left.symm

/-! ## Disjoint redistribution under union -/

theorem Disjoint_of_union_left {h1 h2 h3 : PartialAbstractState}
    (hd : (h1.union h2).Disjoint h3) : h1.Disjoint h3 where
  accounts := fun k => by
    rcases hd.accounts k with hl | hl
    · left; exact (union_accounts_eq_none_iff.mp hl).1
    · right; exact hl
  mints := fun k => by
    rcases hd.mints k with hl | hl
    · left; exact (union_mints_eq_none_iff.mp hl).1
    · right; exact hl
  counters := fun k => by
    rcases hd.counters k with hl | hl
    · left; exact (union_counters_eq_none_iff.mp hl).1
    · right; exact hl

theorem Disjoint_of_union_right {h1 h2 h3 : PartialAbstractState}
    (hd : (h1.union h2).Disjoint h3) : h2.Disjoint h3 where
  accounts := fun k => by
    rcases hd.accounts k with hl | hl
    · left; exact (union_accounts_eq_none_iff.mp hl).2
    · right; exact hl
  mints := fun k => by
    rcases hd.mints k with hl | hl
    · left; exact (union_mints_eq_none_iff.mp hl).2
    · right; exact hl
  counters := fun k => by
    rcases hd.counters k with hl | hl
    · left; exact (union_counters_eq_none_iff.mp hl).2
    · right; exact hl

theorem Disjoint_union_of_both {h1 h2 h3 : PartialAbstractState}
    (hd1 : h1.Disjoint h3) (hd2 : h2.Disjoint h3) :
    (h1.union h2).Disjoint h3 where
  accounts := fun k => by
    rcases hd1.accounts k with hl | hl <;> rcases hd2.accounts k with hl' | hl'
    · left; exact union_accounts_eq_none_iff.mpr ⟨hl, hl'⟩
    · right; exact hl'
    · right; exact hl
    · right; exact hl
  mints := fun k => by
    rcases hd1.mints k with hl | hl <;> rcases hd2.mints k with hl' | hl'
    · left; exact union_mints_eq_none_iff.mpr ⟨hl, hl'⟩
    · right; exact hl'
    · right; exact hl
    · right; exact hl
  counters := fun k => by
    rcases hd1.counters k with hl | hl <;> rcases hd2.counters k with hl' | hl'
    · left; exact union_counters_eq_none_iff.mpr ⟨hl, hl'⟩
    · right; exact hl'
    · right; exact hl
    · right; exact hl

end PartialAbstractState

/-! ## Assertions -/

/-- An abstract assertion is a predicate on partial abstract states. -/
abbrev AbsAssertion := PartialAbstractState → Prop

/-- Separating conjunction: `P ** Q` holds on a partial abstract state
    that splits into two disjoint pieces satisfying `P` and `Q`. -/
def sepConj (P Q : AbsAssertion) : AbsAssertion :=
  fun h => ∃ h1 h2, h1.Disjoint h2 ∧ h1.union h2 = h ∧ P h1 ∧ Q h2

@[inherit_doc] scoped infixr:35 " ** " => sepConj

/-- The empty assertion: holds only on the empty partial abstract state. -/
def emp : AbsAssertion := fun h => h = PartialAbstractState.empty

/-- Account at `key` holds the decoded record `t`, and that's all we own. -/
def accountIs (key : Pubkey) (t : TokenAccount) : AbsAssertion :=
  fun h => h = PartialAbstractState.singletonAccount key t

@[inherit_doc] notation:50 k " ↦ₐ " t => accountIs k t

/-- Mint at `key` holds the decoded record `m`, and that's all we own. -/
def mintIs (key : Pubkey) (m : Mint) : AbsAssertion :=
  fun h => h = PartialAbstractState.singletonMint key m

@[inherit_doc] notation:50 k " ↦ₘ " m => mintIs k m

/-- Counter at `key` holds the decoded record `c`, and that's all we own. -/
def counterIs (key : Pubkey) (c : CounterAccount) : AbsAssertion :=
  fun h => h = PartialAbstractState.singletonCounter key c

@[inherit_doc] notation:50 k " ↦cnt " c => counterIs k c

/-! ## Structural lemmas for `**` -/

theorem sepConj_comm {P Q : AbsAssertion} :
    ∀ h, (P ** Q) h ↔ (Q ** P) h := by
  intro h
  constructor
  · rintro ⟨h1, h2, hd, hu, hP, hQ⟩
    refine ⟨h2, h1, hd.symm, ?_, hQ, hP⟩
    rw [← hu]; exact (PartialAbstractState.union_comm_of_disjoint hd).symm
  · rintro ⟨h1, h2, hd, hu, hQ, hP⟩
    refine ⟨h2, h1, hd.symm, ?_, hP, hQ⟩
    rw [← hu]; exact (PartialAbstractState.union_comm_of_disjoint hd).symm

theorem sepConj_emp_left {P : AbsAssertion} :
    ∀ h, (emp ** P) h ↔ P h := by
  intro h
  constructor
  · rintro ⟨h1, h2, _, hu, hemp, hP⟩
    rw [show h1 = PartialAbstractState.empty from hemp] at hu
    rw [PartialAbstractState.union_empty_left] at hu
    rwa [← hu]
  · intro hP
    exact ⟨PartialAbstractState.empty, h, PartialAbstractState.Disjoint_empty_left,
           PartialAbstractState.union_empty_left, rfl, hP⟩

theorem sepConj_emp_right {P : AbsAssertion} :
    ∀ h, (P ** emp) h ↔ P h := by
  intro h; rw [sepConj_comm]; exact sepConj_emp_left h

theorem sepConj_assoc {P Q R : AbsAssertion} :
    ∀ h, ((P ** Q) ** R) h ↔ (P ** (Q ** R)) h := by
  intro h
  constructor
  · rintro ⟨h_PQ, h_R, hd_PQR, hu_PQR, ⟨h_P, h_Q, hd_PQ, hu_PQ, hP, hQ⟩, hR⟩
    have hd_PQR' : (h_P.union h_Q).Disjoint h_R := hu_PQ ▸ hd_PQR
    have hd_PR : h_P.Disjoint h_R := PartialAbstractState.Disjoint_of_union_left hd_PQR'
    have hd_QR : h_Q.Disjoint h_R := PartialAbstractState.Disjoint_of_union_right hd_PQR'
    have hd_P_QR : h_P.Disjoint (h_Q.union h_R) :=
      (PartialAbstractState.Disjoint_union_of_both hd_PQ.symm hd_PR.symm).symm
    refine ⟨h_P, h_Q.union h_R, hd_P_QR, ?_, hP,
            ⟨h_Q, h_R, hd_QR, rfl, hQ, hR⟩⟩
    rw [PartialAbstractState.union_assoc, hu_PQ]; exact hu_PQR
  · rintro ⟨h_P, h_QR, hd_P_QR, hu_P_QR, hP, ⟨h_Q, h_R, hd_QR, hu_QR, hQ, hR⟩⟩
    have hd_P_QR' : h_P.Disjoint (h_Q.union h_R) := hu_QR ▸ hd_P_QR
    have hd_PQ : h_P.Disjoint h_Q :=
      (PartialAbstractState.Disjoint_of_union_left hd_P_QR'.symm).symm
    have hd_PR : h_P.Disjoint h_R :=
      (PartialAbstractState.Disjoint_of_union_right hd_P_QR'.symm).symm
    have hd_PQ_R : (h_P.union h_Q).Disjoint h_R :=
      PartialAbstractState.Disjoint_union_of_both hd_PR hd_QR
    refine ⟨h_P.union h_Q, h_R, hd_PQ_R, ?_, ⟨h_P, h_Q, hd_PQ, rfl, hP, hQ⟩, hR⟩
    rw [← PartialAbstractState.union_assoc, hu_QR]; exact hu_P_QR

/-! ## Disjointness of singleton accounts -/

/-- Two singleton-account atoms with distinct keys are disjoint. -/
theorem singletonAccount_Disjoint_of_ne
    {k1 k2 : Pubkey} (t1 t2 : TokenAccount) (h : k1 ≠ k2) :
    (PartialAbstractState.singletonAccount k1 t1).Disjoint
      (PartialAbstractState.singletonAccount k2 t2) where
  accounts := fun k => by
    by_cases hk1 : k = k1
    · subst hk1
      right; exact PartialAbstractState.singletonAccount_accounts_other h
    · left; exact PartialAbstractState.singletonAccount_accounts_other hk1
  mints := fun _ => Or.inl (PartialAbstractState.singletonAccount_mints _)
  counters := fun _ => Or.inl (PartialAbstractState.singletonAccount_counters _)

/-- Two singleton-mint atoms with distinct keys are disjoint. -/
theorem singletonMint_Disjoint_of_ne
    {k1 k2 : Pubkey} (m1 m2 : Mint) (h : k1 ≠ k2) :
    (PartialAbstractState.singletonMint k1 m1).Disjoint
      (PartialAbstractState.singletonMint k2 m2) where
  accounts := fun _ => Or.inl (PartialAbstractState.singletonMint_accounts _)
  mints := fun k => by
    by_cases hk1 : k = k1
    · subst hk1
      right; exact PartialAbstractState.singletonMint_mints_other h
    · left; exact PartialAbstractState.singletonMint_mints_other hk1
  counters := fun _ => Or.inl (PartialAbstractState.singletonMint_counters _)

/-- A token-account atom and a mint atom are always disjoint (different
    resource clauses), even at the same key. -/
theorem singletonAccount_Disjoint_singletonMint
    {k1 k2 : Pubkey} (t : TokenAccount) (m : Mint) :
    (PartialAbstractState.singletonAccount k1 t).Disjoint
      (PartialAbstractState.singletonMint k2 m) where
  accounts := fun _ => Or.inr (PartialAbstractState.singletonMint_accounts _)
  mints := fun _ => Or.inl (PartialAbstractState.singletonAccount_mints _)
  counters := fun _ => Or.inl (PartialAbstractState.singletonAccount_counters _)

/-- Two singleton-counter atoms with distinct keys are disjoint. -/
theorem singletonCounter_Disjoint_of_ne
    {k1 k2 : Pubkey} (c1 c2 : CounterAccount) (h : k1 ≠ k2) :
    (PartialAbstractState.singletonCounter k1 c1).Disjoint
      (PartialAbstractState.singletonCounter k2 c2) where
  accounts := fun _ => Or.inl (PartialAbstractState.singletonCounter_accounts _)
  mints := fun _ => Or.inl (PartialAbstractState.singletonCounter_mints _)
  counters := fun k => by
    by_cases hk1 : k = k1
    · subst hk1
      right; exact PartialAbstractState.singletonCounter_counters_other h
    · left; exact PartialAbstractState.singletonCounter_counters_other hk1

/-! ## holdsFor — bridge from AbsAssertion to full AbstractState -/

/-- An abstract assertion `P` holds for a full `AbstractState` `s` when
    some partial state compatible with `s` satisfies `P`. -/
def AbsAssertion.holdsFor (P : AbsAssertion) (s : AbstractState) : Prop :=
  ∃ h : PartialAbstractState, h.CompatibleWith s ∧ P h

theorem holdsFor_iff_pointwise {P Q : AbsAssertion} {s : AbstractState}
    (h : ∀ h, P h ↔ Q h) : P.holdsFor s ↔ Q.holdsFor s := by
  unfold AbsAssertion.holdsFor
  exact ⟨fun ⟨hp, hc, hP⟩ => ⟨hp, hc, (h hp).mp hP⟩,
         fun ⟨hp, hc, hQ⟩ => ⟨hp, hc, (h hp).mpr hQ⟩⟩

end SVM.Solana.Abstract
