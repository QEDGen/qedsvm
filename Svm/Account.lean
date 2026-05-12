namespace Svm.Account

/-- A 32-byte Solana public key as four little-endian U64 chunks.
    Matches sBPF VM representation: programs compare pubkeys via
    four `ldx.dw` loads at byte offsets 0, 8, 16, 24. -/
structure Pubkey where
  c0 : Nat  -- bytes 0-7, little-endian U64
  c1 : Nat  -- bytes 8-15
  c2 : Nat  -- bytes 16-23
  c3 : Nat  -- bytes 24-31
  deriving DecidableEq, BEq, Repr, Inhabited

theorem Pubkey.ext' {a b : Pubkey}
    (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1) (h2 : a.c2 = b.c2) (h3 : a.c3 = b.c3) :
    a = b := by
  cases a; cases b; simp_all

/-- Two pubkeys differ iff at least one chunk differs. -/
theorem Pubkey.ne_iff {a b : Pubkey} :
    a ≠ b ↔ a.c0 ≠ b.c0 ∨ a.c1 ≠ b.c1 ∨ a.c2 ≠ b.c2 ∨ a.c3 ≠ b.c3 := by
  constructor
  · intro h
    if h0 : a.c0 = b.c0 then
      if h1 : a.c1 = b.c1 then
        if h2 : a.c2 = b.c2 then
          if h3 : a.c3 = b.c3 then
            exact absurd (Pubkey.ext' h0 h1 h2 h3) h
          else exact Or.inr (Or.inr (Or.inr h3))
        else exact Or.inr (Or.inr (Or.inl h2))
      else exact Or.inr (Or.inl h1)
    else exact Or.inl h0
  · intro h heq; subst heq
    cases h with
    | inl h => exact h rfl
    | inr h => cases h with
      | inl h => exact h rfl
      | inr h => cases h with
        | inl h => exact h rfl
        | inr h => exact h rfl

abbrev U64 := Nat
abbrev U128 := Nat
abbrev I128 := Int
abbrev U8 := Nat

structure Account where
  key : Pubkey
  authority : Pubkey
  balance : Nat := 0
  writable : Bool := true
  deriving Repr, DecidableEq, BEq

def canWrite (actor : Pubkey) (account : Account) : Prop :=
  account.writable = true /\ account.authority = actor

-- Finding an account by key
def findByKey (p_accounts : List Account) (p_key : Pubkey) : Option Account :=
  p_accounts.find? (fun acc => acc.key = p_key)

-- Finding an account by authority
def findByAuthority (p_accounts : List Account) (p_authority : Pubkey) : Option Account :=
  p_accounts.find? (fun acc => acc.authority = p_authority)

/-! ## List-update lemmas

These were `axiom` declarations until formal-svm Phase 0; they are
standard `List.map` / `List.find?` interaction theorems, provable in
core Lean without Mathlib. Replaces the past comment "full proof would
require more complex induction" — it doesn't. -/

-- Find on a mapped list equals map of find on the original, when the
-- map preserves the predicate's value. Proven by `List.find?_map` from
-- core: `(l.map g).find? p = (l.find? (p ∘ g)).map g`, then observing
-- that `p_h` gives `p_pred ∘ p_f = p_pred` extensionally.
theorem find_map_pred_preserved
    (p_accounts : List Account)
    (p_pred : Account → Bool)
    (p_f : Account → Account)
    (p_h : ∀ acc, p_pred acc = p_pred (p_f acc)) :
    (p_accounts.map p_f).find? p_pred = (p_accounts.find? p_pred).map p_f := by
  rw [List.find?_map]
  have h_funext : p_pred ∘ p_f = p_pred := funext (fun acc => (p_h acc).symm)
  rw [h_funext]

-- Find after updating a different account (by authority) returns the same
-- result as on the unmodified list, since the modified account's authority
-- isn't the target.
theorem find_map_update_other
    (p_accounts : List Account)
    (p_target_authority p_update_authority : Pubkey)
    (p_f : Account → Account)
    (p_h_distinct : p_target_authority ≠ p_update_authority)
    (p_h_preserves_auth : ∀ acc, (p_f acc).authority = acc.authority) :
    findByAuthority
      (p_accounts.map (fun acc =>
        if acc.authority = p_update_authority then p_f acc else acc))
      p_target_authority
      = findByAuthority p_accounts p_target_authority := by
  unfold findByAuthority
  induction p_accounts with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons, List.find?_cons]
    by_cases h_head_update : head.authority = p_update_authority
    · -- head gets transformed; neither head nor (f head) matches target.
      have h_head_not_target : head.authority ≠ p_target_authority := by
        rw [h_head_update]; exact p_h_distinct.symm
      have h_fhead_not_target : (p_f head).authority ≠ p_target_authority := by
        rw [p_h_preserves_auth head]; exact h_head_not_target
      rw [if_pos h_head_update]
      rw [decide_eq_false h_fhead_not_target, decide_eq_false h_head_not_target]
      simp only [Bool.false_eq_true, if_false]
      exact ih
    · -- head unchanged by the conditional update.
      rw [if_neg h_head_update]
      by_cases h_head_target : head.authority = p_target_authority
      · rw [decide_eq_true h_head_target]
      · rw [decide_eq_false h_head_target]
        simp only [Bool.false_eq_true, if_false]
        exact ih

-- Find after updating the target account returns the updated account.
theorem find_map_update_same
    (p_accounts : List Account)
    (p_authority : Pubkey)
    (p_original : Account)
    (p_f : Account → Account)
    (p_h_found : findByAuthority p_accounts p_authority = some p_original)
    (p_h_preserves_auth : ∀ acc, (p_f acc).authority = acc.authority) :
    findByAuthority
      (p_accounts.map (fun acc =>
        if acc.authority = p_authority then p_f acc else acc))
      p_authority
      = some (p_f p_original) := by
  unfold findByAuthority at p_h_found ⊢
  induction p_accounts with
  | nil => simp at p_h_found
  | cons head tail ih =>
    simp only [List.map_cons, List.find?_cons] at p_h_found ⊢
    by_cases h : head.authority = p_authority
    · -- head IS the target; find short-circuited at head in original.
      rw [decide_eq_true h] at p_h_found
      simp only [if_true] at p_h_found
      have h_original : head = p_original := Option.some.inj p_h_found
      subst h_original
      rw [if_pos h]
      have h_fhead_auth : (p_f head).authority = p_authority := by
        rw [p_h_preserves_auth head]; exact h
      rw [decide_eq_true h_fhead_auth]
    · -- head isn't the target; both find?s recurse into tail.
      rw [decide_eq_false h] at p_h_found
      simp only [Bool.false_eq_true, if_false] at p_h_found
      rw [if_neg h]
      rw [decide_eq_false h]
      simp only [Bool.false_eq_true, if_false]
      exact ih p_h_found

-- Key-based version of find_map_update_other.
theorem find_by_key_map_update_other
    (p_accounts : List Account)
    (p_target_key p_update_key : Pubkey)
    (p_f : Account → Account)
    (p_h_distinct : p_target_key ≠ p_update_key)
    (p_h_preserves_key : ∀ acc, (p_f acc).key = acc.key) :
    findByKey
      (p_accounts.map (fun acc =>
        if acc.key = p_update_key then p_f acc else acc))
      p_target_key
      = findByKey p_accounts p_target_key := by
  unfold findByKey
  induction p_accounts with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons, List.find?_cons]
    by_cases h_head_update : head.key = p_update_key
    · have h_head_not_target : head.key ≠ p_target_key := by
        rw [h_head_update]; exact p_h_distinct.symm
      have h_fhead_not_target : (p_f head).key ≠ p_target_key := by
        rw [p_h_preserves_key head]; exact h_head_not_target
      rw [if_pos h_head_update]
      rw [decide_eq_false h_fhead_not_target, decide_eq_false h_head_not_target]
      simp only [Bool.false_eq_true, if_false]
      exact ih
    · rw [if_neg h_head_update]
      by_cases h_head_target : head.key = p_target_key
      · rw [decide_eq_true h_head_target]
      · rw [decide_eq_false h_head_target]
        simp only [Bool.false_eq_true, if_false]
        exact ih

-- Key-based version of find_map_update_same.
theorem find_by_key_map_update_same
    (p_accounts : List Account)
    (p_key : Pubkey)
    (p_original : Account)
    (p_f : Account → Account)
    (p_h_found : findByKey p_accounts p_key = some p_original)
    (p_h_preserves_key : ∀ acc, (p_f acc).key = acc.key) :
    findByKey
      (p_accounts.map (fun acc =>
        if acc.key = p_key then p_f acc else acc))
      p_key
      = some (p_f p_original) := by
  unfold findByKey at p_h_found ⊢
  induction p_accounts with
  | nil => simp at p_h_found
  | cons head tail ih =>
    simp only [List.map_cons, List.find?_cons] at p_h_found ⊢
    by_cases h : head.key = p_key
    · rw [decide_eq_true h] at p_h_found
      simp only [if_true] at p_h_found
      have h_original : head = p_original := Option.some.inj p_h_found
      subst h_original
      rw [if_pos h]
      have h_fhead_key : (p_f head).key = p_key := by
        rw [p_h_preserves_key head]; exact h
      rw [decide_eq_true h_fhead_key]
    · rw [decide_eq_false h] at p_h_found
      simp only [Bool.false_eq_true, if_false] at p_h_found
      rw [if_neg h]
      rw [decide_eq_false h]
      simp only [Bool.false_eq_true, if_false]
      exact ih p_h_found

end Svm.Account

namespace Svm

abbrev Pubkey := Svm.Account.Pubkey
abbrev U64 := Svm.Account.U64
abbrev U128 := Svm.Account.U128
abbrev I128 := Svm.Account.I128
abbrev U8 := Svm.Account.U8
abbrev Account := Svm.Account.Account
abbrev canWrite := Svm.Account.canWrite
abbrev findByKey := Svm.Account.findByKey
abbrev findByAuthority := Svm.Account.findByAuthority
abbrev find_map_pred_preserved := Svm.Account.find_map_pred_preserved
abbrev find_map_update_other := Svm.Account.find_map_update_other
abbrev find_map_update_same := Svm.Account.find_map_update_same
abbrev find_by_key_map_update_other := Svm.Account.find_by_key_map_update_other
abbrev find_by_key_map_update_same := Svm.Account.find_by_key_map_update_same

end Svm
