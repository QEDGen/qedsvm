/-
  Footprint vocabulary for abstract triples.

  `agreesOutside keys s s'` says the two states match on every account
  except those in `keys`. It is the natural shape of the "untouched
  accounts" clause that closes a consumer-facing correctness theorem
  for a multi-account intrinsic ("balances shifted on `src` and `dst`;
  every other key is unchanged").

  Today it appears as a dangling `∀ k, k ≠ src → k ≠ dst → ...`
  conjunct in `tokenTransfer_correct`. As more MIR intrinsics land,
  factoring through `agreesOutside` keeps each consumer theorem
  uniform; downstream MIR composition / frame-rule work will use the
  same predicate as the resource footprint.

  This file is the vocabulary only. Per-intrinsic theorems quote it;
  rewriting `tokenTransfer_correct` to use it is intentionally
  deferred (sequencing with parallel work on Domain.lean).
-/

import SVM.Solana.Abstract.State

namespace SVM.Solana.Abstract

open SVM.Pubkey

/-- `agreesOutside keys s s'`: the two states own the same account
    record (or no record) at every key not listed in `keys`. The
    canonical "frame" predicate for an intrinsic that mutates exactly
    `keys` and leaves every other account untouched.

    Asymmetric reading is intentional — `agreesOutside [src, dst] s s'`
    is the shape that closes a Hoare triple `{s} prog {s'}` where
    `prog` touched only `src` and `dst`. -/
def agreesOutside (keys : List Pubkey) (s s' : AbstractState) : Prop :=
  ∀ k, k ∉ keys → s.get k = s'.get k

namespace agreesOutside

/-- Reflexivity: every state agrees with itself outside any key set. -/
theorem refl (keys : List Pubkey) (s : AbstractState) :
    agreesOutside keys s s :=
  fun _ _ => rfl

/-- Symmetry: agreement is symmetric in the two states. -/
theorem symm {keys : List Pubkey} {s s' : AbstractState} :
    agreesOutside keys s s' → agreesOutside keys s' s :=
  fun h k hk => (h k hk).symm

/-- Transitivity: agreement composes along a chain of states. -/
theorem trans {keys : List Pubkey} {s s' s'' : AbstractState} :
    agreesOutside keys s s' → agreesOutside keys s' s'' →
    agreesOutside keys s s'' :=
  fun h1 h2 k hk => (h1 k hk).trans (h2 k hk)

/-- Monotonicity: enlarging the key set weakens the predicate.
    If two states agree outside a smaller set, they also agree outside
    any superset. -/
theorem mono {keys keys' : List Pubkey} {s s' : AbstractState}
    (h_sub : ∀ k, k ∈ keys → k ∈ keys') :
    agreesOutside keys s s' → agreesOutside keys' s s' :=
  fun h k hk => h k (fun h_in => hk (h_sub k h_in))

/-- Empty key set collapses to full equality on `.get`. -/
theorem empty_iff (s s' : AbstractState) :
    agreesOutside [] s s' ↔ ∀ k, s.get k = s'.get k := by
  constructor
  · intro h k; exact h k (by simp)
  · intro h k _; exact h k

/-- Singleton key set: agreement outside `[a]` means `get` matches on
    every key other than `a`. -/
theorem singleton_iff (a : Pubkey) (s s' : AbstractState) :
    agreesOutside [a] s s' ↔ ∀ k, k ≠ a → s.get k = s'.get k := by
  constructor
  · intro h k hk; exact h k (by simp [hk])
  · intro h k hk; exact h k (by simpa using hk)

/-- Two-key set: agreement outside `[a, b]` matches the shape that
    closes a `tokenTransfer`-style correctness theorem. -/
theorem pair_iff (a b : Pubkey) (s s' : AbstractState) :
    agreesOutside [a, b] s s' ↔
      ∀ k, k ≠ a → k ≠ b → s.get k = s'.get k := by
  constructor
  · intro h k ha hb; exact h k (by simp [ha, hb])
  · intro h k hk
    have ha : k ≠ a := fun h_eq => hk (by simp [h_eq])
    have hb : k ≠ b := fun h_eq => hk (by simp [h_eq])
    exact h k ha hb

end agreesOutside

end SVM.Solana.Abstract
