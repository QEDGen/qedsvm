-- Solana Pattern Proof Library, Layer 2: recognizers.
--
-- Lemmas connecting the Layer-1 predicates to the SL vocabulary that the proven
-- bytecode refinements already use. This first batch harvests the SPL-token
-- arm: the `tokenAcctBalance` atom that `AsmRefinesTokenTransfer` carries in its
-- pre/post is exactly the account whose `amount` field the `balanceAtLeast`
-- predicate reads, so a proven token account (with `amount ≥ n`) refines
-- `balanceAtLeast`.
--
-- These are proven SEMANTICALLY (entailment over the SL model), not by matching
-- bytes. They reuse the existing atoms rather than reinventing, and use only
-- clean tactics (no native_decide), so they stay AxiomAudit-friendly.

import SVM.Solana.Patterns.Predicates
import SVM.Solana.TokenAccount

namespace SVM.Solana.Patterns

open SVM.SBPF
open SVM.Pubkey

/-! ## Separating-conjunction monotonicity (helpers)

`sepConj` is an existential over a disjoint heap split, so weakening one side is
immediate. These let a recognizer weaken a single conjunct of a larger account
assertion in place, without permuting the others. -/

/-- Weaken the left conjunct of a separating conjunction. -/
theorem sepConj_mono_left {P P' Q : Assertion} (h : ∀ ps, P ps → P' ps) :
    ∀ ps, (P ** Q) ps → (P' ** Q) ps := by
  intro ps hpq
  obtain ⟨h1, h2, hd, hu, hP, hQ⟩ := hpq
  exact ⟨h1, h2, hd, hu, h h1 hP, hQ⟩

/-- Weaken the right conjunct of a separating conjunction. -/
theorem sepConj_mono_right {P Q Q' : Assertion} (h : ∀ ps, Q ps → Q' ps) :
    ∀ ps, (P ** Q) ps → (P ** Q') ps := by
  intro ps hpq
  obtain ⟨h1, h2, hd, hu, hP, hQ⟩ := hpq
  exact ⟨h1, h2, hd, hu, hP, h h2 hQ⟩

/-! ## `balanceAtLeast` recognizers -/

/-- Core: an account whose `amount` cell holds a value `≥ n` satisfies
    `balanceAtLeast n`. Same footprint (the amount cell), value weakening. This
    is the layout-general primitive every balance recognizer composes from. -/
theorem balanceAtLeast_of_amountCell (ata n amount : Nat) (h : n ≤ amount) :
    ∀ ps, ((ata + SVM.Solana.AMOUNT_OFF) ↦U64 amount) ps → balanceAtLeast ata n ps := by
  intro ps hps
  exact ⟨amount, h, hps⟩

/-- `balanceAtLeast` weakens in its bound: at-least-`n` implies at-least-`n'`
    for any `n' ≤ n`. -/
theorem balanceAtLeast_weaken (ata n n' : Nat) (h : n' ≤ n) :
    ∀ ps, balanceAtLeast ata n ps → balanceAtLeast ata n' ps := by
  intro ps hb
  obtain ⟨v, hv, hcell⟩ := hb
  exact ⟨v, Nat.le_trans h hv, hcell⟩

/-- HARVEST (SPL token): a token account at `ata` whose balance is `amount ≥ n`
    entails the same account assertion with the `amount` conjunct weakened to the
    security predicate `balanceAtLeast n`. The mint / owner / rest fields flow
    through unchanged. This is the recognizer that ties `balanceAtLeast` to the
    `tokenAcctBalance` atom carried by `AsmRefinesTokenTransfer`. -/
theorem balanceAtLeast_of_tokenAcctBalance
    (ata n amount : Nat) (mint owner : Pubkey) (rest : ByteArray)
    (h : n ≤ amount) :
    ∀ ps, tokenAcctBalance ata mint owner amount rest ps →
      (((ata + SVM.Solana.MINT_OFF)  ↦Pubkey mint) **
       (((ata + SVM.Solana.OWNER_OFF) ↦Pubkey owner) **
        (balanceAtLeast ata n **
         ((ata + SVM.Solana.REST_OFF) ↦Bytes rest)))) ps := by
  intro ps hps
  unfold tokenAcctBalance at hps
  exact sepConj_mono_right
    (sepConj_mono_right
      (sepConj_mono_left (balanceAtLeast_of_amountCell ata n amount h)))
    ps hps

end SVM.Solana.Patterns
