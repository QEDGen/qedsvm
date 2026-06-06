/-
  Discharge PoC: qedgen's parametric `ensures_axiom` shape drops out of a
  lift's layout-general field-list obligation.

  qedgen states a state-mutation contract parametrically, over an opaque
  `State` and an accessor `State → Nat`
  (QEDGen/solana-skills: crates/qedgen/data/proofs/spl/Token.lean):

      axiom ensures_axiom_0 {State} [Inhabited State]
        (pre post : State) (amount : Nat) (from_balance : State → Nat) :
        (from_balance post) = (from_balance pre) - amount

  The `qedsvm_discharge` direction (QEDGen/qedsvm#24) is to PROVE that
  obligation against pinned bytecode instead of axiomatising it. This file
  validates the keystone of that direction: the accessor projection.

  Instantiate `State` as the decoded field list the lift emits (the
  `List (Nat × FieldVal)` that `AsmRefinesFieldUpdate` carries, after the
  `account_agg` byte<->field reshape — keystone #2, already proven), and
  `from_balance` as a `u64` field lookup. Then qedgen's
  `accessor post = accessor pre ± amount` is a pure projection on the
  pre/post field lists. The byte realization is the lift's reshape; this is
  the accessor read on top — and it needs NO raw `readU64`/`Mem` bridge,
  because the field-list route sidesteps it.
-/

import SVM.Solana.Abstract.Refinement
import Generated.VaultRefinement
import SVM.SBPF.Tactic.Discharge
import SVM.Solana.TokenFieldCodec

namespace Examples.DischargePoC

open SVM SVM.SBPF SVM.SBPF.Memory SVM.Pubkey SVM.Solana SVM.Solana.Abstract

-- `u64FieldAt` (qedgen's accessor, instantiated), `u64FieldAt_found` (the
-- generic projection lemma), and the `qedsvm_discharge` tactic now live in
-- the library: `SVM.SBPF.Tactic.Discharge`.

/-! ## Vault: `total post = total pre + 1`, discharged from the real lift

The field lists are exactly `Generated.VaultRefinement`'s
(`{owner:Pubkey@0, total:u64@32, bump:u8@40}`). Given the lift's
`AsmRefinesFieldUpdate` obligation, qedgen's ensures-shape follows by the
accessor projection: the obligation half says the bytecode realises the
field-list transition; the accessor half reads it as the ensures clause. -/
theorem vault_total_discharged
    (cr : CodeReq) (rr : Memory.RegionTable → Prop)
    (baseAddr oldMemD_0 o0 o1 o2 o3 fb4 : Nat) (setupPre setupPost : Assertion)
    (h : AsmRefinesFieldUpdate cr 4 0 0 4 rr baseAddr
          [(0, .pubkey ⟨o0, o1, o2, o3⟩), (32, .u64 oldMemD_0), (40, .byte fb4)]
          [(0, .pubkey ⟨o0, o1, o2, o3⟩), (32, .u64 (oldMemD_0 + 1)), (40, .byte fb4)]
          setupPre setupPost) :
    AsmRefinesFieldUpdate cr 4 0 0 4 rr baseAddr
        [(0, .pubkey ⟨o0, o1, o2, o3⟩), (32, .u64 oldMemD_0), (40, .byte fb4)]
        [(0, .pubkey ⟨o0, o1, o2, o3⟩), (32, .u64 (oldMemD_0 + 1)), (40, .byte fb4)]
        setupPre setupPost
      ∧ u64FieldAt 32 [(0, .pubkey ⟨o0, o1, o2, o3⟩), (32, .u64 (oldMemD_0 + 1)), (40, .byte fb4)]
          = u64FieldAt 32 [(0, .pubkey ⟨o0, o1, o2, o3⟩), (32, .u64 oldMemD_0), (40, .byte fb4)] + 1 :=
  ⟨h, by qedsvm_discharge⟩

/-- End-to-end: the real vault lift (`Generated.VaultRefinement.refines_asm`)
    flows through the discharge to qedgen's `total post = total pre + 1`. The
    `lift` type is `VaultRefinement.refines_asm`'s raw byte-level triple. -/
example
    (cr : CodeReq) (rr : Memory.RegionTable → Prop)
    (baseAddr oldMemD_0 vR2Old vR0Old o0 o1 o2 o3 fb4 : Nat)
    (lift : cuTripleWithinMem 4 0 0 4 cr
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 32 ↦U64 oldMemD_0) **
      (.r2 ↦ᵣ vR2Old) **
      (.r0 ↦ᵣ vR0Old))
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 32 ↦U64 oldMemD_0 + 1) **
      (.r2 ↦ᵣ wrapAdd oldMemD_0 (toU64 1)) **
      (.r0 ↦ᵣ toU64 0)) rr) :
    u64FieldAt 32 [(0, .pubkey ⟨o0, o1, o2, o3⟩), (32, .u64 (oldMemD_0 + 1)), (40, .byte fb4)]
      = u64FieldAt 32 [(0, .pubkey ⟨o0, o1, o2, o3⟩), (32, .u64 oldMemD_0), (40, .byte fb4)] + 1 :=
  (vault_total_discharged cr rr baseAddr oldMemD_0 o0 o1 o2 o3 fb4 _ _
    (Examples.VaultRefinement.refines_asm cr rr baseAddr oldMemD_0 vR2Old vR0Old o0 o1 o2 o3 fb4 lift)).2

/-! ## Token transfer: convergence to the field-list route

The SPL token account as a `FieldVal` field list, the convergence keystone
(`tokenAcctBalance_codec`), and the discharged amount-field `ensures`
(`token_ensures_debit` / `token_ensures_credit`) now live in the library:
`SVM.Solana.TokenFieldCodec`. The SPL layout is fixed, so those `ensures`
are single library facts rather than per-lift emissions. What remains here
is the obligation-level reshape demonstrated on a real `AsmRefinesToken-
Transfer`. -/

/-- Convert a real `AsmRefinesTokenTransfer` obligation into field-list
    (`codecCoarse`) form via the convergence keystone — the token-side
    analogue of the vault's `AsmRefinesFieldUpdate`. -/
theorem transfer_field_obligation
    (cr : CodeReq) (nSteps nCu entry exit : Nat) (rr : Memory.RegionTable → Prop)
    (srcAddr dstAddr : Nat) (tSrc tDst : TokenAccount) (amount : Nat)
    (setupPre setupPost : Assertion)
    (h : AsmRefinesTokenTransfer cr nSteps nCu entry exit rr srcAddr dstAddr
          tSrc tDst amount setupPre setupPost) :
    cuTripleWithinMem nSteps nCu entry exit cr
      (setupPre ** codecCoarse srcAddr (tokenFields tSrc.mint tSrc.owner tSrc.amount tSrc.rest)
               ** codecCoarse dstAddr (tokenFields tDst.mint tDst.owner tDst.amount tDst.rest))
      (setupPost ** codecCoarse srcAddr (tokenFields tSrc.mint tSrc.owner (tSrc.amount - amount) tSrc.rest)
                ** codecCoarse dstAddr (tokenFields tDst.mint tDst.owner (tDst.amount + amount) tDst.rest))
      rr := by
  unfold AsmRefinesTokenTransfer at h
  simpa only [tokenAcctBalanceOf, tokenAcctBalance_codec,
              TokenAccount.withAmount_amount, TokenAccount.withAmount_mint,
              TokenAccount.withAmount_owner, TokenAccount.withAmount_rest] using h

end Examples.DischargePoC
