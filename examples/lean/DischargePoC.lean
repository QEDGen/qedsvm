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

namespace Examples.DischargePoC

open SVM SVM.SBPF SVM.SBPF.Memory SVM.Pubkey SVM.Solana SVM.Solana.Abstract

/-- qedgen's `from_balance : State → Nat`, instantiated: read the `u64`
    field at byte offset `off` from a decoded account. Here `State` is the
    field list the lift produces; `from_balance := u64FieldAt off`. -/
def u64FieldAt (off : Nat) : List (Nat × FieldVal) → Nat
  | [] => 0
  | (o, .u64 v) :: rest => if o = off then v else u64FieldAt off rest
  | _ :: rest => u64FieldAt off rest

/-- Generic accessor evaluation: a `.u64` field at `off` reads its value,
    when the entries before it carry other offsets (true of the lift's
    sorted, distinct-offset field lists). Turns the per-program `simp` into
    a reusable lemma — the projection the discharge tactic applies. -/
theorem u64FieldAt_found (off v : Nat) (before after : List (Nat × FieldVal))
    (hb : ∀ e ∈ before, e.1 ≠ off) :
    u64FieldAt off (before ++ (off, .u64 v) :: after) = v := by
  induction before with
  | nil => simp [u64FieldAt]
  | cons e es ih =>
    have ho : e.1 ≠ off := hb e (by simp)
    have ih' := ih (fun x hx => hb x (by simp [hx]))
    obtain ⟨o, fv⟩ := e
    simp only [List.cons_append]
    cases fv <;> simp_all [u64FieldAt]

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
  ⟨h, by simp [u64FieldAt]⟩

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

The SPL token account `tokenAcctBalance` (mint@0, owner@32, amount@64,
rest@72) IS a `codecCoarse` field list — the convergence keystone that
lets `AsmRefinesTokenTransfer` use the same accessor projection as the
vault, instead of the bespoke `TokenAccount` record (QEDGen/qedsvm#24,
"converge AsmRefinesToken*"). -/

/-- The token field list: the SPL account as a layout-general `FieldVal`
    list (the `account_agg` example in `SVM/SBPF/AccountCodec.lean`). -/
def tokenFields (mint owner : SVM.Pubkey) (amount : Nat) (rest : ByteArray) :
    List (Nat × FieldVal) :=
  [(0, .pubkey mint), (32, .pubkey owner), (64, .u64 amount), (72, .blob [.gap rest])]

/-- **Convergence keystone.** The byte-level token account predicate is the
    coarse codec of its field list. So a token obligation is a field-list
    obligation, and the accessor projection applies. -/
theorem tokenAcctBalance_codec (ata : Nat) (mint owner : SVM.Pubkey) (amount : Nat) (rest : ByteArray) :
    tokenAcctBalance ata mint owner amount rest
      = codecCoarse ata (tokenFields mint owner amount rest) := by
  simp [tokenAcctBalance, tokenFields, MINT_OFF, OWNER_OFF, AMOUNT_OFF, REST_OFF,
        codecCoarse, FieldVal.coarse, segsBytes, FieldSeg.bytes,
        sepConj_emp_right_eq]

/-- The accessor reads the `amount` field (offset 64) of a token field list. -/
@[simp] theorem u64FieldAt_tokenFields (mint owner : SVM.Pubkey) (amount : Nat) (rest : ByteArray) :
    u64FieldAt 64 (tokenFields mint owner amount rest) = amount := by
  simp [u64FieldAt, tokenFields]

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

/-- qedgen `ensures_axiom_0`: `from_balance post = from_balance pre - amount`,
    on the src account's `amount` field, projected from the field list. -/
theorem transfer_ensures_0 (mint owner : SVM.Pubkey) (fromAmt amount : Nat) (rest : ByteArray) :
    u64FieldAt 64 (tokenFields mint owner (fromAmt - amount) rest)
      = u64FieldAt 64 (tokenFields mint owner fromAmt rest) - amount := by
  simp

/-- qedgen `ensures_axiom_1`: `to_balance post = to_balance pre + amount`. -/
theorem transfer_ensures_1 (mint owner : SVM.Pubkey) (toAmt amount : Nat) (rest : ByteArray) :
    u64FieldAt 64 (tokenFields mint owner (toAmt + amount) rest)
      = u64FieldAt 64 (tokenFields mint owner toAmt rest) + amount := by
  simp

end Examples.DischargePoC
