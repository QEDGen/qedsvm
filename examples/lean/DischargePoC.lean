/-
  Discharge PoC (#24): proves qedgen's parametric ensures_axiom against pinned
  bytecode instead of axiomatising it. State = the FieldVal list from the lift
  (after account_agg reshape); from_balance = u64FieldAt. No Mem bridge needed.
-/

import SVM.Solana.Abstract.Refinement
import Generated.VaultRefinement
import SVM.SBPF.Tactic.Discharge

namespace Examples.DischargePoC

open SVM SVM.SBPF SVM.SBPF.Memory SVM.Pubkey SVM.Solana SVM.Solana.Abstract

-- u64FieldAt, u64FieldAt_found, and qedsvm_discharge live in SVM.SBPF.Tactic.Discharge.

/-! ## Vault: `total post = total pre + 1`, discharged from the real lift -/
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

/-- End-to-end: real vault lift flows through discharge to qedgen's `total post = total pre + 1`. -/
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

/-! ## Token arms

The token arms need no reshape PoC anymore: qedlift emits their
`AsmRefinesFieldUpdates` obligation (one `(base, preFields, postFields)`
triple per account) directly off the lift, with per-account `ensures_<role>`
accessor corollaries discharged the same way as `vault_total_discharged`
above — see `examples/lean/PToken/TransferRefinement.lean` (#25). -/

end Examples.DischargePoC
