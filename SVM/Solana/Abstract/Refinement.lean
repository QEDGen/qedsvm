/-
  Refinement obligations — the asm-side shape a compiled program must take to
  refine an account mutation.

  Each `AsmRefines…` declares the shape of an asm `cuTripleWithinMem`. A
  per-program lift discharges it via `qedsvm_discharge`
  (`SVM/SBPF/Tactic/Discharge.lean`).

  All account codecs are layout-general `codecCoarse` field lists (the layout
  a Codama/Anchor IDL describes): `AsmRefinesFieldUpdate` for a single
  account, `AsmRefinesFieldUpdates` for N accounts (the SPL token/mint arms).
  The record-keyed MIR-pilot predicates (`AsmRefinesToken*`) are retired
  (#25); `AsmRefinesCounterIncrement` remains as the minimal record-keyed
  bridge the counter example exercises.

  Framing: an asm proof produces a triple over byte addresses. The bridge does
  NOT establish a layout map `Pubkey → Nat` is correct — that's a per-program
  obligation discharged in concrete proofs.
-/

import SVM.Solana.CounterAccountCodec
import SVM.SBPF.AccountCodec
import SVM.SBPF.CPSSpec

namespace SVM.Solana.Abstract

open SVM.SBPF
open SVM.Solana
open SVM.Pubkey

/-! ## SCOPE of the `AsmRefines*` obligations (H10)

  Each obligation is a PARTIAL-CORRECTNESS `cuTripleWithinMem` over the HAPPY
  PATH, framed over a fixed small account set; it states exactly the field
  SHIFT and nothing more. Deliberately NOT claimed:

  * failure-path behaviour (insufficient funds, non-signer, frozen, wrong mint,
    delegate rules) — not proven to error-and-preserve;
  * a global supply invariant over ALL token accounts — only framed atoms are
    constrained; `setupPre`/`setupPost`/`rr` are opaque;
  * total correctness — post asserts `exitCode = none` within the CU window, not
    whole-transaction termination;
  * any account-tail field beyond the mutated one (L11).

  The frame rule keeps "untouched framed cells preserved" sound only inside the
  frame. Read the names as "the field shift refines", not "the program is
  correct". -/

/-! ## counterIncrement: asm triple shifting a single `counterValOf` atom up by
one. First NON-token refinement (no codec aggregation: one `u64` is coarse =
fine), validating the bridge is layout-general. -/

/-- Asm-side obligation for a `counterIncrement` refinement. The delta is
    the constant `1`, so there is no `amount` parameter. -/
def AsmRefinesCounterIncrement
    (cr : CodeReq) (nSteps nCu entry exit : Nat)
    (rr : Memory.RegionTable → Prop)
    (addr : Nat) (c : CounterAccount)
    (setupPre setupPost : Assertion) : Prop :=
  cuTripleWithinMem nSteps nCu entry exit cr
    (setupPre ** counterValOf addr c)
    (setupPost ** counterValOf addr (c.withCounter (c.counter + 1)))
    rr

/-! ## fieldUpdate — layout-general single-account codec refinement.

Single-field update on an account given by a `FieldVal` layout (Codama IDL
struct). `preFields`/`postFields` differ only at the mutated field; the layout
is a parameter, so ONE predicate covers any account shape. The realizing proof
reshapes both coarse codecs to fine (scattered) form via
`account_agg`/`codecCoarse_eq_fine` and frames the untouched fine atoms. -/

def AsmRefinesFieldUpdate
    (cr : CodeReq) (nSteps nCu entry exit : Nat)
    (rr : Memory.RegionTable → Prop)
    (base : Nat) (preFields postFields : List (Nat × FieldVal))
    (setupPre setupPost : Assertion) : Prop :=
  cuTripleWithinMem nSteps nCu entry exit cr
    (setupPre ** codecCoarse base preFields)
    (setupPost ** codecCoarse base postFields)
    rr

/-! ## fieldUpdates — the N-account generalization (#25).

A multi-account instruction (Transfer debits one account and credits
another; MintTo/Burn shift a mint's supply and a token account's amount
together) states one `(base, preFields, postFields)` transition per account,
`**`-folded across the list in both pre and post. This replaces the bespoke
record-keyed `AsmRefinesToken*` predicates: a token obligation is now the
same layout-general field-list obligation a vault or counter lift targets,
just over more than one account. The single-account `AsmRefinesFieldUpdate`
stays as the form qedgen's discharge adapter consumes. -/

/-- Per-account codec transition: base address, pre and post field lists. -/
abbrev AccountFields := Nat × List (Nat × FieldVal) × List (Nat × FieldVal)

/-- `**`-fold of the accounts' pre-state coarse codecs. -/
def codecsPre : List AccountFields → Assertion
  | [] => emp
  | (base, pre, _) :: rest => codecCoarse base pre ** codecsPre rest

/-- `**`-fold of the accounts' post-state coarse codecs. -/
def codecsPost : List AccountFields → Assertion
  | [] => emp
  | (base, _, post) :: rest => codecCoarse base post ** codecsPost rest

/-- Layout-general N-account codec refinement: every account's field list
    goes pre→post simultaneously within one `cuTripleWithinMem`. -/
def AsmRefinesFieldUpdates
    (cr : CodeReq) (nSteps nCu entry exit : Nat)
    (rr : Memory.RegionTable → Prop)
    (accts : List AccountFields)
    (setupPre setupPost : Assertion) : Prop :=
  cuTripleWithinMem nSteps nCu entry exit cr
    (setupPre ** codecsPre accts)
    (setupPost ** codecsPost accts)
    rr

/-- Sanity: on a singleton list the N-account form is exactly the
    single-account `AsmRefinesFieldUpdate`. -/
theorem asmRefinesFieldUpdates_singleton
    (cr : CodeReq) (nSteps nCu entry exit : Nat)
    (rr : Memory.RegionTable → Prop)
    (base : Nat) (preFields postFields : List (Nat × FieldVal))
    (setupPre setupPost : Assertion) :
    AsmRefinesFieldUpdates cr nSteps nCu entry exit rr
        [(base, preFields, postFields)] setupPre setupPost ↔
      AsmRefinesFieldUpdate cr nSteps nCu entry exit rr
        base preFields postFields setupPre setupPost := by
  simp [AsmRefinesFieldUpdates, AsmRefinesFieldUpdate, codecsPre, codecsPost,
        sepConj_emp_right_eq]

end SVM.Solana.Abstract
