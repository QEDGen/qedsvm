/-
  Refinement obligations — the asm-side shape a compiled program must take to
  refine an account mutation.

  Each `AsmRefines…` declares the shape of an asm `cuTripleWithinMem`. A
  per-program lift discharges it via `qedsvm_discharge`
  (`SVM/SBPF/Tactic/Discharge.lean`); the convergence keystones
  (`TokenFieldCodec.lean`, `MintFieldCodec.lean`) reshape the bespoke
  `tokenAcctBalanceOf` / `mintSupplyOf` atoms into the layout-general
  `codecCoarse` field list these obligations carry.

  The record-keyed SPL predicates (`AsmRefinesToken*`,
  `AsmRefinesCounterIncrement`) remain the bridging input until qedgen consumes
  the discharge form directly (QEDGen/solana-skills#86);
  `AsmRefinesFieldUpdate` is the layout-general form new lifts target.

  Framing: an asm proof produces a triple over byte addresses. The bridge does
  NOT establish a layout map `Pubkey → Nat` is correct — that's a per-program
  obligation discharged in concrete proofs.
-/

import SVM.Solana.TokenAccountCodec
import SVM.Solana.MintAccountCodec
import SVM.Solana.CounterAccountCodec
import SVM.SBPF.AccountCodec
import SVM.SBPF.CPSSpec

namespace SVM.Solana.Abstract

open SVM.SBPF
open SVM.Solana
open SVM.Pubkey

/-! ## SCOPE of the `AsmRefines*` obligations (H10)

  Each `AsmRefines{TokenTransfer,TokenMintTo,TokenBurn}` is a PARTIAL-
  CORRECTNESS `cuTripleWithinMem` over the HAPPY PATH, framed over a fixed
  small account set; it states exactly the balance/supply SHIFT and nothing
  more. Deliberately NOT claimed:

  * failure-path behaviour (insufficient funds, non-signer, frozen, wrong mint,
    delegate rules) — not proven to error-and-preserve;
  * a global supply invariant over ALL token accounts — only framed atoms are
    constrained; `setupPre`/`setupPost`/`rr` are opaque;
  * total correctness — post asserts `exitCode = none` within the CU window, not
    whole-transaction termination;
  * any 93-byte token-tail field beyond `amount`/`supply` (L11).

  The frame rule keeps "untouched framed cells preserved" sound only inside the
  frame. Read the names as "the balance shift refines", not "the program is
  correct". -/

/-! ## tokenTransfer: asm triple whose pre/post mirror the balance shift (src
`amount` down, dst `amount` up). -/

/-- Asm-side obligation for a `tokenTransfer` refinement: a `cuTripleWithinMem`
    over `[entry..exit]` of `cr` whose pre owns an opaque `setupPre` frame then
    two `tokenAcctBalanceOf` atoms (src@`srcAddr`, dst@`dstAddr`), whose post
    applies the `withAmount` shift, with `rr` unconstrained.

    Setup atoms come FIRST to match the right-folded shape of per-instruction
    asm specs. -/
def AsmRefinesTokenTransfer
    (cr : CodeReq) (nSteps nCu entry exit : Nat)
    (rr : Memory.RegionTable → Prop)
    (srcAddr dstAddr : Nat)
    (tSrc tDst : TokenAccount) (amount : Nat)
    (setupPre setupPost : Assertion) : Prop :=
  cuTripleWithinMem nSteps nCu entry exit cr
    (setupPre **
     tokenAcctBalanceOf srcAddr tSrc **
     tokenAcctBalanceOf dstAddr tDst)
    (setupPost **
     tokenAcctBalanceOf srcAddr (tSrc.withAmount (tSrc.amount - amount)) **
     tokenAcctBalanceOf dstAddr (tDst.withAmount (tDst.amount + amount)))
    rr

/-! ## tokenMintTo: asm triple shifting both the `mintSupplyOf` and dst
`tokenAcctBalanceOf` atoms up by `amount`. -/

/-- Asm-side obligation for a `tokenMintTo` refinement. -/
def AsmRefinesTokenMintTo
    (cr : CodeReq) (nSteps nCu entry exit : Nat)
    (rr : Memory.RegionTable → Prop)
    (mintAddr destAddr : Nat)
    (m : Mint) (tDest : TokenAccount) (amount : Nat)
    (setupPre setupPost : Assertion) : Prop :=
  cuTripleWithinMem nSteps nCu entry exit cr
    (setupPre **
     mintSupplyOf mintAddr m **
     tokenAcctBalanceOf destAddr tDest)
    (setupPost **
     mintSupplyOf mintAddr (m.withSupply (m.supply + amount)) **
     tokenAcctBalanceOf destAddr (tDest.withAmount (tDest.amount + amount)))
    rr

/-! ## tokenBurn: src `amount` and mint `supply` each decrease by `amount`. -/

/-- Asm-side obligation for a `tokenBurn` refinement. -/
def AsmRefinesTokenBurn
    (cr : CodeReq) (nSteps nCu entry exit : Nat)
    (rr : Memory.RegionTable → Prop)
    (accountAddr mintAddr : Nat)
    (tAcc : TokenAccount) (m : Mint) (amount : Nat)
    (setupPre setupPost : Assertion) : Prop :=
  cuTripleWithinMem nSteps nCu entry exit cr
    (setupPre **
     tokenAcctBalanceOf accountAddr tAcc **
     mintSupplyOf mintAddr m)
    (setupPost **
     tokenAcctBalanceOf accountAddr (tAcc.withAmount (tAcc.amount - amount)) **
     mintSupplyOf mintAddr (m.withSupply (m.supply - amount)))
    rr

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

/-! ## fieldUpdate — layout-general NON-token codec refinement.

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

end SVM.Solana.Abstract
