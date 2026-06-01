/-
  Refinement bridge — bytecode-level Hoare triples ↔ abstract MIR triples.

  This is the canonical library qedsvm consumers cite to claim
  "this compiled program refines this MIR intrinsic." For each MIR
  statement constructor in `SVM/Solana/Mir.lean`, this file declares:

    1. An asm-side obligation predicate
       (`AsmRefines<Intrinsic>`) — the shape an asm-level
       `cuTripleWithinMem` must take to be considered a refinement.

    2. A combined refinement constructor that bundles the (already
       proven, parametric) abstract triple from
       `SVM/Solana/Abstract/Triples.lean` with the per-program asm
       obligation. Per-program proofs (e.g.
       `Examples.RefinesTokenTransfer.refines_TokenTransfer_minimal`)
       supply the asm obligation; this file does the bookkeeping.

  Scope today: `tokenTransfer` only — the Direction-A MIR pilot
  intrinsic. Each new intrinsic added to `Mir.lean` should land an
  obligation predicate and a constructor here.

  Note on the framing: an asm-side proof produces a triple over byte
  addresses (`srcAddr dstAddr : Nat`); the abstract MIR proof works
  over `Pubkey` keys. The bridge does NOT establish that a given
  layout map `Pubkey → Nat` is correct — that's a per-program
  obligation handled by the layout's discharge in concrete proofs.
  This file just packages the two halves so consumers can quote a
  single combined theorem.
-/

import SVM.Solana.Mir
import SVM.Solana.Abstract.Triples
import SVM.Solana.TokenAccountCodec
import SVM.Solana.MintAccountCodec
import SVM.SBPF.CPSSpec

namespace SVM.Solana.Abstract

open SVM.SBPF
open SVM.Solana
open SVM.Pubkey

/-! ## tokenTransfer

The MIR intrinsic `MirStmt.tokenTransfer src dst amount` errors on a
missing account, self-transfer (`src = dst`), insufficient source
funds, or u64 overflow on the destination. The abstract Hoare triple
(`tokenTransfer_spec`) asserts that, given enough funds and no
overflow, the source account's `amount` field decreases by `amount`
and the destination's increases by `amount`.

A bytecode-level refinement of this intrinsic is an asm Hoare triple
in `tokenAcctBalance`-wrapped form whose pre/post mirror the
abstract balance shift.
-/

/-- Asm-side obligation for a `tokenTransfer` refinement.

    A `cuTripleWithinMem` over the program region `[entry..exit]` of
    code `cr` whose pre-state owns an opaque `setupPre` frame followed
    by two `tokenAcctBalanceOf` atoms (source at byte address `srcAddr`,
    destination at `dstAddr`); whose post-state has the same atoms with
    the abstract `withAmount` shift applied; and whose memory
    obligations (`rr`) are unconstrained.

    Setup atoms (typically register bindings) come FIRST in the chain
    to match the natural right-folded shape of per-instruction asm
    specs — those write `r1 ↦ᵣ … ** r2 ↦ᵣ … ** memory_atoms`. -/
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

/-- Refinement pair for a `tokenTransfer` intrinsic. Witnesses
    simultaneous validity of (1) the abstract Hoare triple over the
    decoded heap and (2) the bytecode-level obligation in
    wrapped form.

    The two halves are independent — the abstract triple is already
    proven by `tokenTransfer_spec`; this structure exists so per-
    program proofs can quote a single combined claim. -/
structure TokenTransferRefinement
    (src dst : Pubkey)
    (tSrc tDst : TokenAccount) (amount : Nat)
    (cr : CodeReq) (nSteps nCu entry exit : Nat)
    (rr : Memory.RegionTable → Prop) (srcAddr dstAddr : Nat)
    (setupPre setupPost : Assertion) : Prop where
  /-- Abstract MIR triple — the spec the asm must refine. -/
  abs_spec : absTriple [.tokenTransfer src dst amount]
               ((src ↦ₐ tSrc) ** (dst ↦ₐ tDst))
               ((src ↦ₐ tSrc.withAmount (tSrc.amount - amount)) **
                (dst ↦ₐ tDst.withAmount (tDst.amount + amount)))
  /-- Asm-side obligation — the bytecode realizes the abstract effect. -/
  asm_spec : AsmRefinesTokenTransfer cr nSteps nCu entry exit rr
              srcAddr dstAddr tSrc tDst amount setupPre setupPost

/-- Constructor: given the asm-side obligation and the abstract
    preconditions, package both halves into a `TokenTransferRefinement`.
    The abstract half is discharged via the already-proven
    `tokenTransfer_spec`. -/
theorem tokenTransferRefinement_intro
    (src dst : Pubkey)
    (tSrc tDst : TokenAccount) (amount : Nat)
    (h_funds : amount ≤ tSrc.amount)
    (h_noOverflow : tDst.amount + amount < 2 ^ 64)
    (cr : CodeReq) (nSteps nCu entry exit : Nat)
    (rr : Memory.RegionTable → Prop) (srcAddr dstAddr : Nat)
    (setupPre setupPost : Assertion)
    (h_asm : AsmRefinesTokenTransfer cr nSteps nCu entry exit rr
              srcAddr dstAddr tSrc tDst amount setupPre setupPost) :
    TokenTransferRefinement src dst tSrc tDst amount
      cr nSteps nCu entry exit rr srcAddr dstAddr setupPre setupPost where
  abs_spec := tokenTransfer_spec src dst tSrc tDst amount h_funds h_noOverflow
  asm_spec := h_asm

/-! ## tokenMintTo

A bytecode-level refinement of `tokenMintTo` is an asm Hoare triple
whose pre/post own a `mintSupplyOf` atom (the mint, supply mutated) and
a `tokenAcctBalanceOf` atom (the destination, amount mutated), each
shifted up by `amount`. -/

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

/-- Refinement pair for a `tokenMintTo` intrinsic. -/
structure TokenMintToRefinement
    (mint dest : Pubkey)
    (m : Mint) (tDest : TokenAccount) (amount : Nat)
    (cr : CodeReq) (nSteps nCu entry exit : Nat)
    (rr : Memory.RegionTable → Prop) (mintAddr destAddr : Nat)
    (setupPre setupPost : Assertion) : Prop where
  abs_spec : absTriple [.tokenMintTo mint dest amount]
               ((mint ↦ₘ m) ** (dest ↦ₐ tDest))
               ((mint ↦ₘ m.withSupply (m.supply + amount)) **
                (dest ↦ₐ tDest.withAmount (tDest.amount + amount)))
  asm_spec : AsmRefinesTokenMintTo cr nSteps nCu entry exit rr
              mintAddr destAddr m tDest amount setupPre setupPost

/-- Constructor: package both halves into a `TokenMintToRefinement`.
    The abstract half is discharged via `tokenMintTo_spec`. -/
theorem tokenMintToRefinement_intro
    (mint dest : Pubkey)
    (m : Mint) (tDest : TokenAccount) (amount : Nat)
    (h_noOvSupply : m.supply + amount < 2 ^ 64)
    (h_noOvDest   : tDest.amount + amount < 2 ^ 64)
    (cr : CodeReq) (nSteps nCu entry exit : Nat)
    (rr : Memory.RegionTable → Prop) (mintAddr destAddr : Nat)
    (setupPre setupPost : Assertion)
    (h_asm : AsmRefinesTokenMintTo cr nSteps nCu entry exit rr
              mintAddr destAddr m tDest amount setupPre setupPost) :
    TokenMintToRefinement mint dest m tDest amount
      cr nSteps nCu entry exit rr mintAddr destAddr setupPre setupPost where
  abs_spec := tokenMintTo_spec mint dest m tDest amount h_noOvSupply h_noOvDest
  asm_spec := h_asm

/-! ## tokenBurn

A bytecode-level refinement of `tokenBurn`: the source token account's
`amount` and the mint's `supply` each decrease by `amount`. -/

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

/-- Refinement pair for a `tokenBurn` intrinsic. -/
structure TokenBurnRefinement
    (account mint : Pubkey)
    (tAcc : TokenAccount) (m : Mint) (amount : Nat)
    (cr : CodeReq) (nSteps nCu entry exit : Nat)
    (rr : Memory.RegionTable → Prop) (accountAddr mintAddr : Nat)
    (setupPre setupPost : Assertion) : Prop where
  abs_spec : absTriple [.tokenBurn account mint amount]
               ((account ↦ₐ tAcc) ** (mint ↦ₘ m))
               ((account ↦ₐ tAcc.withAmount (tAcc.amount - amount)) **
                (mint ↦ₘ m.withSupply (m.supply - amount)))
  asm_spec : AsmRefinesTokenBurn cr nSteps nCu entry exit rr
              accountAddr mintAddr tAcc m amount setupPre setupPost

/-- Constructor: package both halves into a `TokenBurnRefinement`.
    The abstract half is discharged via `tokenBurn_spec`. -/
theorem tokenBurnRefinement_intro
    (account mint : Pubkey)
    (tAcc : TokenAccount) (m : Mint) (amount : Nat)
    (h_funds : amount ≤ tAcc.amount)
    (cr : CodeReq) (nSteps nCu entry exit : Nat)
    (rr : Memory.RegionTable → Prop) (accountAddr mintAddr : Nat)
    (setupPre setupPost : Assertion)
    (h_asm : AsmRefinesTokenBurn cr nSteps nCu entry exit rr
              accountAddr mintAddr tAcc m amount setupPre setupPost) :
    TokenBurnRefinement account mint tAcc m amount
      cr nSteps nCu entry exit rr accountAddr mintAddr setupPre setupPost where
  abs_spec := tokenBurn_spec account mint tAcc m amount h_funds
  asm_spec := h_asm

end SVM.Solana.Abstract
