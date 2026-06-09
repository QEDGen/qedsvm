/-
  Refinement obligations — the asm-side shape a compiled program must take
  to be considered a refinement of an account mutation.

  For each account mutation this file declares an asm-side obligation
  predicate (`AsmRefines…`): the shape an asm-level `cuTripleWithinMem` must
  take. A per-program lift (emitted by qedlift's refinement codegen)
  discharges the predicate, and the discharge route then reads the mutated
  field out of the decoded field list via `qedsvm_discharge`
  (`SVM/SBPF/Tactic/Discharge.lean`) — the convergence keystones
  (`SVM/Solana/TokenFieldCodec.lean`, `MintFieldCodec.lean`) reshape the
  bespoke `tokenAcctBalanceOf` / `mintSupplyOf` atoms into the layout-general
  `codecCoarse` field list these obligations carry.

  The SPL token/mint/counter predicates (`AsmRefinesToken*`,
  `AsmRefinesCounterIncrement`) are record-keyed for historical reasons and
  remain as the bridging input until qedgen consumes the discharge form
  directly (QEDGen/solana-skills#86); `AsmRefinesFieldUpdate` is the
  layout-general form new lifts target.

  Note on the framing: an asm-side proof produces a triple over byte
  addresses (`srcAddr dstAddr : Nat`). The bridge does NOT establish that a
  given layout map `Pubkey → Nat` is correct — that's a per-program
  obligation handled by the layout's discharge in concrete proofs.
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

/-! ## tokenTransfer

A bytecode-level refinement of a token transfer is an asm Hoare triple in
`tokenAcctBalance`-wrapped form whose pre/post mirror the balance shift: the
source account's `amount` field decreases by `amount`, the destination's
increases by `amount`. -/

/-- Asm-side obligation for a `tokenTransfer` refinement.

    A `cuTripleWithinMem` over the program region `[entry..exit]` of code
    `cr` whose pre-state owns an opaque `setupPre` frame followed by two
    `tokenAcctBalanceOf` atoms (source at byte address `srcAddr`, destination
    at `dstAddr`); whose post-state has the same atoms with the `withAmount`
    shift applied; and whose memory obligations (`rr`) are unconstrained.

    Setup atoms (typically register bindings) come FIRST in the chain to
    match the natural right-folded shape of per-instruction asm specs. -/
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

/-! ## tokenMintTo

A bytecode-level refinement of `tokenMintTo` is an asm Hoare triple whose
pre/post own a `mintSupplyOf` atom (the mint, supply mutated) and a
`tokenAcctBalanceOf` atom (the destination, amount mutated), each shifted up
by `amount`. -/

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

/-! ## counterIncrement

A bytecode-level refinement of `counterIncrement` is an asm Hoare triple
whose pre/post own a single `counterValOf` atom (the counter, value
mutated), shifted up by one. The first NON-token refinement: no mint /
owner / amount, no `rest` blob, no codec aggregation (a single `u64` field
is coarse = fine). It validates that the refinement bridge is
layout-general. -/

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

/-! ## fieldUpdate — layout-general NON-token codec refinement

The asm obligation for a single-field update on an account described by a
`FieldVal` layout (the Codama IDL's account struct). `preFields` and
`postFields` differ only at the mutated field; the untouched fields flow
through. Unlike the SPL `AsmRefinesToken*` predicates this is NOT tied to
a fixed record — the layout is a parameter, so ONE predicate covers any
account shape. The realizing proof reshapes both coarse codecs to their
fine (scattered) form via `account_agg`/`codecCoarse_eq_fine` and frames
the untouched fine atoms; for a multi-field non-token account (e.g.
`{owner:Pubkey@0, total:u64@32, bump:u8@40}`) it mechanically frames the
pubkey + byte fields and owns the updated `u64`. This is the layout-driven
codec aggregation, emitted off the token domain. -/

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
