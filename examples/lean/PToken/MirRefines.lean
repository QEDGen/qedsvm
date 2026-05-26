/-
  The synthetic anchor `MinimalTransferAsm` refines the MIR intrinsic
  `MirStmt.tokenTransfer`.

  First proven instance of the
  `Abstract.TokenTransferRefinement` structure from
  `SVM/Solana/Abstract/Refinement.lean`. Bundles:

    1. The already-proven abstract Hoare triple
       (`Abstract.tokenTransfer_spec`).
    2. The synthetic-anchor bytecode triple in `tokenAcctBalance`-
       wrapped form (`p_token_transfer_balance_spec_minimal_wrapped`).

  The asm-side discharge uses two `simp` rewrites to convert
  `tokenAcctBalanceOf` (record-keyed) into `tokenAcctBalance`
  (field-keyed), the form the wrapped synthetic spec ships in. The
  record-keyed form is the natural shape for the MIR refinement;
  the wrapped synthetic spec was stated with explicit fields because
  it predates the codec lifting.

  This file closes the spec-to-asm loop for the synthetic anchor.
  The pinocchio-side wrapped version (the corresponding theorem for
  real p-token Transfer bytecode) is deferred — see issue tracker
  for the framing + SL-reshape blockers in `BalanceSpec.lean`'s
  `p_token_transfer_balance_spec_pinocchio` docstring.
-/

import SVM.Solana
import PToken.BalanceSpec

namespace Examples.MirRefines

open SVM
open SVM.SBPF
open SVM.Solana
open SVM.Solana.Abstract
open Examples.PTokenTransferBalanceSpec

/-- The synthetic `MinimalTransferAsm` realizes the MIR intrinsic
    `tokenTransfer src dst amount`.

    Parameters split into three groups:
      * Abstract: `src`, `dst` (MIR Pubkey keys), `tSrc`, `tDst`
        (token records), `amount`.
      * Asm-side layout: `srcAddr`, `dstAddr` (byte addresses where
        the synthetic anchor expects to find the two accounts) and
        `vR3Old` (the arbitrary value `r3` carries at entry).
      * Preconditions: enough funds, no destination overflow, both
        balances fit in u64 (the asm-side `wrapSub`/`wrapAdd` collapse
        to plain Nat sub/add under these conditions). -/
theorem MinimalTransferAsm_refines_tokenTransfer
    (src dst : SVM.Pubkey) (tSrc tDst : Abstract.TokenAccount)
    (amount : Nat)
    (srcAddr dstAddr vR3Old : Nat)
    (h_funds      : amount ≤ tSrc.amount)
    (h_noOverflow : tDst.amount + amount < 2 ^ 64)
    (h_srcBal     : tSrc.amount < 2 ^ 64)
    (h_dstBal     : tDst.amount < 2 ^ 64) :
    Abstract.TokenTransferRefinement src dst tSrc tDst amount
      Examples.MinimalTransferAsm.minimalTransferCr 6 0 0 6
      (fun rt =>
        ((rt.containsRange (srcAddr + AMOUNT_OFF) 8 = true ∧
            rt.containsWritable (srcAddr + AMOUNT_OFF) 8 = true) ∧
          rt.containsRange (dstAddr + AMOUNT_OFF) 8 = true) ∧
        rt.containsWritable (dstAddr + AMOUNT_OFF) 8 = true)
      srcAddr dstAddr
      ((.r1 ↦ᵣ srcAddr) ** (.r2 ↦ᵣ dstAddr) **
       (.r3 ↦ᵣ vR3Old) ** (.r4 ↦ᵣ amount))
      ((.r1 ↦ᵣ srcAddr) ** (.r2 ↦ᵣ dstAddr) **
       (.r3 ↦ᵣ tDst.amount + amount) ** (.r4 ↦ᵣ amount)) := by
  refine Abstract.tokenTransferRefinement_intro
    src dst tSrc tDst amount h_funds h_noOverflow
    _ _ _ _ _ _ _ _ _ _ ?_
  -- AsmRefinesTokenTransfer obligation. Unfold to a cuTripleWithinMem
  -- goal, then rewrite the record-keyed atoms to the field-keyed form
  -- the synthetic wrapped spec ships in.
  unfold Abstract.AsmRefinesTokenTransfer
  simp only [tokenAcctBalanceOf_eq,
             Abstract.TokenAccount.withAmount_mint,
             Abstract.TokenAccount.withAmount_owner,
             Abstract.TokenAccount.withAmount_amount,
             Abstract.TokenAccount.withAmount_rest]
  -- The synthetic wrapped spec ships with `regs ** balA ** balB` as a
  -- right-folded 6-atom chain. `AsmRefinesTokenTransfer` brackets it
  -- as `setupPre ** balA ** balB` with `setupPre := regs` (a left-
  -- grouped 4-atom chain). Bridge via 3 sepConj_assoc applications.
  refine cuTripleWithinMem_reshape_pre ?_
           (cuTripleWithinMem_reshape_post ?_
             (p_token_transfer_balance_spec_minimal_wrapped
               srcAddr dstAddr amount tSrc.amount tDst.amount vR3Old
               tSrc.mint tDst.mint tSrc.owner tDst.owner tSrc.rest tDst.rest
               h_funds h_noOverflow h_srcBal h_dstBal))
  · -- pre iff: (r1**r2**r3**r4**balA**balB) ↔ ((r1**r2**r3**r4)**balA**balB)
    intro h
    refine Iff.symm ?_
    refine Iff.trans (sepConj_assoc h) ?_
    refine sepConj_iff_congr_right _ ?_ h
    intro h1
    refine Iff.trans (sepConj_assoc h1) ?_
    refine sepConj_iff_congr_right _ ?_ h1
    intro h2
    exact sepConj_assoc h2
  · -- post iff: same shape as pre
    intro h
    refine Iff.symm ?_
    refine Iff.trans (sepConj_assoc h) ?_
    refine sepConj_iff_congr_right _ ?_ h
    intro h1
    refine Iff.trans (sepConj_assoc h1) ?_
    refine sepConj_iff_congr_right _ ?_ h1
    intro h2
    exact sepConj_assoc h2

end Examples.MirRefines
