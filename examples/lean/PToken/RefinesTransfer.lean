/-
  Refinement bridge for the synthetic MinimalTransferAsm anchor.
  Per-program glue lives in Examples, not the core SVM lib.

  Two theorems: `_flat` uses a flat right-folded ** chain (what sl_block_iter
  needs — unfolding tokenAcctBalanceOf mid-chain produces a tree that breaks
  the bridge). `refines_TokenTransfer_minimal` is the tokenAcctBalance-wrapped
  user-facing corollary, discharged via a sepConj-assoc reshape over the flat form.
-/

import «MinimalTransferAsm»
import SVM.Solana.TokenAccountCodec
import SVM.SBPF.InstructionSpecs
import SVM.SBPF.Tactic.SL

namespace Examples.RefinesTokenTransfer

open SVM
open SVM.SBPF
open Memory
open SVM.Solana
open SVM.Solana.Abstract
open Examples.MinimalTransferAsm

/-! ## Flat byte-level refinement (proof workhorse) -/

theorem refines_TokenTransfer_minimal_flat
    (srcAddr dstAddr amount vR3Old : Nat)
    (tSrc tDst : Abstract.TokenAccount)
    (h_funds      : amount ≤ tSrc.amount)
    (h_noOverflow : tDst.amount + amount < 2 ^ 64)
    (h_srcBal     : tSrc.amount < 2 ^ 64)
    (h_dstBal     : tDst.amount < 2 ^ 64) :
    cuTripleWithinMem 6 0 0 6 minimalTransferCr
      ((.r1 ↦ᵣ srcAddr) ** (.r2 ↦ᵣ dstAddr) **
       (.r3 ↦ᵣ vR3Old) ** (.r4 ↦ᵣ amount) **
       (srcAddr + MINT_OFF ↦Pubkey tSrc.mint) **
       (srcAddr + OWNER_OFF ↦Pubkey tSrc.owner) **
       (srcAddr + AMOUNT_OFF ↦U64 tSrc.amount) **
       (srcAddr + REST_OFF ↦Bytes tSrc.rest) **
       (dstAddr + MINT_OFF ↦Pubkey tDst.mint) **
       (dstAddr + OWNER_OFF ↦Pubkey tDst.owner) **
       (dstAddr + AMOUNT_OFF ↦U64 tDst.amount) **
       (dstAddr + REST_OFF ↦Bytes tDst.rest))
      ((.r1 ↦ᵣ srcAddr) ** (.r2 ↦ᵣ dstAddr) **
       (.r3 ↦ᵣ tDst.amount + amount) ** (.r4 ↦ᵣ amount) **
       (srcAddr + MINT_OFF ↦Pubkey tSrc.mint) **
       (srcAddr + OWNER_OFF ↦Pubkey tSrc.owner) **
       (srcAddr + AMOUNT_OFF ↦U64 tSrc.amount - amount) **
       (srcAddr + REST_OFF ↦Bytes tSrc.rest) **
       (dstAddr + MINT_OFF ↦Pubkey tDst.mint) **
       (dstAddr + OWNER_OFF ↦Pubkey tDst.owner) **
       (dstAddr + AMOUNT_OFF ↦U64 tDst.amount + amount) **
       (dstAddr + REST_OFF ↦Bytes tDst.rest))
      (fun rt =>
        ((rt.containsRange (srcAddr + AMOUNT_OFF) 8 = true ∧
            rt.containsWritable (srcAddr + AMOUNT_OFF) 8 = true) ∧
          rt.containsRange (dstAddr + AMOUNT_OFF) 8 = true) ∧
        rt.containsWritable (dstAddr + AMOUNT_OFF) 8 = true) := by
  -- wrapSub/wrapAdd → Nat collapses.
  have h_amt_lt : amount < U64_MODULUS := by unfold U64_MODULUS; omega
  have h_srcBal' : tSrc.amount < U64_MODULUS := by unfold U64_MODULUS; exact h_srcBal
  have h_noOverflow' : tDst.amount + amount < U64_MODULUS := by
    unfold U64_MODULUS; exact h_noOverflow
  have h_wsub : wrapSub tSrc.amount amount = tSrc.amount - amount := by
    show (tSrc.amount + U64_MODULUS - amount % U64_MODULUS) % U64_MODULUS =
         tSrc.amount - amount
    rw [Nat.mod_eq_of_lt h_amt_lt]
    have h_rewrite : tSrc.amount + U64_MODULUS - amount =
                     (tSrc.amount - amount) + U64_MODULUS := by omega
    rw [h_rewrite, Nat.add_mod_right,
        Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) h_srcBal')]
  have h_wadd : wrapAdd tDst.amount amount = tDst.amount + amount := by
    show (tDst.amount + amount) % U64_MODULUS = tDst.amount + amount
    exact Nat.mod_eq_of_lt h_noOverflow'
  -- effectiveAddr → Nat for AMOUNT_OFF.
  have h_ea_src : effectiveAddr srcAddr amountOff = srcAddr + AMOUNT_OFF := by
    unfold effectiveAddr amountOff AMOUNT_OFF; omega
  have h_ea_dst : effectiveAddr dstAddr amountOff = dstAddr + AMOUNT_OFF := by
    unfold effectiveAddr amountOff AMOUNT_OFF; omega
  have h0 := ldxdw_spec .r3 .r1 amountOff vR3Old srcAddr tSrc.amount 0
              (by decide) h_srcBal
  have h1 := sub64_reg_spec .r3 .r4 tSrc.amount amount 1 (by decide)
  rw [h_wsub] at h1
  have h2 := stxdw_spec .r1 .r3 amountOff srcAddr
              (tSrc.amount - amount) tSrc.amount 2
  have h3 := ldxdw_spec .r3 .r2 amountOff (tSrc.amount - amount)
              dstAddr tDst.amount 3 (by decide) h_dstBal
  have h4 := add64_reg_spec .r3 .r4 tDst.amount amount 4 (by decide)
  rw [h_wadd] at h4
  have h5 := stxdw_spec .r2 .r3 amountOff dstAddr
              (tDst.amount + amount) tDst.amount 5
  rw [h_ea_src] at h0 h2
  rw [h_ea_dst] at h3 h5
  unfold minimalTransferCr
  sl_block_iter [h0, h1, h2, h3, h4, h5]

/-! ## Wrapped form — pre/post via `tokenAcctBalance` (sepConj-assoc bridge) -/

/-- Flatten (A**B**C**D)**E into A**B**C**D**E (three sepConj_assoc). -/
private theorem two_block_unfold_iff
    (sMint sOwn sAmt sRest dChain : Assertion) :
    ∀ h, ((sMint ** sOwn ** sAmt ** sRest) ** dChain) h ↔
         (sMint ** sOwn ** sAmt ** sRest ** dChain) h := by
  intro h
  refine Iff.trans (sepConj_assoc h) ?_
  refine sepConj_iff_congr_right sMint ?_ h
  intro h1
  refine Iff.trans (sepConj_assoc h1) ?_
  refine sepConj_iff_congr_right sOwn ?_ h1
  intro h2
  exact sepConj_assoc h2

/-- Thread an iff through a 4-atom register prefix. -/
private theorem reg_prefix_descend_iff
    (a1 a2 a3 a4 : Assertion) {L R : Assertion}
    (hLR : ∀ h, L h ↔ R h) :
    ∀ h, (a1 ** a2 ** a3 ** a4 ** L) h ↔ (a1 ** a2 ** a3 ** a4 ** R) h := by
  intro h
  refine sepConj_iff_congr_right a1 ?_ h
  intro h1
  refine sepConj_iff_congr_right a2 ?_ h1
  intro h2
  refine sepConj_iff_congr_right a3 ?_ h2
  intro h3
  exact sepConj_iff_congr_right a4 hLR h3

/-- Pointwise iff: tokenAcctBalance-wrapped ↔ flat, at both ATA sites. -/
private theorem wrap_iff
    (a1 a2 a3 a4 : Assertion)
    (srcAddr dstAddr : Nat)
    (mintSrc ownerSrc mintDst ownerDst : Pubkey)
    (amtSrc amtDst : Nat)
    (restSrc restDst : ByteArray) :
    ∀ h, (a1 ** a2 ** a3 ** a4 **
            tokenAcctBalance srcAddr mintSrc ownerSrc amtSrc restSrc **
            tokenAcctBalance dstAddr mintDst ownerDst amtDst restDst) h ↔
         (a1 ** a2 ** a3 ** a4 **
            (srcAddr + MINT_OFF ↦Pubkey mintSrc) **
            (srcAddr + OWNER_OFF ↦Pubkey ownerSrc) **
            (srcAddr + AMOUNT_OFF ↦U64 amtSrc) **
            (srcAddr + REST_OFF ↦Bytes restSrc) **
            (dstAddr + MINT_OFF ↦Pubkey mintDst) **
            (dstAddr + OWNER_OFF ↦Pubkey ownerDst) **
            (dstAddr + AMOUNT_OFF ↦U64 amtDst) **
            (dstAddr + REST_OFF ↦Bytes restDst)) h := by
  intro h
  show (a1 ** a2 ** a3 ** a4 **
          ((srcAddr + MINT_OFF ↦Pubkey mintSrc) **
           (srcAddr + OWNER_OFF ↦Pubkey ownerSrc) **
           (srcAddr + AMOUNT_OFF ↦U64 amtSrc) **
           (srcAddr + REST_OFF ↦Bytes restSrc)) **
          ((dstAddr + MINT_OFF ↦Pubkey mintDst) **
           (dstAddr + OWNER_OFF ↦Pubkey ownerDst) **
           (dstAddr + AMOUNT_OFF ↦U64 amtDst) **
           (dstAddr + REST_OFF ↦Bytes restDst))) h ↔ _
  exact reg_prefix_descend_iff a1 a2 a3 a4
    (two_block_unfold_iff _ _ _ _ _) h

/-! ## `refines_TokenTransfer_minimal` — user-facing wrapped corollary -/

theorem refines_TokenTransfer_minimal
    (srcAddr dstAddr amount vR3Old : Nat)
    (tSrc tDst : Abstract.TokenAccount)
    (h_funds      : amount ≤ tSrc.amount)
    (h_noOverflow : tDst.amount + amount < 2 ^ 64)
    (h_srcBal     : tSrc.amount < 2 ^ 64)
    (h_dstBal     : tDst.amount < 2 ^ 64) :
    cuTripleWithinMem 6 0 0 6 minimalTransferCr
      ((.r1 ↦ᵣ srcAddr) ** (.r2 ↦ᵣ dstAddr) **
       (.r3 ↦ᵣ vR3Old) ** (.r4 ↦ᵣ amount) **
       tokenAcctBalance srcAddr tSrc.mint tSrc.owner tSrc.amount tSrc.rest **
       tokenAcctBalance dstAddr tDst.mint tDst.owner tDst.amount tDst.rest)
      ((.r1 ↦ᵣ srcAddr) ** (.r2 ↦ᵣ dstAddr) **
       (.r3 ↦ᵣ tDst.amount + amount) ** (.r4 ↦ᵣ amount) **
       tokenAcctBalance srcAddr tSrc.mint tSrc.owner (tSrc.amount - amount) tSrc.rest **
       tokenAcctBalance dstAddr tDst.mint tDst.owner (tDst.amount + amount) tDst.rest)
      (fun rt =>
        ((rt.containsRange (srcAddr + AMOUNT_OFF) 8 = true ∧
            rt.containsWritable (srcAddr + AMOUNT_OFF) 8 = true) ∧
          rt.containsRange (dstAddr + AMOUNT_OFF) 8 = true) ∧
        rt.containsWritable (dstAddr + AMOUNT_OFF) 8 = true) := by
  have h_flat := refines_TokenTransfer_minimal_flat srcAddr dstAddr amount vR3Old
                   tSrc tDst h_funds h_noOverflow h_srcBal h_dstBal
  refine cuTripleWithinMem_reshape_pre ?_
           (cuTripleWithinMem_reshape_post ?_ h_flat)
  · intro h
    exact (wrap_iff (.r1 ↦ᵣ srcAddr) (.r2 ↦ᵣ dstAddr)
             (.r3 ↦ᵣ vR3Old) (.r4 ↦ᵣ amount)
             srcAddr dstAddr
             tSrc.mint tSrc.owner tDst.mint tDst.owner
             tSrc.amount tDst.amount tSrc.rest tDst.rest h).symm
  · intro h
    exact (wrap_iff (.r1 ↦ᵣ srcAddr) (.r2 ↦ᵣ dstAddr)
             (.r3 ↦ᵣ tDst.amount + amount) (.r4 ↦ᵣ amount)
             srcAddr dstAddr
             tSrc.mint tSrc.owner tDst.mint tDst.owner
             (tSrc.amount - amount) (tDst.amount + amount) tSrc.rest tDst.rest h).symm

end Examples.RefinesTokenTransfer
