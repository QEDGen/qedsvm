/-
  Refinement bridge — abstract `TokenAccount`-level reasoning ↔ asm
  byte-level reasoning, for the synthetic anchor `MinimalTransferAsm`.

  Lives in the Examples lib (not the core SVM lib) because it ties a
  specific asm program to the abstract layer. The SVM lib provides the
  generic infrastructure (AbstractState / MIR / Triples / codec
  bridge); the actual asm-to-abstract correspondence is per-program
  glue and belongs alongside the program.

  This bridge does NOT yet quantify over an arbitrary layout function
  `Pubkey → Option Nat`. For the two-account pilot we take `srcAddr`
  and `dstAddr` as direct parameters. A general `LayoutMap`-typed φ
  comes when a second intrinsic forces it.

  ## Why two theorems

  `refines_TokenTransfer_minimal_flat` is the proof workhorse — it
  states pre/post with **flat** byte-level atoms (one big right-folded
  `**` chain) because that's the shape `sl_block_iter` consumes. The
  per-instruction specs naturally produce flat chains; unfolding
  `tokenAcctBalanceOf` mid-chain produces a *tree* (4 inner atoms per
  account, wrapped at the outer ** boundary), which breaks the
  bridging step.

  `refines_TokenTransfer_minimal` is the user-facing form — pre/post
  stated using `tokenAcctBalanceOf`. The body is a thin sepConj-assoc
  reshape over the flat theorem. This is the theorem Task 9 cites.
-/

import «MinimalTransferAsm»
import SVM.Solana.TokenAccountCodec
import SVM.SBPF.InstructionSpecs
import SVM.SBPF.Tactic.SL

namespace Examples.RefinesTokenTransfer

open SVM.SBPF
open Memory
open SVM.Solana
open SVM.Solana.Abstract
open Examples.MinimalTransferAsm

/-! ## Flat byte-level refinement

The `tokenAcctBalanceOf`-shaped predicates from the user-facing
theorem are spelled out as their 4 per-field SL atoms each (pubkey
mint, pubkey owner, u64 amount, opaque rest). This puts everything
into one flat right-folded chain that `sl_block_iter` can permute and
frame uniformly. -/

theorem refines_TokenTransfer_minimal_flat
    (srcAddr dstAddr amount vR3Old : Nat)
    (tSrc tDst : Abstract.TokenAccount)
    (h_funds      : amount ≤ tSrc.amount)
    (h_noOverflow : tDst.amount + amount < 2 ^ 64)
    (h_srcBal     : tSrc.amount < 2 ^ 64)
    (h_dstBal     : tDst.amount < 2 ^ 64) :
    cuTripleWithinMem 6 0 6 minimalTransferCr
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
  -- Wrap → Nat collapses.
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
  -- Bridge `effectiveAddr a (n : Int)` ↔ `a + n` for the AMOUNT_OFF case.
  have h_ea_src : effectiveAddr srcAddr amountOff = srcAddr + AMOUNT_OFF := by
    unfold effectiveAddr amountOff AMOUNT_OFF; omega
  have h_ea_dst : effectiveAddr dstAddr amountOff = dstAddr + AMOUNT_OFF := by
    unfold effectiveAddr amountOff AMOUNT_OFF; omega
  -- Per-instruction specs.
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

/-! ## On the user-facing `tokenAcctBalanceOf` shape

A naive corollary that restates the flat theorem in
`tokenAcctBalanceOf`-wrapped pre/post hits the SL bracketing mismatch:
`tokenAcctBalanceOf` definitionally unfolds to a 4-atom right-fold,
which when inserted into a larger `**` chain creates a tree
`(4 atoms) ** (4 atoms)` rather than the flat 8-atom right-fold the
`sl_block_iter`-derived theorem produces. The two forms are equal up
to `sepConj_assoc`, but the bridge takes ~30 LoC of pointwise-Iff
chasing per side and is mostly mechanical.

We defer that wrapper to the downstream consumer (Task 9 —
`PTokenTransferBalanceSpec`), which can either unfold its own
`tokenAcctBalance` atoms or apply the reshape inline. Once the
pattern shows up in a third call site, lift it here as a separate
corollary.

The `h_restSrcSz` / `h_restDstSz` arguments aren't needed for the
flat theorem but will be required by the user-facing wrapper (the
`↦Bytes` atom is well-formed only when the byte array has the
declared size).
-/

end Examples.RefinesTokenTransfer
