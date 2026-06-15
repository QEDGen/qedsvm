/-
  Layer 3b: full 75-CU happy-path glue triple for pinocchio p-token Transfer.
  Composes H1+H2+H3a..H3f+H4a+H4b; post contains the balance shift atoms:
    [r1+0xa0] ↦U64 wrapSub srcBalance txAmount
    [r1+0x29a8] ↦U64 wrapAdd dstBalance txAmount
  76th CU is the exit instruction (outside this chain).
  Unification: signerByte%256 = authWord (r0=r5 at H4a entry from H3f loads).
-/

import PToken.ValidationPrelude
import PToken.TransferArm.H1Dispatch
import PToken.TransferArm.H3aAmountAlign
import PToken.TransferArm.H3bIndexBound
import PToken.TransferArm.H3cStateChecks
import PToken.TransferArm.H3dBalanceCheck
import PToken.TransferArm.H3eMintKeyCheck
import PToken.TransferArm.H3fSignerExit
import PToken.TransferArm.H4aDestMintCheck
import PToken.TransferArm.H4bBalanceMutation
import SVM.SBPF.InstructionSpecs
import SVM.SBPF.Tactic.SL
import SVM.SBPF.Macros

namespace Examples.PTokenTransferFullHappyPath

open SVM.SBPF
open Memory
open Examples.PTokenValidationPrelude (validationPreludeCr)
open Examples.PTokenTransferArmDispatch (transferArmDispatchCr)
open Examples.PTokenTransferArmH3aAmountAlign (h3aCr alignedAmount)
open Examples.PTokenTransferArmH3bIndexBound (h3bCr)
open Examples.PTokenTransferArmH3cStateChecks (h3cCr)
open Examples.PTokenTransferArmH3dBalanceCheck (h3dCr)
open Examples.PTokenTransferArmH3eMintKeyCheck (h3eCr)
open Examples.PTokenTransferArmH3fSignerExit (h3fCr)
open Examples.PTokenTransferArmH4aDestMintCheck (h4aCr)
open Examples.PTokenTransferArmH4bBalanceMutation (h4bCr)

/-- The combined CodeReq for the entire 75-CU chain. -/
def fullHappyPathCr : CodeReq :=
  (((((((((transferArmDispatchCr 0 2).union
      (validationPreludeCr 2 10)).union
      (h3aCr 10)).union
      (h3bCr 14)).union
      (h3cCr 20)).union
      (h3dCr 28)).union
      (h3eCr 36)).union
      (h3fCr 48 51)).union
      (h4aCr 51 64)).union
      (h4bCr 64 75)

set_option maxHeartbeats 4000000 in
/-- 75-CU end-to-end triple: disjoint union of all 10 sub-arm pre/post with shared params unified; balance shift is the headline postcondition claim. -/
theorem p_token_transfer_full_happy_path_spec
    (initR0 initR1 initR2 initR3 initR4 initR5 initR6 initR7 : Nat)
    (disc : Nat)
    -- m1/m3 are fixed 0xa5 constants lifted as `let`s; only alignment bytes remain.
    (m2 m4 : Nat)
    (amount : Nat)
    (layoutBound layoutTag : Nat)
    (srcState dstState : Nat)
    (txAmount srcBalance dstBalance : Nat)
    -- src1..src4 pinned to canonMint*; dst1..dst4 pinned to authWord/dstMint*; both groups lifted as `let`s.
    (canonMint1 canonMint2 canonMint3 canonMint4 : Nat)
    (dstMint2 dstMint3 dstMint4 : Nat)
    (authWord signerByte authByte closeFlag : Nat)
    -- Size hypotheses
    (h_amt_in : amount < 2 ^ 64)
    (h_bound_lt : layoutBound < 2 ^ 64)
    (h_tx_lt : txAmount < 2 ^ 64)
    (h_bal_lt : srcBalance < 2 ^ 64)
    (h_dst_bal_lt : dstBalance < 2 ^ 64)
    (h_canon1_lt : canonMint1 < 2 ^ 64) (h_canon2_lt : canonMint2 < 2 ^ 64)
    (h_canon3_lt : canonMint3 < 2 ^ 64) (h_canon4_lt : canonMint4 < 2 ^ 64)
    (h_dm2_lt : dstMint2 < 2 ^ 64) (h_dm3_lt : dstMint3 < 2 ^ 64)
    (h_dm4_lt : dstMint4 < 2 ^ 64)
    (h_auth_lt : authWord < 2 ^ 64)
    (h_disc : disc % 256 = toU64 3)
    (hm2 : m2 % 256 = toU64 0xff)
    (hm4 : m4 % 256 = toU64 0xff)
    (h_bound_ge : layoutBound ≥ 9)
    (h_tag : layoutTag % 256 = toU64 3)
    (h_src_le : srcState % 256 ≤ 2) (h_src_ne : srcState % 256 ≠ 0)
    (h_dst_le : dstState % 256 ≤ 2) (h_dst_ne : dstState % 256 ≠ 0)
    (h_src_ne2 : srcState % 256 ≠ 2) (h_dst_ne2 : dstState % 256 ≠ 2)
    (h_bal_ge : srcBalance ≥ txAmount)
    (h_signer_ne : signerByte % 256 ≠ toU64 1)
    -- H4a chain-coupling: r0=r5 at H4a entry; dest-mint = canonical (baked into dst* lets).
    (h_r0_eq_r5_at_h4a : signerByte % 256 = authWord)
    (h_r4_ne : amount ≠ toU64 0x163)
    (h_amt_ne_0 : txAmount ≠ toU64 0)
    (h_auth_ne_0 : authByte % 256 ≠ toU64 0)
    (h_close_ne_1 : closeFlag % 256 ≠ toU64 1) :
    let m1 : Nat := toU64 0xa5
    let m3 : Nat := toU64 0xa5
    let src1 : Nat := canonMint1
    let src2 : Nat := canonMint2
    let src3 : Nat := canonMint3
    let src4 : Nat := canonMint4
    let dst1 : Nat := authWord
    let dst2 : Nat := dstMint2
    let dst3 : Nat := dstMint3
    let dst4 : Nat := dstMint4
    cuTripleWithinMem 75 0 0 75 fullHappyPathCr
      ((.r0 ↦ᵣ initR0) ** (.r1 ↦ᵣ initR1) ** (.r2 ↦ᵣ initR2) **
        (.r3 ↦ᵣ initR3) ** (.r4 ↦ᵣ initR4) ** (.r5 ↦ᵣ initR5) **
        (.r6 ↦ᵣ initR6) ** (.r7 ↦ᵣ initR7) **
        (effectiveAddr initR1 0 ↦ₘ disc) **
        (effectiveAddr initR1 0x58   ↦U64 m1) **
        (effectiveAddr initR1 0x2910 ↦ₘ m2) **
        (effectiveAddr initR1 0x2960 ↦U64 m3) **
        (effectiveAddr initR1 0x5218 ↦ₘ m4) **
        (effectiveAddr initR1 0x5268 ↦U64 amount) **
        (effectiveAddr (wrapAdd initR1 (alignedAmount amount)) 0x7a78 ↦U64 layoutBound) **
        (effectiveAddr (wrapAdd initR1 (alignedAmount amount)) 0x7a80 ↦ₘ layoutTag) **
        (effectiveAddr initR1 0xcc   ↦ₘ srcState) **
        (effectiveAddr initR1 0x29d4 ↦ₘ dstState) **
        (effectiveAddr (wrapAdd initR1 (alignedAmount amount)) 0x7a81 ↦U64 txAmount) **
        (effectiveAddr initR1 0xa0   ↦U64 srcBalance) **
        (effectiveAddr initR1 0x2968 ↦U64 canonMint1) **
        (effectiveAddr initR1 0x60   ↦U64 src1) **
        (effectiveAddr initR1 0x2970 ↦U64 canonMint2) **
        (effectiveAddr initR1 0x68   ↦U64 src2) **
        (effectiveAddr initR1 0x2978 ↦U64 canonMint3) **
        (effectiveAddr initR1 0x70   ↦U64 src3) **
        (effectiveAddr initR1 0x2980 ↦U64 canonMint4) **
        (effectiveAddr initR1 0x78   ↦U64 src4) **
        (effectiveAddr initR1 0x5220 ↦U64 authWord) **
        (effectiveAddr initR1 0xa8   ↦ₘ signerByte) **
        (effectiveAddr initR1 0x80   ↦U64 dst1) **
        (effectiveAddr initR1 0x5228 ↦U64 dstMint2) **
        (effectiveAddr initR1 0x88   ↦U64 dst2) **
        (effectiveAddr initR1 0x5230 ↦U64 dstMint3) **
        (effectiveAddr initR1 0x90   ↦U64 dst3) **
        (effectiveAddr initR1 0x5238 ↦U64 dstMint4) **
        (effectiveAddr initR1 0x98   ↦U64 dst4) **
        (effectiveAddr initR1 0x5219 ↦ₘ authByte) **
        (effectiveAddr initR1 0x29a8 ↦U64 dstBalance) **
        (effectiveAddr initR1 0xcd   ↦ₘ closeFlag))
      ((.r0 ↦ᵣ toU64 0) ** (.r1 ↦ᵣ initR1) ** (.r2 ↦ᵣ txAmount) **
        (.r3 ↦ᵣ closeFlag % 256) ** (.r4 ↦ᵣ authByte % 256) **
        (.r5 ↦ᵣ dstMint4) ** (.r6 ↦ᵣ toU64 0) ** (.r7 ↦ᵣ toU64 4) **
        (effectiveAddr initR1 0 ↦ₘ disc) **
        (effectiveAddr initR1 0x58   ↦U64 m1) **
        (effectiveAddr initR1 0x2910 ↦ₘ m2) **
        (effectiveAddr initR1 0x2960 ↦U64 m3) **
        (effectiveAddr initR1 0x5218 ↦ₘ m4) **
        (effectiveAddr initR1 0x5268 ↦U64 amount) **
        (effectiveAddr (wrapAdd initR1 (alignedAmount amount)) 0x7a78 ↦U64 layoutBound) **
        (effectiveAddr (wrapAdd initR1 (alignedAmount amount)) 0x7a80 ↦ₘ layoutTag) **
        (effectiveAddr initR1 0xcc   ↦ₘ srcState) **
        (effectiveAddr initR1 0x29d4 ↦ₘ dstState) **
        (effectiveAddr (wrapAdd initR1 (alignedAmount amount)) 0x7a81 ↦U64 txAmount) **
        -- Balance shift (HEADLINE):
        (effectiveAddr initR1 0xa0   ↦U64 wrapSub srcBalance txAmount) **
        (effectiveAddr initR1 0x2968 ↦U64 canonMint1) **
        (effectiveAddr initR1 0x60   ↦U64 src1) **
        (effectiveAddr initR1 0x2970 ↦U64 canonMint2) **
        (effectiveAddr initR1 0x68   ↦U64 src2) **
        (effectiveAddr initR1 0x2978 ↦U64 canonMint3) **
        (effectiveAddr initR1 0x70   ↦U64 src3) **
        (effectiveAddr initR1 0x2980 ↦U64 canonMint4) **
        (effectiveAddr initR1 0x78   ↦U64 src4) **
        (effectiveAddr initR1 0x5220 ↦U64 authWord) **
        (effectiveAddr initR1 0xa8   ↦ₘ signerByte) **
        (effectiveAddr initR1 0x80   ↦U64 dst1) **
        (effectiveAddr initR1 0x5228 ↦U64 dstMint2) **
        (effectiveAddr initR1 0x88   ↦U64 dst2) **
        (effectiveAddr initR1 0x5230 ↦U64 dstMint3) **
        (effectiveAddr initR1 0x90   ↦U64 dst3) **
        (effectiveAddr initR1 0x5238 ↦U64 dstMint4) **
        (effectiveAddr initR1 0x98   ↦U64 dst4) **
        (effectiveAddr initR1 0x5219 ↦ₘ authByte) **
        (effectiveAddr initR1 0x29a8 ↦U64 wrapAdd dstBalance txAmount) **
        (effectiveAddr initR1 0xcd   ↦ₘ closeFlag))
      (fun rt =>
        ((((((((rt.containsRange (effectiveAddr initR1 0) 1 = true ∧
                    ((rt.containsRange (effectiveAddr initR1 88) 8 = true ∧
                          rt.containsRange (effectiveAddr initR1 10512) 1 = true) ∧
                        rt.containsRange (effectiveAddr initR1 10592) 8 = true) ∧
                      rt.containsRange (effectiveAddr initR1 21016) 1 = true) ∧
                  rt.containsRange (effectiveAddr initR1 21096) 8 = true) ∧
                rt.containsRange (effectiveAddr (wrapAdd initR1 (alignedAmount amount)) 31352) 8 = true ∧
                  rt.containsRange (effectiveAddr (wrapAdd initR1 (alignedAmount amount)) 31360) 1 = true) ∧
              rt.containsRange (effectiveAddr initR1 204) 1 = true ∧
                rt.containsRange (effectiveAddr initR1 10708) 1 = true) ∧
            rt.containsRange (effectiveAddr (wrapAdd initR1 (alignedAmount amount)) 31361) 8 = true ∧
              rt.containsRange (effectiveAddr initR1 160) 8 = true) ∧
          ((((((rt.containsRange (effectiveAddr initR1 10600) 8 = true ∧
                        rt.containsRange (effectiveAddr initR1 96) 8 = true) ∧
                      rt.containsRange (effectiveAddr initR1 10608) 8 = true) ∧
                    rt.containsRange (effectiveAddr initR1 104) 8 = true) ∧
                  rt.containsRange (effectiveAddr initR1 10616) 8 = true) ∧
                rt.containsRange (effectiveAddr initR1 112) 8 = true) ∧
              rt.containsRange (effectiveAddr initR1 10624) 8 = true) ∧
            rt.containsRange (effectiveAddr initR1 120) 8 = true) ∧
        rt.containsRange (effectiveAddr initR1 21024) 8 = true ∧
          rt.containsRange (effectiveAddr initR1 168) 1 = true) ∧
      (((((rt.containsRange (effectiveAddr initR1 128) 8 = true ∧
                  rt.containsRange (effectiveAddr initR1 21032) 8 = true) ∧
                rt.containsRange (effectiveAddr initR1 136) 8 = true) ∧
              rt.containsRange (effectiveAddr initR1 21040) 8 = true) ∧
            rt.containsRange (effectiveAddr initR1 144) 8 = true) ∧
          rt.containsRange (effectiveAddr initR1 21048) 8 = true) ∧
        rt.containsRange (effectiveAddr initR1 152) 8 = true) ∧
    (((rt.containsRange (effectiveAddr initR1 21017) 1 = true ∧
            rt.containsWritable (effectiveAddr initR1 160) 8 = true) ∧
          rt.containsRange (effectiveAddr initR1 10664) 8 = true) ∧
        rt.containsWritable (effectiveAddr initR1 10664) 8 = true) ∧
      rt.containsRange (effectiveAddr initR1 205) 1 = true) := by
  -- Intro lets; restore original hypothesis names so the tactic block below runs unchanged.
  intro m1 m3 src1 src2 src3 src4 dst1 dst2 dst3 dst4
  have h_m1_lt : m1 < 2 ^ 64 := by decide
  have h_m3_lt : m3 < 2 ^ 64 := by decide
  have hm1 : m1 = toU64 0xa5 := rfl
  have hm3 : m3 = toU64 0xa5 := rfl
  have h_s1_lt : src1 < 2 ^ 64 := h_canon1_lt
  have h_s2_lt : src2 < 2 ^ 64 := h_canon2_lt
  have h_s3_lt : src3 < 2 ^ 64 := h_canon3_lt
  have h_s4_lt : src4 < 2 ^ 64 := h_canon4_lt
  have h_eq_s1 : src1 = canonMint1 := rfl
  have h_eq_s2 : src2 = canonMint2 := rfl
  have h_eq_s3 : src3 = canonMint3 := rfl
  have h_eq_s4 : src4 = canonMint4 := rfl
  have h_d1_lt : dst1 < 2 ^ 64 := h_auth_lt
  have h_d2_lt : dst2 < 2 ^ 64 := h_dm2_lt
  have h_d3_lt : dst3 < 2 ^ 64 := h_dm3_lt
  have h_d4_lt : dst4 < 2 ^ 64 := h_dm4_lt
  have h_eq_d1 : dst1 = authWord := rfl
  have h_eq_d2 : dst2 = dstMint2 := rfl
  have h_eq_d3 : dst3 = dstMint3 := rfl
  have h_eq_d4 : dst4 = dstMint4 := rfl
  have h_h1 :=
    Examples.PTokenTransferArmDispatch.p_token_transfer_arm_dispatch_spec
      0 2 initR1 initR2 disc h_disc
  have h_h2 :=
    Examples.PTokenValidationPrelude.p_token_transfer_validation_prelude_spec
      2 10 initR1 (disc % 256) m1 m3 m2 m4
      h_m1_lt h_m3_lt hm1 hm2 hm3 hm4
  have h_h3a :=
    Examples.PTokenTransferArmH3aAmountAlign.p_token_transfer_arm_h3a_spec
      10 initR1 initR3 initR4 amount h_amt_in
  have h_h3b :=
    Examples.PTokenTransferArmH3bIndexBound.p_token_transfer_arm_h3b_spec
      14 initR1 (m4 % 256) amount layoutBound layoutTag
      h_bound_lt h_bound_ge h_tag
  -- H3b returns a `let baseAddr := ...; cuTripleWithinMem ...`; reduce so sl_block_iter sees bare cuTripleWithinMem.
  dsimp only [] at h_h3b
  have h_h3c :=
    Examples.PTokenTransferArmH3cStateChecks.p_token_transfer_arm_h3c_spec
      20 initR1 (layoutTag % 256) initR5 initR6 initR7
      srcState dstState h_src_le h_src_ne h_dst_le h_dst_ne
  have h_h3d :=
    Examples.PTokenTransferArmH3dBalanceCheck.p_token_transfer_arm_h3d_spec
      28 initR1 (wrapAdd initR1 (alignedAmount amount))
      srcState dstState txAmount srcBalance
      h_tx_lt h_bal_lt h_src_ne2 h_dst_ne2 h_bal_ge
  -- H3e: r0 = initR0 (no earlier arm touches r0), r5 = dstState%256 (from H3c post).
  have h_h3e :=
    Examples.PTokenTransferArmH3eMintKeyCheck.p_token_transfer_arm_h3e_spec
      36 initR1 initR0 (dstState % 256)
      canonMint1 canonMint2 canonMint3 canonMint4 src1 src2 src3 src4
      h_canon1_lt h_canon2_lt h_canon3_lt h_canon4_lt
      h_s1_lt h_s2_lt h_s3_lt h_s4_lt h_eq_s1 h_eq_s2 h_eq_s3 h_eq_s4
  have h_h3f :=
    Examples.PTokenTransferArmH3fSignerExit.p_token_transfer_arm_h3f_spec
      48 51 src4 initR1 canonMint4 authWord signerByte
      h_auth_lt h_signer_ne
  -- H4a: r0=signerByte%256, r5=authWord at entry; spec uses mint1 for both, so instantiate to authWord and coerce via h_r0_eq_r5_at_h4a.
  have h_h4a :=
    Examples.PTokenTransferArmH4aDestMintCheck.p_token_transfer_arm_h4a_spec
      51 64 initR1 amount (toU64 1)
      authWord dstMint2 dstMint3 dstMint4 dst1 dst2 dst3 dst4
      h_dm2_lt h_dm3_lt h_dm4_lt
      h_d1_lt h_d2_lt h_d3_lt h_d4_lt h_eq_d1 h_eq_d2 h_eq_d3 h_eq_d4 h_r4_ne
  have h_h4b :=
    Examples.PTokenTransferArmH4bBalanceMutation.p_token_transfer_arm_h4b_spec
      64 75 dst4 initR1 amount txAmount srcBalance dstBalance
      authByte closeFlag h_dst_bal_lt h_amt_ne_0 h_auth_ne_0 h_close_ne_1
  -- Align H3f post-r0 (signerByte%256) to H4a pre-r0 (authWord).
  rw [h_r0_eq_r5_at_h4a] at h_h3f
  unfold fullHappyPathCr
  sl_block_iter [h_h1, h_h2, h_h3a, h_h3b, h_h3c, h_h3d,
                 h_h3e, h_h3f, h_h4a, h_h4b]

/-! ## 76-CU terminating triple — happy path + success-exit

Extends `p_token_transfer_full_happy_path_spec` (75 CU) with `.exit` at PC 75.
Adds `callStackIs []` to pre (required: `.exit` only exits when call stack is empty;
otherwise pops a frame). The atom threads through all 10 sub-arms untouched. -/

set_option maxHeartbeats 8000000 in
theorem p_token_transfer_full_happy_path_terminates
    (initR0 initR1 initR2 initR3 initR4 initR5 initR6 initR7 : Nat)
    (disc : Nat)
    (m2 m4 : Nat)
    (amount : Nat)
    (layoutBound layoutTag : Nat)
    (srcState dstState : Nat)
    (txAmount srcBalance dstBalance : Nat)
    (canonMint1 canonMint2 canonMint3 canonMint4 : Nat)
    (dstMint2 dstMint3 dstMint4 : Nat)
    (authWord signerByte authByte closeFlag : Nat)
    (h_amt_in : amount < 2 ^ 64)
    (h_bound_lt : layoutBound < 2 ^ 64)
    (h_tx_lt : txAmount < 2 ^ 64)
    (h_bal_lt : srcBalance < 2 ^ 64)
    (h_dst_bal_lt : dstBalance < 2 ^ 64)
    (h_canon1_lt : canonMint1 < 2 ^ 64) (h_canon2_lt : canonMint2 < 2 ^ 64)
    (h_canon3_lt : canonMint3 < 2 ^ 64) (h_canon4_lt : canonMint4 < 2 ^ 64)
    (h_dm2_lt : dstMint2 < 2 ^ 64) (h_dm3_lt : dstMint3 < 2 ^ 64)
    (h_dm4_lt : dstMint4 < 2 ^ 64)
    (h_auth_lt : authWord < 2 ^ 64)
    (h_disc : disc % 256 = toU64 3)
    (hm2 : m2 % 256 = toU64 0xff)
    (hm4 : m4 % 256 = toU64 0xff)
    (h_bound_ge : layoutBound ≥ 9)
    (h_tag : layoutTag % 256 = toU64 3)
    (h_src_le : srcState % 256 ≤ 2) (h_src_ne : srcState % 256 ≠ 0)
    (h_dst_le : dstState % 256 ≤ 2) (h_dst_ne : dstState % 256 ≠ 0)
    (h_src_ne2 : srcState % 256 ≠ 2) (h_dst_ne2 : dstState % 256 ≠ 2)
    (h_bal_ge : srcBalance ≥ txAmount)
    (h_signer_ne : signerByte % 256 ≠ toU64 1)
    (h_r0_eq_r5_at_h4a : signerByte % 256 = authWord)
    (h_r4_ne : amount ≠ toU64 0x163)
    (h_amt_ne_0 : txAmount ≠ toU64 0)
    (h_auth_ne_0 : authByte % 256 ≠ toU64 0)
    (h_close_ne_1 : closeFlag % 256 ≠ toU64 1) :
    let m1 : Nat := toU64 0xa5
    let m3 : Nat := toU64 0xa5
    let src1 : Nat := canonMint1
    let src2 : Nat := canonMint2
    let src3 : Nat := canonMint3
    let src4 : Nat := canonMint4
    let dst1 : Nat := authWord
    let dst2 : Nat := dstMint2
    let dst3 : Nat := dstMint3
    let dst4 : Nat := dstMint4
    cuTripleAbortsWithinMem 76 0 0
      (fullHappyPathCr.union (CodeReq.singleton 75 .exit))
      (((.r0 ↦ᵣ initR0) ** (.r1 ↦ᵣ initR1) ** (.r2 ↦ᵣ initR2) **
        (.r3 ↦ᵣ initR3) ** (.r4 ↦ᵣ initR4) ** (.r5 ↦ᵣ initR5) **
        (.r6 ↦ᵣ initR6) ** (.r7 ↦ᵣ initR7) **
        (effectiveAddr initR1 0 ↦ₘ disc) **
        (effectiveAddr initR1 0x58   ↦U64 m1) **
        (effectiveAddr initR1 0x2910 ↦ₘ m2) **
        (effectiveAddr initR1 0x2960 ↦U64 m3) **
        (effectiveAddr initR1 0x5218 ↦ₘ m4) **
        (effectiveAddr initR1 0x5268 ↦U64 amount) **
        (effectiveAddr (wrapAdd initR1 (alignedAmount amount)) 0x7a78 ↦U64 layoutBound) **
        (effectiveAddr (wrapAdd initR1 (alignedAmount amount)) 0x7a80 ↦ₘ layoutTag) **
        (effectiveAddr initR1 0xcc   ↦ₘ srcState) **
        (effectiveAddr initR1 0x29d4 ↦ₘ dstState) **
        (effectiveAddr (wrapAdd initR1 (alignedAmount amount)) 0x7a81 ↦U64 txAmount) **
        (effectiveAddr initR1 0xa0   ↦U64 srcBalance) **
        (effectiveAddr initR1 0x2968 ↦U64 canonMint1) **
        (effectiveAddr initR1 0x60   ↦U64 src1) **
        (effectiveAddr initR1 0x2970 ↦U64 canonMint2) **
        (effectiveAddr initR1 0x68   ↦U64 src2) **
        (effectiveAddr initR1 0x2978 ↦U64 canonMint3) **
        (effectiveAddr initR1 0x70   ↦U64 src3) **
        (effectiveAddr initR1 0x2980 ↦U64 canonMint4) **
        (effectiveAddr initR1 0x78   ↦U64 src4) **
        (effectiveAddr initR1 0x5220 ↦U64 authWord) **
        (effectiveAddr initR1 0xa8   ↦ₘ signerByte) **
        (effectiveAddr initR1 0x80   ↦U64 dst1) **
        (effectiveAddr initR1 0x5228 ↦U64 dstMint2) **
        (effectiveAddr initR1 0x88   ↦U64 dst2) **
        (effectiveAddr initR1 0x5230 ↦U64 dstMint3) **
        (effectiveAddr initR1 0x90   ↦U64 dst3) **
        (effectiveAddr initR1 0x5238 ↦U64 dstMint4) **
        (effectiveAddr initR1 0x98   ↦U64 dst4) **
        (effectiveAddr initR1 0x5219 ↦ₘ authByte) **
        (effectiveAddr initR1 0x29a8 ↦U64 dstBalance) **
        (effectiveAddr initR1 0xcd   ↦ₘ closeFlag)) **
        callStackIs [])
      (fun rt =>
        ((((((((rt.containsRange (effectiveAddr initR1 0) 1 = true ∧
                    ((rt.containsRange (effectiveAddr initR1 88) 8 = true ∧
                          rt.containsRange (effectiveAddr initR1 10512) 1 = true) ∧
                        rt.containsRange (effectiveAddr initR1 10592) 8 = true) ∧
                      rt.containsRange (effectiveAddr initR1 21016) 1 = true) ∧
                  rt.containsRange (effectiveAddr initR1 21096) 8 = true) ∧
                rt.containsRange (effectiveAddr (wrapAdd initR1 (alignedAmount amount)) 31352) 8 = true ∧
                  rt.containsRange (effectiveAddr (wrapAdd initR1 (alignedAmount amount)) 31360) 1 = true) ∧
              rt.containsRange (effectiveAddr initR1 204) 1 = true ∧
                rt.containsRange (effectiveAddr initR1 10708) 1 = true) ∧
            rt.containsRange (effectiveAddr (wrapAdd initR1 (alignedAmount amount)) 31361) 8 = true ∧
              rt.containsRange (effectiveAddr initR1 160) 8 = true) ∧
          ((((((rt.containsRange (effectiveAddr initR1 10600) 8 = true ∧
                        rt.containsRange (effectiveAddr initR1 96) 8 = true) ∧
                      rt.containsRange (effectiveAddr initR1 10608) 8 = true) ∧
                    rt.containsRange (effectiveAddr initR1 104) 8 = true) ∧
                  rt.containsRange (effectiveAddr initR1 10616) 8 = true) ∧
                rt.containsRange (effectiveAddr initR1 112) 8 = true) ∧
              rt.containsRange (effectiveAddr initR1 10624) 8 = true) ∧
            rt.containsRange (effectiveAddr initR1 120) 8 = true) ∧
        rt.containsRange (effectiveAddr initR1 21024) 8 = true ∧
          rt.containsRange (effectiveAddr initR1 168) 1 = true) ∧
      (((((rt.containsRange (effectiveAddr initR1 128) 8 = true ∧
                  rt.containsRange (effectiveAddr initR1 21032) 8 = true) ∧
                rt.containsRange (effectiveAddr initR1 136) 8 = true) ∧
              rt.containsRange (effectiveAddr initR1 21040) 8 = true) ∧
            rt.containsRange (effectiveAddr initR1 144) 8 = true) ∧
          rt.containsRange (effectiveAddr initR1 21048) 8 = true) ∧
        rt.containsRange (effectiveAddr initR1 152) 8 = true) ∧
    (((rt.containsRange (effectiveAddr initR1 21017) 1 = true ∧
            rt.containsWritable (effectiveAddr initR1 160) 8 = true) ∧
          rt.containsRange (effectiveAddr initR1 10664) 8 = true) ∧
        rt.containsWritable (effectiveAddr initR1 10664) 8 = true) ∧
      rt.containsRange (effectiveAddr initR1 205) 1 = true)
      (toU64 0) := by
  intro m1 m3 src1 src2 src3 src4 dst1 dst2 dst3 dst4
  have h_full :=
    p_token_transfer_full_happy_path_spec
      initR0 initR1 initR2 initR3 initR4 initR5 initR6 initR7
      disc m2 m4 amount layoutBound layoutTag srcState dstState
      txAmount srcBalance dstBalance
      canonMint1 canonMint2 canonMint3 canonMint4
      dstMint2 dstMint3 dstMint4
      authWord signerByte authByte closeFlag
      h_amt_in h_bound_lt h_tx_lt h_bal_lt h_dst_bal_lt
      h_canon1_lt h_canon2_lt h_canon3_lt h_canon4_lt
      h_dm2_lt h_dm3_lt h_dm4_lt h_auth_lt
      h_disc hm2 hm4 h_bound_ge h_tag
      h_src_le h_src_ne h_dst_le h_dst_ne h_src_ne2 h_dst_ne2 h_bal_ge
      h_signer_ne h_r0_eq_r5_at_h4a h_r4_ne
      h_amt_ne_0 h_auth_ne_0 h_close_ne_1
  intro F hF fetch hcr s hPF hpc hex hbud h_reg
  -- Split union: fullHappyPathCr (PCs 0..74) and singleton at PC 75 are disjoint.
  have hd_cr : fullHappyPathCr.Disjoint (CodeReq.singleton 75 .exit) := by
    unfold fullHappyPathCr
    sl_disjoint_codereq
  have hcr_full := CodeReq.SatisfiedBy_of_union_left hcr
  have hcr_exit := CodeReq.SatisfiedBy_of_union_right hd_cr hcr
  -- Frame callStackIs [] into FullHappyPath pre/post via cuTripleWithinMem_frame_right.
  have h_full_framed :=
    cuTripleWithinMem_frame_right (callStackIs []) (pcFree_callStackIs _) h_full
  obtain ⟨k1, hk1, hpc_mid, hex_mid, hcu1, hQF⟩ :=
    h_full_framed F hF fetch hcr_full s hPF hpc hex (by omega) h_reg
  -- Reshape via two assoc.mp's to peel off (.r0 ↦ᵣ toU64 0) from the framed post.
  have hQF_outer := holdsFor_sepConj_assoc.mp hQF
  have hQF' := holdsFor_sepConj_assoc.mp hQF_outer
  have hmid_cs : (executeFn fetch s k1).callStack = [] := by
    obtain ⟨hp_mid, hcompat_mid, h_post_full, h_csF, hd_post_csF, hu_post_csF,
            h_post_sat, h_csF_sat⟩ := hQF_outer
    obtain ⟨h_cs, h_F, hd_cs_F, hu_cs_F, h_cs_pred, h_F_sat⟩ := h_csF_sat
    have h_cs_cs : h_cs.callStack = some [] := by
      rw [show h_cs = PartialState.singletonCallStack [] from h_cs_pred]
      exact PartialState.singletonCallStack_callStack_self
    have h_csF_cs : h_csF.callStack = some [] :=
      hu_cs_F ▸ PartialState.union_callStack_of_left_some h_cs_cs
    have h_post_full_cs : h_post_full.callStack = none := by
      rcases hd_post_csF.callStack with h | h
      · exact h
      · rw [h_csF_cs] at h; exact absurd h (by simp)
    have hp_mid_cs : hp_mid.callStack = some [] := by
      rw [← hu_post_csF, PartialState.union_callStack_of_left_none h_post_full_cs]
      exact h_csF_cs
    exact hcompat_mid.callStack [] hp_mid_cs
  have hbud_mid : (executeFn fetch s k1).cuConsumed + 1 ≤
      (executeFn fetch s k1).cuBudget := by
    rw [executeFn_preserves_cuBudget]
    omega
  -- pcFree of R is discharged by recursively applying pcFree_sepConj across all atoms.
  have exit_result : ∃ k, k ≤ 1 ∧
      (executeFn fetch (executeFn fetch s k1) k).exitCode = some (toU64 0) := by
    refine exit_aborts_spec (toU64 0) 75 _ ?_ fetch hcr_exit
      (executeFn fetch s k1) hQF' hpc_mid hex_mid hbud_mid hmid_cs
    repeat (first
      | exact hF
      | exact pcFree_callStackIs _
      | exact pcFree_regIs _ _
      | exact pcFree_memByteIs _ _
      | exact pcFree_memU64Is _ _
      | apply pcFree_sepConj)
  obtain ⟨k2, hk2, hex_end⟩ := exit_result
  refine ⟨k1 + k2, ?_, ?_, ?_⟩
  · have : k1 + k2 ≤ 75 + 1 := Nat.add_le_add hk1 hk2
    omega
  · rw [executeFn_compose]; exact hex_end
  · rw [executeFn_compose]
    rcases Nat.eq_or_lt_of_le hk2 with hk2_eq | hk2_lt
    · subst hk2_eq
      have hfetch_exit : fetch (executeFn fetch s k1).pc = some .exit := by
        rw [hpc_mid]
        exact hcr_exit 75 _ CodeReq.singleton_self
      have hexec1 : executeFn fetch (executeFn fetch s k1) 1
          = chargeCu (step .exit (executeFn fetch s k1)) := by
        rw [show (1 : Nat) = 0 + 1 from rfl,
            executeFn_step fetch (executeFn fetch s k1) 0 _ hex_mid
              (by omega) hfetch_exit,
            executeFn_zero]
      have hstep_exit : step .exit (executeFn fetch s k1) =
          { (executeFn fetch s k1) with
              exitCode := some ((executeFn fetch s k1).regs.get .r0) } := by
        simp only [step, hmid_cs]
      rw [hexec1, hstep_exit]
      show (executeFn fetch s k1).cuConsumed + 1 ≤ s.cuConsumed + 76 + 0
      omega
    · have hk2_0 : k2 = 0 := by omega
      subst hk2_0
      rw [executeFn_zero]
      show (executeFn fetch s k1).cuConsumed ≤ s.cuConsumed + 76 + 0
      omega

end Examples.PTokenTransferFullHappyPath
