/-
  Layer 3b artifact: **Full end-to-end happy-path glue triple** for the
  pinocchio p-token Transfer instruction. Composes all 10 sub-arm
  Hoare triples (H1 + H2 + H3a..H3f + H4a + H4b) at concrete bases,
  producing a single Hoare triple over a 75-CU chain that advances
  PC 0 → 75 and **shifts source and destination token balances**.

  This is the headline correctness claim of the Layer 3b chain: under
  a structured precondition (mainly: discriminator = 3, magic bytes
  match, source/dest states are Initialized, source balance covers
  amount, source/dest mint pubkey words match the canonical), the
  postcondition contains the balance mutation atoms

      [r1 + 0xa0]   ↦U64 wrapSub srcBalance txAmount
      [r1 + 0x29a8] ↦U64 wrapAdd dstBalance txAmount

  PC layout (synthetic linear chain, not real-image PCs — same approach
  L2Bytecode.lean uses for its callee at base=100):

      H1 at base  0, target  2   ( 2 CU, dispatch)
      H2 at base  2, target 10   ( 8 CU, validation prelude)
      H3a at base 10, exit  14   ( 4 CU, amount-align arithmetic)
      H3b at base 14, exit  20   ( 6 CU, layout-index bounds)
      H3c at base 20, exit  28   ( 8 CU, src/dst state checks)
      H3d at base 28, exit  36   ( 8 CU, balance-cover check)
      H3e at base 36, exit  48   (12 CU, src-mint key verify)
      H3f at base 48, target 51  ( 3 CU, signer-exit jump)
      H4a at base 51, target 64  (13 CU, dst-mint key verify)
      H4b at base 64, target 75  (11 CU, balance mutation)

  Total: 75 CU. The actual mollusk-validated p-token Transfer is
  76 CU; the missing CU is the final `exit` instruction outside this
  chain (the chain ends at the jne that hops to a tail block).

  This artifact threads the intermediate register state — r2 carries
  txAmount and r3 carries srcBalance from H3d through H3e/H3f/H4a
  (none of which touch r2/r3) into H4b which uses them to compute the
  balance shift. The chain's precondition unifies shared parameters
  (initR1, mint canonical words, etc.) across all sub-arms.

  **Unification constraints** that must hold across sub-arms:
  - signerByte % 256 = authWord (r0 and r5 at H4a entry, both derived
    from H3f loads — H4a's spec uses the SAME variable `mint1` for
    both r0 and r5's incoming values, so we require their equality).
  - amount = txAmount (H3a loads amount from [r1+0x5268]; H3d loads
    txAmount from [baseAddr+0x7a81]; not technically required since
    the two cells are distinct addresses, but kept as a parameter
    choice — the chain uses txAmount for the balance arithmetic).
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
/-- End-to-end Hoare triple over the 10-arm happy-path chain.

    The precondition is the disjoint union of all 10 sub-arm
    preconditions, with shared parameters unified across arms. The
    postcondition contains the balance shift (the headline claim) as
    well as the threaded register/memory state from each arm.

    Memory cells touched by multiple arms are threaded once
    (e.g. `[r1+0xa0]` is in H3d's pre as srcBalance and in H4b's
    pre/post as the source-balance cell that gets mutated). -/
theorem p_token_transfer_full_happy_path_spec
    (initR0 initR1 initR2 initR3 initR4 initR5 initR6 initR7 : Nat)
    -- Discriminator (H1)
    (disc : Nat)
    -- Magic bytes (H2): m1 and m3 are fixed constants 0xa5 (lifted to
    -- `let`s in the body); only the alignment-byte parameters remain.
    (m2 m4 : Nat)
    -- Amount / aligned-index (H3a, H3b, H3d)
    (amount : Nat)
    (layoutBound layoutTag : Nat)
    -- State bytes (H3c, H3d)
    (srcState dstState : Nat)
    -- Balance fields (H3d, H4b)
    (txAmount srcBalance dstBalance : Nat)
    -- Canonical mint words (H3e); the source-account mint words
    -- (src1..src4) are pinned by hypothesis to the canonical mints,
    -- lifted to `let`s in the type below.
    (canonMint1 canonMint2 canonMint3 canonMint4 : Nat)
    -- Destination-account mint words and dest-canonical mint words (H4a)
    (dst1 dst2 dst3 dst4 : Nat)
    (dstMint2 dstMint3 dstMint4 : Nat)
    -- Authority/signer (H3f, H4b)
    (authWord signerByte authByte closeFlag : Nat)
    -- Size hypotheses
    (h_amt_in : amount < 2 ^ 64)
    (h_bound_lt : layoutBound < 2 ^ 64)
    (h_tx_lt : txAmount < 2 ^ 64)
    (h_bal_lt : srcBalance < 2 ^ 64)
    (h_dst_bal_lt : dstBalance < 2 ^ 64)
    (h_canon1_lt : canonMint1 < 2 ^ 64) (h_canon2_lt : canonMint2 < 2 ^ 64)
    (h_canon3_lt : canonMint3 < 2 ^ 64) (h_canon4_lt : canonMint4 < 2 ^ 64)
    (h_d1_lt : dst1 < 2 ^ 64) (h_d2_lt : dst2 < 2 ^ 64)
    (h_d3_lt : dst3 < 2 ^ 64) (h_d4_lt : dst4 < 2 ^ 64)
    (h_dm2_lt : dstMint2 < 2 ^ 64) (h_dm3_lt : dstMint3 < 2 ^ 64)
    (h_dm4_lt : dstMint4 < 2 ^ 64)
    (h_auth_lt : authWord < 2 ^ 64)
    -- H1: discriminator = 3
    (h_disc : disc % 256 = toU64 3)
    -- H2: magic-byte matches (m1 and m3 are now constant lets in the body)
    (hm2 : m2 % 256 = toU64 0xff)
    (hm4 : m4 % 256 = toU64 0xff)
    -- H3b: layout bound and tag
    (h_bound_ge : layoutBound ≥ 9)
    (h_tag : layoutTag % 256 = toU64 3)
    -- H3c: state ∈ {1, 2} (TokenAccount::Initialized or Frozen ruled out below)
    (h_src_le : srcState % 256 ≤ 2) (h_src_ne : srcState % 256 ≠ 0)
    (h_dst_le : dstState % 256 ≤ 2) (h_dst_ne : dstState % 256 ≠ 0)
    -- H3d: state ≠ Frozen, balance covers amount
    (h_src_ne2 : srcState % 256 ≠ 2) (h_dst_ne2 : dstState % 256 ≠ 2)
    (h_bal_ge : srcBalance ≥ txAmount)
    -- H3e: source-mint = canonical (lifted as `let`s in the type)
    -- H3f: not signer (`jne r0, 0x1` taken)
    (h_signer_ne : signerByte % 256 ≠ toU64 1)
    -- H4a: dest-mint = canonical, and chain-coupling r0=r5 at H4a entry
    (h_r0_eq_r5_at_h4a : signerByte % 256 = authWord)
    (h_eq_d1 : dst1 = authWord) (h_eq_d2 : dst2 = dstMint2)
    (h_eq_d3 : dst3 = dstMint3) (h_eq_d4 : dst4 = dstMint4)
    (h_r4_ne : amount ≠ toU64 0x163)
    -- H4b: nonzero amount, nonzero auth, close-flag != 1 (jne taken)
    (h_amt_ne_0 : txAmount ≠ toU64 0)
    (h_auth_ne_0 : authByte % 256 ≠ toU64 0)
    (h_close_ne_1 : closeFlag % 256 ≠ toU64 1) :
    -- Witnesses lifted into the type as `let`s. Magic-byte cells m1
    -- and m3 are fixed constants; source-mint words src1..src4 are
    -- pinned by hypothesis to the canonical mint words. The body
    -- `intro`s them before the existing tactic block runs.
    let m1 : Nat := toU64 0xa5
    let m3 : Nat := toU64 0xa5
    let src1 : Nat := canonMint1
    let src2 : Nat := canonMint2
    let src3 : Nat := canonMint3
    let src4 : Nat := canonMint4
    cuTripleWithinMem 75 0 0 75 fullHappyPathCr
      -- PRECONDITION: all register and memory state at chain entry
      ((.r0 ↦ᵣ initR0) ** (.r1 ↦ᵣ initR1) ** (.r2 ↦ᵣ initR2) **
        (.r3 ↦ᵣ initR3) ** (.r4 ↦ᵣ initR4) ** (.r5 ↦ᵣ initR5) **
        (.r6 ↦ᵣ initR6) ** (.r7 ↦ᵣ initR7) **
        -- Discriminator (H1)
        (effectiveAddr initR1 0 ↦ₘ disc) **
        -- Magic bytes (H2)
        (effectiveAddr initR1 0x58   ↦U64 m1) **
        (effectiveAddr initR1 0x2910 ↦ₘ m2) **
        (effectiveAddr initR1 0x2960 ↦U64 m3) **
        (effectiveAddr initR1 0x5218 ↦ₘ m4) **
        -- Amount (H3a)
        (effectiveAddr initR1 0x5268 ↦U64 amount) **
        -- Layout cells (H3b) — at baseAddr-offset
        (effectiveAddr (wrapAdd initR1 (alignedAmount amount)) 0x7a78 ↦U64 layoutBound) **
        (effectiveAddr (wrapAdd initR1 (alignedAmount amount)) 0x7a80 ↦ₘ layoutTag) **
        -- State bytes (H3c)
        (effectiveAddr initR1 0xcc   ↦ₘ srcState) **
        (effectiveAddr initR1 0x29d4 ↦ₘ dstState) **
        -- TxAmount + srcBalance (H3d)
        (effectiveAddr (wrapAdd initR1 (alignedAmount amount)) 0x7a81 ↦U64 txAmount) **
        (effectiveAddr initR1 0xa0   ↦U64 srcBalance) **
        -- Canonical-mint pubkey words (H3e)
        (effectiveAddr initR1 0x2968 ↦U64 canonMint1) **
        (effectiveAddr initR1 0x60   ↦U64 src1) **
        (effectiveAddr initR1 0x2970 ↦U64 canonMint2) **
        (effectiveAddr initR1 0x68   ↦U64 src2) **
        (effectiveAddr initR1 0x2978 ↦U64 canonMint3) **
        (effectiveAddr initR1 0x70   ↦U64 src3) **
        (effectiveAddr initR1 0x2980 ↦U64 canonMint4) **
        (effectiveAddr initR1 0x78   ↦U64 src4) **
        -- Authority word + signer byte (H3f)
        (effectiveAddr initR1 0x5220 ↦U64 authWord) **
        (effectiveAddr initR1 0xa8   ↦ₘ signerByte) **
        -- Dest-mint cells + dest-canonical mint cells (H4a)
        (effectiveAddr initR1 0x80   ↦U64 dst1) **
        (effectiveAddr initR1 0x5228 ↦U64 dstMint2) **
        (effectiveAddr initR1 0x88   ↦U64 dst2) **
        (effectiveAddr initR1 0x5230 ↦U64 dstMint3) **
        (effectiveAddr initR1 0x90   ↦U64 dst3) **
        (effectiveAddr initR1 0x5238 ↦U64 dstMint4) **
        (effectiveAddr initR1 0x98   ↦U64 dst4) **
        -- H4b cells: authByte, dstBalance, closeFlag
        (effectiveAddr initR1 0x5219 ↦ₘ authByte) **
        (effectiveAddr initR1 0x29a8 ↦U64 dstBalance) **
        (effectiveAddr initR1 0xcd   ↦ₘ closeFlag))
      -- POSTCONDITION: register state at chain exit + balance shift
      ((.r0 ↦ᵣ toU64 0) ** (.r1 ↦ᵣ initR1) ** (.r2 ↦ᵣ txAmount) **
        (.r3 ↦ᵣ closeFlag % 256) ** (.r4 ↦ᵣ authByte % 256) **
        (.r5 ↦ᵣ dstMint4) ** (.r6 ↦ᵣ toU64 0) ** (.r7 ↦ᵣ toU64 4) **
        -- Discriminator (unchanged)
        (effectiveAddr initR1 0 ↦ₘ disc) **
        -- Magic bytes (unchanged)
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
        -- Balance shift — the HEADLINE claim:
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
        -- Balance shift — the HEADLINE claim, destination side:
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
  -- Introduce the type-level `let`s into the proof context, then
  -- restore the original hypothesis names as local `have`s so the
  -- existing tactic block (which references hm1/hm3/h_m1_lt/h_m3_lt
  -- and h_eq_s1..s4/h_s1_lt..s4_lt by name) runs unchanged.
  intro m1 m3 src1 src2 src3 src4
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
  -- Instantiate each sub-arm spec at its base PC with the threaded
  -- intermediate state. Pre/post atom values are alpha-renamed to
  -- the chain-level names where the threading happens.
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
  -- H3b's spec returns a `let baseAddr := ...; cuTripleWithinMem ...`.
  -- Reduce the let so sl_block_iter sees a bare `cuTripleWithinMem`.
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
  -- H3e: at entry, r0 = initR0 (chain's, since no earlier arm touches r0),
  -- r5 = dstState % 256 (from H3c's post). The spec's `initR0`, `initR5`
  -- are arbitrary register-slot values; we thread the chain's values.
  have h_h3e :=
    Examples.PTokenTransferArmH3eMintKeyCheck.p_token_transfer_arm_h3e_spec
      36 initR1 initR0 (dstState % 256)
      canonMint1 canonMint2 canonMint3 canonMint4 src1 src2 src3 src4
      h_canon1_lt h_canon2_lt h_canon3_lt h_canon4_lt
      h_s1_lt h_s2_lt h_s3_lt h_s4_lt h_eq_s1 h_eq_s2 h_eq_s3 h_eq_s4
  -- H3f at base 48, target 51: enters with r0=src4 (from H3e), r5=canonMint4 (from H3e).
  have h_h3f :=
    Examples.PTokenTransferArmH3fSignerExit.p_token_transfer_arm_h3f_spec
      48 51 src4 initR1 canonMint4 authWord signerByte
      h_auth_lt h_signer_ne
  -- H4a at base 51, target 64: r0 = signerByte%256, r5 = authWord at entry.
  -- The spec uses `mint1` for BOTH r0's and r5's entry value, so we
  -- instantiate H4a's `mint1` to `authWord` and rely on
  -- `h_r0_eq_r5_at_h4a : signerByte % 256 = authWord` to coerce.
  have h_h4a :=
    Examples.PTokenTransferArmH4aDestMintCheck.p_token_transfer_arm_h4a_spec
      51 64 initR1 amount (toU64 1)
      authWord dstMint2 dstMint3 dstMint4 dst1 dst2 dst3 dst4
      h_dm2_lt h_dm3_lt h_dm4_lt
      h_d1_lt h_d2_lt h_d3_lt h_d4_lt h_eq_d1 h_eq_d2 h_eq_d3 h_eq_d4 h_r4_ne
  -- H4b at base 64, target 75: r0 = dst4 (from H4a), r2 = txAmount (preserved
  -- from H3d), r3 = srcBalance (preserved from H3d), r4 = initR4 (preserved).
  have h_h4b :=
    Examples.PTokenTransferArmH4bBalanceMutation.p_token_transfer_arm_h4b_spec
      64 75 dst4 initR1 amount txAmount srcBalance dstBalance
      authByte closeFlag h_dst_bal_lt h_amt_ne_0 h_auth_ne_0 h_close_ne_1
  -- Rewrite H3f's post-r0 = signerByte%256 to = authWord so it matches
  -- H4a's pre-r0 = authWord.
  rw [h_r0_eq_r5_at_h4a] at h_h3f
  unfold fullHappyPathCr
  sl_block_iter [h_h1, h_h2, h_h3a, h_h3b, h_h3c, h_h3d,
                 h_h3e, h_h3f, h_h4a, h_h4b]

/-! ## 76-CU terminating triple — happy path + success-exit

Extends `p_token_transfer_full_happy_path_spec` (75 CU, ends in
running state at PC 75) with the program's final `.exit` instruction
at PC 75 (1 step, 0 CU surcharge — `.exit` is not a syscall). Composes
to a `cuTripleAbortsWithinMem 76` claim: the program reaches
`exitCode = some (toU64 0)` (success exit) within 76 steps from PC 0.

The precondition adds `callStackIs []` to the FullHappyPath pre,
expressing that the program is at top-level entry (no caller frame).
This is required because `.exit`'s success branch only fires when the
call stack is empty; with a non-empty stack, `.exit` instead pops a
frame and returns. The `callStackIs []` atom flows through all 10
sub-arm Hoare triples in the universal `R` (the chain never touches
the call stack).

The result is a `cuTripleAbortsWithinMem` (memory-aware aborting
triple) because the chain has memory ops and a region requirement. -/

set_option maxHeartbeats 8000000 in
theorem p_token_transfer_full_happy_path_terminates
    (initR0 initR1 initR2 initR3 initR4 initR5 initR6 initR7 : Nat)
    (disc : Nat)
    -- m1 and m3 are fixed constants 0xa5 (lifted in body); only m2 m4 remain.
    (m2 m4 : Nat)
    (amount : Nat)
    (layoutBound layoutTag : Nat)
    (srcState dstState : Nat)
    (txAmount srcBalance dstBalance : Nat)
    -- Source-mint words src1..src4 are pinned to canonMint*, lifted as `let`s.
    (canonMint1 canonMint2 canonMint3 canonMint4 : Nat)
    (dst1 dst2 dst3 dst4 : Nat)
    (dstMint2 dstMint3 dstMint4 : Nat)
    (authWord signerByte authByte closeFlag : Nat)
    (h_amt_in : amount < 2 ^ 64)
    (h_bound_lt : layoutBound < 2 ^ 64)
    (h_tx_lt : txAmount < 2 ^ 64)
    (h_bal_lt : srcBalance < 2 ^ 64)
    (h_dst_bal_lt : dstBalance < 2 ^ 64)
    (h_canon1_lt : canonMint1 < 2 ^ 64) (h_canon2_lt : canonMint2 < 2 ^ 64)
    (h_canon3_lt : canonMint3 < 2 ^ 64) (h_canon4_lt : canonMint4 < 2 ^ 64)
    (h_d1_lt : dst1 < 2 ^ 64) (h_d2_lt : dst2 < 2 ^ 64)
    (h_d3_lt : dst3 < 2 ^ 64) (h_d4_lt : dst4 < 2 ^ 64)
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
    (h_eq_d1 : dst1 = authWord) (h_eq_d2 : dst2 = dstMint2)
    (h_eq_d3 : dst3 = dstMint3) (h_eq_d4 : dst4 = dstMint4)
    (h_r4_ne : amount ≠ toU64 0x163)
    (h_amt_ne_0 : txAmount ≠ toU64 0)
    (h_auth_ne_0 : authByte % 256 ≠ toU64 0)
    (h_close_ne_1 : closeFlag % 256 ≠ toU64 1) :
    -- Witnesses lifted as `let`s; mirrors the FullHappyPath spec.
    let m1 : Nat := toU64 0xa5
    let m3 : Nat := toU64 0xa5
    let src1 : Nat := canonMint1
    let src2 : Nat := canonMint2
    let src3 : Nat := canonMint3
    let src4 : Nat := canonMint4
    cuTripleAbortsWithinMem 76 0 0
      (fullHappyPathCr.union (CodeReq.singleton 75 .exit))
      -- PRECONDITION: FullHappyPath's pre (in explicit left-grouped
      -- form via outer parens) framed with callStackIs []. The
      -- left-grouping matches the shape produced by
      -- `cuTripleWithinMem_frame_right`, so no extra reshape is needed
      -- inside the proof.
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
  -- The composition: FullHappyPath (75 CU, PC 0→75) seq'd with .exit
  -- at PC 75 (1 CU, success exit). We compose at the
  -- cuTripleAbortsWithinMem level by:
  --   1. Lift FullHappyPath via cuTripleWithinMem_frame_right to add
  --      callStackIs [] to both pre and post.
  --   2. Compose with exit_aborts_spec_cuTriple via the new
  --      cuTripleWithinMem_seq_abort_pure lemma.
  --   3. Reshape pre and post atoms via cuTripleAbortsWithinMem_weaken.
  -- Introduce the type-level `let`s; the FullHappyPath spec has the
  -- same shape so its call below sees the same names.
  intro m1 m3 src1 src2 src3 src4
  have h_full :=
    p_token_transfer_full_happy_path_spec
      initR0 initR1 initR2 initR3 initR4 initR5 initR6 initR7
      disc m2 m4 amount layoutBound layoutTag srcState dstState
      txAmount srcBalance dstBalance
      canonMint1 canonMint2 canonMint3 canonMint4
      dst1 dst2 dst3 dst4
      dstMint2 dstMint3 dstMint4
      authWord signerByte authByte closeFlag
      h_amt_in h_bound_lt h_tx_lt h_bal_lt h_dst_bal_lt
      h_canon1_lt h_canon2_lt h_canon3_lt h_canon4_lt
      h_d1_lt h_d2_lt h_d3_lt h_d4_lt
      h_dm2_lt h_dm3_lt h_dm4_lt h_auth_lt
      h_disc hm2 hm4 h_bound_ge h_tag
      h_src_le h_src_ne h_dst_le h_dst_ne h_src_ne2 h_dst_ne2 h_bal_ge
      h_signer_ne h_r0_eq_r5_at_h4a
      h_eq_d1 h_eq_d2 h_eq_d3 h_eq_d4 h_r4_ne
      h_amt_ne_0 h_auth_ne_0 h_close_ne_1
  -- h_full : cuTripleWithinMem 75 0 0 75 fullHappyPathCr <pre> <post> <rr>
  -- Drop into the unfolded `cuTripleAbortsWithinMem` definition.
  intro F hF fetch hcr s hPF hpc hex h_reg
  -- Split the CodeReq: the union is fullHappyPathCr (PCs 0..74) plus
  -- the singleton exit at PC 75. These are disjoint by PC range.
  have hd_cr : fullHappyPathCr.Disjoint (CodeReq.singleton 75 .exit) := by
    -- fullHappyPathCr covers PCs 0..74; the singleton is at PC 75.
    -- The strict disjointness check would walk the CR tree, but for
    -- our purposes any address either lies in fullHappyPathCr's range
    -- or equals 75 (not both). The sl_disjoint_codereq tactic
    -- mechanises this, but here we go through unfold and decide:
    unfold fullHappyPathCr
    sl_disjoint_codereq
  have hcr_full := CodeReq.SatisfiedBy_of_union_left hcr
  have hcr_exit := CodeReq.SatisfiedBy_of_union_right hd_cr hcr
  -- Lift FullHappyPath to a triple with callStackIs [] framed into
  -- pre/post via cuTripleWithinMem_frame_right. Now
  -- pre = FullHappyPath.pre ** callStackIs []  (matching our 76-CU pre).
  -- post = FullHappyPath.post ** callStackIs [].
  have h_full_framed :=
    cuTripleWithinMem_frame_right (callStackIs []) (pcFree_callStackIs _) h_full
  -- Apply h_full_framed at s with universal R = F.
  obtain ⟨k1, hk1, hpc_mid, hex_mid, hcu1, hQF⟩ :=
    h_full_framed F hF fetch hcr_full s hPF hpc hex h_reg
  -- hQF : ((FullHappyPath.post ** callStackIs []) ** F).holdsFor mid.
  -- Reshape via two assoc.mp's to peel off (.r0 ↦ᵣ toU64 0):
  --   (FullHappyPath.post ** callStackIs []) ** F
  --   ⇒ (((.r0 ↦ᵣ toU64 0) ** PostRest) ** callStackIs []) ** F
  --   assoc.mp: ((.r0 ↦ᵣ toU64 0) ** PostRest) ** (callStackIs [] ** F)
  --   assoc.mp: (.r0 ↦ᵣ toU64 0) ** (PostRest ** (callStackIs [] ** F))
  have hQF_outer := holdsFor_sepConj_assoc.mp hQF
  have hQF' := holdsFor_sepConj_assoc.mp hQF_outer
  -- Extract (executeFn fetch s k1).callStack = [] from hQF_outer's
  -- frame: ((.r0 ↦ᵣ toU64 0) ** PostRest) ** (callStackIs [] ** F).
  have hmid_cs : (executeFn fetch s k1).callStack = [] := by
    obtain ⟨hp_mid, hcompat_mid, h_post_full, h_csF, hd_post_csF, hu_post_csF,
            h_post_sat, h_csF_sat⟩ := hQF_outer
    obtain ⟨h_cs, h_F, hd_cs_F, hu_cs_F, h_cs_pred, h_F_sat⟩ := h_csF_sat
    have h_cs_cs : h_cs.callStack = some [] := by
      rw [show h_cs = PartialState.singletonCallStack [] from h_cs_pred]
      exact PartialState.singletonCallStack_callStack_self
    have h_csF_cs : h_csF.callStack = some [] :=
      hu_cs_F ▸ PartialState.union_callStack_of_left_some h_cs_cs
    -- h_post_full = (.r0 ↦ᵣ toU64 0) ** PostRest holds at it; no callStack atom.
    have h_post_full_cs : h_post_full.callStack = none := by
      rcases hd_post_csF.callStack with h | h
      · exact h
      · rw [h_csF_cs] at h; exact absurd h (by simp)
    have hp_mid_cs : hp_mid.callStack = some [] := by
      rw [← hu_post_csF, PartialState.union_callStack_of_left_none h_post_full_cs]
      exact h_csF_cs
    exact hcompat_mid.callStack [] hp_mid_cs
  -- Invoke exit_aborts_spec with R = PostRest ** (callStackIs [] ** F).
  -- The R is determined by unification with hQF'; the pcFree side
  -- condition is discharged by recursively applying pcFree_sepConj
  -- across all atoms (registers, memory cells, callStackIs, and finally
  -- F whose pc-freeness comes from the universal-R hypothesis hF).
  have exit_result : ∃ k, k ≤ 1 ∧
      (executeFn fetch (executeFn fetch s k1) k).exitCode = some (toU64 0) := by
    refine exit_aborts_spec (toU64 0) 75 _ ?_ fetch hcr_exit
      (executeFn fetch s k1) hQF' hpc_mid hex_mid hmid_cs
    -- pcFree of R: walk pcFree_sepConj across the nested ** structure,
    -- discharging each atom by its pcFree lemma, and the trailing F via hF.
    repeat (first
      | exact hF
      | exact pcFree_callStackIs _
      | exact pcFree_regIs _ _
      | exact pcFree_memByteIs _ _
      | exact pcFree_memU64Is _ _
      | apply pcFree_sepConj)
  obtain ⟨k2, hk2, hex_end⟩ := exit_result
  refine ⟨k1 + k2, ?_, ?_, ?_⟩
  · -- k1 + k2 ≤ 75 + 1 = 76
    have : k1 + k2 ≤ 75 + 1 := Nat.add_le_add hk1 hk2
    omega
  · rw [executeFn_compose]; exact hex_end
  · -- cuConsumed: k1 segment consumes ≤ 0, k2 segment (which is .exit)
    -- consumes ≤ 0 since .exit doesn't bump cuConsumed.
    rw [executeFn_compose]
    rcases Nat.eq_or_lt_of_le hk2 with hk2_eq | hk2_lt
    · subst hk2_eq
      have hfetch_exit : fetch (executeFn fetch s k1).pc = some .exit := by
        rw [hpc_mid]
        exact hcr_exit 75 _ CodeReq.singleton_self
      have hexec1 : executeFn fetch (executeFn fetch s k1) 1
          = step .exit (executeFn fetch s k1) := by
        rw [show (1 : Nat) = 0 + 1 from rfl,
            executeFn_step fetch (executeFn fetch s k1) 0 _ hex_mid hfetch_exit,
            executeFn_zero]
      have hstep_exit : step .exit (executeFn fetch s k1) =
          { (executeFn fetch s k1) with
              exitCode := some ((executeFn fetch s k1).regs.get .r0) } := by
        simp only [step, hmid_cs]
      rw [hexec1, hstep_exit]
      show (executeFn fetch s k1).cuConsumed ≤ s.cuConsumed + 0
      exact hcu1
    · have hk2_0 : k2 = 0 := by omega
      subst hk2_0
      rw [executeFn_zero]
      show (executeFn fetch s k1).cuConsumed ≤ s.cuConsumed + 0
      exact hcu1

end Examples.PTokenTransferFullHappyPath
