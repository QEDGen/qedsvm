/-
  High-level Transfer balance-shift theorems.

  `p_token_transfer_balance_spec`: wraps a flat byte-level triple in
  tokenAcctBalance by definitional unfold. h_asm is supplied by Layer 3b artifacts.

  `p_token_transfer_balance_spec_minimal`: same shape anchored to the synthetic
  MinimalTransferAsm; stated in flat form to avoid the SL bracketing mismatch.

  ## SCOPE — what these theorems do NOT claim (H10)

  Partial-correctness triples over the HAPPY PATH of a TWO-account transfer:
  * HAPPY PATH ONLY — failure paths (insufficient funds, frozen, wrong mint,
    delegate) are out of scope. `_h_sameMint : True` is a no-op placeholder.
  * TWO ACCOUNTS — preserves_supply is (preA-x)+(preB+x)=preA+preB for the
    pair only, NOT total-supply conservation over all token accounts.
  * NO-OVERFLOW EXCLUDED — h_noOverflow carves out the SPL Overflow range.
  * PARTIAL CORRECTNESS — post has exitCode = none (still running), not
    whole-transaction total correctness.
  * TOKEN-TAIL OPAQUE — 93-byte rest blob (L11): frozen/delegate out of scope.
-/

import SVM.Solana.TokenAccount
import SVM.SBPF.InstructionSpecs
import SVM.SBPF.Tactic.SL
import PToken.RefinesTransfer
import PToken.TransferArm.FullHappyPath

namespace Examples.PTokenTransferBalanceSpec

open SVM.SBPF
open SVM.Solana
open SVM.Pubkey
open Memory

/-- High-level Transfer refinement target. Captures the balance shift
    induced by an SPL Token v3 Transfer of `x` units from `ataA` to
    `ataB`, both holding token accounts for the same `mint`.

    Inputs are abstract over the concrete bytecode (`transferCr`,
    `entryPc`, `exitPc`, `nSteps`) and over the setup-prelude state
    the bytecode reads at entry (instruction data, accounts array,
    signer authority). Concrete instantiations supply these from
    Layer 3b artifacts (`transferArmCr`, `callerContPc`, etc.).

    Preconditions:
    * `h_funds`: source has enough balance (`x ≤ preA`).
    * `h_noOverflow`: destination won't overflow u64 (`preB + x < 2^64`).
    * `h_disjoint`: the two ATA byte ranges don't overlap.
    * `h_sameMint`: both ATAs are for the same `mint`. Transfer
      (unchecked variant) does NOT enforce this on-chain — the
      precondition makes the high-level theorem honest about that
      foot-gun. TransferChecked would replace this with a runtime
      check and the precondition would move into a post-condition.
    * `h_restA`, `h_restB`: opaque tail bytes are well-sized.
    * `h_setup`: the rest of the entry-time state (signer authority,
      ix data carrying `x`, accounts pointers, ...) is captured by an
      opaque `setupPre` predicate; the post-state's matching
      `setupPost` is what survives the Transfer with mutations bound.

    Post-condition: `tokenAcctBalance` for `ataA` shifts to
    `preA - x`; for `ataB` shifts to `preB + x`. Mint, owner, and the
    opaque tail bytes flow through unchanged on both accounts. -/
theorem p_token_transfer_balance_spec
    -- Abstract bytecode parameters (filled by downstream Layer 3b
    -- instantiation):
    (nSteps nCu entryPc exitPc : Nat)
    (transferCr : CodeReq)
    -- Token / account parameters:
    (x preA preB : Nat) (mint authA authB : Pubkey)
    (ataA ataB : Nat) (restA restB : ByteArray)
    -- Opaque setup-prelude state:
    (setupPre setupPost : Assertion)
    -- Region requirement (which memory regions the proof relies on):
    (rr : Memory.RegionTable → Prop)
    -- Preconditions:
    (_h_funds      : x ≤ preA)
    (_h_noOverflow : preB + x < 2 ^ 64)
    (_h_disjoint   : ataA + TOKEN_ACCOUNT_SIZE ≤ ataB ∨
                     ataB + TOKEN_ACCOUNT_SIZE ≤ ataA)
    (_h_sameMint   : True)  -- Transfer (unchecked) doesn't enforce; see docstring
    (_h_restA      : restA.size = REST_SIZE)
    (_h_restB      : restB.size = REST_SIZE)
    -- Flat byte-level triple; consumers discharge via Layer 3b artifacts.
    (h_asm : cuTripleWithinMem nSteps nCu entryPc exitPc transferCr
              ( ( ((ataA + MINT_OFF)   ↦Pubkey mint)  **
                  ((ataA + OWNER_OFF)  ↦Pubkey authA) **
                  ((ataA + AMOUNT_OFF) ↦U64    preA)  **
                  ((ataA + REST_OFF)   ↦Bytes  restA) ) **
                ( ((ataB + MINT_OFF)   ↦Pubkey mint)  **
                  ((ataB + OWNER_OFF)  ↦Pubkey authB) **
                  ((ataB + AMOUNT_OFF) ↦U64    preB)  **
                  ((ataB + REST_OFF)   ↦Bytes  restB) ) **
                setupPre )
              ( ( ((ataA + MINT_OFF)   ↦Pubkey mint)  **
                  ((ataA + OWNER_OFF)  ↦Pubkey authA) **
                  ((ataA + AMOUNT_OFF) ↦U64    (preA - x)) **
                  ((ataA + REST_OFF)   ↦Bytes  restA) ) **
                ( ((ataB + MINT_OFF)   ↦Pubkey mint)  **
                  ((ataB + OWNER_OFF)  ↦Pubkey authB) **
                  ((ataB + AMOUNT_OFF) ↦U64    (preB + x)) **
                  ((ataB + REST_OFF)   ↦Bytes  restB) ) **
                setupPost )
              rr) :
    cuTripleWithinMem nSteps nCu entryPc exitPc transferCr
      ( tokenAcctBalance ataA mint authA preA restA **
        tokenAcctBalance ataB mint authB preB restB **
        setupPre )
      ( tokenAcctBalance ataA mint authA (preA - x) restA **
        tokenAcctBalance ataB mint authB (preB + x) restB **
        setupPost )
      rr := by
  unfold tokenAcctBalance
  exact h_asm

/-! ## Arithmetic sanity: two-account supply conservation (H10, happy-path only) -/

theorem p_token_transfer_preserves_supply
    (x preA preB : Nat) (_h_funds : x ≤ preA)
    (_h_noOverflow : preB + x < 2 ^ 64) :
    (preA - x) + (preB + x) = preA + preB := by
  omega

/-! ## Synthetic anchor (flat form, MinimalTransferAsm) -/

theorem p_token_transfer_balance_spec_minimal
    (srcAddr dstAddr amount preA preB vR3Old : Nat)
    (mintSrc mintDst ownerSrc ownerDst : Pubkey)
    (restSrc restDst : ByteArray)
    (h_funds      : amount ≤ preA)
    (h_noOverflow : preB + amount < 2 ^ 64)
    (h_srcBal     : preA < 2 ^ 64)
    (h_dstBal     : preB < 2 ^ 64) :
    cuTripleWithinMem 6 0 0 6 Examples.MinimalTransferAsm.minimalTransferCr
      ((.r1 ↦ᵣ srcAddr) ** (.r2 ↦ᵣ dstAddr) **
       (.r3 ↦ᵣ vR3Old) ** (.r4 ↦ᵣ amount) **
       (srcAddr + MINT_OFF ↦Pubkey mintSrc) **
       (srcAddr + OWNER_OFF ↦Pubkey ownerSrc) **
       (srcAddr + AMOUNT_OFF ↦U64 preA) **
       (srcAddr + REST_OFF ↦Bytes restSrc) **
       (dstAddr + MINT_OFF ↦Pubkey mintDst) **
       (dstAddr + OWNER_OFF ↦Pubkey ownerDst) **
       (dstAddr + AMOUNT_OFF ↦U64 preB) **
       (dstAddr + REST_OFF ↦Bytes restDst))
      ((.r1 ↦ᵣ srcAddr) ** (.r2 ↦ᵣ dstAddr) **
       (.r3 ↦ᵣ preB + amount) ** (.r4 ↦ᵣ amount) **
       (srcAddr + MINT_OFF ↦Pubkey mintSrc) **
       (srcAddr + OWNER_OFF ↦Pubkey ownerSrc) **
       (srcAddr + AMOUNT_OFF ↦U64 preA - amount) **
       (srcAddr + REST_OFF ↦Bytes restSrc) **
       (dstAddr + MINT_OFF ↦Pubkey mintDst) **
       (dstAddr + OWNER_OFF ↦Pubkey ownerDst) **
       (dstAddr + AMOUNT_OFF ↦U64 preB + amount) **
       (dstAddr + REST_OFF ↦Bytes restDst))
      (fun rt =>
        ((rt.containsRange (srcAddr + AMOUNT_OFF) 8 = true ∧
            rt.containsWritable (srcAddr + AMOUNT_OFF) 8 = true) ∧
          rt.containsRange (dstAddr + AMOUNT_OFF) 8 = true) ∧
        rt.containsWritable (dstAddr + AMOUNT_OFF) 8 = true) :=
  Examples.RefinesTokenTransfer.refines_TokenTransfer_minimal_flat
    srcAddr dstAddr amount vR3Old
    { mint := mintSrc, owner := ownerSrc, amount := preA, rest := restSrc }
    { mint := mintDst, owner := ownerDst, amount := preB, rest := restDst }
    h_funds h_noOverflow h_srcBal h_dstBal

/-! ## Wrapped synthetic anchor (tokenAcctBalance form) -/

theorem p_token_transfer_balance_spec_minimal_wrapped
    (srcAddr dstAddr amount preA preB vR3Old : Nat)
    (mintSrc mintDst ownerSrc ownerDst : Pubkey)
    (restSrc restDst : ByteArray)
    (h_funds      : amount ≤ preA)
    (h_noOverflow : preB + amount < 2 ^ 64)
    (h_srcBal     : preA < 2 ^ 64)
    (h_dstBal     : preB < 2 ^ 64) :
    cuTripleWithinMem 6 0 0 6 Examples.MinimalTransferAsm.minimalTransferCr
      ((.r1 ↦ᵣ srcAddr) ** (.r2 ↦ᵣ dstAddr) **
       (.r3 ↦ᵣ vR3Old) ** (.r4 ↦ᵣ amount) **
       tokenAcctBalance srcAddr mintSrc ownerSrc preA restSrc **
       tokenAcctBalance dstAddr mintDst ownerDst preB restDst)
      ((.r1 ↦ᵣ srcAddr) ** (.r2 ↦ᵣ dstAddr) **
       (.r3 ↦ᵣ preB + amount) ** (.r4 ↦ᵣ amount) **
       tokenAcctBalance srcAddr mintSrc ownerSrc (preA - amount) restSrc **
       tokenAcctBalance dstAddr mintDst ownerDst (preB + amount) restDst)
      (fun rt =>
        ((rt.containsRange (srcAddr + AMOUNT_OFF) 8 = true ∧
            rt.containsWritable (srcAddr + AMOUNT_OFF) 8 = true) ∧
          rt.containsRange (dstAddr + AMOUNT_OFF) 8 = true) ∧
        rt.containsWritable (dstAddr + AMOUNT_OFF) 8 = true) :=
  Examples.RefinesTokenTransfer.refines_TokenTransfer_minimal
    srcAddr dstAddr amount vR3Old
    { mint := mintSrc, owner := ownerSrc, amount := preA, rest := restSrc }
    { mint := mintDst, owner := ownerDst, amount := preB, rest := restDst }
    h_funds h_noOverflow h_srcBal h_dstBal

/-! ## Real pinocchio version — FullHappyPath with unsigned-clean balance atoms.

Same flat form as FullHappyPath but with h_funds/h_noOverflow collapsing
wrapSub/wrapAdd to (srcBalance - txAmount)/(dstBalance + txAmount).
tokenAcctBalance-wrapped form deferred (needs framing of ataB OWNER/REST +
signerByte reshape). -/

set_option maxHeartbeats 4000000 in
set_option linter.unusedVariables false in
theorem p_token_transfer_balance_spec_pinocchio
    (initR0 initR1 initR2 initR3 initR4 initR5 initR6 initR7 : Nat)
    (disc : Nat)
    -- m1, m3 are constants 0xa5, lifted as `let`s.
    (m2 m4 : Nat)
    (amount : Nat)
    (layoutBound layoutTag : Nat)
    (srcState dstState : Nat)
    (txAmount srcBalance dstBalance : Nat)
    -- src*/dst* pinned to canonMint*/authWord/dstMint*, lifted as `let`s.
    (canonMint1 canonMint2 canonMint3 canonMint4 : Nat)
    (dstMint2 dstMint3 dstMint4 : Nat)
    (authWord signerByte authByte closeFlag : Nat)
    -- Size bounds (same as FullHappyPath)
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
    -- Sub-arm hypotheses (same as FullHappyPath)
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
    (h_close_ne_1 : closeFlag % 256 ≠ toU64 1)
    -- h_funds enables the wrapSub collapse; linter-disable because omega picks it up implicitly.
    (h_funds      : txAmount ≤ srcBalance)
    (h_noOverflow : dstBalance + txAmount < 2 ^ 64) :
    -- Witnesses as `let`s (mirrors FullHappyPath).
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
    cuTripleWithinMem 75 0 0 75
      Examples.PTokenTransferFullHappyPath.fullHappyPathCr
      -- PRECONDITION (identical to FullHappyPath)
      ((.r0 ↦ᵣ initR0) ** (.r1 ↦ᵣ initR1) ** (.r2 ↦ᵣ initR2) **
        (.r3 ↦ᵣ initR3) ** (.r4 ↦ᵣ initR4) ** (.r5 ↦ᵣ initR5) **
        (.r6 ↦ᵣ initR6) ** (.r7 ↦ᵣ initR7) **
        (effectiveAddr initR1 0 ↦ₘ disc) **
        (effectiveAddr initR1 0x58   ↦U64 m1) **
        (effectiveAddr initR1 0x2910 ↦ₘ m2) **
        (effectiveAddr initR1 0x2960 ↦U64 m3) **
        (effectiveAddr initR1 0x5218 ↦ₘ m4) **
        (effectiveAddr initR1 0x5268 ↦U64 amount) **
        (effectiveAddr (wrapAdd initR1 (Examples.PTokenTransferArmH3aAmountAlign.alignedAmount amount)) 0x7a78 ↦U64 layoutBound) **
        (effectiveAddr (wrapAdd initR1 (Examples.PTokenTransferArmH3aAmountAlign.alignedAmount amount)) 0x7a80 ↦ₘ layoutTag) **
        (effectiveAddr initR1 0xcc   ↦ₘ srcState) **
        (effectiveAddr initR1 0x29d4 ↦ₘ dstState) **
        (effectiveAddr (wrapAdd initR1 (Examples.PTokenTransferArmH3aAmountAlign.alignedAmount amount)) 0x7a81 ↦U64 txAmount) **
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
      -- POSTCONDITION (FullHappyPath except balance atoms in unsigned-clean form)
      ((.r0 ↦ᵣ toU64 0) ** (.r1 ↦ᵣ initR1) ** (.r2 ↦ᵣ txAmount) **
        (.r3 ↦ᵣ closeFlag % 256) ** (.r4 ↦ᵣ authByte % 256) **
        (.r5 ↦ᵣ dstMint4) ** (.r6 ↦ᵣ toU64 0) ** (.r7 ↦ᵣ toU64 4) **
        (effectiveAddr initR1 0 ↦ₘ disc) **
        (effectiveAddr initR1 0x58   ↦U64 m1) **
        (effectiveAddr initR1 0x2910 ↦ₘ m2) **
        (effectiveAddr initR1 0x2960 ↦U64 m3) **
        (effectiveAddr initR1 0x5218 ↦ₘ m4) **
        (effectiveAddr initR1 0x5268 ↦U64 amount) **
        (effectiveAddr (wrapAdd initR1 (Examples.PTokenTransferArmH3aAmountAlign.alignedAmount amount)) 0x7a78 ↦U64 layoutBound) **
        (effectiveAddr (wrapAdd initR1 (Examples.PTokenTransferArmH3aAmountAlign.alignedAmount amount)) 0x7a80 ↦ₘ layoutTag) **
        (effectiveAddr initR1 0xcc   ↦ₘ srcState) **
        (effectiveAddr initR1 0x29d4 ↦ₘ dstState) **
        (effectiveAddr (wrapAdd initR1 (Examples.PTokenTransferArmH3aAmountAlign.alignedAmount amount)) 0x7a81 ↦U64 txAmount) **
        -- Balance shift — unsigned-clean form (the HEADLINE claim):
        (effectiveAddr initR1 0xa0   ↦U64 (srcBalance - txAmount)) **
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
        (effectiveAddr initR1 0x29a8 ↦U64 (dstBalance + txAmount)) **
        (effectiveAddr initR1 0xcd   ↦ₘ closeFlag))
      (fun rt =>
        ((((((((rt.containsRange (effectiveAddr initR1 0) 1 = true ∧
                    ((rt.containsRange (effectiveAddr initR1 88) 8 = true ∧
                          rt.containsRange (effectiveAddr initR1 10512) 1 = true) ∧
                        rt.containsRange (effectiveAddr initR1 10592) 8 = true) ∧
                      rt.containsRange (effectiveAddr initR1 21016) 1 = true) ∧
                  rt.containsRange (effectiveAddr initR1 21096) 8 = true) ∧
                rt.containsRange (effectiveAddr (wrapAdd initR1 (Examples.PTokenTransferArmH3aAmountAlign.alignedAmount amount)) 31352) 8 = true ∧
                  rt.containsRange (effectiveAddr (wrapAdd initR1 (Examples.PTokenTransferArmH3aAmountAlign.alignedAmount amount)) 31360) 1 = true) ∧
              rt.containsRange (effectiveAddr initR1 204) 1 = true ∧
                rt.containsRange (effectiveAddr initR1 10708) 1 = true) ∧
            rt.containsRange (effectiveAddr (wrapAdd initR1 (Examples.PTokenTransferArmH3aAmountAlign.alignedAmount amount)) 31361) 8 = true ∧
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
  intro m1 m3 src1 src2 src3 src4 dst1 dst2 dst3 dst4
  have h_full :=
    Examples.PTokenTransferFullHappyPath.p_token_transfer_full_happy_path_spec
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
  -- Collapse wrapSub/wrapAdd to unsigned form (mirrors RefinesTransfer.lean h_wsub/h_wadd).
  have h_tx_lt' : txAmount < U64_MODULUS := by unfold U64_MODULUS; exact h_tx_lt
  have h_bal_lt' : srcBalance < U64_MODULUS := by unfold U64_MODULUS; exact h_bal_lt
  have h_noOverflow' : dstBalance + txAmount < U64_MODULUS := by
    unfold U64_MODULUS; exact h_noOverflow
  have h_wsub : wrapSub srcBalance txAmount = srcBalance - txAmount := by
    show (srcBalance + U64_MODULUS - txAmount % U64_MODULUS) % U64_MODULUS =
         srcBalance - txAmount
    rw [Nat.mod_eq_of_lt h_tx_lt']
    have h_rewrite : srcBalance + U64_MODULUS - txAmount =
                     (srcBalance - txAmount) + U64_MODULUS := by omega
    rw [h_rewrite, Nat.add_mod_right,
        Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) h_bal_lt')]
  have h_wadd : wrapAdd dstBalance txAmount = dstBalance + txAmount := by
    show (dstBalance + txAmount) % U64_MODULUS = dstBalance + txAmount
    exact Nat.mod_eq_of_lt h_noOverflow'
  rw [h_wsub, h_wadd] at h_full
  exact h_full

end Examples.PTokenTransferBalanceSpec
