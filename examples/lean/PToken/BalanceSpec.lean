/-
  High-level Transfer refinement target — two theorems.

  ## `p_token_transfer_balance_spec` — `tokenAcctBalance` lifting lemma (PROVEN)

  Lifts an asm-level Hoare triple in the **flat byte-level form**
  (each TokenAccount field spelled out as a separate `↦Pubkey` /
  `↦U64` / `↦Bytes` atom) to the `tokenAcctBalance`-wrapped form
  downstream consumers use. The lift is a definitional unfolding
  — `tokenAcctBalance` is defined as that 4-atom right-fold, so
  the wrapped post follows from the unfolded post by `unfold`.

  Practical instantiations supply `h_asm` via Layer 3b artifacts:
  - `MinimalTransferAsm` (synthetic 6-insn anchor, proven via
    `Examples.RefinesTokenTransfer.refines_TokenTransfer_minimal_flat`).
    See `p_token_transfer_balance_spec_minimal` below for the
    discharge.
  - `Examples.PTokenTransferFullHappyPath.p_token_transfer_full_happy_path_spec`
    (real pinocchio 75-CU happy path, proven). The flat atoms produced
    by that theorem live at offsets `[r1+0xa0]` (source amount) and
    `[r1+0x29a8]` (destination amount) — choose `ataA := initR1 + 0x60`
    and `ataB := initR1 + 0x2968` to align `ataA+AMOUNT_OFF` /
    `ataB+AMOUNT_OFF` with those concrete offsets. Bridging the
    `↦Pubkey` mint/owner atoms to the 4-`↦U64` form the chain
    uses needs a `Pubkey ↔ (U64×4)` reshape lemma — deferred until
    a downstream consumer demands it.

  ## `p_token_transfer_balance_spec_minimal` — synthetic anchor (PROVEN)

  Same theorem shape, but for the synthetic `MinimalTransferAsm`
  fixture (the refinement-pilot's asm anchor). Cites
  `Examples.RefinesTokenTransfer.refines_TokenTransfer_minimal_flat`.
  Stated in the **flat** byte-level form (4 atoms per account
  spelled out) — consistent with the Layer-3b artifact style and
  avoids the SL bracketing mismatch that a `tokenAcctBalance`-wrapped
  form would introduce. The wrapped form is the eventual user-facing
  shape; it's deferred until a downstream theorem actually consumes
  it (at which point the wrapper lift is worth writing).

  Per the Direction-A MIR design (qedgen issue #66), this theorem is
  the canonical lowering target for a `Stmt::TokenTransfer { from, to,
  amount }` MIR node — `runMir`-of-`TokenTransfer` IS exactly this
  predicate shift. The synthetic-anchor version is the first proven
  instance of that lowering.
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
    -- Asm-level triple in tokenAcctBalance-unfolded form. Practical
    -- consumers discharge via Layer 3b artifacts; see file docstring
    -- for `MinimalTransferAsm` and `FullHappyPath` discharge routes.
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

/-! ## Sanity check — high-level effect is balance-preserving.

    Pure arithmetic property, proven directly. Used downstream to
    establish that the spec doesn't accidentally create or destroy
    tokens. Composes with `p_token_transfer_balance_spec` to derive
    the standard "total supply invariant" theorem. -/

theorem p_token_transfer_preserves_supply
    (x preA preB : Nat) (_h_funds : x ≤ preA)
    (_h_noOverflow : preB + x < 2 ^ 64) :
    (preA - x) + (preB + x) = preA + preB := by
  omega

/-! ## Synthetic-anchor version — proven via the refinement bridge.

This is the first proven instance of the `tokenAcctBalance`-shifting
shape that `p_token_transfer_balance_spec` aspires to. Anchored to
the synthetic `MinimalTransferAsm` codegen pattern (Tasks 8-10 of the
refinement pilot) rather than real pinocchio bytecode.

Stated in the flat byte-level form (one big `**` chain per account,
not wrapped in `tokenAcctBalance`) to match the shape
`Examples.RefinesTokenTransfer.refines_TokenTransfer_minimal_flat`
ships in — see that file's docstring for the bracketing-mismatch
rationale. The `tokenAcctBalance`-wrapped variant is the eventual
user-facing form; it follows by a sepConj-assoc reshape on top of
this theorem when downstream demand justifies the wrapper. -/

theorem p_token_transfer_balance_spec_minimal
    -- Token / account parameters:
    (srcAddr dstAddr amount preA preB vR3Old : Nat)
    (mintSrc mintDst ownerSrc ownerDst : Pubkey)
    (restSrc restDst : ByteArray)
    -- Preconditions matching the abstract `tokenTransfer_spec`:
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

/-! ## Wrapped synthetic anchor — the user-facing shape

Companion to `p_token_transfer_balance_spec_minimal` that states pre/
post via `tokenAcctBalance` (the wrapper SL atom) instead of the flat
4-atoms-per-account form. Discharges through
`Examples.RefinesTokenTransfer.refines_TokenTransfer_minimal`, which
in turn lifts the flat triple via three `sepConj_assoc` applications
inside the wrap iff.

This is the synthetic counterpart to the deferred pinocchio-side
wrap. Demonstrates that the lift mechanism works end-to-end on an
asm anchor, ahead of the more involved pinocchio reshape work. -/

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

/-! ## Real-pinocchio version — proven via the FullHappyPath chain.

This is the second proven instance of the balance-shifting shape, this time
anchored to the **real pinocchio p-token Transfer happy path** (75 CU, 10
sub-arm chain) rather than the synthetic `MinimalTransferAsm`. Cites
`Examples.PTokenTransferFullHappyPath.p_token_transfer_full_happy_path_spec`.

The statement is in the **same flat byte-level form** as the FullHappyPath
artifact: 38 atoms (8 registers + 30 memory cells) in the right-folded
chain. The only change from FullHappyPath's post is that the two balance
atoms

    [r1 + 0xa0]   ↦U64 wrapSub srcBalance txAmount
    [r1 + 0x29a8] ↦U64 wrapAdd dstBalance txAmount

are exposed in their unsigned-clean form

    [r1 + 0xa0]   ↦U64 (srcBalance - txAmount)
    [r1 + 0x29a8] ↦U64 (dstBalance + txAmount)

under the additional preconditions `h_funds : txAmount ≤ srcBalance` (so
`wrapSub` doesn't underflow) and `h_noOverflow : dstBalance + txAmount <
2^64` (so `wrapAdd` doesn't wrap). The unsigned form is what downstream
consumers (e.g. the MIR `TokenTransfer` lowering, Direction A) want; the
wrap form is what the bytecode literally produces.

The `tokenAcctBalance`-wrapped form (mirroring `p_token_transfer_balance_spec`'s
signature with `ataA := initR1 + 0x60`, `ataB := initR1 + 0x2968`) is **not**
established here. Getting there requires framing in two missing atoms
(`ataB + OWNER_OFF = initR1 + 0x2988` and `ataB + REST_OFF = initR1 +
0x29b0`) plus reshaping the 1-byte `signerByte` (currently at
`initR1 + 0xa8`) into a 93-byte `↦Bytes` claim. Both gaps need
non-trivial frame and SL reshape work; deferred until a downstream
consumer demands the wrap. -/

set_option maxHeartbeats 4000000 in
set_option linter.unusedVariables false in
theorem p_token_transfer_balance_spec_pinocchio
    (initR0 initR1 initR2 initR3 initR4 initR5 initR6 initR7 : Nat)
    (disc : Nat)
    (m1 m3 : Nat) (m2 m4 : Nat)
    (amount : Nat)
    (layoutBound layoutTag : Nat)
    (srcState dstState : Nat)
    (txAmount srcBalance dstBalance : Nat)
    (canonMint1 canonMint2 canonMint3 canonMint4 : Nat)
    (src1 src2 src3 src4 : Nat)
    (dst1 dst2 dst3 dst4 : Nat)
    (dstMint2 dstMint3 dstMint4 : Nat)
    (authWord signerByte authByte closeFlag : Nat)
    -- Size hypotheses (same as FullHappyPath)
    (h_m1_lt : m1 < 2 ^ 64)
    (h_m3_lt : m3 < 2 ^ 64)
    (h_amt_in : amount < 2 ^ 64)
    (h_bound_lt : layoutBound < 2 ^ 64)
    (h_tx_lt : txAmount < 2 ^ 64)
    (h_bal_lt : srcBalance < 2 ^ 64)
    (h_dst_bal_lt : dstBalance < 2 ^ 64)
    (h_canon1_lt : canonMint1 < 2 ^ 64) (h_canon2_lt : canonMint2 < 2 ^ 64)
    (h_canon3_lt : canonMint3 < 2 ^ 64) (h_canon4_lt : canonMint4 < 2 ^ 64)
    (h_s1_lt : src1 < 2 ^ 64) (h_s2_lt : src2 < 2 ^ 64)
    (h_s3_lt : src3 < 2 ^ 64) (h_s4_lt : src4 < 2 ^ 64)
    (h_d1_lt : dst1 < 2 ^ 64) (h_d2_lt : dst2 < 2 ^ 64)
    (h_d3_lt : dst3 < 2 ^ 64) (h_d4_lt : dst4 < 2 ^ 64)
    (h_dm2_lt : dstMint2 < 2 ^ 64) (h_dm3_lt : dstMint3 < 2 ^ 64)
    (h_dm4_lt : dstMint4 < 2 ^ 64)
    (h_auth_lt : authWord < 2 ^ 64)
    -- Sub-arm structural hypotheses (same as FullHappyPath)
    (h_disc : disc % 256 = toU64 3)
    (hm1 : m1 = toU64 0xa5)
    (hm2 : m2 % 256 = toU64 0xff)
    (hm3 : m3 = toU64 0xa5)
    (hm4 : m4 % 256 = toU64 0xff)
    (h_bound_ge : layoutBound ≥ 9)
    (h_tag : layoutTag % 256 = toU64 3)
    (h_src_le : srcState % 256 ≤ 2) (h_src_ne : srcState % 256 ≠ 0)
    (h_dst_le : dstState % 256 ≤ 2) (h_dst_ne : dstState % 256 ≠ 0)
    (h_src_ne2 : srcState % 256 ≠ 2) (h_dst_ne2 : dstState % 256 ≠ 2)
    (h_bal_ge : srcBalance ≥ txAmount)
    (h_eq_s1 : src1 = canonMint1) (h_eq_s2 : src2 = canonMint2)
    (h_eq_s3 : src3 = canonMint3) (h_eq_s4 : src4 = canonMint4)
    (h_signer_ne : signerByte % 256 ≠ toU64 1)
    (h_r0_eq_r5_at_h4a : signerByte % 256 = authWord)
    (h_eq_d1 : dst1 = authWord) (h_eq_d2 : dst2 = dstMint2)
    (h_eq_d3 : dst3 = dstMint3) (h_eq_d4 : dst4 = dstMint4)
    (h_r4_ne : amount ≠ toU64 0x163)
    (h_amt_ne_0 : txAmount ≠ toU64 0)
    (h_auth_ne_0 : authByte % 256 ≠ toU64 0)
    (h_close_ne_1 : closeFlag % 256 ≠ toU64 1)
    -- High-level Transfer preconditions enabling the unsigned-clean rewrite:
    -- `h_funds` is picked up by `omega` inside `h_wsub` to prove the wrap
    -- collapse; the Lean linter doesn't see omega's auto-pickup, hence the
    -- linter-disable below.
    (h_funds      : txAmount ≤ srcBalance)
    (h_noOverflow : dstBalance + txAmount < 2 ^ 64) :
    cuTripleWithinMem 75 0 0 75
      Examples.PTokenTransferFullHappyPath.fullHappyPathCr
      -- PRECONDITION — identical to FullHappyPath
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
      -- POSTCONDITION — identical to FullHappyPath EXCEPT the two
      -- balance atoms are stated in unsigned-clean form.
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
  -- Cite the proven FullHappyPath triple.
  have h_full :=
    Examples.PTokenTransferFullHappyPath.p_token_transfer_full_happy_path_spec
      initR0 initR1 initR2 initR3 initR4 initR5 initR6 initR7
      disc m1 m3 m2 m4 amount layoutBound layoutTag srcState dstState
      txAmount srcBalance dstBalance
      canonMint1 canonMint2 canonMint3 canonMint4
      src1 src2 src3 src4
      dst1 dst2 dst3 dst4
      dstMint2 dstMint3 dstMint4
      authWord signerByte authByte closeFlag
      h_m1_lt h_m3_lt h_amt_in h_bound_lt h_tx_lt h_bal_lt h_dst_bal_lt
      h_canon1_lt h_canon2_lt h_canon3_lt h_canon4_lt
      h_s1_lt h_s2_lt h_s3_lt h_s4_lt
      h_d1_lt h_d2_lt h_d3_lt h_d4_lt
      h_dm2_lt h_dm3_lt h_dm4_lt h_auth_lt
      h_disc hm1 hm2 hm3 hm4 h_bound_ge h_tag
      h_src_le h_src_ne h_dst_le h_dst_ne h_src_ne2 h_dst_ne2 h_bal_ge
      h_eq_s1 h_eq_s2 h_eq_s3 h_eq_s4 h_signer_ne h_r0_eq_r5_at_h4a
      h_eq_d1 h_eq_d2 h_eq_d3 h_eq_d4 h_r4_ne
      h_amt_ne_0 h_auth_ne_0 h_close_ne_1
  -- Wrap-arithmetic collapse to unsigned form. Mirrors the
  -- `h_wsub`/`h_wadd` pattern from RefinesTransfer.lean L86-100.
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
