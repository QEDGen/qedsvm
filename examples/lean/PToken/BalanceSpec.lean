/-
  High-level Transfer refinement target — two theorems.

  ## `p_token_transfer_balance_spec` — REAL pinocchio Transfer (sorry'd)

  A `tokenAcctBalance`-shifting Hoare triple over the full p-token
  Transfer happy path. Body is `sorry` and remains so pending two
  prerequisites:

  1. Layer 3b closes the remaining 24 CU of the p-token Transfer
     happy path (the balance-mutation slice — the existing
     PTokenTransferArm* artifacts cover 52/76 CU of FP-softfloat
     plumbing but don't touch TokenAccount fields).
  2. A follow-up lemma shows pinocchio's emitted asm matches the
     `MinimalTransferAsm` codegen pattern (or is a documented
     variant) — at which point this theorem follows by reusing the
     refinement bridge below.

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

namespace Examples.PTokenTransferBalanceSpec

open SVM.SBPF
open SVM.Solana
open SVM.Pubkey

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
    (nSteps entryPc exitPc : Nat)
    (transferCr : CodeReq)
    -- Token / account parameters:
    (x preA preB : Nat) (mint authA authB : Pubkey)
    (ataA ataB : Nat) (restA restB : ByteArray)
    -- Opaque setup-prelude state:
    (setupPre setupPost : Assertion)
    -- Region requirement (which memory regions the proof relies on):
    (rr : Memory.RegionTable → Prop)
    -- Preconditions:
    (h_funds      : x ≤ preA)
    (h_noOverflow : preB + x < 2 ^ 64)
    (h_disjoint   : ataA + TOKEN_ACCOUNT_SIZE ≤ ataB ∨
                    ataB + TOKEN_ACCOUNT_SIZE ≤ ataA)
    (h_sameMint   : True)  -- Transfer (unchecked) doesn't enforce; see docstring
    (h_restA      : restA.size = REST_SIZE)
    (h_restB      : restB.size = REST_SIZE) :
    cuTripleWithinMem nSteps entryPc exitPc transferCr
      ( tokenAcctBalance ataA mint authA preA restA **
        tokenAcctBalance ataB mint authB preB restB **
        setupPre )
      ( tokenAcctBalance ataA mint authA (preA - x) restA **
        tokenAcctBalance ataB mint authB (preB + x) restB **
        setupPost )
      rr := by
  sorry

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
    cuTripleWithinMem 6 0 6 Examples.MinimalTransferAsm.minimalTransferCr
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

end Examples.PTokenTransferBalanceSpec
