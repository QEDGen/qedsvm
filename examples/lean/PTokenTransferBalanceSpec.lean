/-
  High-level Transfer refinement target — *statement only*.

  This is the qedsvm-side artifact for the conversation question
  "can we describe the spec of a Transfer at a higher level?": a
  `tokenAcctBalance`-shifting Hoare triple over the full p-token
  Transfer happy path.

  The theorem body is `sorry`. The Layer 3b grind (currently 52/76 CU
  in `PTokenTransferArmTwoCallsExt`) will close out the full
  bytecode-level triple `p_token_transfer_arm_full_spec`; once that
  lands, the body here is a thin refinement — unfold `tokenAcctBalance`
  on both sides, apply the full Layer 3b triple, discharge the
  arithmetic shift via `omega`, frame the unchanged `mint` / `owner` /
  `rest` atoms.

  Per the Direction-A MIR design (qedgen issue #66), this theorem is
  the canonical lowering target for a `Stmt::TokenTransfer { from, to,
  amount }` MIR node — `runMir`-of-`TokenTransfer` IS exactly this
  predicate shift. Per-program qedgen-generated proofs will eventually
  cite this lemma directly.
-/

import Svm.Solana.TokenAccount
import Svm.SBPF.InstructionSpecs
import Svm.SBPF.SLTactic

namespace Examples.PTokenTransferBalanceSpec

open Svm.SBPF
open Svm.Solana
open Svm.Account

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

end Examples.PTokenTransferBalanceSpec
