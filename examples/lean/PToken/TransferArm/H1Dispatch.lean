/-
  Layer 3b artifact (happy-path chain, H1): Hoare triple over the
  2-instruction p-token **entry dispatch** at bytes 0x828-0x830 of
  `qedsvm-rs/tests/fixtures/p_token.so` (release `p-token@v1.0.0-rc.1`).

  This is the first arm in a re-targeted happy-path chain. The earlier
  L1-L6 series (`L1Setup` ... `L6FarJump`) proves the FP-precision
  validation path the pinocchio compiler emits behind a precision
  guard — confirmed off-path for `Transfer { amount: 250 }` by
  trace investigation 2026-05-25. H1-H... covers the PCs actually
  visited by the standard fixture.

  Trace anchor: `STEP pc=000000c6` (ldxb reads `0x03` into r2) followed
  by `STEP pc=000000c7` (jeq matches, jumps to pc=00000130 — the magic-
  byte account-layout cascade). The 2 CU here are the entire dispatch.

  The 2 instructions, lifted from `qedsvm-rs/tests/fixtures/p_token.disasm`:

  ```
  828: 71 12 00 00 ...      ldxb r2, [r1 + 0x0]            ← read discriminator
  830: 15 02 6d 00 03 .. .. jeq  r2, 0x3, +0x6d            ← Transfer? jump to validation
  ```

  Semantics: pinocchio's entrypoint reads the instruction discriminator
  byte from the first byte of its input region (r1 points at the
  Solana program input buffer; offset 0 holds the discriminator after
  pinocchio's zero-copy layout), then dispatches on `3 = Transfer`. The
  happy path under the hypothesis "discriminator = 3" lands at the
  jeq target (locally `dispatchTarget`).

  Spec: given `disc % 256 = toU64 3` in the precondition, executes
  2 CU advancing PC 0 → `dispatchTarget`, leaving r1 and the input
  byte preserved and r2 = `disc % 256`.

  PC layout mirrors `PTokenValidationPrelude.lean`'s convention: the
  jeq target value `1 + 1 + 0x6d = 0x6f` is a synthetic local PC
  capturing the disasm offset field for visual link, not an absolute
  image PC (real-image lddw counts diverge between byte and PC arithmetic).
  Glue consumers re-instantiate at the actual absolute target.
-/

import SVM.SBPF.InstructionSpecs
import SVM.SBPF.Tactic.SL
import SVM.SBPF.Macros

namespace Examples.PTokenTransferArmDispatch

open SVM.SBPF
open Memory

/-- Synthetic local PC for the jeq target on the Transfer dispatch.
    Computed as `1 + 1 + 0x6d` (PC of jeq + 1 + the jeq's offset field).
    Real image PC differs because of lddw byte-vs-PC counts; downstream
    glue picks the absolute value. -/
def dispatchTarget : Nat := 0x6f

/-- The CodeReq for the 2-instruction Transfer-arm dispatch. -/
def transferArmDispatchCr : CodeReq :=
  (CodeReq.singleton 0 (.ldx .byte .r2 .r1 0)).union
    (CodeReq.singleton 1 (.jeq .r2 (.imm 3) dispatchTarget))

theorem p_token_transfer_arm_dispatch_spec
    (initR1 initR2 disc : Nat)
    (h_disc : disc % 256 = toU64 3) :
    cuTripleWithinMem 2 0 0 dispatchTarget transferArmDispatchCr
      ((.r1 ↦ᵣ initR1) ** (.r2 ↦ᵣ initR2) **
        (effectiveAddr initR1 0 ↦ₘ disc))
      ((.r1 ↦ᵣ initR1) ** (.r2 ↦ᵣ disc % 256) **
        (effectiveAddr initR1 0 ↦ₘ disc))
      (fun rt => rt.containsRange (effectiveAddr initR1 0) 1 = true) := by
  -- h0: ldxb reads the discriminator byte → r2 := disc % 256.
  have h0 := ldxb_spec .r2 .r1 0 initR2 initR1 disc 0 (by decide)
  -- h1: jeq's exit PC is `if disc % 256 = toU64 3 then dispatchTarget else 1+1`.
  have h1 := jeq_imm_spec .r2 3 (disc % 256) 1 dispatchTarget
  -- Collapse the conditional: under h_disc the jeq is taken.
  rw [show (if (disc % 256) = toU64 3 then dispatchTarget else 1 + 1) = dispatchTarget
        from by rw [h_disc]; simp] at h1
  sl_block_iter [h0, h1]

end Examples.PTokenTransferArmDispatch
