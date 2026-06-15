/-
  L3b H1: 2-insn entry dispatch at bytes 0x828-0x830 (p-token@v1.0.0-rc.1).

  Reads discriminator byte into r2 (ldxb), then jeq on `disc % 256 = 3` (Transfer).
  Happy path: 2 CU, pc → dispatchTarget. H1-H... re-targets the chain after
  trace investigation confirmed L1-L6 covers the off-path FP-precision guard.

  `dispatchTarget` = synthetic local PC `1+1+0x6d`; glue consumers re-instantiate
  at the actual absolute target (lddw byte-vs-PC counts differ in real image).
-/

import SVM.SBPF.InstructionSpecs
import SVM.SBPF.Tactic.SL
import SVM.SBPF.Macros

namespace Examples.PTokenTransferArmDispatch

open SVM.SBPF
open Memory

/-- Synthetic local target = `1+1+0x6d` (PC+1+offset); real image PC differs. -/
def dispatchTarget : Nat := 0x6f

/-- CodeReq for the 2-insn dispatch; jeq target supplied externally (not shifted). -/
def transferArmDispatchCr (base : Nat) (target : Nat) : CodeReq :=
  cr![ base + 0 ↦ .ldx .byte .r2 .r1 0,
       base + 1 ↦ .jeq .r2 (.imm 3) target ]

theorem p_token_transfer_arm_dispatch_spec
    (base : Nat) (target : Nat)
    (initR1 initR2 disc : Nat)
    (h_disc : disc % 256 = toU64 3) :
    cuTripleWithinMem 2 0 base target (transferArmDispatchCr base target)
      ((.r1 ↦ᵣ initR1) ** (.r2 ↦ᵣ initR2) **
        (effectiveAddr initR1 0 ↦ₘ disc))
      ((.r1 ↦ᵣ initR1) ** (.r2 ↦ᵣ disc % 256) **
        (effectiveAddr initR1 0 ↦ₘ disc))
      (fun rt => rt.containsRange (effectiveAddr initR1 0) 1 = true) := by
  have h0 := ldxb_spec .r2 .r1 0 initR2 initR1 disc (base + 0) (by decide)
  have h1 := jeq_imm_spec .r2 3 (disc % 256) (base + 1) target
  -- h_disc collapses the jeq: target taken.
  rw [show (if (disc % 256) = toU64 3 then target else (base + 1) + 1) = target
        from by rw [h_disc]; simp] at h1
  unfold transferArmDispatchCr
  sl_block_iter [h0, h1]

end Examples.PTokenTransferArmDispatch
