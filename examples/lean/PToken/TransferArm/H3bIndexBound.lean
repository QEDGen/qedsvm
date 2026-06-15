/-
  L3b H3b: 6-insn index-bound check (bytes 0x8708-0x8730, p-token@v1.0.0-rc.1).

  Continues H3a (r3=alignedAmount, r4=amount). Computes r2 = input+alignedAmount,
  loads layout markers at +0x7a78/+0x7a80, validates via two not-taken jumps (cell≥9, byte=3).
  6 CU, pc → 6. Two if-collapses: jlt-NT (layoutBound≥9), jne-NT (layoutTag%256=3).
-/

import PToken.TransferArm.H3aAmountAlign
import SVM.SBPF.InstructionSpecs
import SVM.SBPF.Tactic.SL
import SVM.SBPF.Macros

namespace Examples.PTokenTransferArmH3bIndexBound

open SVM.SBPF
open Memory
open Examples.PTokenTransferArmH3aAmountAlign (alignedAmount)

/-- H3b CodeReq; error-PC targets are synthetic (if-collapses make them irrelevant). -/
def h3bErrPc : Nat := 100

def h3bCr (base : Nat) : CodeReq :=
  cr![ base + 0 ↦ .mov64 .r2 (.reg .r1),
       base + 1 ↦ .add64 .r2 (.reg .r3),
       base + 2 ↦ .ldx .dword .r3 .r2 0x7a78,
       base + 3 ↦ .jlt .r3 (.imm 9) h3bErrPc,
       base + 4 ↦ .ldx .byte .r3 .r2 0x7a80,
       base + 5 ↦ .jne .r3 (.imm 3) h3bErrPc ]

theorem p_token_transfer_arm_h3b_spec
    (base : Nat)
    (initR1 initR2 amount : Nat)
    (layoutBound : Nat)  -- cell at [r2+0x7a78], must be ≥ 9
    (layoutTag : Nat)    -- byte at [r2+0x7a80], must be 3 mod 256
    (h_bound_lt : layoutBound < 2 ^ 64)
    (h_bound_ge : layoutBound ≥ 9)
    (h_tag : layoutTag % 256 = toU64 3) :
    let baseAddr := wrapAdd initR1 (alignedAmount amount)
    cuTripleWithinMem 6 0 base (base + 6) (h3bCr base)
      ((.r1 ↦ᵣ initR1) ** (.r2 ↦ᵣ initR2) **
        (.r3 ↦ᵣ alignedAmount amount) **
        (effectiveAddr baseAddr 0x7a78 ↦U64 layoutBound) **
        (effectiveAddr baseAddr 0x7a80 ↦ₘ layoutTag))
      ((.r1 ↦ᵣ initR1) ** (.r2 ↦ᵣ baseAddr) **
        (.r3 ↦ᵣ layoutTag % 256) **
        (effectiveAddr baseAddr 0x7a78 ↦U64 layoutBound) **
        (effectiveAddr baseAddr 0x7a80 ↦ₘ layoutTag))
      (fun rt =>
        rt.containsRange (effectiveAddr baseAddr 0x7a78) 8 = true ∧
        rt.containsRange (effectiveAddr baseAddr 0x7a80) 1 = true) := by
  intro baseAddr
  have h0 := mov64_reg_spec .r2 .r1 initR2 initR1 (base + 0) (by decide)
  have h1 := add64_reg_spec .r2 .r3 initR1 (alignedAmount amount) (base + 1) (by decide)
  have h2 := ldxdw_spec .r3 .r2 0x7a78 (alignedAmount amount) baseAddr
                        layoutBound (base + 2) (by decide) h_bound_lt
  have h3 := jlt_imm_spec .r3 9 layoutBound (base + 3) h3bErrPc
  have h4 := ldxb_spec .r3 .r2 0x7a80 layoutBound baseAddr layoutTag (base + 4) (by decide)
  have h5 := jne_imm_spec .r3 3 (layoutTag % 256) (base + 5) h3bErrPc
  -- Collapse jlt (layoutBound ≥ 9).
  rw [show (if layoutBound < toU64 9 then h3bErrPc else (base + 3) + 1) = base + 4 from by
        have hno : ¬ (layoutBound < toU64 9) := by
          show ¬ (layoutBound < 9); omega
        rw [if_neg hno]] at h3
  -- Collapse jne (layoutTag % 256 = 3).
  rw [show (if (layoutTag % 256) ≠ toU64 3 then h3bErrPc else (base + 5) + 1) = base + 6 from by
        rw [h_tag]; simp] at h5
  unfold h3bCr
  sl_block_iter [h0, h1, h2, h3, h4, h5]

end Examples.PTokenTransferArmH3bIndexBound
