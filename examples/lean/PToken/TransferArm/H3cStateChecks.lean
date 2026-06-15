/-
  Layer 3b H3c: 8 CU triple (bytes 0x8738-0x8770, p_token.so).
  Sets r6=3, r7=0; loads src/dst state bytes and validates each ∈ {1,2} (not 0, not >2).
  4 conditional-collapse: 2 jgt-NT + 2 jeq-NT.
-/

import PToken.TransferArm.H3bIndexBound
import SVM.SBPF.InstructionSpecs
import SVM.SBPF.Tactic.SL
import SVM.SBPF.Macros

namespace Examples.PTokenTransferArmH3cStateChecks

open SVM.SBPF
open Memory

def h3cErrPc : Nat := 200

def h3cCr (base : Nat) : CodeReq :=
  cr![ base + 0 ↦ .mov64 .r6 (.imm 3),
       base + 1 ↦ .mov64 .r7 (.imm 0),
       base + 2 ↦ .ldx .byte .r3 .r1 0xcc,
       base + 3 ↦ .jgt .r3 (.imm 2) h3cErrPc,
       base + 4 ↦ .jeq .r3 (.imm 0) h3cErrPc,
       base + 5 ↦ .ldx .byte .r5 .r1 0x29d4,
       base + 6 ↦ .jgt .r5 (.imm 2) h3cErrPc,
       base + 7 ↦ .jeq .r5 (.imm 0) h3cErrPc ]

theorem p_token_transfer_arm_h3c_spec
    (base : Nat)
    (initR1 initR3 initR5 initR6 initR7 : Nat)
    (srcState dstState : Nat)
    (h_src_le : srcState % 256 ≤ 2)
    (h_src_ne : srcState % 256 ≠ 0)
    (h_dst_le : dstState % 256 ≤ 2)
    (h_dst_ne : dstState % 256 ≠ 0) :
    cuTripleWithinMem 8 0 base (base + 8) (h3cCr base)
      ((.r1 ↦ᵣ initR1) ** (.r3 ↦ᵣ initR3) ** (.r5 ↦ᵣ initR5) **
        (.r6 ↦ᵣ initR6) ** (.r7 ↦ᵣ initR7) **
        (effectiveAddr initR1 0xcc ↦ₘ srcState) **
        (effectiveAddr initR1 0x29d4 ↦ₘ dstState))
      ((.r1 ↦ᵣ initR1) ** (.r3 ↦ᵣ srcState % 256) **
        (.r5 ↦ᵣ dstState % 256) **
        (.r6 ↦ᵣ toU64 3) ** (.r7 ↦ᵣ toU64 0) **
        (effectiveAddr initR1 0xcc ↦ₘ srcState) **
        (effectiveAddr initR1 0x29d4 ↦ₘ dstState))
      (fun rt =>
        rt.containsRange (effectiveAddr initR1 0xcc) 1 = true ∧
        rt.containsRange (effectiveAddr initR1 0x29d4) 1 = true) := by
  have h0 := mov64_imm_spec .r6 3 initR6 (base + 0) (by decide)
  have h1 := mov64_imm_spec .r7 0 initR7 (base + 1) (by decide)
  have h2 := ldxb_spec .r3 .r1 0xcc initR3 initR1 srcState (base + 2) (by decide)
  have h3 := jgt_imm_spec .r3 2 (srcState % 256) (base + 3) h3cErrPc
  have h4 := jeq_imm_spec .r3 0 (srcState % 256) (base + 4) h3cErrPc
  have h5 := ldxb_spec .r5 .r1 0x29d4 initR5 initR1 dstState (base + 5) (by decide)
  have h6 := jgt_imm_spec .r5 2 (dstState % 256) (base + 6) h3cErrPc
  have h7 := jeq_imm_spec .r5 0 (dstState % 256) (base + 7) h3cErrPc
  rw [show (if srcState % 256 > toU64 2 then h3cErrPc else (base + 3) + 1) = base + 4 from by
        have hno : ¬ (srcState % 256 > toU64 2) := by
          show ¬ (srcState % 256 > 2); omega
        rw [if_neg hno]] at h3
  rw [show (if srcState % 256 = toU64 0 then h3cErrPc else (base + 4) + 1) = base + 5 from by
        have hno : ¬ (srcState % 256 = toU64 0) := by
          show ¬ (srcState % 256 = 0); omega
        rw [if_neg hno]] at h4
  rw [show (if dstState % 256 > toU64 2 then h3cErrPc else (base + 6) + 1) = base + 7 from by
        have hno : ¬ (dstState % 256 > toU64 2) := by
          show ¬ (dstState % 256 > 2); omega
        rw [if_neg hno]] at h6
  rw [show (if dstState % 256 = toU64 0 then h3cErrPc else (base + 7) + 1) = base + 8 from by
        have hno : ¬ (dstState % 256 = toU64 0) := by
          show ¬ (dstState % 256 = 0); omega
        rw [if_neg hno]] at h7
  unfold h3cCr
  sl_block_iter [h0, h1, h2, h3, h4, h5, h6, h7]

end Examples.PTokenTransferArmH3cStateChecks
