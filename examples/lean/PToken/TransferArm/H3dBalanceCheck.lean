/-
  L3b H3d: 8-insn frozen-check + balance-check (bytes 0x8778-0x87b0, p-token@v1.0.0-rc.1).

  Continues H3c. Resets r6/r7, checks neither account is frozen (state≠2), loads txAmount
  via same-register ldxdw (r2←mem[r2+0x7a81]; required `ldxdw_same_spec`), loads srcBalance,
  validates srcBalance≥txAmount. 8 CU, 3 if-collapses (2 jeq-NT + 1 jlt-reg-NT).
-/

import PToken.TransferArm.H3cStateChecks
import SVM.SBPF.InstructionSpecs
import SVM.SBPF.Tactic.SL
import SVM.SBPF.Macros

namespace Examples.PTokenTransferArmH3dBalanceCheck

open SVM.SBPF
open Memory

def h3dErrPc : Nat := 300

def h3dCr (base : Nat) : CodeReq :=
  cr![ base + 0 ↦ .mov64 .r6 (.imm 0),
       base + 1 ↦ .mov64 .r7 (.imm 0x11),
       base + 2 ↦ .jeq .r3 (.imm 2) h3dErrPc,
       base + 3 ↦ .jeq .r5 (.imm 2) h3dErrPc,
       base + 4 ↦ .ldx .dword .r2 .r2 0x7a81,
       base + 5 ↦ .mov64 .r7 (.imm 1),
       base + 6 ↦ .ldx .dword .r3 .r1 0xa0,
       base + 7 ↦ .jlt .r3 (.reg .r2) h3dErrPc ]

theorem p_token_transfer_arm_h3d_spec
    (base : Nat)
    (initR1 baseAddr srcState dstState txAmount srcBalance : Nat)
    (h_amt_lt : txAmount < 2 ^ 64)
    (h_bal_lt : srcBalance < 2 ^ 64)
    (h_src_ne2 : srcState % 256 ≠ 2)
    (h_dst_ne2 : dstState % 256 ≠ 2)
    (h_bal_ge : srcBalance ≥ txAmount) :
    cuTripleWithinMem 8 0 base (base + 8) (h3dCr base)
      ((.r1 ↦ᵣ initR1) ** (.r2 ↦ᵣ baseAddr) **
        (.r3 ↦ᵣ srcState % 256) ** (.r5 ↦ᵣ dstState % 256) **
        (.r6 ↦ᵣ toU64 3) ** (.r7 ↦ᵣ toU64 0) **
        (effectiveAddr baseAddr 0x7a81 ↦U64 txAmount) **
        (effectiveAddr initR1 0xa0 ↦U64 srcBalance))
      ((.r1 ↦ᵣ initR1) ** (.r2 ↦ᵣ txAmount) **
        (.r3 ↦ᵣ srcBalance) ** (.r5 ↦ᵣ dstState % 256) **
        (.r6 ↦ᵣ toU64 0) ** (.r7 ↦ᵣ toU64 1) **
        (effectiveAddr baseAddr 0x7a81 ↦U64 txAmount) **
        (effectiveAddr initR1 0xa0 ↦U64 srcBalance))
      (fun rt =>
        rt.containsRange (effectiveAddr baseAddr 0x7a81) 8 = true ∧
        rt.containsRange (effectiveAddr initR1 0xa0) 8 = true) := by
  have h0 := mov64_imm_spec .r6 0 (toU64 3) (base + 0) (by decide)
  have h1 := mov64_imm_spec .r7 0x11 (toU64 0) (base + 1) (by decide)
  have h2 := jeq_imm_spec .r3 2 (srcState % 256) (base + 2) h3dErrPc
  have h3 := jeq_imm_spec .r5 2 (dstState % 256) (base + 3) h3dErrPc
  -- Same-register load: base from r2, result written back to r2.
  have h4 := ldxdw_same_spec .r2 0x7a81 baseAddr txAmount (base + 4) (by decide) h_amt_lt
  have h5 := mov64_imm_spec .r7 1 (toU64 0x11) (base + 5) (by decide)
  have h6 := ldxdw_spec .r3 .r1 0xa0 (srcState % 256) initR1 srcBalance (base + 6)
                        (by decide) h_bal_lt
  have h7 := jlt_reg_spec .r3 .r2 srcBalance txAmount (base + 7) h3dErrPc
  rw [show (if srcState % 256 = toU64 2 then h3dErrPc else (base + 2) + 1) = base + 3 from by
        have hno : ¬ (srcState % 256 = toU64 2) := by
          show ¬ (srcState % 256 = 2); omega
        rw [if_neg hno]] at h2
  rw [show (if dstState % 256 = toU64 2 then h3dErrPc else (base + 3) + 1) = base + 4 from by
        have hno : ¬ (dstState % 256 = toU64 2) := by
          show ¬ (dstState % 256 = 2); omega
        rw [if_neg hno]] at h3
  rw [show (if srcBalance < txAmount then h3dErrPc else (base + 7) + 1) = base + 8 from by
        have hno : ¬ (srcBalance < txAmount) := by omega
        rw [if_neg hno]] at h7
  unfold h3dCr
  sl_block_iter [h0, h1, h2, h3, h4, h5, h6, h7]

end Examples.PTokenTransferArmH3dBalanceCheck
