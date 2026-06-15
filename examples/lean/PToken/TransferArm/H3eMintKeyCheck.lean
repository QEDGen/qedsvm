/-
  Layer 3b H3e: 12 CU triple (bytes 0x87b8-0x8810, p_token.so).
  Validates source account mint = canonical mint, word-by-word (4×u64, 4 jne-NT collapses).
  Post: r0=src4, r5=mint4, 8 cells preserved.
-/

import PToken.TransferArm.H3dBalanceCheck
import SVM.SBPF.InstructionSpecs
import SVM.SBPF.Tactic.SL
import SVM.SBPF.Macros

namespace Examples.PTokenTransferArmH3eMintKeyCheck

open SVM.SBPF
open Memory

def h3eErrPc : Nat := 400

def h3eCr (base : Nat) : CodeReq :=
  cr![ base + 0  ↦ .ldx .dword .r5 .r1 0x2968,
       base + 1  ↦ .ldx .dword .r0 .r1 0x60,
       base + 2  ↦ .jne .r0 (.reg .r5) h3eErrPc,
       base + 3  ↦ .ldx .dword .r5 .r1 0x2970,
       base + 4  ↦ .ldx .dword .r0 .r1 0x68,
       base + 5  ↦ .jne .r0 (.reg .r5) h3eErrPc,
       base + 6  ↦ .ldx .dword .r5 .r1 0x2978,
       base + 7  ↦ .ldx .dword .r0 .r1 0x70,
       base + 8  ↦ .jne .r0 (.reg .r5) h3eErrPc,
       base + 9  ↦ .ldx .dword .r5 .r1 0x2980,
       base + 10 ↦ .ldx .dword .r0 .r1 0x78,
       base + 11 ↦ .jne .r0 (.reg .r5) h3eErrPc ]

theorem p_token_transfer_arm_h3e_spec
    (base : Nat)
    (initR1 initR0 initR5 : Nat)
    (mint1 mint2 mint3 mint4 src1 src2 src3 src4 : Nat)
    (h_m1_lt : mint1 < 2 ^ 64) (h_m2_lt : mint2 < 2 ^ 64)
    (h_m3_lt : mint3 < 2 ^ 64) (h_m4_lt : mint4 < 2 ^ 64)
    (h_s1_lt : src1 < 2 ^ 64) (h_s2_lt : src2 < 2 ^ 64)
    (h_s3_lt : src3 < 2 ^ 64) (h_s4_lt : src4 < 2 ^ 64)
    (h_eq1 : src1 = mint1) (h_eq2 : src2 = mint2)
    (h_eq3 : src3 = mint3) (h_eq4 : src4 = mint4) :
    cuTripleWithinMem 12 0 base (base + 12) (h3eCr base)
      ((.r0 ↦ᵣ initR0) ** (.r1 ↦ᵣ initR1) ** (.r5 ↦ᵣ initR5) **
        (effectiveAddr initR1 0x2968 ↦U64 mint1) **
        (effectiveAddr initR1 0x60   ↦U64 src1) **
        (effectiveAddr initR1 0x2970 ↦U64 mint2) **
        (effectiveAddr initR1 0x68   ↦U64 src2) **
        (effectiveAddr initR1 0x2978 ↦U64 mint3) **
        (effectiveAddr initR1 0x70   ↦U64 src3) **
        (effectiveAddr initR1 0x2980 ↦U64 mint4) **
        (effectiveAddr initR1 0x78   ↦U64 src4))
      ((.r0 ↦ᵣ src4) ** (.r1 ↦ᵣ initR1) ** (.r5 ↦ᵣ mint4) **
        (effectiveAddr initR1 0x2968 ↦U64 mint1) **
        (effectiveAddr initR1 0x60   ↦U64 src1) **
        (effectiveAddr initR1 0x2970 ↦U64 mint2) **
        (effectiveAddr initR1 0x68   ↦U64 src2) **
        (effectiveAddr initR1 0x2978 ↦U64 mint3) **
        (effectiveAddr initR1 0x70   ↦U64 src3) **
        (effectiveAddr initR1 0x2980 ↦U64 mint4) **
        (effectiveAddr initR1 0x78   ↦U64 src4))
      (fun rt =>
        ((((((rt.containsRange (effectiveAddr initR1 0x2968) 8 = true ∧
             rt.containsRange (effectiveAddr initR1 0x60) 8 = true) ∧
             rt.containsRange (effectiveAddr initR1 0x2970) 8 = true) ∧
             rt.containsRange (effectiveAddr initR1 0x68) 8 = true) ∧
             rt.containsRange (effectiveAddr initR1 0x2978) 8 = true) ∧
             rt.containsRange (effectiveAddr initR1 0x70) 8 = true) ∧
             rt.containsRange (effectiveAddr initR1 0x2980) 8 = true) ∧
             rt.containsRange (effectiveAddr initR1 0x78) 8 = true) := by
  have h0  := ldxdw_spec .r5 .r1 0x2968 initR5 initR1 mint1 (base + 0)  (by decide) h_m1_lt
  have h1  := ldxdw_spec .r0 .r1 0x60   initR0 initR1 src1  (base + 1)  (by decide) h_s1_lt
  have h2  := jne_reg_spec .r0 .r5 src1 mint1 (base + 2) h3eErrPc
  have h3  := ldxdw_spec .r5 .r1 0x2970 mint1 initR1 mint2 (base + 3)  (by decide) h_m2_lt
  have h4  := ldxdw_spec .r0 .r1 0x68   src1  initR1 src2  (base + 4)  (by decide) h_s2_lt
  have h5  := jne_reg_spec .r0 .r5 src2 mint2 (base + 5) h3eErrPc
  have h6  := ldxdw_spec .r5 .r1 0x2978 mint2 initR1 mint3 (base + 6)  (by decide) h_m3_lt
  have h7  := ldxdw_spec .r0 .r1 0x70   src2  initR1 src3  (base + 7)  (by decide) h_s3_lt
  have h8  := jne_reg_spec .r0 .r5 src3 mint3 (base + 8) h3eErrPc
  have h9  := ldxdw_spec .r5 .r1 0x2980 mint3 initR1 mint4 (base + 9)  (by decide) h_m4_lt
  have h10 := ldxdw_spec .r0 .r1 0x78   src3  initR1 src4  (base + 10) (by decide) h_s4_lt
  have h11 := jne_reg_spec .r0 .r5 src4 mint4 (base + 11) h3eErrPc
  rw [show (if src1 ≠ mint1 then h3eErrPc else (base + 2) + 1) = base + 3 from by
        rw [h_eq1]; simp] at h2
  rw [show (if src2 ≠ mint2 then h3eErrPc else (base + 5) + 1) = base + 6 from by
        rw [h_eq2]; simp] at h5
  rw [show (if src3 ≠ mint3 then h3eErrPc else (base + 8) + 1) = base + 9 from by
        rw [h_eq3]; simp] at h8
  rw [show (if src4 ≠ mint4 then h3eErrPc else (base + 11) + 1) = base + 12 from by
        rw [h_eq4]; simp] at h11
  unfold h3eCr
  sl_block_iter [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]

end Examples.PTokenTransferArmH3eMintKeyCheck
