/-
  Layer 3b H4a: 13 CU triple (bytes 0x96A0-0x9700, p_token.so).
  Validates dst account mint = canonical, word-by-word (4 jne-reg-NT); final jne r4,0x163 TAKEN.
  r5 at entry inherited from H3f (holds mint word 1). Post: r0=dst4, r5=mint4, r7=4.
-/

import PToken.TransferArm.H3fSignerExit
import SVM.SBPF.InstructionSpecs
import SVM.SBPF.Tactic.SL
import SVM.SBPF.Macros

namespace Examples.PTokenTransferArmH4aDestMintCheck

open SVM.SBPF
open Memory

/-- Synthetic local PC for the final-jne-taken target; downstream glue sets the absolute PC. -/
def h4aTarget : Nat := 0x80
def h4aErrPc : Nat := 0x500

def h4aCr (base : Nat) (target : Nat) : CodeReq :=
  cr![ base + 0  ↦ .mov64 .r7 (.imm 4),
       base + 1  ↦ .ldx .dword .r0 .r1 0x80,
       base + 2  ↦ .jne .r0 (.reg .r5) h4aErrPc,
       base + 3  ↦ .ldx .dword .r5 .r1 0x5228,
       base + 4  ↦ .ldx .dword .r0 .r1 0x88,
       base + 5  ↦ .jne .r0 (.reg .r5) h4aErrPc,
       base + 6  ↦ .ldx .dword .r5 .r1 0x5230,
       base + 7  ↦ .ldx .dword .r0 .r1 0x90,
       base + 8  ↦ .jne .r0 (.reg .r5) h4aErrPc,
       base + 9  ↦ .ldx .dword .r5 .r1 0x5238,
       base + 10 ↦ .ldx .dword .r0 .r1 0x98,
       base + 11 ↦ .jne .r0 (.reg .r5) h4aErrPc,
       base + 12 ↦ .jne .r4 (.imm 0x163) target ]

theorem p_token_transfer_arm_h4a_spec
    (base : Nat) (target : Nat)
    (initR1 initR4 initR7 : Nat)
    (mint1 mint2 mint3 mint4 dst1 dst2 dst3 dst4 : Nat)
    (h_m2_lt : mint2 < 2 ^ 64) (h_m3_lt : mint3 < 2 ^ 64) (h_m4_lt : mint4 < 2 ^ 64)
    (h_d1_lt : dst1 < 2 ^ 64) (h_d2_lt : dst2 < 2 ^ 64)
    (h_d3_lt : dst3 < 2 ^ 64) (h_d4_lt : dst4 < 2 ^ 64)
    (h_eq1 : dst1 = mint1) (h_eq2 : dst2 = mint2)
    (h_eq3 : dst3 = mint3) (h_eq4 : dst4 = mint4)
    (h_r4_ne : initR4 ≠ toU64 0x163) :
    cuTripleWithinMem 13 0 base target (h4aCr base target)
      ((.r0 ↦ᵣ mint1) ** (.r1 ↦ᵣ initR1) **
        (.r4 ↦ᵣ initR4) ** (.r5 ↦ᵣ mint1) ** (.r7 ↦ᵣ initR7) **
        (effectiveAddr initR1 0x80   ↦U64 dst1) **
        (effectiveAddr initR1 0x5228 ↦U64 mint2) **
        (effectiveAddr initR1 0x88   ↦U64 dst2) **
        (effectiveAddr initR1 0x5230 ↦U64 mint3) **
        (effectiveAddr initR1 0x90   ↦U64 dst3) **
        (effectiveAddr initR1 0x5238 ↦U64 mint4) **
        (effectiveAddr initR1 0x98   ↦U64 dst4))
      ((.r0 ↦ᵣ dst4) ** (.r1 ↦ᵣ initR1) **
        (.r4 ↦ᵣ initR4) ** (.r5 ↦ᵣ mint4) ** (.r7 ↦ᵣ toU64 4) **
        (effectiveAddr initR1 0x80   ↦U64 dst1) **
        (effectiveAddr initR1 0x5228 ↦U64 mint2) **
        (effectiveAddr initR1 0x88   ↦U64 dst2) **
        (effectiveAddr initR1 0x5230 ↦U64 mint3) **
        (effectiveAddr initR1 0x90   ↦U64 dst3) **
        (effectiveAddr initR1 0x5238 ↦U64 mint4) **
        (effectiveAddr initR1 0x98   ↦U64 dst4))
      (fun rt =>
        (((((rt.containsRange (effectiveAddr initR1 0x80) 8 = true ∧
             rt.containsRange (effectiveAddr initR1 0x5228) 8 = true) ∧
             rt.containsRange (effectiveAddr initR1 0x88) 8 = true) ∧
             rt.containsRange (effectiveAddr initR1 0x5230) 8 = true) ∧
             rt.containsRange (effectiveAddr initR1 0x90) 8 = true) ∧
             rt.containsRange (effectiveAddr initR1 0x5238) 8 = true) ∧
             rt.containsRange (effectiveAddr initR1 0x98) 8 = true) := by
  have h0  := mov64_imm_spec .r7 4 initR7 (base + 0) (by decide)
  have h1  := ldxdw_spec .r0 .r1 0x80 mint1 initR1 dst1 (base + 1) (by decide) h_d1_lt
  have h2  := jne_reg_spec .r0 .r5 dst1 mint1 (base + 2) h4aErrPc
  have h3  := ldxdw_spec .r5 .r1 0x5228 mint1 initR1 mint2 (base + 3) (by decide) h_m2_lt
  have h4  := ldxdw_spec .r0 .r1 0x88 dst1 initR1 dst2 (base + 4) (by decide) h_d2_lt
  have h5  := jne_reg_spec .r0 .r5 dst2 mint2 (base + 5) h4aErrPc
  have h6  := ldxdw_spec .r5 .r1 0x5230 mint2 initR1 mint3 (base + 6) (by decide) h_m3_lt
  have h7  := ldxdw_spec .r0 .r1 0x90 dst2 initR1 dst3 (base + 7) (by decide) h_d3_lt
  have h8  := jne_reg_spec .r0 .r5 dst3 mint3 (base + 8) h4aErrPc
  have h9  := ldxdw_spec .r5 .r1 0x5238 mint3 initR1 mint4 (base + 9) (by decide) h_m4_lt
  have h10 := ldxdw_spec .r0 .r1 0x98 dst3 initR1 dst4 (base + 10) (by decide) h_d4_lt
  have h11 := jne_reg_spec .r0 .r5 dst4 mint4 (base + 11) h4aErrPc
  have h12 := jne_imm_spec .r4 0x163 initR4 (base + 12) target
  rw [show (if dst1 ≠ mint1 then h4aErrPc else (base + 2) + 1) = base + 3 from by
        rw [h_eq1]; simp] at h2
  rw [show (if dst2 ≠ mint2 then h4aErrPc else (base + 5) + 1) = base + 6 from by
        rw [h_eq2]; simp] at h5
  rw [show (if dst3 ≠ mint3 then h4aErrPc else (base + 8) + 1) = base + 9 from by
        rw [h_eq3]; simp] at h8
  rw [show (if dst4 ≠ mint4 then h4aErrPc else (base + 11) + 1) = base + 12 from by
        rw [h_eq4]; simp] at h11
  rw [show (if initR4 ≠ toU64 0x163 then target else (base + 12) + 1) = target from by
        rw [if_pos h_r4_ne]] at h12
  unfold h4aCr
  sl_block_iter [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]

end Examples.PTokenTransferArmH4aDestMintCheck
