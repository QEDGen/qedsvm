/-
  Layer 3b artifact (happy-path chain, H3e): Hoare triple over the
  next 12 instructions of the p-token Transfer main body at bytes
  0x87b8-0x8810 of `qedsvm-rs/tests/fixtures/p_token.so`.

  Continues H3d. Four (mint-word, src-word, jne-not-taken) triples
  enforce that the source account's mint pubkey matches the canonical
  mint key from the input layout. The 32-byte pubkey is split into
  4 u64 words; each pair must be equal.

  The 12 instructions:

  ```
  87b8: 79 15 68 29 ...   ldxdw r5, [r1 + 0x2968]   ← mint word 1
  87c0: 79 10 60 00 ...   ldxdw r0, [r1 + 0x60]     ← src  word 1
  87c8: 5d 50 ff 02 ...   jne   r0, r5, +0x2ff      ← NOT taken (= mint1)
  87d0: 79 15 70 29 ...   ldxdw r5, [r1 + 0x2970]   ← mint word 2
  87d8: 79 10 68 00 ...   ldxdw r0, [r1 + 0x68]     ← src  word 2
  87e0: 5d 50 fc 02 ...   jne   r0, r5, +0x2fc      ← NOT taken
  87e8: 79 15 78 29 ...   ldxdw r5, [r1 + 0x2978]   ← mint word 3
  87f0: 79 10 70 00 ...   ldxdw r0, [r1 + 0x70]     ← src  word 3
  87f8: 5d 50 f9 02 ...   jne   r0, r5, +0x2f9      ← NOT taken
  8800: 79 15 80 29 ...   ldxdw r5, [r1 + 0x2980]   ← mint word 4
  8808: 79 10 78 00 ...   ldxdw r0, [r1 + 0x78]     ← src  word 4
  8810: 5d 50 f6 02 ...   jne   r0, r5, +0x2f6      ← NOT taken
  ```

  Spec: 12 CU advancing PC 0 → 12. Post:
  - r0 := mint4 (last loaded src word = last loaded mint word)
  - r5 := mint4
  - r1, r2, r3, r6, r7 unchanged
  - 8 mem cells preserved.

  4 if-collapses (all jne-reg-not-taken under mintN = srcN).
-/

import PToken.TransferArm.H3dBalanceCheck
import SVM.SBPF.InstructionSpecs
import SVM.SBPF.Tactic.SL
import SVM.SBPF.Macros

namespace Examples.PTokenTransferArmH3eMintKeyCheck

open SVM.SBPF
open Memory

def h3eErrPc : Nat := 400

def h3eCr : CodeReq :=
  (((((((((((CodeReq.singleton 0  (.ldx .dword .r5 .r1 0x2968)).union
            (CodeReq.singleton 1  (.ldx .dword .r0 .r1 0x60))).union
            (CodeReq.singleton 2  (.jne .r0 (.reg .r5) h3eErrPc))).union
            (CodeReq.singleton 3  (.ldx .dword .r5 .r1 0x2970))).union
            (CodeReq.singleton 4  (.ldx .dword .r0 .r1 0x68))).union
            (CodeReq.singleton 5  (.jne .r0 (.reg .r5) h3eErrPc))).union
            (CodeReq.singleton 6  (.ldx .dword .r5 .r1 0x2978))).union
            (CodeReq.singleton 7  (.ldx .dword .r0 .r1 0x70))).union
            (CodeReq.singleton 8  (.jne .r0 (.reg .r5) h3eErrPc))).union
            (CodeReq.singleton 9  (.ldx .dword .r5 .r1 0x2980))).union
            (CodeReq.singleton 10 (.ldx .dword .r0 .r1 0x78))).union
            (CodeReq.singleton 11 (.jne .r0 (.reg .r5) h3eErrPc))

theorem p_token_transfer_arm_h3e_spec
    (initR1 initR0 initR5 : Nat)
    (mint1 mint2 mint3 mint4 src1 src2 src3 src4 : Nat)
    (h_m1_lt : mint1 < 2 ^ 64) (h_m2_lt : mint2 < 2 ^ 64)
    (h_m3_lt : mint3 < 2 ^ 64) (h_m4_lt : mint4 < 2 ^ 64)
    (h_s1_lt : src1 < 2 ^ 64) (h_s2_lt : src2 < 2 ^ 64)
    (h_s3_lt : src3 < 2 ^ 64) (h_s4_lt : src4 < 2 ^ 64)
    (h_eq1 : src1 = mint1) (h_eq2 : src2 = mint2)
    (h_eq3 : src3 = mint3) (h_eq4 : src4 = mint4) :
    cuTripleWithinMem 12 0 0 12 h3eCr
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
  have h0  := ldxdw_spec .r5 .r1 0x2968 initR5 initR1 mint1 0  (by decide) h_m1_lt
  have h1  := ldxdw_spec .r0 .r1 0x60   initR0 initR1 src1  1  (by decide) h_s1_lt
  have h2  := jne_reg_spec .r0 .r5 src1 mint1 2 h3eErrPc
  have h3  := ldxdw_spec .r5 .r1 0x2970 mint1 initR1 mint2 3  (by decide) h_m2_lt
  have h4  := ldxdw_spec .r0 .r1 0x68   src1  initR1 src2  4  (by decide) h_s2_lt
  have h5  := jne_reg_spec .r0 .r5 src2 mint2 5 h3eErrPc
  have h6  := ldxdw_spec .r5 .r1 0x2978 mint2 initR1 mint3 6  (by decide) h_m3_lt
  have h7  := ldxdw_spec .r0 .r1 0x70   src2  initR1 src3  7  (by decide) h_s3_lt
  have h8  := jne_reg_spec .r0 .r5 src3 mint3 8 h3eErrPc
  have h9  := ldxdw_spec .r5 .r1 0x2980 mint3 initR1 mint4 9  (by decide) h_m4_lt
  have h10 := ldxdw_spec .r0 .r1 0x78   src3  initR1 src4  10 (by decide) h_s4_lt
  have h11 := jne_reg_spec .r0 .r5 src4 mint4 11 h3eErrPc
  -- Collapse each jne under srcN = mintN.
  rw [show (if src1 ≠ mint1 then h3eErrPc else 2 + 1) = 3 from by
        rw [h_eq1]; simp] at h2
  rw [show (if src2 ≠ mint2 then h3eErrPc else 5 + 1) = 6 from by
        rw [h_eq2]; simp] at h5
  rw [show (if src3 ≠ mint3 then h3eErrPc else 8 + 1) = 9 from by
        rw [h_eq3]; simp] at h8
  rw [show (if src4 ≠ mint4 then h3eErrPc else 11 + 1) = 12 from by
        rw [h_eq4]; simp] at h11
  sl_block_iter [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]

end Examples.PTokenTransferArmH3eMintKeyCheck
