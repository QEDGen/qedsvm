/-
  Layer 3b artifact (happy-path chain, H4a): Hoare triple over the
  13 instructions of the destination-account mint-key validation at
  bytes 0x96A0-0x9700 of `qedsvm-rs/tests/fixtures/p_token.so`.

  Entered via H3f's `jne r0, 0x1` (taken). Validates that the
  destination account's mint pubkey matches the canonical mint key
  word-for-word (mirror of H3e for the destination side), then a
  final `jne r4, 0x163` whose-taken-branch hops to H4b at byte 0xA300.

  The 13 instructions:

  ```
  96a0: mov64 r7, 0x4
  96a8: ldxdw r0, [r1 + 0x80]    ← dst mint word 1
  96b0: jne   r0, r5, ...         ← NOT taken: dst1 = mint1 (r5 inherited from H3f)
  96b8: ldxdw r5, [r1 + 0x5228]   ← mint canonical word 2
  96c0: ldxdw r0, [r1 + 0x88]     ← dst mint word 2
  96c8: jne   r0, r5, ...         ← NOT taken
  96d0: ldxdw r5, [r1 + 0x5230]   ← canonical word 3
  96d8: ldxdw r0, [r1 + 0x90]     ← dst word 3
  96e0: jne   r0, r5, ...         ← NOT taken
  96e8: ldxdw r5, [r1 + 0x5238]   ← canonical word 4
  96f0: ldxdw r0, [r1 + 0x98]     ← dst word 4
  96f8: jne   r0, r5, ...         ← NOT taken
  9700: jne   r4, 0x163, ...      ← TAKEN: r4 ≠ 0x163 (trace: r4 = 0)
  ```

  Notice: the first jne reuses `r5` from H3f's exit (which holds
  the value loaded from `[r1+0x5220]`). The chain composition pulls
  `r5 = mint1` from H3f's post and requires mem at `r1+0x80` to
  equal that same `mint1`.

  Spec: 13 CU advancing PC 0 → h4aTarget (synthetic local PC for
  the final-jne taken branch). Post:
  - r0 := dst4  (= mint4 under the equality hypotheses)
  - r5 := mint4
  - r7 := 4
  - r4 unchanged
  - 8 mem cells preserved.

  5 if-collapses (4 jne-reg-NT + 1 jne-imm-TAKEN).
-/

import PToken.TransferArm.H3fSignerExit
import SVM.SBPF.InstructionSpecs
import SVM.SBPF.Tactic.SL
import SVM.SBPF.Macros

namespace Examples.PTokenTransferArmH4aDestMintCheck

open SVM.SBPF
open Memory

/-- Synthetic local PC for the final-jne-taken target. Mirrors
    H1/H3f convention; downstream glue picks the actual absolute PC. -/
def h4aTarget : Nat := 0x80
def h4aErrPc : Nat := 0x500

def h4aCr : CodeReq :=
  ((((((((((((CodeReq.singleton 0  (.mov64 .r7 (.imm 4))).union
              (CodeReq.singleton 1  (.ldx .dword .r0 .r1 0x80))).union
              (CodeReq.singleton 2  (.jne .r0 (.reg .r5) h4aErrPc))).union
              (CodeReq.singleton 3  (.ldx .dword .r5 .r1 0x5228))).union
              (CodeReq.singleton 4  (.ldx .dword .r0 .r1 0x88))).union
              (CodeReq.singleton 5  (.jne .r0 (.reg .r5) h4aErrPc))).union
              (CodeReq.singleton 6  (.ldx .dword .r5 .r1 0x5230))).union
              (CodeReq.singleton 7  (.ldx .dword .r0 .r1 0x90))).union
              (CodeReq.singleton 8  (.jne .r0 (.reg .r5) h4aErrPc))).union
              (CodeReq.singleton 9  (.ldx .dword .r5 .r1 0x5238))).union
              (CodeReq.singleton 10 (.ldx .dword .r0 .r1 0x98))).union
              (CodeReq.singleton 11 (.jne .r0 (.reg .r5) h4aErrPc))).union
              (CodeReq.singleton 12 (.jne .r4 (.imm 0x163) h4aTarget))

theorem p_token_transfer_arm_h4a_spec
    (initR1 initR4 initR7 : Nat)
    (mint1 mint2 mint3 mint4 dst1 dst2 dst3 dst4 : Nat)
    (h_m2_lt : mint2 < 2 ^ 64) (h_m3_lt : mint3 < 2 ^ 64) (h_m4_lt : mint4 < 2 ^ 64)
    (h_d1_lt : dst1 < 2 ^ 64) (h_d2_lt : dst2 < 2 ^ 64)
    (h_d3_lt : dst3 < 2 ^ 64) (h_d4_lt : dst4 < 2 ^ 64)
    (h_eq1 : dst1 = mint1) (h_eq2 : dst2 = mint2)
    (h_eq3 : dst3 = mint3) (h_eq4 : dst4 = mint4)
    (h_r4_ne : initR4 ≠ toU64 0x163) :
    cuTripleWithinMem 13 0 0 h4aTarget h4aCr
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
  have h0  := mov64_imm_spec .r7 4 initR7 0 (by decide)
  have h1  := ldxdw_spec .r0 .r1 0x80 mint1 initR1 dst1 1 (by decide) h_d1_lt
  have h2  := jne_reg_spec .r0 .r5 dst1 mint1 2 h4aErrPc
  have h3  := ldxdw_spec .r5 .r1 0x5228 mint1 initR1 mint2 3 (by decide) h_m2_lt
  have h4  := ldxdw_spec .r0 .r1 0x88 dst1 initR1 dst2 4 (by decide) h_d2_lt
  have h5  := jne_reg_spec .r0 .r5 dst2 mint2 5 h4aErrPc
  have h6  := ldxdw_spec .r5 .r1 0x5230 mint2 initR1 mint3 6 (by decide) h_m3_lt
  have h7  := ldxdw_spec .r0 .r1 0x90 dst2 initR1 dst3 7 (by decide) h_d3_lt
  have h8  := jne_reg_spec .r0 .r5 dst3 mint3 8 h4aErrPc
  have h9  := ldxdw_spec .r5 .r1 0x5238 mint3 initR1 mint4 9 (by decide) h_m4_lt
  have h10 := ldxdw_spec .r0 .r1 0x98 dst3 initR1 dst4 10 (by decide) h_d4_lt
  have h11 := jne_reg_spec .r0 .r5 dst4 mint4 11 h4aErrPc
  have h12 := jne_imm_spec .r4 0x163 initR4 12 h4aTarget
  -- Collapse the 4 NT jne's.
  rw [show (if dst1 ≠ mint1 then h4aErrPc else 2 + 1) = 3 from by
        rw [h_eq1]; simp] at h2
  rw [show (if dst2 ≠ mint2 then h4aErrPc else 5 + 1) = 6 from by
        rw [h_eq2]; simp] at h5
  rw [show (if dst3 ≠ mint3 then h4aErrPc else 8 + 1) = 9 from by
        rw [h_eq3]; simp] at h8
  rw [show (if dst4 ≠ mint4 then h4aErrPc else 11 + 1) = 12 from by
        rw [h_eq4]; simp] at h11
  -- Collapse the final TAKEN jne.
  rw [show (if initR4 ≠ toU64 0x163 then h4aTarget else 12 + 1) = h4aTarget from by
        rw [if_pos h_r4_ne]] at h12
  sl_block_iter [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]

end Examples.PTokenTransferArmH4aDestMintCheck
