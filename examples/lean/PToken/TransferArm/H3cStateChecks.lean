/-
  Layer 3b artifact (happy-path chain, H3c): Hoare triple over the
  next 8 instructions of the p-token Transfer main body at bytes
  0x8738-0x8770 of `qedsvm-rs/tests/fixtures/p_token.so`.

  Continues H3b. Two immediate-loads set up loop-variable r6/r7,
  then two `(ldxb + jgt + jeq)` micro-patterns validate the source
  and destination account-state bytes (both must be Initialized = 1,
  not Uninitialized = 0 and not too large > 2).

  The 8 instructions:

  ```
  8738: b7 06 00 00 03 00 ...   mov64 r6, 0x3
  8740: b7 07 00 00 00 00 ...   mov64 r7, 0x0
  8748: 71 13 cc 00 00 00 ...   ldxb r3, [r1 + 0xcc]    ← src state byte
  8750: 25 03 0f 03 02 00 ...   jgt r3, 0x2, +0x30f     ← NOT taken: state ≤ 2
  8758: 15 03 97 04 00 00 ...   jeq r3, 0x0, +0x497     ← NOT taken: state ≠ 0
  8760: 71 15 d4 29 00 00 ...   ldxb r5, [r1 + 0x29d4]  ← dst state byte
  8768: 25 05 0c 03 02 00 ...   jgt r5, 0x2, +0x30c     ← NOT taken: state ≤ 2
  8770: 15 05 94 04 00 00 ...   jeq r5, 0x0, +0x494     ← NOT taken: state ≠ 0
  ```

  Trace values for the standard fixture: src state = dst state = 1
  (TokenAccount::Initialized). Both `r3` and `r5` end up as 1.

  Spec: 8 CU advancing PC 0 → 8. Post:
  - r6 := 3 (constant, used by later code as a loop count or tag)
  - r7 := 0 (constant)
  - r3 := srcState % 256 (loaded byte)
  - r5 := dstState % 256 (loaded byte)
  - r1, mem cells preserved.

  4 if-collapses (2 jgt-not-taken, 2 jeq-not-taken). The collapses
  unfold `toU64 imm` so omega/rfl can close.
-/

import PToken.TransferArm.H3bIndexBound
import SVM.SBPF.InstructionSpecs
import SVM.SBPF.Tactic.SL
import SVM.SBPF.Macros

namespace Examples.PTokenTransferArmH3cStateChecks

open SVM.SBPF
open Memory

def h3cErrPc : Nat := 200

def h3cCr : CodeReq :=
  (((((((CodeReq.singleton 0 (.mov64 .r6 (.imm 3))).union
        (CodeReq.singleton 1 (.mov64 .r7 (.imm 0)))).union
        (CodeReq.singleton 2 (.ldx .byte .r3 .r1 0xcc))).union
        (CodeReq.singleton 3 (.jgt .r3 (.imm 2) h3cErrPc))).union
        (CodeReq.singleton 4 (.jeq .r3 (.imm 0) h3cErrPc))).union
        (CodeReq.singleton 5 (.ldx .byte .r5 .r1 0x29d4))).union
        (CodeReq.singleton 6 (.jgt .r5 (.imm 2) h3cErrPc))).union
        (CodeReq.singleton 7 (.jeq .r5 (.imm 0) h3cErrPc))

theorem p_token_transfer_arm_h3c_spec
    (initR1 initR3 initR5 initR6 initR7 : Nat)
    (srcState dstState : Nat)
    (h_src_le : srcState % 256 ≤ 2)
    (h_src_ne : srcState % 256 ≠ 0)
    (h_dst_le : dstState % 256 ≤ 2)
    (h_dst_ne : dstState % 256 ≠ 0) :
    cuTripleWithinMem 8 0 0 8 h3cCr
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
  have h0 := mov64_imm_spec .r6 3 initR6 0 (by decide)
  have h1 := mov64_imm_spec .r7 0 initR7 1 (by decide)
  have h2 := ldxb_spec .r3 .r1 0xcc initR3 initR1 srcState 2 (by decide)
  have h3 := jgt_imm_spec .r3 2 (srcState % 256) 3 h3cErrPc
  have h4 := jeq_imm_spec .r3 0 (srcState % 256) 4 h3cErrPc
  have h5 := ldxb_spec .r5 .r1 0x29d4 initR5 initR1 dstState 5 (by decide)
  have h6 := jgt_imm_spec .r5 2 (dstState % 256) 6 h3cErrPc
  have h7 := jeq_imm_spec .r5 0 (dstState % 256) 7 h3cErrPc
  -- Collapse the four cond branches.
  rw [show (if srcState % 256 > toU64 2 then h3cErrPc else 3 + 1) = 4 from by
        have hno : ¬ (srcState % 256 > toU64 2) := by
          show ¬ (srcState % 256 > 2); omega
        rw [if_neg hno]] at h3
  rw [show (if srcState % 256 = toU64 0 then h3cErrPc else 4 + 1) = 5 from by
        have hno : ¬ (srcState % 256 = toU64 0) := by
          show ¬ (srcState % 256 = 0); omega
        rw [if_neg hno]] at h4
  rw [show (if dstState % 256 > toU64 2 then h3cErrPc else 6 + 1) = 7 from by
        have hno : ¬ (dstState % 256 > toU64 2) := by
          show ¬ (dstState % 256 > 2); omega
        rw [if_neg hno]] at h6
  rw [show (if dstState % 256 = toU64 0 then h3cErrPc else 7 + 1) = 8 from by
        have hno : ¬ (dstState % 256 = toU64 0) := by
          show ¬ (dstState % 256 = 0); omega
        rw [if_neg hno]] at h7
  sl_block_iter [h0, h1, h2, h3, h4, h5, h6, h7]

end Examples.PTokenTransferArmH3cStateChecks
