/-
  Layer 3b artifact (happy-path chain, H3b): Hoare triple over the
  next 6 instructions of the p-token Transfer main body at bytes
  0x8708-0x8730 of `qedsvm-rs/tests/fixtures/p_token.so`.

  Continues H3a. H3a left r3 = `alignedAmount amount` and r4 = amount;
  H3b uses r3 as an index into the input buffer to load two layout
  markers and validates them with two `not-taken` conditional jumps.

  The 6 instructions:

  ```
  8708: bf 12 00 00 ...     mov64 r2, r1
  8710: 0f 32 00 00 ...     add64 r2, r3           ← r2 := input + alignedAmount
  8718: 79 23 78 7a ...     ldxdw r3, [r2 + 0x7a78]
  8720: a5 03 97 f0 09 ..   jlt r3, 0x9, -0xf69    ← NOT taken: cell ≥ 9
  8728: 71 23 80 7a ...     ldxb r3, [r2 + 0x7a80]
  8730: 55 03 95 f0 03 ..   jne r3, 0x3, -0xf6b    ← NOT taken: cell byte = 3
  ```

  Trace values for amount=250 (alignedAmount=256): r2 = initR1+256,
  layout cell at r2+0x7a78 = 9, layout byte at r2+0x7a80 = 3. Both
  cond exits stay on the happy path under those hypotheses.

  Spec: 6 CU advancing PC 0 → 6. Post:
  - r2 := wrapAdd initR1 (alignedAmount amount)  (input + index)
  - r3 := 3                                       (loaded layout byte, mod 256)
  - r1 unchanged.

  Two if-collapses (jlt-not-taken via `cell ≥ 9`; jne-not-taken via
  `cellByte % 256 = 3`) — same pattern as `PTokenValidationPrelude`.
-/

import PToken.TransferArm.H3aAmountAlign
import SVM.SBPF.InstructionSpecs
import SVM.SBPF.Tactic.SL
import SVM.SBPF.Macros

namespace Examples.PTokenTransferArmH3bIndexBound

open SVM.SBPF
open Memory
open Examples.PTokenTransferArmH3aAmountAlign (alignedAmount)

/-- CodeReq for H3b's 6 instructions. The jlt and jne targets are
    far-away error PCs; pick any non-clashing synthetic value (here
    100). The if-collapses make these targets irrelevant at the
    proof level. -/
def h3bErrPc : Nat := 100

def h3bCr (base : Nat) : CodeReq :=
  (((((CodeReq.singleton (base + 0) (.mov64 .r2 (.reg .r1))).union
      (CodeReq.singleton (base + 1) (.add64 .r2 (.reg .r3)))).union
      (CodeReq.singleton (base + 2) (.ldx .dword .r3 .r2 0x7a78))).union
      (CodeReq.singleton (base + 3) (.jlt .r3 (.imm 9) h3bErrPc))).union
      (CodeReq.singleton (base + 4) (.ldx .byte .r3 .r2 0x7a80))).union
      (CodeReq.singleton (base + 5) (.jne .r3 (.imm 3) h3bErrPc))

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
  -- h0: mov64 r2, r1 → r2 := initR1.
  have h0 := mov64_reg_spec .r2 .r1 initR2 initR1 (base + 0) (by decide)
  -- h1: add64 r2, r3 → r2 := wrapAdd initR1 (alignedAmount amount) = baseAddr.
  have h1 := add64_reg_spec .r2 .r3 initR1 (alignedAmount amount) (base + 1) (by decide)
  -- h2: ldxdw r3, [r2 + 0x7a78] → r3 := layoutBound.
  have h2 := ldxdw_spec .r3 .r2 0x7a78 (alignedAmount amount) baseAddr
                        layoutBound (base + 2) (by decide) h_bound_lt
  -- h3: jlt r3, 9 → NOT taken under layoutBound ≥ 9.
  have h3 := jlt_imm_spec .r3 9 layoutBound (base + 3) h3bErrPc
  -- h4: ldxb r3, [r2 + 0x7a80] → r3 := layoutTag % 256.
  have h4 := ldxb_spec .r3 .r2 0x7a80 layoutBound baseAddr layoutTag (base + 4) (by decide)
  -- h5: jne r3, 3 → NOT taken under layoutTag % 256 = 3.
  have h5 := jne_imm_spec .r3 3 (layoutTag % 256) (base + 5) h3bErrPc
  -- Collapse the jlt: layoutBound ≥ 9 ⟹ ¬ (layoutBound < 9).
  rw [show (if layoutBound < toU64 9 then h3bErrPc else (base + 3) + 1) = base + 4 from by
        have hno : ¬ (layoutBound < toU64 9) := by
          show ¬ (layoutBound < 9); omega
        rw [if_neg hno]] at h3
  -- Collapse the jne: layoutTag % 256 = toU64 3 ⟹ ¬ (≠).
  rw [show (if (layoutTag % 256) ≠ toU64 3 then h3bErrPc else (base + 5) + 1) = base + 6 from by
        rw [h_tag]; simp] at h5
  unfold h3bCr
  sl_block_iter [h0, h1, h2, h3, h4, h5]

end Examples.PTokenTransferArmH3bIndexBound
