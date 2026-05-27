/-
  Layer 3b artifact (happy-path chain, H3a): Hoare triple over the
  first 4 instructions of the p-token Transfer **main body** at
  bytes 0x86E8-0x8700 of `qedsvm-rs/tests/fixtures/p_token.so`.

  This is the first sub-arm of H3 (the 41-insn main body block the
  trace visits at PCs 0xf97-0xfbf). H3 is split into sub-arms to keep
  each proof tractable; H3a covers pure arithmetic — load the decoded
  amount, then compute its 8-byte-aligned upper bound.

  The 4 instructions:

  ```
  86e8: 79 14 68 52 ...      ldxdw r4, [r1 + 0x5268]   ← load decoded amount
  86f0: bf 43 00 00 ...      mov64 r3, r4
  86f8: 07 03 00 00 07 ..    add64 r3, 0x7
  8700: 57 03 00 00 f8 ff .. and64 r3, -0x8            ← r3 := alignTo8(amount)
  ```

  Semantics: pinocchio reads the decoded `amount` (Transfer's u64
  argument) from a fixed offset in its input layout, then computes
  `(amount + 7) & ~7` — the smallest multiple of 8 that is ≥ amount.
  This aligned value is reused as an index into the input buffer
  (subsequent instructions add r3 to r1 and load layout markers from
  there). The arithmetic is unconditional and has no branches.

  Spec: 4 CU advancing PC 0 → 4. Post:
  - `r4 := amount`
  - `r3 := ((amount+7) &&& -8) (mod 2^64)`
  - `r1` and the amount memory cell preserved.

  No memory writes; the rr-predicate covers the 8-byte amount cell.
-/

import SVM.SBPF.InstructionSpecs
import SVM.SBPF.Tactic.SL
import SVM.SBPF.Macros

namespace Examples.PTokenTransferArmH3aAmountAlign

open SVM.SBPF
open Memory

/-- The 8-byte-aligned upper bound of `amount` — `(amount + 7) & ~7`
    in BPF semantics (wrapping add + bitwise-and against the sign-
    extended `-8` immediate, then `% 2^64`). Kept as an abbreviation
    so downstream sub-arms can reference it without unfolding. -/
def alignedAmount (amount : Nat) : Nat :=
  ((wrapAdd amount (toU64 7)) &&& toU64 (-8)) % U64_MODULUS

/-- CodeReq for H3a's 4 instructions, base-shifted. -/
def h3aCr (base : Nat) : CodeReq :=
  cr![ base + 0 ↦ .ldx .dword .r4 .r1 0x5268,
       base + 1 ↦ .mov64 .r3 (.reg .r4),
       base + 2 ↦ .add64 .r3 (.imm 7),
       base + 3 ↦ .and64 .r3 (.imm (-8)) ]

theorem p_token_transfer_arm_h3a_spec
    (base : Nat)
    (initR1 initR3 initR4 amount : Nat)
    (h_amt : amount < 2 ^ 64) :
    cuTripleWithinMem 4 0 base (base + 4) (h3aCr base)
      ((.r1 ↦ᵣ initR1) ** (.r3 ↦ᵣ initR3) ** (.r4 ↦ᵣ initR4) **
        (effectiveAddr initR1 0x5268 ↦U64 amount))
      ((.r1 ↦ᵣ initR1) ** (.r3 ↦ᵣ alignedAmount amount) **
        (.r4 ↦ᵣ amount) **
        (effectiveAddr initR1 0x5268 ↦U64 amount))
      (fun rt => rt.containsRange (effectiveAddr initR1 0x5268) 8 = true) := by
  -- h0: ldxdw r4, [r1 + 0x5268] → r4 := amount.
  have h0 := ldxdw_spec .r4 .r1 0x5268 initR4 initR1 amount (base + 0) (by decide) h_amt
  -- h1: mov64 r3, r4 → r3 := r4's value (= amount after h0).
  have h1 := mov64_reg_spec .r3 .r4 initR3 amount (base + 1) (by decide)
  -- h2: add64 r3, 0x7 → r3 := wrapAdd amount (toU64 7).
  have h2 := add64_imm_spec .r3 7 amount (base + 2) (by decide)
  -- h3: and64 r3, -0x8 → r3 := alignedAmount amount.
  have h3 := and64_imm_spec .r3 (-8) (wrapAdd amount (toU64 7)) (base + 3) (by decide)
  unfold h3aCr
  sl_block_iter [h0, h1, h2, h3]

end Examples.PTokenTransferArmH3aAmountAlign
