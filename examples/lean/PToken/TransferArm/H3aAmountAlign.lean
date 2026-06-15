/-
  Layer 3b H3a: 4 CU Hoare triple (bytes 0x86E8-0x8700, p_token.so).
  Loads decoded amount from [r1+0x5268], computes r3 := (amount+7)&~7 (8-byte alignment index).
  Post: r4=amount, r3=alignedAmount, r1/cell preserved.
-/

import SVM.SBPF.InstructionSpecs
import SVM.SBPF.Tactic.SL
import SVM.SBPF.Macros

namespace Examples.PTokenTransferArmH3aAmountAlign

open SVM.SBPF
open Memory

/-- `(amount + 7) & ~7` in BPF semantics; shared with downstream sub-arms. -/
def alignedAmount (amount : Nat) : Nat :=
  ((wrapAdd amount (toU64 7)) &&& toU64 (-8)) % U64_MODULUS

/-- CodeReq for H3a's 4 instructions (base-shifted). -/
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
  have h0 := ldxdw_spec .r4 .r1 0x5268 initR4 initR1 amount (base + 0) (by decide) h_amt
  have h1 := mov64_reg_spec .r3 .r4 initR3 amount (base + 1) (by decide)
  have h2 := add64_imm_spec .r3 7 amount (base + 2) (by decide)
  have h3 := and64_imm_spec .r3 (-8) (wrapAdd amount (toU64 7)) (base + 3) (by decide)
  unfold h3aCr
  sl_block_iter [h0, h1, h2, h3]

end Examples.PTokenTransferArmH3aAmountAlign
