/-
  Layer 3b #2: 4 CU setup triple (bytes 0x76e8-0x7700, p_token.so).
  Zeroes stack slot at r10-0x828, loads r1=r6 (saved input ptr), zeroes r2.
  NOTE: validates r10-relative negative-offset stxdw through sl_block_iter (methodology retired).
-/

import SVM.SBPF.InstructionSpecs
import SVM.SBPF.Tactic.SL
import SVM.SBPF.Macros

namespace Examples.PTokenTransferArmSetup

open SVM.SBPF
open Memory

/-- Stack slot offset -0x828 = -2088. -/
def stackSlotOff : Int := -2088

def transferArmSetupCr : CodeReq :=
  cr![ 0 ↦ .mov64 .r1 (.imm 0),
       1 ↦ .stx .dword .r10 stackSlotOff .r1,
       2 ↦ .mov64 .r1 (.reg .r6),
       3 ↦ .mov64 .r2 (.imm 0) ]

theorem p_token_transfer_arm_setup_spec
    (initR1 initR2 initR6 initR10 oldStackVal : Nat) :
    cuTripleWithinMem 4 0 0 4 transferArmSetupCr
      ((.r1 ↦ᵣ initR1) ** (.r10 ↦ᵣ initR10) **
        (effectiveAddr initR10 stackSlotOff ↦U64 oldStackVal) **
        (.r6 ↦ᵣ initR6) ** (.r2 ↦ᵣ initR2))
      ((.r1 ↦ᵣ initR6) ** (.r10 ↦ᵣ initR10) **
        (effectiveAddr initR10 stackSlotOff ↦U64 toU64 0) **
        (.r6 ↦ᵣ initR6) ** (.r2 ↦ᵣ toU64 0))
      (fun rt => rt.containsWritable (effectiveAddr initR10 stackSlotOff) 8 = true) := by
  have h0 := mov64_imm_spec .r1 0 initR1 0 (by decide)
  have h1 := stxdw_spec .r10 .r1 stackSlotOff initR10 (toU64 0) oldStackVal 1
  have h2 := mov64_reg_spec .r1 .r6 (toU64 0) initR6 2 (by decide)
  have h3 := mov64_imm_spec .r2 0 initR2 3 (by decide)
  sl_block_iter [h0, h1, h2, h3]

end Examples.PTokenTransferArmSetup
