/-
  L3b H3f: 3-insn signer check (bytes 0x8818-0x8828, p-token@v1.0.0-rc.1).

  Completes H3. Loads authWord (r5) + signerByte (r0), then jne fires (signer≠1),
  hopping over error block into H4. 3 CU, pc → h3fTarget. 1 if-collapse (jne-taken).
-/

import PToken.TransferArm.H3eMintKeyCheck
import SVM.SBPF.InstructionSpecs
import SVM.SBPF.Tactic.SL
import SVM.SBPF.Macros

namespace Examples.PTokenTransferArmH3fSignerExit

open SVM.SBPF
open Memory

/-- Synthetic local jne target (`2+1+0x1ce`); glue re-instantiates at actual absolute PC. -/
def h3fTarget : Nat := 0x1d1

def h3fCr (base : Nat) (target : Nat) : CodeReq :=
  cr![ base + 0 ↦ .ldx .dword .r5 .r1 0x5220,
       base + 1 ↦ .ldx .byte .r0 .r1 0xa8,
       base + 2 ↦ .jne .r0 (.imm 1) target ]

theorem p_token_transfer_arm_h3f_spec
    (base : Nat) (target : Nat)
    (initR0 initR1 initR5 authWord signerByte : Nat)
    (h_auth_lt : authWord < 2 ^ 64)
    (h_signer_ne : signerByte % 256 ≠ toU64 1) :
    cuTripleWithinMem 3 0 base target (h3fCr base target)
      ((.r0 ↦ᵣ initR0) ** (.r1 ↦ᵣ initR1) ** (.r5 ↦ᵣ initR5) **
        (effectiveAddr initR1 0x5220 ↦U64 authWord) **
        (effectiveAddr initR1 0xa8 ↦ₘ signerByte))
      ((.r0 ↦ᵣ signerByte % 256) ** (.r1 ↦ᵣ initR1) **
        (.r5 ↦ᵣ authWord) **
        (effectiveAddr initR1 0x5220 ↦U64 authWord) **
        (effectiveAddr initR1 0xa8 ↦ₘ signerByte))
      (fun rt =>
        rt.containsRange (effectiveAddr initR1 0x5220) 8 = true ∧
        rt.containsRange (effectiveAddr initR1 0xa8) 1 = true) := by
  have h0 := ldxdw_spec .r5 .r1 0x5220 initR5 initR1 authWord (base + 0) (by decide) h_auth_lt
  have h1 := ldxb_spec .r0 .r1 0xa8 initR0 initR1 signerByte (base + 1) (by decide)
  have h2 := jne_imm_spec .r0 1 (signerByte % 256) (base + 2) target
  -- jne fires under signerByte % 256 ≠ 1.
  rw [show (if (signerByte % 256) ≠ toU64 1 then target else (base + 2) + 1) = target from by
        rw [if_pos h_signer_ne]] at h2
  unfold h3fCr
  sl_block_iter [h0, h1, h2]

end Examples.PTokenTransferArmH3fSignerExit
