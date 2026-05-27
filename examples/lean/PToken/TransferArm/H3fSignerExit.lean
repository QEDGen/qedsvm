/-
  Layer 3b artifact (happy-path chain, H3f): Hoare triple over the
  final 3 instructions of the p-token Transfer main body at bytes
  0x8818-0x8828 of `qedsvm-rs/tests/fixtures/p_token.so`.

  Completes the H3 (main body) sub-chain. Loads an authority-related
  word and a signer flag byte, then jumps forward (NEGATE-and-take
  pattern: jne fires when signer is NOT 1, hopping over an
  error-handling block and landing in H4).

  The 3 instructions:

  ```
  8818: 79 15 20 52 ...   ldxdw r5, [r1 + 0x5220]   ← authority-related word
  8820: 71 10 a8 00 ...   ldxb  r0, [r1 + 0xa8]     ← signer flag byte
  8828: 55 00 ce 01 01 .. jne   r0, 0x1, +0x1ce     ← TAKEN: signer flag ≠ 1
  ```

  Trace at this slice (happy path): byte at [r1+0xa8] is 0, so the
  jne fires and execution leaves the H3 body, landing in the H4
  region at byte 0x96A0 (~PC 4457 in the full image). The next
  H-arm (H4) covers that landing site.

  Spec: 3 CU advancing PC 0 → h3fTarget (synthetic local target
  capturing the disasm offset field, like `dispatchTarget` in H1
  and `transferArmTarget` in PTokenValidationPrelude). Post:
  - r0 := signerByte % 256
  - r5 := authWord
  - r1, mem cells preserved.

  1 if-collapse (jne-taken under signerByte % 256 ≠ 1).
-/

import PToken.TransferArm.H3eMintKeyCheck
import SVM.SBPF.InstructionSpecs
import SVM.SBPF.Tactic.SL
import SVM.SBPF.Macros

namespace Examples.PTokenTransferArmH3fSignerExit

open SVM.SBPF
open Memory

/-- Synthetic local exit PC for H3f's jne (`2 + 1 + 0x1ce = 0x1d1`).
    Mirrors H1's `dispatchTarget` convention. Glue consumers
    re-instantiate at the actual absolute target (~PC 4457 = byte 0x96A0). -/
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
