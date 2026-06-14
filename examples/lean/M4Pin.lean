/-
Regression pins for the soundness-audit M4 decode-time fail-closed checks.

agave's verifier rejects three classes of malformed instruction at LOAD
time; the Lean decoder previously assigned them well-defined semantics
(fail-open). `SVM.SBPF.Decode` now fails closed (decodes to `none`):

  1. CannotWriteR10        — an instruction that WRITES the read-only
                             frame pointer r10.
  2. JumpToMiddleOfLddw    — a branch target landing on the 2nd slot of
                             an `lddw`.
  3. ShiftWithOverflow     — an immediate shift ≥ the register width.

Each pin checks the malformed form decodes to `none` AND that the
adjacent VALID form still decodes — so the checks are precise (they do
not over-reject real instructions, in particular `stx [r10+off], rN`
stack stores and shifts below the width).
-/
import SVM.SBPF.Decode

namespace Examples.M4Pin
open SVM.SBPF

/-! ## ShiftWithOverflow: immediate shift ≥ width fails closed -/

/-- `lsh64 r1, 64` (shift = width) decodes to `none`. -/
theorem lsh64_imm64_fails :
    Decode.decodeInsn (Decode.bytesOfHex "6701000040000000") #[0] 0 = none := by
  native_decide

/-- `lsh64 r1, 63` (shift < width) still decodes. -/
theorem lsh64_imm63_ok :
    Decode.decodeInsn (Decode.bytesOfHex "670100003f000000") #[0] 0
      = some (.lsh64 .r1 (.imm 63), 8) := by native_decide

/-- `rsh64 r1, 64` fails closed. -/
theorem rsh64_imm64_fails :
    Decode.decodeInsn (Decode.bytesOfHex "7701000040000000") #[0] 0 = none := by
  native_decide

/-- `lsh32 r1, 32` (shift = 32-bit width) fails closed. -/
theorem lsh32_imm32_fails :
    Decode.decodeInsn (Decode.bytesOfHex "6401000020000000") #[0] 0 = none := by
  native_decide

/-- `lsh32 r1, 31` still decodes. -/
theorem lsh32_imm31_ok :
    Decode.decodeInsn (Decode.bytesOfHex "640100001f000000") #[0] 0
      = some (.lsh32 .r1 (.imm 31), 8) := by native_decide

/-! ## CannotWriteR10: writing the frame pointer fails closed -/

/-- `mov64 r10, 0` (writes the frame pointer) decodes to `none`. -/
theorem mov64_r10_fails :
    Decode.decodeInsn (Decode.bytesOfHex "b70a000000000000") #[0] 0 = none := by
  native_decide

/-- `mov64 r9, 0` (a normal register) still decodes. -/
theorem mov64_r9_ok :
    Decode.decodeInsn (Decode.bytesOfHex "b709000000000000") #[0] 0
      = some (.mov64 .r9 (.imm 0), 8) := by native_decide

/-- `ldx r10, [r1+0]` (LOADS into r10) decodes to `none`. -/
theorem ldx_into_r10_fails :
    Decode.decodeInsn (Decode.bytesOfHex "791a000000000000") #[0] 0 = none := by
  native_decide

/-- `stx [r10-8], r1` uses r10 as a memory BASE (not a register write), so
    it still decodes — stack stores stay valid (the over-rejection guard). -/
theorem stx_r10_base_ok :
    Decode.decodeInsn (Decode.bytesOfHex "7b1af8ff00000000") #[0] 0
      = some (.stx .dword .r10 (-8) .r1, 8) := by native_decide

/-! ## JumpToMiddleOfLddw: a branch into an `lddw`'s 2nd slot fails closed -/

/-- `lddw r0, 1` (slots 0-1) ; `ja -2` (targets slot 1, the lddw's 2nd
    slot) ; `exit`. The mid-`lddw` jump fails the whole decode. -/
theorem jump_into_lddw_fails :
    Decode.decodeProgram (Decode.bytesOfHex
      ("18000000010000000000000000000000" ++
       "0500feff00000000" ++
       "9500000000000000")) = none := by native_decide

/-- Same program but `ja -3` targets slot 0 (the `lddw`'s START, a valid
    instruction boundary) — decodes fine. Shows the check is precise. -/
theorem jump_to_lddw_start_ok :
    (Decode.decodeProgram (Decode.bytesOfHex
      ("18000000010000000000000000000000" ++
       "0500fdff00000000" ++
       "9500000000000000"))).isSome = true := by native_decide

end Examples.M4Pin
