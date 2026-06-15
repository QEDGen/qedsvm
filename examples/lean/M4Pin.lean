/-
Regression pins for audit M4: three fail-closed decode checks.
agave rejects at load time; Decode now returns none for:
  1. CannotWriteR10 — writes the read-only frame pointer.
  2. JumpToMiddleOfLddw — branch targets the 2nd slot of an lddw.
  3. ShiftWithOverflow — immediate shift ≥ register width.
Each class has a none pin and an adjacent valid-form pin (no over-rejection).
-/
import SVM.SBPF.Decode

namespace Examples.M4Pin
open SVM.SBPF

/-! ## ShiftWithOverflow: immediate shift ≥ width fails closed -/

/-- `lsh64 r1, 64` (shift = width) decodes to none. -/
theorem lsh64_imm64_fails :
    Decode.decodeInsn (Decode.bytesOfHex "6701000040000000") #[0] 0 = none := by
  native_decide

/-- `lsh64 r1, 63` (shift < width) decodes normally. -/
theorem lsh64_imm63_ok :
    Decode.decodeInsn (Decode.bytesOfHex "670100003f000000") #[0] 0
      = some (.lsh64 .r1 (.imm 63), 8) := by native_decide

/-- `rsh64 r1, 64` fails closed. -/
theorem rsh64_imm64_fails :
    Decode.decodeInsn (Decode.bytesOfHex "7701000040000000") #[0] 0 = none := by
  native_decide

/-- `lsh32 r1, 32` (shift = 32-bit width) decodes to none. -/
theorem lsh32_imm32_fails :
    Decode.decodeInsn (Decode.bytesOfHex "6401000020000000") #[0] 0 = none := by
  native_decide

/-- `lsh32 r1, 31` decodes normally. -/
theorem lsh32_imm31_ok :
    Decode.decodeInsn (Decode.bytesOfHex "640100001f000000") #[0] 0
      = some (.lsh32 .r1 (.imm 31), 8) := by native_decide

/-! ## CannotWriteR10: writing the frame pointer fails closed -/

/-- `mov64 r10, 0` (writes frame pointer) decodes to none. -/
theorem mov64_r10_fails :
    Decode.decodeInsn (Decode.bytesOfHex "b70a000000000000") #[0] 0 = none := by
  native_decide

/-- `mov64 r9, 0` decodes normally. -/
theorem mov64_r9_ok :
    Decode.decodeInsn (Decode.bytesOfHex "b709000000000000") #[0] 0
      = some (.mov64 .r9 (.imm 0), 8) := by native_decide

/-- `ldx r10, [r1+0]` (loads INTO r10) decodes to none. -/
theorem ldx_into_r10_fails :
    Decode.decodeInsn (Decode.bytesOfHex "791a000000000000") #[0] 0 = none := by
  native_decide

/-- `stx [r10-8], r1` uses r10 as base (not a write), so stack stores still decode. -/
theorem stx_r10_base_ok :
    Decode.decodeInsn (Decode.bytesOfHex "7b1af8ff00000000") #[0] 0
      = some (.stx .dword .r10 (-8) .r1, 8) := by native_decide

/-! ## JumpToMiddleOfLddw: a branch into an `lddw`'s 2nd slot fails closed -/

/-- lddw r0, 1 ; ja -2 (targets lddw's 2nd slot) ; exit — mid-lddw jump fails whole decode. -/
theorem jump_into_lddw_fails :
    Decode.decodeProgram (Decode.bytesOfHex
      ("18000000010000000000000000000000" ++
       "0500feff00000000" ++
       "9500000000000000")) = none := by native_decide

/-- Same program but `ja -3` targets lddw slot 0 (valid boundary) — decodes fine. -/
theorem jump_to_lddw_start_ok :
    (Decode.decodeProgram (Decode.bytesOfHex
      ("18000000010000000000000000000000" ++
       "0500fdff00000000" ++
       "9500000000000000"))).isSome = true := by native_decide

end Examples.M4Pin
