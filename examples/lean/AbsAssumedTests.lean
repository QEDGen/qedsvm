/-
  Unit checks for the abstract interpreter's assumed input words and constant folding
  (solana-skills#450). Pinocchio's lazy entrypoint computes the next account's pointer as
  `align8(r1 + data_len + 0x286f)`. With the data length assumed, the pointer stays an
  input offset.
-/
import SVM.SBPF.AbsInterp

open SVM.SBPF

/-- `add r1, r5` with `r5` an assumed length: still an input pointer. -/
example : (absStepA [(0x58, .dword, 48)] { r1 := .inPtr 0, r5 := .inLoad .dword 0x58 }
    (.add64 .r1 (.reg .r5))).r1 = .inPtr 48 := by decide

/-- Without the assumption the load is unknown, so the sum is too. -/
example : (absStepA [] { r1 := .inPtr 0, r5 := .inLoad .dword 0x58 }
    (.add64 .r1 (.reg .r5))).r1 = .top := by decide

/-- `and r2, -8` aligns an input pointer down. -/
example : (absStepA [] { r2 := .inPtr 0x289f } (.and64 .r2 (.imm (-8)))).r2 = .inPtr 0x2898 := by
  decide

/-- Constants fold, with 64-bit wrap. -/
example : (absStepA [] { r3 := .const 5 } (.add64 .r3 (.imm 7))).r3 = .const 12 := by decide

/-- Every other instruction keeps the existing transfer. -/
example : absStepA [(0x58, .dword, 48)] { r1 := .inPtr 0 } (.mov64 .r2 (.reg .r1)) =
    absStep { r1 := .inPtr 0 } (.mov64 .r2 (.reg .r1)) := by decide
