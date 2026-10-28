/-
  `Outcome` on real runs (#94): a clean exit, a fault, an out-of-CU stop,
  and what consensus keeps of each. Proved by `native_decide` over decode +
  execute, like `RunnerTests`.

  Reproduce with `lake build SVM.SBPF.OutcomeTests`.
-/

import SVM.SBPF.Runner
import SVM.SBPF.Outcome

namespace SVM.SBPF.OutcomeTests

open SVM.SBPF

private def runV0 (hex : String) (cfg : Runner.RunConfig := {}) : Option Outcome := do
  let insns ← Decode.decodeProgramV0 (Decode.bytesOfHex hex) [(Elf.entrypointHash, 0)]
  let s := Runner.executeFnCpi cfg.programRegistry (Runner.fetchFromArray insns)
    (Runner.initialState cfg) cfg.cuBudget
  return Outcome.ofState s cfg.input.size cfg.cuBudget

/-- The parts of an outcome these tests compare. -/
private def summary : Option Outcome → String
  | some (.ok r0 cu input rd) => s!"ok r0={r0} cu={cu} input={input.toList} rd={rd.size}"
  | some (.fault e cu) => s!"fault {repr e} cu={cu}"
  | some .cuExceeded => "cuExceeded"
  | none => "decode failed"

private def consensus (budget : Nat) : Option Outcome → String
  | some o => match o.consensus budget with
    | .success cu input _ => s!"success cu={cu} input={input.toList}"
    | .failed cu => s!"failed cu={cu}"
  | none => "decode failed"

-- `stb [r1+0], 0x2a; mov64 r0, 0; exit`: a clean exit that writes the input.
private def storeExit := "720100002a000000" ++ "b700000000000000" ++ "9500000000000000"
private def storeCfg : Runner.RunConfig := { input := ⟨#[0, 0, 0, 0]⟩, cuBudget := 100 }

example : summary (runV0 storeExit storeCfg) = "ok r0=0 cu=3 input=[42, 0, 0, 0] rd=0" := by
  native_decide
example : consensus 100 (runV0 storeExit storeCfg) = "success cu=3 input=[42, 0, 0, 0]" := by
  native_decide

-- `mov64 r0, 7; exit`: a non-zero exit fails the transaction, keeping its CU.
private def exit7 := "b700000007000000" ++ "9500000000000000"

example : summary (runV0 exit7 { cuBudget := 100 }) = "ok r0=7 cu=2 input=[] rd=0" := by
  native_decide
example : consensus 100 (runV0 exit7 { cuBudget := 100 }) = "failed cu=2" := by native_decide

-- `mov64 r1, 0; mov64 r0, 1; div64 r0, r1; exit`: a fault, with the CU used up to it.
private def divZero :=
  "b701000000000000" ++ "b700000001000000" ++ "3f10000000000000" ++ "9500000000000000"

example : summary (runV0 divZero { cuBudget := 100 }) =
    "fault SVM.SBPF.VmError.divideByZero cu=3" := by native_decide
example : consensus 100 (runV0 divZero { cuBudget := 100 }) = "failed cu=3" := by native_decide

-- `exit7` with a 1 CU budget: out of CU, and the chain charges the whole budget.
example : summary (runV0 exit7 { cuBudget := 1 }) = "cuExceeded" := by native_decide
example : consensus 1 (runV0 exit7 { cuBudget := 1 }) = "failed cu=1" := by native_decide

end SVM.SBPF.OutcomeTests
