/-
Regression pins for the L1 fault-vs-exit distinction (audit L1).

exitCode alone is ambiguous: a clean exit with r0 = ERR_ABORT is numerically
identical to a fault. vmError is the disambiguating channel: abort sites set
it; clean exits leave it none. Pins lock both directions and all toSentinel
equalities, ensuring specs can assert faults via `vmError = some e`.
-/
import SVM.SBPF.Execute

namespace Examples.L1Pin
open SVM.SBPF

/-- State with r0 = ERR_ABORT and empty call stack, so `exit` terminates. -/
def cleanExitState : State := { (default : State) with regs := { r0 := ERR_ABORT } }

/-- Clean `exit` with r0 = ERR_ABORT: exitCode = some ERR_ABORT but vmError = none. -/
theorem clean_exit_sentinel_no_fault :
    (step .exit cleanExitState).exitCode = some ERR_ABORT ∧
    (step .exit cleanExitState).vmError = none := by
  refine ⟨rfl, rfl⟩

/-- `.callx` fails closed: it sets the typed fault AND the sentinel. -/
theorem callx_sets_vmError :
    (step (.callx .r0) (default : State)).vmError = some .unsupportedInstruction ∧
    (step (.callx .r0) (default : State)).exitCode = some ERR_UNSUPPORTED_INSTRUCTION := by
  refine ⟨rfl, rfl⟩

/-- `abort` sets vmError = some .abort AND the ERR_ABORT sentinel. -/
theorem abort_sets_vmError :
    (SVM.SBPF.Abort.execAbort (default : State)).vmError = some .abort ∧
    (SVM.SBPF.Abort.execAbort (default : State)).exitCode = some ERR_ABORT := by
  refine ⟨rfl, rfl⟩

/-- abort and clean exit share the same exitCode; only abort sets vmError — collision resolved. -/
theorem sentinel_collision_distinguished :
    (SVM.SBPF.Abort.execAbort (default : State)).exitCode
      = (step .exit cleanExitState).exitCode ∧
    (SVM.SBPF.Abort.execAbort (default : State)).vmError = some .abort ∧
    (step .exit cleanExitState).vmError = none := by
  refine ⟨rfl, rfl, rfl⟩

/-! ## `VmError.toSentinel` agrees with the legacy `ERR_*` constants -/

theorem toSentinel_divideByZero : VmError.divideByZero.toSentinel = ERR_DIVIDE_BY_ZERO := rfl
theorem toSentinel_invalidPc : VmError.invalidPc.toSentinel = ERR_INVALID_PC := rfl
theorem toSentinel_abort : VmError.abort.toSentinel = ERR_ABORT := rfl
theorem toSentinel_accessViolation : VmError.accessViolation.toSentinel = ERR_ACCESS_VIOLATION := rfl
theorem toSentinel_unsupported : VmError.unsupportedInstruction.toSentinel = ERR_UNSUPPORTED_INSTRUCTION := rfl
theorem toSentinel_callDepth : VmError.callDepthExceeded.toSentinel = ERR_CALL_DEPTH_EXCEEDED := rfl
theorem toSentinel_returnDataTooLarge : VmError.returnDataTooLarge.toSentinel = ERR_RETURN_DATA_TOO_LARGE := rfl
theorem toSentinel_invalidLength : VmError.invalidLength.toSentinel = ERR_INVALID_LENGTH := rfl
theorem toSentinel_invalidAttribute : VmError.invalidAttribute.toSentinel = ERR_INVALID_ATTRIBUTE := rfl
theorem toSentinel_badSeeds : VmError.badSeeds.toSentinel = ERR_BAD_SEEDS := rfl
theorem toSentinel_readonlyModified : VmError.readonlyModified.toSentinel = ERR_READONLY_MODIFIED := rfl
theorem toSentinel_invalidRealloc : VmError.invalidRealloc.toSentinel = ERR_INVALID_REALLOC := rfl

end Examples.L1Pin
