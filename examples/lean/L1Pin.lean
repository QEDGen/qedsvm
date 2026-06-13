/-
Regression pins for the L1 fault-vs-exit distinction (audit L1).

The `ERR_*` sentinels live in `exitCode : Option Nat`, so an `exit` of
exactly a sentinel VALUE is numerically indistinguishable from the fault.
`State.vmError : Option VmError` is the typed channel that disambiguates:
every abort site sets it alongside the `exitCode` sentinel, and a clean
`exit` never does. These pins lock both directions:

  - a clean `exit` whose r0 equals a fault sentinel sets `exitCode` to
    that sentinel but leaves `vmError = none`;
  - each fault site sets `vmError = some <the typed fault>` AND the
    matching `exitCode` sentinel, with `VmError.toSentinel` agreeing.

So a spec can now assert "the program FAULTED" as `vmError = some e`,
which no clean exit can satisfy — closing the collision.
-/
import SVM.SBPF.Execute

namespace Examples.L1Pin
open SVM.SBPF

/-- A state whose r0 is the `ERR_ABORT` sentinel and whose call stack is
    empty (so `exit` terminates the program). -/
def cleanExitState : State := { (default : State) with regs := { r0 := ERR_ABORT } }

/-- A CLEAN `exit` carrying r0 = `ERR_ABORT` reports that sentinel in
    `exitCode` — yet `vmError` stays `none`. This is exactly the
    `sentinel_exit.so` program in the model: not a fault. -/
theorem clean_exit_sentinel_no_fault :
    (step .exit cleanExitState).exitCode = some ERR_ABORT ∧
    (step .exit cleanExitState).vmError = none := by
  refine ⟨rfl, rfl⟩

/-- `.callx` fails closed: it sets the typed fault AND the sentinel. -/
theorem callx_sets_vmError :
    (step (.callx .r0) (default : State)).vmError = some .unsupportedInstruction ∧
    (step (.callx .r0) (default : State)).exitCode = some ERR_UNSUPPORTED_INSTRUCTION := by
  refine ⟨rfl, rfl⟩

/-- `abort` sets `vmError = some .abort` and the same `ERR_ABORT`
    sentinel a clean exit can carry — but now they are distinguishable
    via `vmError`. -/
theorem abort_sets_vmError :
    (SVM.SBPF.Abort.execAbort (default : State)).vmError = some .abort ∧
    (SVM.SBPF.Abort.execAbort (default : State)).exitCode = some ERR_ABORT := by
  refine ⟨rfl, rfl⟩

/-- THE collision, now resolved: an `abort` and a clean `exit` of the
    `ERR_ABORT` value report the SAME `exitCode`, but only the abort sets
    `vmError`. A spec phrased over `vmError` cannot be satisfied by the
    clean exit. -/
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

end Examples.L1Pin
