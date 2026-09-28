/-
  The runner's CPI invoke step as a `Cpi.applyResult` transition.

  `Runner.stepCpi` is the per-instruction step of `executeFnCpiWithFuel`
  with the callee's sub-run as a parameter. Every branch of an invoke
  (`sol_invoke_signed{,_c}`) — depth limit, writable aliasing, native
  dispatch, unregistered program, failed callee build, BPF sub-run — commits
  through `applyResult` once the caller's per-step CU (`chargeCu`) is folded
  into the result's `cuConsumed` (`stepCpi_is_transition`).

  `runnerCallee registry sc` is the callee relation the concrete runner
  induces: the results `r` for which some fuel makes the charged invoke step
  equal `applyResult s r`.
-/

import SVM.SBPF.Runner
import SVM.SBPF.CpiContract

namespace SVM.SBPF
namespace Cpi

/-- The callee relation the runner induces for invoke syscall `sc`. -/
def runnerCallee (registry : Nat → Option ByteArray) (sc : Syscall) : CalleeSemantics :=
  fun s r => ∃ fuel',
    chargeCu (Runner.stepCpi registry (Runner.executeFnCpiWithFuel registry) s fuel' (.call sc))
      = applyResult s r

/-- `chargeCu` after a commit is a commit with one more callee CU. -/
theorem chargeCu_applyResult (s : State) (r : CalleeResult) :
    chargeCu (applyResult s r) = applyResult s { r with cuConsumed := r.cuConsumed + 1 } := by
  simp only [chargeCu, applyResult, Nat.add_assoc]

/-- The fail-closed invoke arms (r0 := 1, no memory change) are commits of an
    error result carrying the caller's own channels. -/
theorem chargeCu_invokeFail (s : State) :
    chargeCu { s with regs := s.regs.set .r0 1, pc := s.pc + 1,
                      cuConsumed := s.cuConsumed + Cpi.cu }
      = applyResult s ⟨1, s.mem, s.log, s.returnData, s.returnDataProgId, 1⟩ := by
  simp only [chargeCu, applyResult, Nat.one_ne_zero, if_false]

/-- Every branch of `cpiCallNextState` on an invoke syscall, charged its
    per-step CU, is an `applyResult` commit, for any callee runner.
    `extract_lets` keeps the heavy lets (pid fold, account parsers) opaque so
    `split` sees only the five structural branches (as in
    `cpiCallNextState_bounded`). -/
theorem cpiCallNextState_is_transition (registry : Nat → Option ByteArray) (s : State)
    (sc : Syscall) (fuel' : Nat) (runCallee : ByteArray → Option (State × Memory.Mem × Nat))
    (hsc : sc = .sol_invoke_signed ∨ sc = .sol_invoke_signed_c) :
    ∃ r, chargeCu (Runner.cpiCallNextState registry s sc fuel' runCallee) = applyResult s r := by
  rcases hsc with rfl | rfl <;>
    (unfold Runner.cpiCallNextState
     extract_lets
     repeat' split
     all_goals
       first
         | exact ⟨_, chargeCu_invokeFail s⟩
         | exact ⟨_, chargeCu_applyResult _ _⟩)

/-- Every branch of the runner's invoke step is an `applyResult` transition.
    Witnesses: fail-closed arms (depth, aliasing, unregistered, failed callee
    build) `⟨1, s.mem, s.log, s.returnData, s.returnDataProgId, 1⟩`; native
    `⟨nr.r0, nr.mem, s.log, s.returnData, s.returnDataProgId, nr.cu + 1⟩`;
    BPF `⟨subFinal.exitCode.getD 1, newMem, subFinal.log, subFinal.returnData,
    subFinal.returnDataProgId, subFinal.cuConsumed + 1⟩`. The `+ 1` is
    `chargeCu`'s per-step unit. -/
theorem stepCpi_is_transition (registry : Nat → Option ByteArray)
    (subRun : (Nat → Option Insn) → State → Nat → State × Nat) (s : State) (fuel' : Nat)
    (sc : Syscall) (hsc : sc = .sol_invoke_signed ∨ sc = .sol_invoke_signed_c) :
    ∃ r, chargeCu (Runner.stepCpi registry subRun s fuel' (.call sc)) = applyResult s r := by
  -- `extract_lets` keeps the ABI decoding lets opaque; a bare `exact` makes
  -- the unifier whnf them and times out on the C arm.
  rcases hsc with rfl | rfl <;>
    (unfold Runner.stepCpi
     extract_lets
     exact cpiCallNextState_is_transition registry s _ fuel' _ (by simp))

end Cpi
end SVM.SBPF
