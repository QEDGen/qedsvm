/-
  Bridge from the spec-level stepper (`executeFn`) to the runtime stepper
  (`Runner.executeFnCpi`) used by `Runner.run`.

  Why: `cuTripleWithin` is stated in terms of `executeFn fetch s k`. The
  actual `Runner.run` entrypoint uses `Runner.executeFnCpi` to additionally
  handle cross-program-invocation (the two `sol_invoke_signed*` syscalls).
  For any program whose decoded instruction stream contains no CPI-call,
  the two steppers coincide; this file proves exactly that.

  Closes the "spec-level stepper ≠ runtime stepper" half of the decode →
  spec wiring gap.
-/

import Svm.SBPF.Runner
import Svm.SBPF.CPSSpec

namespace Svm.SBPF

/-- Whether an instruction is a CPI-call — the only two cases where
    `Runner.executeFnCpiWithFuel` diverges from `step insn s`. -/
def Insn.isCpiCall : Insn → Bool
  | .call .sol_invoke_signed   => true
  | .call .sol_invoke_signed_c => true
  | _                          => false

namespace Runner

/-- The per-instruction step body of `executeFnCpiWithFuel` collapses to
    `step insn s` whenever the fetched instruction is not a CPI-call.

    This is the workhorse case lemma; `executeFnCpi_eq_executeFn_of_no_cpi`
    inducts on fuel and invokes it at each step. The case split on `insn`
    has small per-arm bodies thanks to the `cpiCallNextState` extraction
    in `Runner.lean`. -/
private theorem stepBody_eq_step_of_noCpi
    {registry : Nat → Option ByteArray} {s : State} {insn : Insn} {fuel' : Nat}
    {runCallee₁ runCallee₂ : ByteArray → Option (State × Memory.Mem × Nat)}
    (hnc : Insn.isCpiCall insn = false) :
    (match insn with
      | .call .sol_invoke_signed =>
        cpiCallNextState registry s .sol_invoke_signed fuel' runCallee₁
      | .call .sol_invoke_signed_c =>
        cpiCallNextState registry s .sol_invoke_signed_c fuel' runCallee₂
      | _ => step insn s) = step insn s := by
  cases insn with
  | call sc => cases sc <;> first | rfl | (simp [Insn.isCpiCall] at hnc)
  | _ => rfl

/-- `executeFnCpi ≡ executeFn` on programs that never invoke CPI.

    Concretely: if the fetch function never produces an instruction that
    triggers the CPI-call arm of `executeFnCpiWithFuel`, then running for
    any amount of fuel under `executeFnCpi` produces the same final state
    as running under the pure `executeFn` stepper that `cuTripleWithin`
    reasons about. -/
theorem executeFnCpi_eq_executeFn_of_no_cpi
    (registry : Nat → Option ByteArray) (fetch : Nat → Option Insn)
    (s : State) (fuel : Nat)
    (h : ∀ a i, fetch a = some i → Insn.isCpiCall i = false) :
    executeFnCpi registry fetch s fuel = executeFn fetch s fuel := by
  -- Strengthen to the `.1` form of the WithFuel stepper so we can induct.
  suffices hAux : ∀ (s : State) (fuel : Nat),
      (executeFnCpiWithFuel registry fetch s fuel).1 = executeFn fetch s fuel by
    show (executeFnCpiWithFuel registry fetch s fuel).1 = _
    exact hAux s fuel
  clear s fuel
  intro s fuel
  induction fuel generalizing s with
  | zero =>
    -- Both definitions return `s` at fuel = 0.
    rfl
  | succ fuel' ih =>
    show (executeFnCpiWithFuel registry fetch s (fuel' + 1)).1 = executeFn fetch s (fuel' + 1)
    cases hex : s.exitCode with
    | some code =>
      -- Halted: executeFnCpiWithFuel returns (s, fuel'+1); executeFn returns s.
      have hlhs : (executeFnCpiWithFuel registry fetch s (fuel' + 1)).1 = s := by
        simp only [executeFnCpiWithFuel, hex]
      have hrhs : executeFn fetch s (fuel' + 1) = s :=
        executeFn_halted fetch s (fuel' + 1) code hex
      rw [hlhs, hrhs]
    | none =>
      cases hf : fetch s.pc with
      | none =>
        -- Invalid PC: both write ERR_INVALID_PC and halt.
        have hlhs : (executeFnCpiWithFuel registry fetch s (fuel' + 1)).1 =
            { s with exitCode := some ERR_INVALID_PC } := by
          simp only [executeFnCpiWithFuel, hex, hf]
        have hrhs : executeFn fetch s (fuel' + 1) =
            { s with exitCode := some ERR_INVALID_PC } := by
          simp only [executeFn, hex, hf]
        rw [hlhs, hrhs]
      | some insn =>
        have hnc : Insn.isCpiCall insn = false := h s.pc insn hf
        have hlhs : (executeFnCpiWithFuel registry fetch s (fuel' + 1)).1 =
                    (executeFnCpiWithFuel registry fetch (step insn s) fuel').1 := by
          simp only [executeFnCpiWithFuel, hex, hf, TRACE_STEPS, Bool.false_eq_true,
                     if_false]
          congr 1
          cases insn with
          | call sc => cases sc <;> first | rfl | (simp [Insn.isCpiCall] at hnc)
          | _ => rfl
        have hrhs : executeFn fetch s (fuel' + 1) = executeFn fetch (step insn s) fuel' :=
          executeFn_step fetch s fuel' insn hex hf
        rw [hlhs, hrhs]
        exact ih (step insn s)

/-- Convenience corollary specialized to `fetchFromArray`. The hypothesis
    becomes a property of the concrete instruction array — discharged
    by `decide` once the array is a closed literal. -/
theorem executeFnCpi_eq_executeFn_of_no_cpi_array
    (registry : Nat → Option ByteArray) (insns : Array Insn)
    (s : State) (fuel : Nat)
    (h : ∀ i, i ∈ insns → Insn.isCpiCall i = false) :
    executeFnCpi registry (fetchFromArray insns) s fuel =
      executeFn (fetchFromArray insns) s fuel := by
  apply executeFnCpi_eq_executeFn_of_no_cpi
  intro a i hfetch
  unfold fetchFromArray at hfetch
  by_cases hbnd : a < insns.size
  · simp [hbnd] at hfetch
    exact h i (Array.mem_iff_getElem.mpr ⟨a, hbnd, hfetch⟩)
  · simp [hbnd] at hfetch

end Runner
end Svm.SBPF
