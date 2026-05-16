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

/-! ## End-to-end soundness: cuTripleWithin lifts to Runner.run

These are the headline theorems of this file. Together with
`executeFnCpi_eq_executeFn_of_no_cpi_array`, they say: if you've
proved a `cuTripleWithin` over the decoded instruction array of a
bytecode, the same property holds for the actual bytes when executed
by `Runner.run`. -/

/-- **Form A (witness):** A `cuTripleWithin` proven over a decoded
    instruction array produces a k-step witness state inside the
    pure-`executeFn` trace launched from `Runner.initialState cfg`,
    where the post-assertion `Q` holds.

    The witness is in terms of `executeFn`, not `Runner.run`, because
    `cuTripleWithin` only constrains the trace up to step k. To
    conclude about `run`'s output state, use `run_terminates_with_spec`
    below (it requires the spec to land on an `Insn.exit`). -/
theorem run_reaches_spec
    {N exit_ : Nat} {cr : CodeReq} {P Q : Assertion}
    (insns : Array Insn) (cfg : RunConfig)
    (hcr : cr.SatisfiedBy (fetchFromArray insns))
    (htrip : cuTripleWithin N 0 exit_ cr P Q)
    (hP : P.holdsFor (initialState cfg)) :
    ∃ k, k ≤ N ∧
      (executeFn (fetchFromArray insns) (initialState cfg) k).pc = exit_ ∧
      (executeFn (fetchFromArray insns) (initialState cfg) k).exitCode = none ∧
      Q.holdsFor (executeFn (fetchFromArray insns) (initialState cfg) k) := by
  -- Instantiate the triple with R = emp; coerce P ⇔ P ** emp on holdsFor.
  have hPemp : (P ** emp).holdsFor (initialState cfg) := by
    rcases hP with ⟨hp, hcompat, hPhp⟩
    exact ⟨hp, hcompat, (sepConj_emp_right hp).mpr hPhp⟩
  obtain ⟨k, hk, hpc, hex, hQemp⟩ :=
    htrip emp pcFree_emp (fetchFromArray insns) hcr (initialState cfg) hPemp
          (initialState_pc cfg) (initialState_exitCode cfg)
  refine ⟨k, hk, hpc, hex, ?_⟩
  rcases hQemp with ⟨hp, hcompat, hQhp⟩
  exact ⟨hp, hcompat, (sepConj_emp_right hp).mp hQhp⟩

/-! ### Form B (terminated run) is deferred

The natural next theorem — "if the spec lands on an `Insn.exit`, then
`Runner.run bs cfg` returns a halted state in which Q-related facts
hold" — needs more infrastructure than fits in this session:

1. **`callStack`-empty invariant.** `step .exit s` halts only when
   `s.callStack = []`; with a non-empty call stack it pops a frame
   instead. The witness state from Form A might have a non-empty
   `callStack` if the program used `.call_local` without an unmatched
   `.exit`. A clean statement either requires the user to discharge
   an invariant, or we prove `callStack = []` from a syntactic
   hypothesis (no `.call_local` reachable on the path to `exit_`).

2. **Q-stability under the exit step.** `step .exit s` modifies
   `s.exitCode` (and possibly `s.regs.r0`). If Q observes either field,
   Q at the witness state and Q at the halted state can differ. For
   typical Solana specs Q doesn't mention these — but stating that
   formally needs a sub-class of "exit-stable" assertions.

The Session-3 worked example (`RunnerSpecDemo.lean`) sidesteps both
by handling the exit step manually for a known three-instruction
program, which will inform Form B's right signature. -/

end Runner
end Svm.SBPF
