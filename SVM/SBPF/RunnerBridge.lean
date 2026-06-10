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

import SVM.SBPF.Runner
import SVM.SBPF.CPSSpec

namespace SVM.SBPF

/-- Whether an instruction is a CPI-call — the only two cases where
    `Runner.executeFnCpiWithFuel` diverges from `step insn s`. -/
def Insn.isCpiCall : Insn → Bool
  | .call .sol_invoke_signed   => true
  | .call .sol_invoke_signed_c => true
  | _                          => false

/-- Whether an instruction is `.call_local` — the only `step` arm that
    *pushes* onto `callStack`. The `.exit` arm with non-empty `callStack`
    *pops*, but the run starts with `callStack = []` and never grows it
    unless a `.call_local` is fetched along the way. -/
def Insn.isCallLocal : Insn → Bool
  | .call_local _ => true
  | _             => false

-- `commitOptional_preserves_callStack` lives in `Machine.lean` (moved
-- there during lift #3 so it's in scope for `InstructionSpecs.lean` —
-- RunnerBridge imports CPSSpec downstream of InstructionSpecs).

/-- `execTryFind` preserves `callStack` in both match arms. Companion
    to `execTryFind_preserves_regions` at `Pda.lean:193`. -/
@[simp] theorem execTryFind_preserves_callStack (s : State) :
    (Pda.execTryFind s).callStack = s.callStack := by
  simp only [Pda.execTryFind]
  split <;> simp

/-- `execSyscall` never modifies `callStack`. The CPI-stub
    `Cpi.exec` just sets `r0 := 0`; all other syscalls touch only
    `regs`/`mem`/`log`/`returnData`. -/
@[simp] theorem execSyscall_preserves_callStack (sc : Syscall) (s : State) :
    (execSyscall sc s).callStack = s.callStack := by
  cases sc <;> first | rfl | simp [execSyscall]

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
          simp only [executeFnCpiWithFuel, hex, hf, Runner.traceStep,
                     TRACE_STEPS, Bool.false_eq_true, if_false]
          congr 1
          cases insn with
          | call sc => cases sc <;> first | rfl | (simp [Insn.isCpiCall] at hnc)
          | _ => rfl
        have hrhs : executeFn fetch s (fuel' + 1) = executeFn fetch (step insn s) fuel' :=
          executeFn_step fetch s fuel' insn hex hf
        rw [hlhs, hrhs]
        exact ih (step insn s)

/-- Lift a "for all members of an Array Insn" property to a "for all
    fetch lookups" property. Used to discharge the fetch-form
    hypotheses in `executeFnCpi_eq_executeFn_of_no_cpi`,
    `executeFn_callStack_empty`, etc. from a simpler
    `∀ i ∈ insns, ...` premise. -/
theorem fetchFromArray_property_of_mem
    {insns : Array Insn} {P : Insn → Bool}
    (h : ∀ i, i ∈ insns → P i = false) :
    ∀ a i, fetchFromArray insns a = some i → P i = false := by
  intro a i hfetch
  unfold fetchFromArray at hfetch
  by_cases hbnd : a < insns.size
  · simp [hbnd] at hfetch
    exact h i (Array.mem_iff_getElem.mpr ⟨a, hbnd, hfetch⟩)
  · simp [hbnd] at hfetch

/-- Convenience corollary specialized to `fetchFromArray`. The hypothesis
    becomes a property of the concrete instruction array — discharged
    by `decide` once the array is a closed literal. -/
theorem executeFnCpi_eq_executeFn_of_no_cpi_array
    (registry : Nat → Option ByteArray) (insns : Array Insn)
    (s : State) (fuel : Nat)
    (h : ∀ i, i ∈ insns → Insn.isCpiCall i = false) :
    executeFnCpi registry (fetchFromArray insns) s fuel =
      executeFn (fetchFromArray insns) s fuel :=
  executeFnCpi_eq_executeFn_of_no_cpi registry (fetchFromArray insns) s fuel
    (fetchFromArray_property_of_mem h)

/-! ## callStack-empty invariant

The `.exit` instruction halts *only* when `s.callStack = []`. With a
non-empty `callStack` it pops the top frame and continues execution.
The demos rely on the halting behavior, so we prove that — under the
hypothesis that no `.call_local` (the only push) is fetched along the
way — `callStack = []` is preserved throughout the trace. -/

/-- One-step preservation. For any instruction that's neither
    `.call_local` (which would push) nor a CPI-call (which routes
    through `executeFnCpiWithFuel`'s body, not `step`), `step insn s`
    keeps `s.callStack = []` intact.

    Most cases are trivial record updates that don't mention
    `callStack`; the `.exit` arm depends on `h_cs` to take the halt
    branch; the `.call syscall` arm routes through
    `execSyscall_preserves_callStack`. -/
theorem step_callStack_empty_preserved (insn : Insn) (s : State)
    (h_cs : s.callStack = [])
    (h_ncl : Insn.isCallLocal insn = false) :
    (step insn s).callStack = [] := by
  cases insn with
  | call_local _ => simp [Insn.isCallLocal] at h_ncl
  | exit =>
    -- step .exit with callStack=[] takes the halt arm:
    -- { s with exitCode := some _ }.callStack = s.callStack = []
    simp only [step, h_cs]
  | call sc =>
    -- step .call syscall = { (execSyscall sc s) with pc := _, cuConsumed := _ }
    -- callStack = (execSyscall sc s).callStack = s.callStack = []
    simp only [step, execSyscall_preserves_callStack]
    exact h_cs
  | _ =>
    -- All remaining arms are record updates that don't set callStack,
    -- so the result's callStack reduces (via field projection) to
    -- s.callStack, which is [] by h_cs.
    first
    | exact h_cs
    | (simp only [step]; exact h_cs)
    | (simp only [step]; split <;> exact h_cs)

/-- Trace invariant: under no-`.call_local` non-CPI fetch from an
    initial `callStack = []` state, `executeFn` keeps `callStack`
    empty for any fuel. -/
theorem executeFn_callStack_empty (fetch : Nat → Option Insn) (s : State) (k : Nat)
    (h_cs : s.callStack = [])
    (h_safe : ∀ a i, fetch a = some i → Insn.isCallLocal i = false) :
    (executeFn fetch s k).callStack = [] := by
  induction k generalizing s with
  | zero => exact h_cs
  | succ k' ih =>
    unfold executeFn
    cases hex : s.exitCode with
    | some _ => exact h_cs
    | none =>
      cases hf : fetch s.pc with
      | none => exact h_cs
      | some insn =>
        have hncl : Insn.isCallLocal insn = false := h_safe s.pc insn hf
        have h_step : (step insn s).callStack = [] :=
          step_callStack_empty_preserved insn s h_cs hncl
        exact ih (step insn s) h_step

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
    (htrip : cuTripleWithin N 0 0 exit_ cr P Q)
    (hP : P.holdsFor (initialState cfg)) :
    ∃ k, k ≤ N ∧
      (executeFn (fetchFromArray insns) (initialState cfg) k).pc = exit_ ∧
      (executeFn (fetchFromArray insns) (initialState cfg) k).exitCode = none ∧
      Q.holdsFor (executeFn (fetchFromArray insns) (initialState cfg) k) := by
  -- Instantiate the triple with R = emp; coerce P ⇔ P ** emp on holdsFor.
  have hPemp : (P ** emp).holdsFor (initialState cfg) := by
    rcases hP with ⟨hp, hcompat, hPhp⟩
    exact ⟨hp, hcompat, (sepConj_emp_right hp).mpr hPhp⟩
  obtain ⟨k, hk, hpc, hex, _hcu, hQemp⟩ :=
    htrip emp pcFree_emp (fetchFromArray insns) hcr (initialState cfg) hPemp
          (initialState_pc cfg) (initialState_exitCode cfg)
  refine ⟨k, hk, hpc, hex, ?_⟩
  rcases hQemp with ⟨hp, hcompat, hQhp⟩
  exact ⟨hp, hcompat, (sepConj_emp_right hp).mp hQhp⟩

/-- **Form A-mem:** Memory-region variant of `run_reaches_spec`.
    Threads the `rr : RegionTable → Prop` precondition through
    `cuTripleWithinMem`. Useful for macro specs that pin region
    requirements (e.g. `containsRange ∧ containsWritable`). -/
theorem run_reaches_spec_mem
    {N exit_ : Nat} {cr : CodeReq} {P Q : Assertion}
    {rr : Memory.RegionTable → Prop}
    (insns : Array Insn) (cfg : RunConfig)
    (hcr : cr.SatisfiedBy (fetchFromArray insns))
    (htrip : cuTripleWithinMem N 0 0 exit_ cr P Q rr)
    (hP : P.holdsFor (initialState cfg))
    (hregions : rr (initialState cfg).regions) :
    ∃ k, k ≤ N ∧
      (executeFn (fetchFromArray insns) (initialState cfg) k).pc = exit_ ∧
      (executeFn (fetchFromArray insns) (initialState cfg) k).exitCode = none ∧
      Q.holdsFor (executeFn (fetchFromArray insns) (initialState cfg) k) := by
  obtain ⟨k, hk, hpc, hex, _hcu, hQ⟩ :=
    htrip.toExec hcr hP (initialState_pc cfg) (initialState_exitCode cfg) hregions
  exact ⟨k, hk, hpc, hex, hQ⟩

/-- Shared core: given a Form-A-style k-step witness state at the
    `Insn.exit` slot, plus the no-CPI / no-call_local / budget
    hypotheses, conclude that `Runner.run` returns `step Insn.exit s_k`.
    Factored out so both `run_terminates_with_spec` and
    `run_terminates_with_spec_mem` can share the post-exit composition. -/
private theorem run_terminates_after_witness
    {N k exit_ : Nat} {Q : Assertion}
    {bs : ByteArray} {insns : Array Insn} {cfg : RunConfig}
    (hdecode : Decode.decodeProgram bs = some insns)
    (hexit_fetch : fetchFromArray insns exit_ = some Insn.exit)
    (hnoCpi : ∀ i, i ∈ insns → Insn.isCpiCall i = false)
    (hnoCallLocal : ∀ i, i ∈ insns → Insn.isCallLocal i = false)
    (hbudget : N + 1 ≤ cfg.cuBudget)
    (hk : k ≤ N)
    (hpc : (executeFn (fetchFromArray insns) (initialState cfg) k).pc = exit_)
    (hex : (executeFn (fetchFromArray insns) (initialState cfg) k).exitCode = none)
    (hQ : Q.holdsFor (executeFn (fetchFromArray insns) (initialState cfg) k)) :
    let s_witness := executeFn (fetchFromArray insns) (initialState cfg) k
    s_witness.pc = exit_ ∧
    s_witness.exitCode = none ∧
    Q.holdsFor s_witness ∧
    Runner.run bs cfg = some (step Insn.exit s_witness) ∧
    (step Insn.exit s_witness).exitCode = some s_witness.regs.r0 := by
  -- callStack stays empty along the trace from initialState (no `.call_local`).
  have hcs : (executeFn (fetchFromArray insns) (initialState cfg) k).callStack = [] :=
    executeFn_callStack_empty (fetchFromArray insns) (initialState cfg) k
      (initialState_callStack cfg) (fetchFromArray_property_of_mem hnoCallLocal)
  refine ⟨hpc, hex, hQ, ?_, ?_⟩
  · -- Goal: Runner.run bs cfg = some (step Insn.exit s_witness)
    have h_step_exit_halted :
        (step Insn.exit (executeFn (fetchFromArray insns) (initialState cfg) k)).exitCode =
          some ((executeFn (fetchFromArray insns) (initialState cfg) k).regs.get Reg.r0) := by
      simp only [step, hcs]
    have h_one_step : executeFn (fetchFromArray insns)
        (executeFn (fetchFromArray insns) (initialState cfg) k) 1 =
        step Insn.exit (executeFn (fetchFromArray insns) (initialState cfg) k) := by
      have hf : (fetchFromArray insns)
          (executeFn (fetchFromArray insns) (initialState cfg) k).pc = some Insn.exit := by
        rw [hpc]; exact hexit_fetch
      rw [executeFn_step (fetchFromArray insns)
          (executeFn (fetchFromArray insns) (initialState cfg) k) 0 Insn.exit hex hf]
      simp [executeFn]
    have h_k1 : executeFn (fetchFromArray insns) (initialState cfg) (k + 1) =
                step Insn.exit (executeFn (fetchFromArray insns) (initialState cfg) k) := by
      rw [executeFn_compose (fetchFromArray insns) (initialState cfg) k 1, h_one_step]
    have h_halted_after_k1 : ∀ m,
        executeFn (fetchFromArray insns)
          (step Insn.exit (executeFn (fetchFromArray insns) (initialState cfg) k)) m =
          step Insn.exit (executeFn (fetchFromArray insns) (initialState cfg) k) := by
      intro m
      exact executeFn_halted (fetchFromArray insns) _ m _ h_step_exit_halted
    have h_kp1_le : k + 1 ≤ cfg.cuBudget := Nat.le_trans (Nat.add_le_add_right hk 1) hbudget
    have h_full : executeFn (fetchFromArray insns) (initialState cfg) cfg.cuBudget =
                  step Insn.exit (executeFn (fetchFromArray insns) (initialState cfg) k) := by
      have h_eq : cfg.cuBudget = (k + 1) + (cfg.cuBudget - (k + 1)) :=
        (Nat.add_sub_cancel' h_kp1_le).symm
      rw [h_eq, executeFn_compose (fetchFromArray insns) (initialState cfg) (k + 1)
            (cfg.cuBudget - (k + 1)), h_k1, h_halted_after_k1]
    have h_bridge : executeFnCpi cfg.programRegistry (fetchFromArray insns)
                                  (initialState cfg) cfg.cuBudget =
                    executeFn (fetchFromArray insns) (initialState cfg) cfg.cuBudget :=
      executeFnCpi_eq_executeFn_of_no_cpi_array cfg.programRegistry insns
        (initialState cfg) cfg.cuBudget hnoCpi
    unfold Runner.run
    rw [hdecode]
    show some _ = some _
    congr 1
    rw [h_bridge, h_full]
  · -- Goal: (step Insn.exit s_witness).exitCode = some s_witness.regs.r0
    -- step .exit on callStack=[] produces { s with exitCode := some (regs.get .r0) }.
    -- After rewriting callStack via hcs, the match's [] arm fires; .exitCode
    -- projection on the record literal then reduces by iota.
    show (step Insn.exit (executeFn (fetchFromArray insns) (initialState cfg) k)).exitCode = _
    unfold step
    rw [hcs]
    rfl

/-- **Form B (terminated run):** Given that the spec lands on an
    `Insn.exit` and the program has no `.call_local` or CPI-call,
    `Runner.run bs cfg` produces a halted state equal to
    `step Insn.exit s_witness`, where `s_witness` is the Form-A
    k-step witness. Q holds at the witness (pre-exit) state;
    `s_witness.regs.r0` is surfaced as `Runner.run`'s exit code.

    Q-stability under the exit step is not claimed — typical Solana
    specs don't mention `r0`/`exitCode`, but stating that formally is
    a separate framework. Callers project the parts of Q they need
    from the witness state, then use the run-output-equals-step-exit
    equation to link to `Runner.run`'s output. -/
theorem run_terminates_with_spec
    {N exit_ : Nat} {cr : CodeReq} {P Q : Assertion}
    {bs : ByteArray} {insns : Array Insn} {cfg : RunConfig}
    (hdecode : Decode.decodeProgram bs = some insns)
    (hcr : cr.SatisfiedBy (fetchFromArray insns))
    (hexit_fetch : fetchFromArray insns exit_ = some Insn.exit)
    (hnoCpi : ∀ i, i ∈ insns → Insn.isCpiCall i = false)
    (hnoCallLocal : ∀ i, i ∈ insns → Insn.isCallLocal i = false)
    (htrip : cuTripleWithin N 0 0 exit_ cr P Q)
    (hP : P.holdsFor (initialState cfg))
    (hbudget : N + 1 ≤ cfg.cuBudget) :
    ∃ k, k ≤ N ∧
      let s_witness := executeFn (fetchFromArray insns) (initialState cfg) k
      s_witness.pc = exit_ ∧
      s_witness.exitCode = none ∧
      Q.holdsFor s_witness ∧
      Runner.run bs cfg = some (step Insn.exit s_witness) ∧
      (step Insn.exit s_witness).exitCode = some s_witness.regs.r0 := by
  obtain ⟨k, hk, hpc, hex, hQ⟩ := run_reaches_spec insns cfg hcr htrip hP
  exact ⟨k, hk, run_terminates_after_witness hdecode hexit_fetch hnoCpi hnoCallLocal
    hbudget hk hpc hex hQ⟩

/-- **Form B-mem (terminated run, memory-region variant):** Mirrors
    `run_terminates_with_spec` but takes a `cuTripleWithinMem` plus
    the region-condition discharge `hregions`. The macro library is
    proven in `cuTripleWithinMem` form (memory specs carry an `rr`
    region predicate); this is the variant the Session-3 demos use. -/
theorem run_terminates_with_spec_mem
    {N exit_ : Nat} {cr : CodeReq} {P Q : Assertion}
    {rr : Memory.RegionTable → Prop}
    {bs : ByteArray} {insns : Array Insn} {cfg : RunConfig}
    (hdecode : Decode.decodeProgram bs = some insns)
    (hcr : cr.SatisfiedBy (fetchFromArray insns))
    (hexit_fetch : fetchFromArray insns exit_ = some Insn.exit)
    (hnoCpi : ∀ i, i ∈ insns → Insn.isCpiCall i = false)
    (hnoCallLocal : ∀ i, i ∈ insns → Insn.isCallLocal i = false)
    (htrip : cuTripleWithinMem N 0 0 exit_ cr P Q rr)
    (hP : P.holdsFor (initialState cfg))
    (hregions : rr (initialState cfg).regions)
    (hbudget : N + 1 ≤ cfg.cuBudget) :
    ∃ k, k ≤ N ∧
      let s_witness := executeFn (fetchFromArray insns) (initialState cfg) k
      s_witness.pc = exit_ ∧
      s_witness.exitCode = none ∧
      Q.holdsFor s_witness ∧
      Runner.run bs cfg = some (step Insn.exit s_witness) ∧
      (step Insn.exit s_witness).exitCode = some s_witness.regs.r0 := by
  obtain ⟨k, hk, hpc, hex, hQ⟩ :=
    run_reaches_spec_mem insns cfg hcr htrip hP hregions
  exact ⟨k, hk, run_terminates_after_witness hdecode hexit_fetch hnoCpi hnoCallLocal
    hbudget hk hpc hex hQ⟩

end Runner
end SVM.SBPF
