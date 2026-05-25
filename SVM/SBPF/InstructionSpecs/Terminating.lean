import SVM.SBPF.InstructionSpecs.Syscalls.Sysvar

namespace SVM.SBPF

open Memory

/-! ## Terminating triples — abort / sol_panic_ / exit

These three instructions intentionally halt execution with a non-`none`
exitCode. They use `cuTripleAbortsWithin` (defined in `CPSSpec.lean`),
which captures "this PC aborts within N steps with this errCode" without
asserting any post-state — there is none, the program is stuck.

`abort` and `sol_panic_` both set `exitCode := some ERR_ABORT` (see
`SVM.SBPF.Abort.execAbort` / `execPanic` and the executor's `.call`
arm in `Execute.lean`). `sol_panic_` additionally appends the
caller-supplied message bytes to `State.log`, but the message pointers in
r1/r2/r3 are not constrained at the SL level — diagnostic output is
silent in `PartialState`.

`exit` is the success-exit instruction: when the callStack is empty it
sets `exitCode := some (r0)`. The callStack discipline is not yet
modelled by `PartialState` (see deferred lift #3); the `exit_aborts_spec`
theorem therefore takes `s.callStack = []` as an extra hypothesis. -/

/-- `.call .abort`: unconditional abort. The syscall ignores all
    register inputs and sets `exitCode := some ERR_ABORT`. Precondition is
    `emp`: the spec owns no resources; the universally-quantified frame
    carries everything else through unobserved up to the point of
    abort. -/
theorem call_abort_aborts_spec (pc : Nat) :
    cuTripleAbortsWithin 1 pc
      (CodeReq.singleton pc (.call .abort))
      emp ERR_ABORT := by
  intro R hRfree fetch hcr s hPR hpc hex
  obtain ⟨hp, hcompat, h1, hR, hd, hu, hP1, hRsat⟩ := hPR
  -- emp pre: h1 = empty.
  rw [hP1, PartialState.union_empty_left] at hu
  rw [hP1] at hd
  clear hP1 h1
  have hfetch : fetch s.pc = some (.call .abort) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hexec : executeFn fetch s 1 =
      { (Abort.execAbort s) with pc := s.pc + 1
                                 cuConsumed := (Abort.execAbort s).cuConsumed
                                   + syscallCu .abort s } := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch,
        executeFn_zero]
    simp only [step, execSyscall]
  refine ⟨1, Nat.le_refl 1, ?_⟩
  rw [hexec]
  -- post: exitCode = some ERR_ABORT
  show (Abort.execAbort s).exitCode = some ERR_ABORT
  rfl

/-- `.call .sol_panic_`: unconditional abort with logging of the message
    pointed to by r1/r2 (file/line in r3/r4/r5 are diagnostic and silent
    at the SL level). Sets `exitCode := some ERR_ABORT`.

    Same `emp` precondition as `abort`: the caller's message-pointer
    registers are not constrained by this triple — they're already loaded
    by the caller and the resulting `log` entry is silent in
    `PartialState`. -/
theorem call_sol_panic_aborts_spec (pc : Nat) :
    cuTripleAbortsWithin 1 pc
      (CodeReq.singleton pc (.call .sol_panic_))
      emp ERR_ABORT := by
  intro R hRfree fetch hcr s hPR hpc hex
  obtain ⟨hp, hcompat, h1, hR, hd, hu, hP1, hRsat⟩ := hPR
  rw [hP1, PartialState.union_empty_left] at hu
  rw [hP1] at hd
  clear hP1 h1
  have hfetch : fetch s.pc = some (.call .sol_panic_) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hexec : executeFn fetch s 1 =
      { (Abort.execPanic s) with pc := s.pc + 1
                                 cuConsumed := (Abort.execPanic s).cuConsumed
                                   + syscallCu .sol_panic_ s } := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch,
        executeFn_zero]
    simp only [step, execSyscall]
  refine ⟨1, Nat.le_refl 1, ?_⟩
  rw [hexec]
  show (Abort.execPanic s).exitCode = some ERR_ABORT
  rfl

/-- `Insn.exit` with empty callStack: the success-exit instruction sets
    `exitCode := some (r0)`, picking up the program's return value from
    register r0.

    Because the empty-callStack condition is not yet expressible in
    `PartialState` (see deferred lift #3, "callStack in PartialState"),
    this spec is stated as a standalone `cuTripleAbortsWithin` parametric
    over an `s.callStack = []` hypothesis threaded through a customised
    universal-state body. Concretely we prove the existential after
    inlining the abort-triple definition and adding the extra hypothesis
    as a side condition.

    Pre: `(.r0 ↦ᵣ vR0)`; side condition: `s.callStack = []`; post errCode:
    `vR0`. The "success-exit" case (exitCode = 0) follows by specializing
    `vR0 := 0`. -/
theorem exit_aborts_spec (vR0 pc : Nat) :
    ∀ (R : Assertion), R.pcFree →
    ∀ (fetch : Nat → Option Insn),
      (CodeReq.singleton pc .exit).SatisfiedBy fetch →
    ∀ (s : State), ((.r0 ↦ᵣ vR0) ** R).holdsFor s → s.pc = pc →
        s.exitCode = none → s.callStack = [] →
      ∃ k, k ≤ 1 ∧ (executeFn fetch s k).exitCode = some vR0 := by
  intro R hRfree fetch hcr s hPR hpc hex hcs
  obtain ⟨hp, hcompat, h1, hR, hd, hu, hreg, hRsat⟩ := hPR
  rw [hreg] at hu hd
  clear hreg h1
  have hcr_regs := hcompat.regs
  have hp_regs_r0 : hp.regs .r0 = some vR0 := by
    rw [← hu]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have hs_regs_r0 : s.regs.get .r0 = vR0 := hcr_regs .r0 vR0 hp_regs_r0
  have hfetch : fetch s.pc = some .exit := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hexec : executeFn fetch s 1 = step .exit s := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch,
        executeFn_zero]
  have hstep : step .exit s = { s with exitCode := some (s.regs.get .r0) } := by
    simp only [step, hcs]
  refine ⟨1, Nat.le_refl 1, ?_⟩
  rw [hexec, hstep]
  show some (s.regs.get .r0) = some vR0
  rw [hs_regs_r0]


end SVM.SBPF
