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
theorem call_abort_faults_spec (pc : Nat) (nCu : Nat)
    (hCu : ∀ s : State,
        (step (.call .abort) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleFaultsWithin 1 nCu pc
      (CodeReq.singleton pc (.call .abort))
      emp .abort := by
  intro R hRfree fetch hcr s hPR hpc hex hbud
  obtain ⟨hp, hcompat, h1, hR, hd, hu, hP1, hRsat⟩ := hPR
  -- emp pre: h1 = empty.
  rw [hP1, PartialState.union_empty_left] at hu
  rw [hP1] at hd
  clear hP1 h1
  have hfetch : fetch s.pc = some (.call .abort) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hstep_eq : executeFn fetch s 1 = chargeCu (step (.call .abort) s) := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch, executeFn_zero]
  have hexec : executeFn fetch s 1 =
      chargeCu { (Abort.execAbort s) with
                 pc := s.pc + 1
                 cuConsumed := (Abort.execAbort s).cuConsumed
                   + syscallCu .abort s } := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch,
        executeFn_zero]
    simp only [step, execSyscall]
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_⟩
  · rw [hexec]
    -- post: exitCode = some (VmError.abort).toSentinel = some ERR_ABORT
    show (Abort.execAbort s).exitCode = some VmError.abort.toSentinel
    rfl
  · rw [hexec]
    -- post: the TYPED fault is `.abort` (L1)
    show (Abort.execAbort s).vmError = some .abort
    rfl
  · rw [hstep_eq]
    show (step (.call .abort) s).cuConsumed + 1 ≤ s.cuConsumed + 1 + nCu
    have := hCu s; omega

/-- The original abort triple, derived from the typed-fault spec by
    forgetting the `vmError` conjunct (`VmError.abort.toSentinel = ERR_ABORT`).
    Kept for the existing `cuTripleAbortsWithin` consumers. -/
theorem call_abort_aborts_spec (pc : Nat) (nCu : Nat)
    (hCu : ∀ s : State,
        (step (.call .abort) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleAbortsWithin 1 nCu pc
      (CodeReq.singleton pc (.call .abort))
      emp ERR_ABORT :=
  cuTripleFaultsWithin_toAborts (call_abort_faults_spec pc nCu hCu)

/-- `.call .sol_panic_`: unconditional abort with logging of the message
    pointed to by r1/r2 (file/line in r3/r4/r5 are diagnostic and silent
    at the SL level). Sets `exitCode := some ERR_ABORT`.

    Same `emp` precondition as `abort`: the caller's message-pointer
    registers are not constrained by this triple — they're already loaded
    by the caller and the resulting `log` entry is silent in
    `PartialState`. -/
theorem call_sol_panic_faults_spec (pc : Nat) (nCu : Nat)
    (hCu : ∀ s : State,
        (step (.call .sol_panic_) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleFaultsWithin 1 nCu pc
      (CodeReq.singleton pc (.call .sol_panic_))
      emp .abort := by
  intro R hRfree fetch hcr s hPR hpc hex hbud
  obtain ⟨hp, hcompat, h1, hR, hd, hu, hP1, hRsat⟩ := hPR
  rw [hP1, PartialState.union_empty_left] at hu
  rw [hP1] at hd
  clear hP1 h1
  have hfetch : fetch s.pc = some (.call .sol_panic_) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hstep_eq : executeFn fetch s 1 = chargeCu (step (.call .sol_panic_) s) := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch, executeFn_zero]
  have hexec : executeFn fetch s 1 =
      chargeCu { (Abort.execPanic s) with
                 pc := s.pc + 1
                 cuConsumed := (Abort.execPanic s).cuConsumed
                   + syscallCu .sol_panic_ s } := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch,
        executeFn_zero]
    simp only [step, execSyscall]
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_⟩
  · rw [hexec]
    show (Abort.execPanic s).exitCode = some VmError.abort.toSentinel
    rfl
  · rw [hexec]
    show (Abort.execPanic s).vmError = some .abort
    rfl
  · rw [hstep_eq]
    show (step (.call .sol_panic_) s).cuConsumed + 1 ≤ s.cuConsumed + 1 + nCu
    have := hCu s; omega

/-- The original `sol_panic_` abort triple, derived from the typed-fault
    spec. -/
theorem call_sol_panic_aborts_spec (pc : Nat) (nCu : Nat)
    (hCu : ∀ s : State,
        (step (.call .sol_panic_) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleAbortsWithin 1 nCu pc
      (CodeReq.singleton pc (.call .sol_panic_))
      emp ERR_ABORT :=
  cuTripleFaultsWithin_toAborts (call_sol_panic_faults_spec pc nCu hCu)

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
        s.exitCode = none → s.cuConsumed + 1 ≤ s.cuBudget → s.callStack = [] →
      ∃ k, k ≤ 1 ∧ (executeFn fetch s k).exitCode = some vR0 := by
  intro R hRfree fetch hcr s hPR hpc hex hbud hcs
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
  have hexec : executeFn fetch s 1 = chargeCu (step .exit s) := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch,
        executeFn_zero]
  have hstep : step .exit s = { s with exitCode := some (s.regs.get .r0) } := by
    simp only [step, hcs]
  refine ⟨1, Nat.le_refl 1, ?_⟩
  rw [hexec, hstep]
  show some (s.regs.get .r0) = some vR0
  rw [hs_regs_r0]

/-- SL-form wrapper around `exit_aborts_spec`: packages the empty
    callStack hypothesis into the assertion `callStackIs []` so that the
    spec becomes a standard `cuTripleAbortsWithin`.

    Step cost is 1; `cuConsumed` does not bump for `.exit` (see
    `Execute.lean` `step .exit` arm — no syscall, no surcharge), so
    `nCu = 0`. -/
theorem exit_aborts_spec_cuTriple (vR0 pc : Nat) :
    cuTripleAbortsWithin 1 0 pc (CodeReq.singleton pc .exit)
      ((.r0 ↦ᵣ vR0) ** callStackIs []) vR0 := by
  intro R hRfree fetch hcr s hPR hpc hex hbud
  -- Destructure ((.r0 ↦ᵣ vR0) ** callStackIs []) ** R.
  obtain ⟨hp, hcompat, h_PQ, h_R, hd_PQR, hu_PQR, h_PQ_sat, h_R_sat⟩ := hPR
  obtain ⟨h_r0, h_cs, hd_r0_cs, hu_r0_cs, h_r0_pred, h_cs_pred⟩ := h_PQ_sat
  -- Chase callStack: callStackIs [] atom owns h_cs.callStack = some [].
  have h_cs_cs : h_cs.callStack = some [] := by
    show h_cs.callStack = some []
    rw [show h_cs = PartialState.singletonCallStack [] from h_cs_pred]
    exact PartialState.singletonCallStack_callStack_self
  have h_r0_cs : h_r0.callStack = none := by
    rw [show h_r0 = PartialState.singletonReg .r0 vR0 from h_r0_pred]
    exact PartialState.singletonReg_callStack
  -- Push h_cs_cs up through hu_r0_cs to get h_PQ.callStack = some [].
  have h_PQ_cs : h_PQ.callStack = some [] := by
    rw [← hu_r0_cs, PartialState.union_callStack_of_left_none h_r0_cs]
    exact h_cs_cs
  -- Push up through hu_PQR to hp.callStack = some [], then to s.
  have hp_cs : hp.callStack = some [] :=
    hu_PQR ▸ PartialState.union_callStack_of_left_some h_PQ_cs
  have hcs : s.callStack = [] := hcompat.callStack [] hp_cs
  -- Reshape pre as (.r0 ↦ᵣ vR0) ** (callStackIs [] ** R) so the inner
  -- sepConj matches exit_aborts_spec's expected frame shape.
  have hRfree' : (callStackIs [] ** R).pcFree :=
    pcFree_sepConj (pcFree_callStackIs _) hRfree
  have hPR' : ((.r0 ↦ᵣ vR0) ** (callStackIs [] ** R)).holdsFor s :=
    holdsFor_sepConj_assoc.mp ⟨hp, hcompat, h_PQ, h_R, hd_PQR, hu_PQR,
      ⟨h_r0, h_cs, hd_r0_cs, hu_r0_cs, h_r0_pred, h_cs_pred⟩, h_R_sat⟩
  obtain ⟨k, hk, hexc⟩ :=
    exit_aborts_spec vR0 pc (callStackIs [] ** R) hRfree' fetch hcr s hPR'
      hpc hex (by omega) hcs
  -- exit_aborts_spec gives k ≤ 1 and exitCode = some vR0. We need to
  -- bound cuConsumed delta ≤ 0. `.exit` does not bump cuConsumed
  -- (only the `.call` syscall arm does — see Execute.lean), so for
  -- k = 0 it's trivial and for k = 1 we unfold step .exit to confirm.
  refine ⟨k, hk, hexc, ?_⟩
  -- k ≤ 1, so k = 0 or k = 1.
  rcases Nat.eq_or_lt_of_le hk with hk_eq | hk_lt
  · -- k = 1
    subst hk_eq
    show (executeFn fetch s 1).cuConsumed ≤ s.cuConsumed + 1 + 0
    have hfetch : fetch s.pc = some .exit := by
      rw [hpc]; exact hcr pc _ CodeReq.singleton_self
    have hexec1 : executeFn fetch s 1 = chargeCu (step .exit s) := by
      rw [show (1 : Nat) = 0 + 1 from rfl,
          executeFn_step fetch s 0 _ hex (by omega) hfetch,
          executeFn_zero]
    have hstep : step .exit s = { s with exitCode := some (s.regs.get .r0) } := by
      simp only [step, hcs]
    rw [hexec1, hstep]
    show s.cuConsumed + 1 ≤ s.cuConsumed + 1 + 0
    omega
  · -- k < 1, so k = 0
    have hk0 : k = 0 := by omega
    subst hk0
    show (executeFn fetch s 0).cuConsumed ≤ s.cuConsumed + 1 + 0
    rw [executeFn_zero]; omega

/-! ## Error-exit collapse — `mov64 r0, err; exit` / `lddw r0, err; exit`

The canonical error-handler landing in compiled Solana programs is a
two-instruction block: set r0 to a constant error code, exit. (Pinocchio
encodes `ProgramError` as `code <<< 32`, which exceeds the 32-bit
`mov64` immediate, so the dispatch-mismatch exit uses `lddw`; small
ad-hoc codes use `mov64`. p_token has 6 `mov64` + 1 `lddw` of these.)

One lemma per shape discharges every such block in one `apply` — the
"error-path collapse" lever from the recovery-pipeline issue. Both are
plain compositions: `{mov64,lddw}_spec` ⨾ `exit_aborts_spec_cuTriple`
via `cuTripleAbortsWithin_seq_abort`. -/

/-- `mov64 r0, err; exit` aborts with `toU64 err`, from any prior r0. -/
theorem errorExit_spec (err : Int) (vR0Old pc : Nat) :
    cuTripleAbortsWithin 2 0 pc
      ((CodeReq.singleton pc (.mov64 .r0 (.imm err))).union
        (CodeReq.singleton (pc + 1) .exit))
      ((.r0 ↦ᵣ vR0Old) ** callStackIs [])
      (toU64 err) :=
  cuTripleAbortsWithin_seq_abort
    (CodeReq.singleton_disjoint_singleton _ _ (by omega))
    (cuTripleWithin_frame_right (callStackIs []) (pcFree_callStackIs _)
      (mov64_imm_spec .r0 err vR0Old pc (by decide)))
    (exit_aborts_spec_cuTriple (toU64 err) (pc + 1))

/-- `lddw r0, err; exit` aborts with `toU64 err`, from any prior r0.
    The lddw form carries 64-bit error codes (pinocchio's
    `ProgramError` encoding `code <<< 32`). -/
theorem errorExit_lddw_spec (err : Int) (vR0Old pc : Nat) :
    cuTripleAbortsWithin 2 0 pc
      ((CodeReq.singleton pc (.lddw .r0 err)).union
        (CodeReq.singleton (pc + 1) .exit))
      ((.r0 ↦ᵣ vR0Old) ** callStackIs [])
      (toU64 err) :=
  cuTripleAbortsWithin_seq_abort
    (CodeReq.singleton_disjoint_singleton _ _ (by omega))
    (cuTripleWithin_frame_right (callStackIs []) (pcFree_callStackIs _)
      (lddw_spec .r0 err vR0Old pc (by decide)))
    (exit_aborts_spec_cuTriple (toU64 err) (pc + 1))

/-! The other half of the idiom: error blocks that set r0 and JUMP to a
shared bare-`exit` block instead of carrying their own exit (p_token's
transfer arm routes every error landing through the single `exit` at
logical 3542). Same collapse, one extra `ja` hop. -/

/-- `mov64 r0, err; ja tgt` with `exit` at `tgt`: aborts with
    `toU64 err`. The side conditions just say the shared exit doesn't
    overlap the two-instruction landing. -/
theorem errorExitJa_spec (err : Int) (vR0Old pc tgt : Nat)
    (h1 : pc ≠ tgt) (h2 : pc + 1 ≠ tgt) :
    cuTripleAbortsWithin 3 0 pc
      (((CodeReq.singleton pc (.mov64 .r0 (.imm err))).union
        (CodeReq.singleton (pc + 1) (.ja tgt))).union
        (CodeReq.singleton tgt .exit))
      ((.r0 ↦ᵣ vR0Old) ** callStackIs [])
      (toU64 err) :=
  cuTripleAbortsWithin_seq_abort
    (CodeReq.Disjoint_union_left
      (CodeReq.singleton_disjoint_singleton _ _ h1)
      (CodeReq.singleton_disjoint_singleton _ _ h2))
    (cuTripleWithin_seq
      (CodeReq.singleton_disjoint_singleton _ _ (by omega))
      (cuTripleWithin_frame_right (callStackIs []) (pcFree_callStackIs _)
        (mov64_imm_spec .r0 err vR0Old pc (by decide)))
      (cuTripleWithin_widen_emp ((.r0 ↦ᵣ toU64 err) ** callStackIs [])
        (pcFree_sepConj (pcFree_regIs _ _) (pcFree_callStackIs _))
        (ja_spec tgt (pc + 1))))
    (exit_aborts_spec_cuTriple (toU64 err) tgt)

/-- `lddw r0, err; ja tgt` with `exit` at `tgt`: aborts with
    `toU64 err`. The 64-bit-immediate variant of `errorExitJa_spec`. -/
theorem errorExitJa_lddw_spec (err : Int) (vR0Old pc tgt : Nat)
    (h1 : pc ≠ tgt) (h2 : pc + 1 ≠ tgt) :
    cuTripleAbortsWithin 3 0 pc
      (((CodeReq.singleton pc (.lddw .r0 err)).union
        (CodeReq.singleton (pc + 1) (.ja tgt))).union
        (CodeReq.singleton tgt .exit))
      ((.r0 ↦ᵣ vR0Old) ** callStackIs [])
      (toU64 err) :=
  cuTripleAbortsWithin_seq_abort
    (CodeReq.Disjoint_union_left
      (CodeReq.singleton_disjoint_singleton _ _ h1)
      (CodeReq.singleton_disjoint_singleton _ _ h2))
    (cuTripleWithin_seq
      (CodeReq.singleton_disjoint_singleton _ _ (by omega))
      (cuTripleWithin_frame_right (callStackIs []) (pcFree_callStackIs _)
        (lddw_spec .r0 err vR0Old pc (by decide)))
      (cuTripleWithin_widen_emp ((.r0 ↦ᵣ toU64 err) ** callStackIs [])
        (pcFree_sepConj (pcFree_regIs _ _) (pcFree_callStackIs _))
        (ja_spec tgt (pc + 1))))
    (exit_aborts_spec_cuTriple (toU64 err) tgt)

end SVM.SBPF
