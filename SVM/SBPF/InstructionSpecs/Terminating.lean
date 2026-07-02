import SVM.SBPF.InstructionSpecs.Syscalls.Sysvar

namespace SVM.SBPF

open Memory

/-! ## Terminating triples — abort / sol_panic_ / exit

These intentionally halt with a non-`none` exitCode, via `cuTripleAbortsWithin`
("this PC aborts within N steps with this errCode", no post-state since stuck).

`abort`/`sol_panic_` both set `exitCode := some ERR_ABORT`; `sol_panic_` also
appends message bytes to `log`, but the r1/r2/r3 pointers are unconstrained at
the SL level (diagnostic output is silent in `PartialState`).

`exit` is success-exit: empty callStack sets `exitCode := some (r0)`. callStack
discipline isn't yet in `PartialState` (deferred lift #3), so `exit_aborts_spec`
takes `s.callStack = []` as an extra hypothesis. -/

/-- `.call .abort`: unconditional abort, sets `exitCode := some ERR_ABORT,
    vmError := some .abort`. PRE-PARAMETRIC over `P`: abort reads nothing so it
    faults from ANY precondition, letting a per-lift corollary compose the
    prefix's post `Q` straight into the abort tail. -/
theorem call_abort_faults_spec (P : Assertion) (pc : Nat) (nCu : Nat)
    (hCu : ∀ s : State,
        (step (.call .abort) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleFaultsWithin 1 nCu pc
      (CodeReq.singleton pc (.call .abort))
      P .abort := by
  intro R hRfree fetch hcr s hPR hpc hex hbud
  -- The abort ignores its pre, so `hPR` is not destructured.
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
    -- VmError.abort.toSentinel = ERR_ABORT
    show (Abort.execAbort s).exitCode = some VmError.abort.toSentinel
    rfl
  · rw [hexec]
    -- typed fault `.abort` (L1)
    show (Abort.execAbort s).vmError = some .abort
    rfl
  · rw [hstep_eq]
    show (step (.call .abort) s).cuConsumed + 1 ≤ s.cuConsumed + 1 + nCu
    have := hCu s; omega

/-- Original abort triple, derived from the typed-fault spec by forgetting the
    `vmError` conjunct. Kept for existing `cuTripleAbortsWithin` consumers. -/
theorem call_abort_aborts_spec (pc : Nat) (nCu : Nat)
    (hCu : ∀ s : State,
        (step (.call .abort) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleAbortsWithin 1 nCu pc
      (CodeReq.singleton pc (.call .abort))
      emp ERR_ABORT :=
  cuTripleFaultsWithin_toAborts (call_abort_faults_spec emp pc nCu hCu)

/-! ## The per-lift fault corollary (Phase 7 sub-item 3 — emitter shape)

The canonical `*_fault_correct` the emitter mechanizes for a lift whose walked
trace ends in a typed fault: compose the running prefix (`cuTripleWithin[Mem]`)
with the terminal fault spec via `cuTripleFaultsWithin_seq_fault` (Mem variant
`cuTripleWithinMem_seq_fault_pure`), surfacing `vmError = some e`. Below is the
minimal worked instance `mov r0, 5; abort`, proving a typed `.abort` FAULT
(distinct from a clean exit of the same `ERR_ABORT` sentinel, L1). -/

theorem mov_then_abort_fault_correct (vR0Old : Nat) (nCu : Nat)
    (hCu : ∀ s : State,
        (step (.call .abort) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleFaultsWithin (1 + 1) (0 + nCu) 0
      ((CodeReq.singleton 0 (.mov64 .r0 (.imm 5))).union
        (CodeReq.singleton 1 (.call .abort)))
      (.r0 ↦ᵣ vR0Old) .abort :=
  cuTripleFaultsWithin_seq_fault
    (CodeReq.singleton_disjoint_singleton _ _ (by decide))
    (mov64_imm_spec .r0 5 vR0Old 0 (by decide))
    (call_abort_faults_spec (.r0 ↦ᵣ toU64 5) 1 nCu hCu)

/-- The Mem-variant (the shape a real region-carrying lift composes): the
    running prefix is a `cuTripleWithinMem`, the abort tail a pure fault. -/
theorem mov_then_abort_fault_correct_mem (vR0Old : Nat) (nCu : Nat)
    (hCu : ∀ s : State,
        (step (.call .abort) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleFaultsWithinMem (1 + 1) (0 + nCu) 0
      ((CodeReq.singleton 0 (.mov64 .r0 (.imm 5))).union
        (CodeReq.singleton 1 (.call .abort)))
      (.r0 ↦ᵣ vR0Old) (fun _ => True) .abort :=
  cuTripleWithinMem_seq_fault_pure
    (CodeReq.singleton_disjoint_singleton _ _ (by decide))
    (mov64_imm_spec .r0 5 vR0Old 0 (by decide)).toMem
    (call_abort_faults_spec (.r0 ↦ᵣ toU64 5) 1 nCu hCu)

/-- `.call .sol_invoke_signed`: the PROOF-facing CPI is the fail-closed
    `Cpi.exec` stub (audit C4/C5) — it faults with `exitCode :=
    some ERR_UNSUPPORTED_INSTRUCTION, vmError := some .unsupportedInstruction`
    rather than fabricate an effect-free invoke. PRE-PARAMETRIC over `P` like
    `call_abort_faults_spec`, so a per-lift corollary composes an
    invoke-terminated prefix straight into this tail. The runner
    (`executeFnCpiWithFuel`) executes the real CPI; the ENVELOPE the caller
    hands the syscall is a claim about the prefix's post
    (`SVM.Solana.cpiEnvelope`), independent of this stub. -/
theorem call_sol_invoke_signed_faults_spec (P : Assertion) (pc : Nat) (nCu : Nat)
    (hCu : ∀ s : State,
        (step (.call .sol_invoke_signed) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleFaultsWithin 1 nCu pc
      (CodeReq.singleton pc (.call .sol_invoke_signed))
      P .unsupportedInstruction := by
  intro R hRfree fetch hcr s hPR hpc hex hbud
  have hfetch : fetch s.pc = some (.call .sol_invoke_signed) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hstep_eq : executeFn fetch s 1
      = chargeCu (step (.call .sol_invoke_signed) s) := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch, executeFn_zero]
  have hexec : executeFn fetch s 1 =
      chargeCu { (Cpi.exec s) with
                 pc := s.pc + 1
                 cuConsumed := (Cpi.exec s).cuConsumed
                   + syscallCu .sol_invoke_signed s } := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch,
        executeFn_zero]
    simp only [step, execSyscall]
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_⟩
  · rw [hexec]
    show (Cpi.exec s).exitCode = some VmError.unsupportedInstruction.toSentinel
    rfl
  · rw [hexec]
    show (Cpi.exec s).vmError = some .unsupportedInstruction
    rfl
  · rw [hstep_eq]
    show (step (.call .sol_invoke_signed) s).cuConsumed + 1
        ≤ s.cuConsumed + 1 + nCu
    have := hCu s; omega

/-- `.call .sol_invoke_signed_c`: the C-ABI CPI routes through the same
    fail-closed `Cpi.exec` stub — identical typed fault. -/
theorem call_sol_invoke_signed_c_faults_spec (P : Assertion) (pc : Nat) (nCu : Nat)
    (hCu : ∀ s : State,
        (step (.call .sol_invoke_signed_c) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleFaultsWithin 1 nCu pc
      (CodeReq.singleton pc (.call .sol_invoke_signed_c))
      P .unsupportedInstruction := by
  intro R hRfree fetch hcr s hPR hpc hex hbud
  have hfetch : fetch s.pc = some (.call .sol_invoke_signed_c) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hstep_eq : executeFn fetch s 1
      = chargeCu (step (.call .sol_invoke_signed_c) s) := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch, executeFn_zero]
  have hexec : executeFn fetch s 1 =
      chargeCu { (Cpi.exec s) with
                 pc := s.pc + 1
                 cuConsumed := (Cpi.exec s).cuConsumed
                   + syscallCu .sol_invoke_signed_c s } := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch,
        executeFn_zero]
    simp only [step, execSyscall]
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_⟩
  · rw [hexec]
    show (Cpi.exec s).exitCode = some VmError.unsupportedInstruction.toSentinel
    rfl
  · rw [hexec]
    show (Cpi.exec s).vmError = some .unsupportedInstruction
    rfl
  · rw [hstep_eq]
    show (step (.call .sol_invoke_signed_c) s).cuConsumed + 1
        ≤ s.cuConsumed + 1 + nCu
    have := hCu s; omega

/-- `.call .sol_panic_`: unconditional abort logging the message at r1/r2
    (r3/r4/r5 file/line are diagnostic, silent at SL). Sets
    `exitCode := some ERR_ABORT`, `vmError := some .abort`. PRE-PARAMETRIC over
    `P` (like `call_abort_faults_spec`): the message-pointer registers are
    unconstrained and the `log` entry is silent in `PartialState`, so the panic
    faults from ANY precondition — letting a per-lift `*_fault_correct`
    corollary flow the prefix's post `Q` straight into the panic tail. -/
theorem call_sol_panic_faults_spec (P : Assertion) (pc : Nat) (nCu : Nat)
    (hCu : ∀ s : State,
        (step (.call .sol_panic_) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleFaultsWithin 1 nCu pc
      (CodeReq.singleton pc (.call .sol_panic_))
      P .abort := by
  intro R hRfree fetch hcr s hPR hpc hex hbud
  -- The panic ignores its pre, so `hPR` is not destructured.
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
  cuTripleFaultsWithin_toAborts (call_sol_panic_faults_spec emp pc nCu hCu)

/-- Panic analog of `mov_then_abort_fault_correct_mem`: validates the
    `*_fault_correct` emitter output shape for a `.call .sol_panic_` terminal
    (no `.so` fixture is buildable — the no_std panic handler is `loop {}`, so
    a Rust `panic!` never reaches `sol_panic_`). The emitter renders exactly
    this composition, differing only in the syscall constructor. -/
theorem mov_then_panic_fault_correct_mem (vR0Old : Nat) (nCu : Nat)
    (hCu : ∀ s : State,
        (step (.call .sol_panic_) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleFaultsWithinMem (1 + 1) (0 + nCu) 0
      ((CodeReq.singleton 0 (.mov64 .r0 (.imm 5))).union
        (CodeReq.singleton 1 (.call .sol_panic_)))
      (.r0 ↦ᵣ vR0Old) (fun _ => True) .abort :=
  cuTripleWithinMem_seq_fault_pure
    (CodeReq.singleton_disjoint_singleton _ _ (by decide))
    (mov64_imm_spec .r0 5 vR0Old 0 (by decide)).toMem
    (call_sol_panic_faults_spec (.r0 ↦ᵣ toU64 5) 1 nCu hCu)

/-- `Insn.exit` with empty callStack: success-exit, sets `exitCode := some (r0)`.

    The empty-callStack condition isn't yet expressible in `PartialState`
    (deferred lift #3), so this is stated standalone, parametric over an
    `s.callStack = []` side hypothesis threaded through an inlined abort-triple
    body. Pre `(.r0 ↦ᵣ vR0)`, post errCode `vR0`; the success case (exitCode = 0)
    specializes `vR0 := 0`. -/
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

/-- SL-form wrapper around `exit_aborts_spec`: packages the empty-callStack
    hypothesis into `callStackIs []` to get a standard `cuTripleAbortsWithin`.
    `nCu = 0` because `.exit` doesn't bump `cuConsumed` (no syscall surcharge,
    see Execute.lean `step .exit`). -/
theorem exit_aborts_spec_cuTriple (vR0 pc : Nat) :
    cuTripleAbortsWithin 1 0 pc (CodeReq.singleton pc .exit)
      ((.r0 ↦ᵣ vR0) ** callStackIs []) vR0 := by
  intro R hRfree fetch hcr s hPR hpc hex hbud
  obtain ⟨hp, hcompat, h_PQ, h_R, hd_PQR, hu_PQR, h_PQ_sat, h_R_sat⟩ := hPR
  obtain ⟨h_r0, h_cs, hd_r0_cs, hu_r0_cs, h_r0_pred, h_cs_pred⟩ := h_PQ_sat
  -- callStackIs [] atom owns h_cs.callStack = some [].
  have h_cs_cs : h_cs.callStack = some [] := by
    show h_cs.callStack = some []
    rw [show h_cs = PartialState.singletonCallStack [] from h_cs_pred]
    exact PartialState.singletonCallStack_callStack_self
  have h_r0_cs : h_r0.callStack = none := by
    rw [show h_r0 = PartialState.singletonReg .r0 vR0 from h_r0_pred]
    exact PartialState.singletonReg_callStack
  -- Push callStack = some [] up through h_PQ, hp, to s.
  have h_PQ_cs : h_PQ.callStack = some [] := by
    rw [← hu_r0_cs, PartialState.union_callStack_of_left_none h_r0_cs]
    exact h_cs_cs
  have hp_cs : hp.callStack = some [] :=
    hu_PQR ▸ PartialState.union_callStack_of_left_some h_PQ_cs
  have hcs : s.callStack = [] := hcompat.callStack [] hp_cs
  -- Reshape pre to .r0 ** (callStackIs [] ** R) for exit_aborts_spec's frame shape.
  have hRfree' : (callStackIs [] ** R).pcFree :=
    pcFree_sepConj (pcFree_callStackIs _) hRfree
  have hPR' : ((.r0 ↦ᵣ vR0) ** (callStackIs [] ** R)).holdsFor s :=
    holdsFor_sepConj_assoc.mp ⟨hp, hcompat, h_PQ, h_R, hd_PQR, hu_PQR,
      ⟨h_r0, h_cs, hd_r0_cs, hu_r0_cs, h_r0_pred, h_cs_pred⟩, h_R_sat⟩
  obtain ⟨k, hk, hexc⟩ :=
    exit_aborts_spec vR0 pc (callStackIs [] ** R) hRfree' fetch hcr s hPR'
      hpc hex (by omega) hcs
  -- Bound cuConsumed delta ≤ 0: `.exit` doesn't bump cuConsumed (only `.call`
  -- does, see Execute.lean), so trivial at k=0, unfold step .exit at k=1.
  refine ⟨k, hk, hexc, ?_⟩
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

Canonical compiled error-handler landing: set r0 to a constant code, exit.
(Pinocchio encodes `ProgramError` as `code <<< 32` exceeding the 32-bit `mov64`
immediate, so the dispatch-mismatch exit uses `lddw`; ad-hoc codes use `mov64`.
p_token has 6 `mov64` + 1 `lddw`.) One lemma per shape discharges each block in
one `apply`: `{mov64,lddw}_spec` ⨾ `exit_aborts_spec_cuTriple` via
`cuTripleAbortsWithin_seq_abort`. -/

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
    The lddw form carries 64-bit codes (pinocchio's `code <<< 32`). -/
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

/-! Other half of the idiom: error blocks that set r0 and JUMP to a shared
bare-`exit` block (p_token's transfer arm routes every error landing through
the single `exit` at logical 3542). Same collapse, one extra `ja` hop. -/

/-- `mov64 r0, err; ja tgt` with `exit` at `tgt`: aborts with `toU64 err`.
    Side conditions: the shared exit doesn't overlap the landing. -/
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
