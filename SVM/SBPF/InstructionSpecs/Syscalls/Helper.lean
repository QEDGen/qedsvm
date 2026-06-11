import SVM.SBPF.InstructionSpecs.ControlFlow

namespace SVM.SBPF

open Memory

/-! ## Generic syscall helper: writes only `r0`, leaves everything else alone

Many syscalls (logging, return-data set, get-stack-height, etc.) follow a
common shape at the SL level: write some value to `r0`, leave registers /
memory / pc otherwise unchanged. The actual `step` result mutates
`State.log`, `State.returnData`, `State.cuConsumed`, or other observable
side-channel fields — but those are all silent in `PartialState` by design.

This helper captures the pattern. Each concrete syscall spec just supplies
four projection lemmas (`regs`, `mem`, `pc`, `exitCode`) on the step
result, plus the new `r0` value. -/

theorem cuTripleWithin_syscall_writes_r0_only
    (sc : Syscall) (vNew : Nat) (pc : Nat) (nCu : Nat)
    (h_step_regs : ∀ s : State, (step (.call sc) s).regs = s.regs.set .r0 vNew)
    (h_step_mem  : ∀ s : State, (step (.call sc) s).mem = s.mem)
    (h_step_pc   : ∀ s : State, (step (.call sc) s).pc = s.pc + 1)
    (h_step_exit : ∀ s : State, s.exitCode = none →
        (step (.call sc) s).exitCode = none)
    (h_step_returnData :
      ∀ s : State, (step (.call sc) s).returnData = s.returnData)
    (h_step_callStack :
      ∀ s : State, (step (.call sc) s).callStack = s.callStack)
    (h_step_cu : ∀ s : State,
        (step (.call sc) s).cuConsumed ≤ s.cuConsumed + nCu) :
    ∀ r0Old, cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call sc))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ vNew) := by
  intro r0Old R hRfree fetch hcr s hPR hpc hex hbud
  obtain ⟨hp, hcompat, h1, hR, hd, hu, hreg, hRsat⟩ := hPR
  rw [hreg] at hu hd
  clear hreg h1
  have hcr_regs := hcompat.regs
  have hcm_mem := hcompat.mem
  have hcm_rd  := hcompat.returnData
  have hcm_cs  := hcompat.callStack
  have hd_regs := hd.regs
  have hfetch : fetch s.pc = some (.call sc) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hstep_eq : executeFn fetch s 1 = chargeCu (step (.call sc) s) := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch,
        executeFn_zero]
  have hexec_regs : (executeFn fetch s 1).regs = s.regs.set .r0 vNew := by
    rw [hstep_eq]; exact h_step_regs s
  have hexec_mem : (executeFn fetch s 1).mem = s.mem := by
    rw [hstep_eq]; exact h_step_mem s
  have hexec_pc : (executeFn fetch s 1).pc = s.pc + 1 := by
    rw [hstep_eq]; exact h_step_pc s
  have hexec_exit : (executeFn fetch s 1).exitCode = none := by
    rw [hstep_eq]; exact h_step_exit s hex
  have hexec_rd : (executeFn fetch s 1).returnData = s.returnData := by
    rw [hstep_eq]; exact h_step_returnData s
  have hexec_cs : (executeFn fetch s 1).callStack = s.callStack := by
    rw [hstep_eq]; exact h_step_callStack s
  have hexec_cu : (executeFn fetch s 1).cuConsumed ≤ s.cuConsumed + 1 + nCu := by
    rw [hstep_eq]
    show (step (.call sc) s).cuConsumed + 1 ≤ s.cuConsumed + 1 + nCu
    have := h_step_cu s; omega
  have hR_no_r0 : hR.regs .r0 = none := by
    rcases hd_regs .r0 with h | h
    · rw [PartialState.singletonReg_regs_self] at h; nomatch h
    · exact h
  have hR_no_pc : hR.pc = none := hRfree _ hRsat
  have hp_regs_other : ∀ r, r ≠ .r0 → hp.regs r = hR.regs r := by
    intro r hr; rw [← hu]
    exact PartialState.union_regs_of_left_none
      (PartialState.singletonReg_regs_other hr)
  have hp_mem : ∀ a, hp.mem a = hR.mem a := by
    intro a; rw [← hu]
    exact PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)
  have hp_rd : hp.returnData = hR.returnData := by
    rw [← hu]
    exact PartialState.union_returnData_of_left_none
      PartialState.singletonReg_returnData
  have hp_cs : hp.callStack = hR.callStack := by
    rw [← hu]
    exact PartialState.union_callStack_of_left_none
      PartialState.singletonReg_callStack
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_, ?_⟩
  · rw [hexec_pc, hpc]
  · exact hexec_exit
  · exact hexec_cu
  · refine ⟨(PartialState.singletonReg .r0 vNew).union hR, ?_,
            PartialState.singletonReg .r0 vNew, hR, ?_, rfl, rfl, hRsat⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro r v hvr
        by_cases hr : r = .r0
        · rw [hr] at hvr
          rw [PartialState.union_regs_of_left_some
              PartialState.singletonReg_regs_self] at hvr
          have hveq : v = vNew := (Option.some.inj hvr).symm
          rw [hr, hveq, hexec_regs]
          exact RegFile.get_set_self _ _ _ (by decide : (.r0 : Reg) ≠ .r10)
        · rw [PartialState.union_regs_of_left_none
              (PartialState.singletonReg_regs_other hr)] at hvr
          rw [hexec_regs]
          show (s.regs.set .r0 vNew).get r = v
          rw [RegFile.get_set_diff _ _ _ _ hr]
          exact hcr_regs r v ((hp_regs_other r hr).symm ▸ hvr)
      · intro a v hva
        rw [PartialState.union_mem_of_left_none
            (PartialState.singletonReg_mem _)] at hva
        rw [hexec_mem]
        exact hcm_mem a v ((hp_mem a).symm ▸ hva)
      · intro v hvp
        rw [PartialState.union_pc_of_left_none
            PartialState.singletonReg_pc] at hvp
        rw [hR_no_pc] at hvp
        nomatch hvp
      · intro rd hva
        rw [PartialState.union_returnData_of_left_none
            PartialState.singletonReg_returnData] at hva
        rw [hexec_rd]
        exact hcm_rd rd (hp_rd ▸ hva)
      · intro cs hva
        rw [PartialState.union_callStack_of_left_none
            PartialState.singletonReg_callStack] at hva
        rw [hexec_cs]
        exact hcm_cs cs (hp_cs ▸ hva)
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro r
        by_cases hr : r = .r0
        · rw [hr]; right; exact hR_no_r0
        · left; exact PartialState.singletonReg_regs_other hr
      · intro a; left; exact PartialState.singletonReg_mem a
      · left; exact PartialState.singletonReg_pc
      · left; exact PartialState.singletonReg_returnData
      · left; exact PartialState.singletonReg_callStack

/-! ## Generic syscall helper: writes a STATE-DEPENDENT value to `r0`

Like `cuTripleWithin_syscall_writes_r0_only`, but for syscalls whose new
`r0` value depends on State fields that are SILENT in `PartialState`
(e.g. `sol_remaining_compute_units` reads the CU meter). The SL post can
only say "`r0` was written to SOME value" — the existential. The proof is
identical to the fixed-value helper with `vNew := f s`; the post witness
is `⟨f s, rfl⟩`. -/

theorem cuTripleWithin_syscall_writes_r0_fn
    (sc : Syscall) (f : State → Nat) (pc : Nat) (nCu : Nat)
    (h_step_regs : ∀ s : State, (step (.call sc) s).regs = s.regs.set .r0 (f s))
    (h_step_mem  : ∀ s : State, (step (.call sc) s).mem = s.mem)
    (h_step_pc   : ∀ s : State, (step (.call sc) s).pc = s.pc + 1)
    (h_step_exit : ∀ s : State, s.exitCode = none →
        (step (.call sc) s).exitCode = none)
    (h_step_returnData :
      ∀ s : State, (step (.call sc) s).returnData = s.returnData)
    (h_step_callStack :
      ∀ s : State, (step (.call sc) s).callStack = s.callStack)
    (h_step_cu : ∀ s : State,
        (step (.call sc) s).cuConsumed ≤ s.cuConsumed + nCu) :
    ∀ r0Old, cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call sc))
      (.r0 ↦ᵣ r0Old)
      (fun h => ∃ v, h = PartialState.singletonReg .r0 v) := by
  intro r0Old R hRfree fetch hcr s hPR hpc hex hbud
  obtain ⟨hp, hcompat, h1, hR, hd, hu, hreg, hRsat⟩ := hPR
  rw [hreg] at hu hd
  clear hreg h1
  have hcr_regs := hcompat.regs
  have hcm_mem := hcompat.mem
  have hcm_rd  := hcompat.returnData
  have hcm_cs  := hcompat.callStack
  have hd_regs := hd.regs
  have hfetch : fetch s.pc = some (.call sc) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hstep_eq : executeFn fetch s 1 = chargeCu (step (.call sc) s) := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch,
        executeFn_zero]
  have hexec_regs : (executeFn fetch s 1).regs = s.regs.set .r0 (f s) := by
    rw [hstep_eq]; exact h_step_regs s
  have hexec_mem : (executeFn fetch s 1).mem = s.mem := by
    rw [hstep_eq]; exact h_step_mem s
  have hexec_pc : (executeFn fetch s 1).pc = s.pc + 1 := by
    rw [hstep_eq]; exact h_step_pc s
  have hexec_exit : (executeFn fetch s 1).exitCode = none := by
    rw [hstep_eq]; exact h_step_exit s hex
  have hexec_rd : (executeFn fetch s 1).returnData = s.returnData := by
    rw [hstep_eq]; exact h_step_returnData s
  have hexec_cs : (executeFn fetch s 1).callStack = s.callStack := by
    rw [hstep_eq]; exact h_step_callStack s
  have hexec_cu : (executeFn fetch s 1).cuConsumed ≤ s.cuConsumed + 1 + nCu := by
    rw [hstep_eq]
    show (step (.call sc) s).cuConsumed + 1 ≤ s.cuConsumed + 1 + nCu
    have := h_step_cu s; omega
  have hR_no_r0 : hR.regs .r0 = none := by
    rcases hd_regs .r0 with h | h
    · rw [PartialState.singletonReg_regs_self] at h; nomatch h
    · exact h
  have hR_no_pc : hR.pc = none := hRfree _ hRsat
  have hp_regs_other : ∀ r, r ≠ .r0 → hp.regs r = hR.regs r := by
    intro r hr; rw [← hu]
    exact PartialState.union_regs_of_left_none
      (PartialState.singletonReg_regs_other hr)
  have hp_mem : ∀ a, hp.mem a = hR.mem a := by
    intro a; rw [← hu]
    exact PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)
  have hp_rd : hp.returnData = hR.returnData := by
    rw [← hu]
    exact PartialState.union_returnData_of_left_none
      PartialState.singletonReg_returnData
  have hp_cs : hp.callStack = hR.callStack := by
    rw [← hu]
    exact PartialState.union_callStack_of_left_none
      PartialState.singletonReg_callStack
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_, ?_⟩
  · rw [hexec_pc, hpc]
  · exact hexec_exit
  · exact hexec_cu
  · refine ⟨(PartialState.singletonReg .r0 (f s)).union hR, ?_,
            PartialState.singletonReg .r0 (f s), hR, ?_, rfl, ⟨f s, rfl⟩, hRsat⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro r v hvr
        by_cases hr : r = .r0
        · rw [hr] at hvr
          rw [PartialState.union_regs_of_left_some
              PartialState.singletonReg_regs_self] at hvr
          have hveq : v = f s := (Option.some.inj hvr).symm
          rw [hr, hveq, hexec_regs]
          exact RegFile.get_set_self _ _ _ (by decide : (.r0 : Reg) ≠ .r10)
        · rw [PartialState.union_regs_of_left_none
              (PartialState.singletonReg_regs_other hr)] at hvr
          rw [hexec_regs]
          show (s.regs.set .r0 (f s)).get r = v
          rw [RegFile.get_set_diff _ _ _ _ hr]
          exact hcr_regs r v ((hp_regs_other r hr).symm ▸ hvr)
      · intro a v hva
        rw [PartialState.union_mem_of_left_none
            (PartialState.singletonReg_mem _)] at hva
        rw [hexec_mem]
        exact hcm_mem a v ((hp_mem a).symm ▸ hva)
      · intro v hvp
        rw [PartialState.union_pc_of_left_none
            PartialState.singletonReg_pc] at hvp
        rw [hR_no_pc] at hvp
        nomatch hvp
      · intro rd hva
        rw [PartialState.union_returnData_of_left_none
            PartialState.singletonReg_returnData] at hva
        rw [hexec_rd]
        exact hcm_rd rd (hp_rd ▸ hva)
      · intro cs hva
        rw [PartialState.union_callStack_of_left_none
            PartialState.singletonReg_callStack] at hva
        rw [hexec_cs]
        exact hcm_cs cs (hp_cs ▸ hva)
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro r
        by_cases hr : r = .r0
        · rw [hr]; right; exact hR_no_r0
        · left; exact PartialState.singletonReg_regs_other hr
      · intro a; left; exact PartialState.singletonReg_mem a
      · left; exact PartialState.singletonReg_pc
      · left; exact PartialState.singletonReg_returnData
      · left; exact PartialState.singletonReg_callStack

/-! ## CPI syscalls: `sol_invoke_signed` / `sol_invoke_signed_c`

The proof-facing step-level CPI is a FAIL-CLOSED stub
(`Cpi.exec = { exitCode := some ERR_UNSUPPORTED_INSTRUCTION }`): a real
cross-program invocation mutates callee account memory, sets return
data, enforces privilege/signer/depth rules, and can fail — none of
which is modeled in `step`. Rather than fabricate a successful,
effect-free invoke (which a lift could read as "all account memory
unchanged"), `step` aborts. The real cross-program execution lives in
`Runner.cpiCallNextState` (reached via `executeFnCpiWithFuel`), which the
diff_mollusk CPI tests exercise; that path intercepts CPI before `step`
and is unaffected by this stub.

So a lift over `step` that reaches a CPI proves an ABORT at that point.
These `*_aborts_spec`s state exactly that. A future proof-side CPI model
that agrees with `cpiCallNextState` would replace them with effectful
postconditions. See docs/SOUNDNESS_AUDIT_* (C4/C5). -/

theorem call_sol_invoke_signed_aborts_spec (pc : Nat) (nCu : Nat)
    (hCu : ∀ s : State,
        (step (.call .sol_invoke_signed) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleAbortsWithin 1 nCu pc
      (CodeReq.singleton pc (.call .sol_invoke_signed))
      emp ERR_UNSUPPORTED_INSTRUCTION := by
  intro R hRfree fetch hcr s hPR hpc hex hbud
  obtain ⟨hp, hcompat, h1, hR, hd, hu, hP1, hRsat⟩ := hPR
  rw [hP1, PartialState.union_empty_left] at hu
  rw [hP1] at hd
  clear hP1 h1
  have hfetch : fetch s.pc = some (.call .sol_invoke_signed) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hstep_eq : executeFn fetch s 1 =
      chargeCu (step (.call .sol_invoke_signed) s) := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch, executeFn_zero]
  have hexec : executeFn fetch s 1 =
      chargeCu { (Cpi.exec s) with pc := s.pc + 1
                                   cuConsumed := (Cpi.exec s).cuConsumed
                                     + syscallCu .sol_invoke_signed s } := by
    rw [hstep_eq]
    simp only [step, execSyscall]
  refine ⟨1, Nat.le_refl 1, ?_, ?_⟩
  · rw [hexec]
    show (Cpi.exec s).exitCode = some ERR_UNSUPPORTED_INSTRUCTION
    rfl
  · rw [hstep_eq]
    show (step (.call .sol_invoke_signed) s).cuConsumed + 1
      ≤ s.cuConsumed + 1 + nCu
    have := hCu s; omega

theorem call_sol_invoke_signed_c_aborts_spec (pc : Nat) (nCu : Nat)
    (hCu : ∀ s : State,
        (step (.call .sol_invoke_signed_c) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleAbortsWithin 1 nCu pc
      (CodeReq.singleton pc (.call .sol_invoke_signed_c))
      emp ERR_UNSUPPORTED_INSTRUCTION := by
  intro R hRfree fetch hcr s hPR hpc hex hbud
  obtain ⟨hp, hcompat, h1, hR, hd, hu, hP1, hRsat⟩ := hPR
  rw [hP1, PartialState.union_empty_left] at hu
  rw [hP1] at hd
  clear hP1 h1
  have hfetch : fetch s.pc = some (.call .sol_invoke_signed_c) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hstep_eq : executeFn fetch s 1 =
      chargeCu (step (.call .sol_invoke_signed_c) s) := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch, executeFn_zero]
  have hexec : executeFn fetch s 1 =
      chargeCu { (Cpi.exec s) with pc := s.pc + 1
                                   cuConsumed := (Cpi.exec s).cuConsumed
                                     + syscallCu .sol_invoke_signed_c s } := by
    rw [hstep_eq]
    simp only [step, execSyscall]
  refine ⟨1, Nat.le_refl 1, ?_, ?_⟩
  · rw [hexec]
    show (Cpi.exec s).exitCode = some ERR_UNSUPPORTED_INSTRUCTION
    rfl
  · rw [hstep_eq]
    show (step (.call .sol_invoke_signed_c) s).cuConsumed + 1
      ≤ s.cuConsumed + 1 + nCu
    have := hCu s; omega

end SVM.SBPF
