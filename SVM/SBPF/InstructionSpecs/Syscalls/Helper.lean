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
    (sc : Syscall) (vNew : Nat) (pc : Nat)
    (h_step_regs : ∀ s : State, (step (.call sc) s).regs = s.regs.set .r0 vNew)
    (h_step_mem  : ∀ s : State, (step (.call sc) s).mem = s.mem)
    (h_step_pc   : ∀ s : State, (step (.call sc) s).pc = s.pc + 1)
    (h_step_exit : ∀ s : State, s.exitCode = none →
        (step (.call sc) s).exitCode = none)
    (h_step_returnData :
      ∀ s : State, (step (.call sc) s).returnData = s.returnData)
    (h_step_callStack :
      ∀ s : State, (step (.call sc) s).callStack = s.callStack) :
    ∀ r0Old, cuTripleWithin 1 pc (pc + 1)
      (CodeReq.singleton pc (.call sc))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ vNew) := by
  intro r0Old R hRfree fetch hcr s hPR hpc hex
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
  have hstep_eq : executeFn fetch s 1 = step (.call sc) s := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch,
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
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_⟩
  · rw [hexec_pc, hpc]
  · exact hexec_exit
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


end SVM.SBPF
