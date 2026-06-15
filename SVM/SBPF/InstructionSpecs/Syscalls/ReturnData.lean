import SVM.SBPF.InstructionSpecs.Syscalls.Log

namespace SVM.SBPF

open Memory


/-! ## Syscall: `sol_get_return_data` — H6 output region check

H6: `execGet` routes both output writes (buffer `[r1, r1+copyLen)` + 32-byte
setter id `[r3, r3+32)`) through `guardWrite`, so out-of-region/non-writable
output traps with a typed `accessViolation` (`execGet_faults_oob`).

The old `call_sol_get_return_data_spec` is DELETED: UNCONSUMED (no lift
composed it), and its success post no longer holds for an unguarded
out-of-region output — the honest characterization is the fault lemma. -/


/-! ## Silent-syscall helper: `cuTripleWithin_syscall_silent`

For syscalls whose `step` is a no-op on `PartialState` (regs/mem match, pc+1).
Spec `emp ↓ emp`: advances pc, consumes CU, touches no SL-tracked resource;
with the frame rule it transports any pc-free assertion through the call. -/

theorem cuTripleWithin_syscall_silent
    (sc : Syscall) (pc : Nat) (nCu : Nat)
    (h_step_regs : ∀ s : State, (step (.call sc) s).regs = s.regs)
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
    cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call sc))
      emp
      emp := by
  intro R hRfree fetch hcr s hPR hpc hex hbud
  obtain ⟨hp, hcompat, hP, hR, _, hu, hPemp, hRsat⟩ := hPR
  have hcr_regs := hcompat.regs
  have hcm_mem := hcompat.mem
  have hcm_pc := hcompat.pc
  have hcm_rd := hcompat.returnData
  have hcm_cs := hcompat.callStack
  have hfetch : fetch s.pc = some (.call sc) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hstep_eq : executeFn fetch s 1 = chargeCu (step (.call sc) s) := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch,
        executeFn_zero]
  have hexec_regs : (executeFn fetch s 1).regs = s.regs := by
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
  -- hp = empty.union h_R = h_R; transport hcompat to (executeFn fetch s 1).
  have hP_empty : hP = PartialState.empty := hPemp
  have hp_eq : hp = hR := by
    rw [← hu, hP_empty, PartialState.union_empty_left]
  refine ⟨1, Nat.le_refl 1, ?_, hexec_exit, hexec_cu, ?_⟩
  · rw [hexec_pc, hpc]
  · refine ⟨PartialState.empty.union hR, ?_, PartialState.empty, hR,
            ?_, rfl, rfl, hRsat⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro r v hvr
        rw [PartialState.union_regs_of_left_none
            (PartialState.empty_regs r)] at hvr
        rw [hexec_regs]
        exact hcr_regs r v (hp_eq ▸ hvr)
      · intro a v hva
        rw [PartialState.union_mem_of_left_none
            (PartialState.empty_mem a)] at hva
        rw [hexec_mem]
        exact hcm_mem a v (hp_eq ▸ hva)
      · intro v hvp
        rw [PartialState.union_pc_of_left_none
            PartialState.empty_pc] at hvp
        have hR_no_pc : hR.pc = none := hRfree _ hRsat
        rw [hR_no_pc] at hvp
        nomatch hvp
      · intro rd hva
        rw [PartialState.union_returnData_of_left_none
            PartialState.empty_returnData] at hva
        rw [hexec_rd]
        exact hcm_rd rd (hp_eq ▸ hva)
      · intro cs hva
        rw [PartialState.union_callStack_of_left_none
            PartialState.empty_callStack] at hva
        rw [hexec_cs]
        exact hcm_cs cs (hp_eq ▸ hva)
    · refine ⟨fun r => ?_, fun a => ?_, ?_, ?_, ?_⟩
      · left; exact PartialState.empty_regs r
      · left; exact PartialState.empty_mem a
      · left; exact PartialState.empty_pc
      · left; exact PartialState.empty_returnData
      · left; exact PartialState.empty_callStack

/-! ## Syscall: `sol_remaining_compute_units`

H7: `execRemainingComputeUnits` writes the REAL remaining budget to `r0`
(`cuBudget − (cuConsumed + 1 + Misc.cu)`, H5 metering). The meter fields are
SILENT in `PartialState`, so the honest post is existential ("`r0` set to SOME
value"): a lift can't prove "`r0` preserved" (false on chain) nor pin the
returned budget. -/

theorem call_sol_remaining_compute_units_spec (pc : Nat) (nCu : Nat)
    (hCu : ∀ s : State,
        (step (.call .sol_remaining_compute_units) s).cuConsumed ≤ s.cuConsumed + nCu) :
    ∀ r0Old, cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_remaining_compute_units))
      (.r0 ↦ᵣ r0Old)
      (fun h => ∃ v, h = PartialState.singletonReg .r0 v) :=
  cuTripleWithin_syscall_writes_r0_fn .sol_remaining_compute_units
    (fun s => s.cuBudget - (s.cuConsumed + 1 + Misc.cu)) pc nCu
    (fun s => by simp [step, execSyscall, Misc.execRemainingComputeUnits])
    (fun s => by simp [step, execSyscall, Misc.execRemainingComputeUnits])
    (fun s => by simp [step, execSyscall, Misc.execRemainingComputeUnits])
    (fun s hex => by simp [step, execSyscall, Misc.execRemainingComputeUnits]; exact hex)
    (fun s => by simp [step, execSyscall, Misc.execRemainingComputeUnits])
    (fun s => by simp [step, execSyscall, Misc.execRemainingComputeUnits])
    hCu


end SVM.SBPF
