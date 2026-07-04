import SVM.SBPF.InstructionSpecs.Syscalls.Mem

namespace SVM.SBPF

open Memory

/-! ## Sysvar getters — H6 note

All six sysvar-getter success specs were retired once each output write gained a
`guardWrite` region check (H6 stage 4a/4c): the unconditional success triples
became false (the write can fault) and had no consumers. Fault direction pinned
model-side by `Sysvar.{zeroFillR1,execRent,execEpochSchedule}_faults_oob` and
cross-engine by `oob_clock_sysvar.so`. -/

/-! ## H6 OOB-fault triple — `sol_get_clock_sysvar` (write-region family)

The `cuTripleFaultsWithinMem` for the clock getter (`execClock = zeroFillR1 s
40`): its 40-byte output `[r1, r1+40)` routes through `guardWrite`, so an
out-of-region `r1` traps with `.accessViolation`. The write-region (`rr` uses
`containsWritable`, vs the secp read-region's `containsRange`) sibling of
`call_sol_secp256k1_recover_faults_oob_spec`; the `*_fault_correct` emitter
composes it with a register-setup prefix exactly the same way. -/
theorem call_sol_get_clock_sysvar_faults_oob_spec (r1V : Nat) (pc : Nat) (nCu : Nat)
    (hCu : ∀ s : State,
        (step (.call .sol_get_clock_sysvar) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleFaultsWithinMem 1 nCu pc
      (CodeReq.singleton pc (.call .sol_get_clock_sysvar))
      (.r1 ↦ᵣ r1V)
      (fun rt => rt.containsWritable r1V 40 = false)
      .accessViolation := by
  intro R hRfree fetch hcr s hPR hpc hex hbud h_region
  obtain ⟨hp, hcompat, h_P, h_R, hd_PR, hu_PR, h_P_pred, h_R_sat⟩ := hPR
  have hcr_regs := hcompat.regs
  have h_P_regs_r1 : h_P.regs .r1 = some r1V := by
    rw [h_P_pred]; exact PartialState.singletonReg_regs_self
  have hp_regs_r1 : hp.regs .r1 = some r1V := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r1
  have hr1 : s.regs.r1 = r1V := hcr_regs .r1 r1V hp_regs_r1
  have hoob : s.regions.containsWritable s.regs.r1 40 = false := by rw [hr1]; exact h_region
  have hfetch : fetch s.pc = some (.call .sol_get_clock_sysvar) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hstep_eq : executeFn fetch s 1
      = chargeCu (step (.call .sol_get_clock_sysvar) s) := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch, executeFn_zero]
  have hexec : executeFn fetch s 1 =
      chargeCu { (Sysvar.execClock s) with
                 pc := s.pc + 1
                 cuConsumed := (Sysvar.execClock s).cuConsumed
                   + syscallCu .sol_get_clock_sysvar s } := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch, executeFn_zero]
    simp only [step, execSyscall]
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_⟩
  · rw [hexec]
    show (Sysvar.execClock s).exitCode = some VmError.accessViolation.toSentinel
    exact Sysvar.zeroFillR1_faults_oob_exitCode s 40 (by decide) hoob
  · rw [hexec]
    show (Sysvar.execClock s).vmError = some .accessViolation
    exact Sysvar.zeroFillR1_faults_oob s 40 (by decide) hoob
  · rw [hstep_eq]
    show (step (.call .sol_get_clock_sysvar) s).cuConsumed + 1
      ≤ s.cuConsumed + 1 + nCu
    have := hCu s; omega

/-! ## H6 OOB-fault triple — `sol_get_rent_sysvar`

Same write-region shape as the clock getter, but through the de-simp'd
hand-coded 17-byte `execRent` write (`guardWrite [r1, r1+17)`). -/
theorem call_sol_get_rent_sysvar_faults_oob_spec (r1V : Nat) (pc : Nat) (nCu : Nat)
    (hCu : ∀ s : State,
        (step (.call .sol_get_rent_sysvar) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleFaultsWithinMem 1 nCu pc
      (CodeReq.singleton pc (.call .sol_get_rent_sysvar))
      (.r1 ↦ᵣ r1V)
      (fun rt => rt.containsWritable r1V 17 = false)
      .accessViolation := by
  intro R hRfree fetch hcr s hPR hpc hex hbud h_region
  obtain ⟨hp, hcompat, h_P, h_R, hd_PR, hu_PR, h_P_pred, h_R_sat⟩ := hPR
  have hcr_regs := hcompat.regs
  have h_P_regs_r1 : h_P.regs .r1 = some r1V := by
    rw [h_P_pred]; exact PartialState.singletonReg_regs_self
  have hp_regs_r1 : hp.regs .r1 = some r1V := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r1
  have hr1 : s.regs.r1 = r1V := hcr_regs .r1 r1V hp_regs_r1
  have hoob : s.regions.containsWritable s.regs.r1 17 = false := by rw [hr1]; exact h_region
  have hfetch : fetch s.pc = some (.call .sol_get_rent_sysvar) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hstep_eq : executeFn fetch s 1
      = chargeCu (step (.call .sol_get_rent_sysvar) s) := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch, executeFn_zero]
  have hexec : executeFn fetch s 1 =
      chargeCu { (Sysvar.execRent s) with
                 pc := s.pc + 1
                 cuConsumed := (Sysvar.execRent s).cuConsumed
                   + syscallCu .sol_get_rent_sysvar s } := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch, executeFn_zero]
    simp only [step, execSyscall]
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_⟩
  · rw [hexec]
    show (Sysvar.execRent s).exitCode = some VmError.accessViolation.toSentinel
    exact Sysvar.execRent_faults_oob_exitCode s hoob
  · rw [hexec]
    show (Sysvar.execRent s).vmError = some .accessViolation
    exact Sysvar.execRent_faults_oob s hoob
  · rw [hstep_eq]
    show (step (.call .sol_get_rent_sysvar) s).cuConsumed + 1
      ≤ s.cuConsumed + 1 + nCu
    have := hCu s; omega

end SVM.SBPF
