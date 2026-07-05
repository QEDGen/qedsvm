import SVM.SBPF.InstructionSpecs.ControlFlow

namespace SVM.SBPF

open Memory

/-! ## Generic syscall helper: writes only `r0`, leaves everything else alone

SL shape shared by many syscalls (logging, return-data set, get-stack-height):
write `r0`, leave regs/mem/pc unchanged. The `step` result also mutates
`log`/`returnData`/`cuConsumed` etc., but those are silent in `PartialState`. -/

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

/-! ## Region-checked variant: writes `r0`, reads a fixed slice at `rAddr`

Audit H6. Like the r0-only helper but for a syscall reading a fixed slice
`[addrV, addrV+rLen)` (e.g. `sol_log_pubkey`). The precondition pins `rAddr`
to name the slice; the `rr` requirement `containsRange addrV rLen` is what
each region-conditional step projection needs to collapse `guardRead`. -/
theorem cuTripleWithinMem_syscall_writes_r0_reads_fixed
    (sc : Syscall) (vNew : Nat) (pc : Nat) (nCu : Nat)
    (rAddr : Reg) (addrV rLen : Nat) (hAddr : rAddr ≠ .r0)
    (h_step_regs : ∀ s : State, s.regs.get rAddr = addrV →
        s.regions.containsRange addrV rLen = true →
        (step (.call sc) s).regs = s.regs.set .r0 vNew)
    (h_step_mem  : ∀ s : State, s.regs.get rAddr = addrV →
        s.regions.containsRange addrV rLen = true →
        (step (.call sc) s).mem = s.mem)
    (h_step_pc   : ∀ s : State, (step (.call sc) s).pc = s.pc + 1)
    (h_step_exit : ∀ s : State, s.exitCode = none →
        s.regs.get rAddr = addrV →
        s.regions.containsRange addrV rLen = true →
        (step (.call sc) s).exitCode = none)
    (h_step_returnData :
      ∀ s : State, (step (.call sc) s).returnData = s.returnData)
    (h_step_callStack :
      ∀ s : State, (step (.call sc) s).callStack = s.callStack)
    (h_step_cu : ∀ s : State,
        (step (.call sc) s).cuConsumed ≤ s.cuConsumed + nCu) :
    ∀ r0Old, cuTripleWithinMem 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call sc))
      ((.r0 ↦ᵣ r0Old) ** (rAddr ↦ᵣ addrV))
      ((.r0 ↦ᵣ vNew) ** (rAddr ↦ᵣ addrV))
      (fun rt => rt.containsRange addrV rLen = true) := by
  intro r0Old R hRfree fetch hcr s hPR hpc hex hbud h_region
  obtain ⟨hp, hcompat, h_P, hR, hd_PR, hu_PR, h_P_sat, hRsat⟩ := hPR
  obtain ⟨h_r0, h_rA, hd_r0_rA, hu_r0_rA, h_r0_pred, h_rA_pred⟩ := h_P_sat
  rw [h_r0_pred] at hu_r0_rA hd_r0_rA
  rw [h_rA_pred] at hu_r0_rA hd_r0_rA
  clear h_r0_pred h_rA_pred h_r0 h_rA
  have hcr_regs := hcompat.regs
  have hcm_mem := hcompat.mem
  have hcm_rd  := hcompat.returnData
  have hcm_cs  := hcompat.callStack
  -- Climb r0/rAddr values up through h_P to s.regs.
  have h_P_regs_r0 : h_P.regs .r0 = some r0Old := by
    rw [← hu_r0_rA]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_regs_rA : h_P.regs rAddr = some addrV := by
    rw [← hu_r0_rA,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other hAddr)]
    exact PartialState.singletonReg_regs_self
  have h_P_mem : ∀ a, h_P.mem a = none := by
    intro a
    rw [← hu_r0_rA,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
    exact PartialState.singletonReg_mem a
  have hp_regs_r0 : hp.regs .r0 = some r0Old := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r0
  have hp_regs_rA : hp.regs rAddr = some addrV := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_rA
  have hs_regs_rA : s.regs.get rAddr = addrV := hcr_regs rAddr addrV hp_regs_rA
  -- Fetch + per-field facts about (executeFn fetch s 1).
  have hfetch : fetch s.pc = some (.call sc) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hstep_eq : executeFn fetch s 1 = chargeCu (step (.call sc) s) := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch, executeFn_zero]
  have hexec_regs : (executeFn fetch s 1).regs = s.regs.set .r0 vNew := by
    rw [hstep_eq]; exact h_step_regs s hs_regs_rA h_region
  have hexec_mem : (executeFn fetch s 1).mem = s.mem := by
    rw [hstep_eq]; exact h_step_mem s hs_regs_rA h_region
  have hexec_pc : (executeFn fetch s 1).pc = s.pc + 1 := by
    rw [hstep_eq]; exact h_step_pc s
  have hexec_exit : (executeFn fetch s 1).exitCode = none := by
    rw [hstep_eq]; exact h_step_exit s hex hs_regs_rA h_region
  have hexec_rd : (executeFn fetch s 1).returnData = s.returnData := by
    rw [hstep_eq]; exact h_step_returnData s
  have hexec_cs : (executeFn fetch s 1).callStack = s.callStack := by
    rw [hstep_eq]; exact h_step_callStack s
  have hexec_cu : (executeFn fetch s 1).cuConsumed ≤ s.cuConsumed + 1 + nCu := by
    rw [hstep_eq]
    show (step (.call sc) s).cuConsumed + 1 ≤ s.cuConsumed + 1 + nCu
    have := h_step_cu s; omega
  -- h_R: r0, rAddr, pc absent (from outer disjointness with h_P).
  have hd_PR_regs := hd_PR.regs
  have hR_no_r0 : hR.regs .r0 = none := by
    rcases hd_PR_regs .r0 with h | h
    · rw [h_P_regs_r0] at h; nomatch h
    · exact h
  have hR_no_rA : hR.regs rAddr = none := by
    rcases hd_PR_regs rAddr with h | h
    · rw [h_P_regs_rA] at h; nomatch h
    · exact h
  have hR_no_pc : hR.pc = none := hRfree _ hRsat
  -- hp ⟷ hR projection helpers for the unowned components.
  have hp_mem : ∀ a, hp.mem a = hR.mem a := by
    intro a; rw [← hu_PR,
      PartialState.union_mem_of_left_none (h_P_mem a)]
  have h_P_rd : h_P.returnData = none := by
    rw [← hu_r0_rA, PartialState.union_returnData_of_left_none
        PartialState.singletonReg_returnData]
    exact PartialState.singletonReg_returnData
  have h_P_cs : h_P.callStack = none := by
    rw [← hu_r0_rA, PartialState.union_callStack_of_left_none
        PartialState.singletonReg_callStack]
    exact PartialState.singletonReg_callStack
  have hp_rd : hp.returnData = hR.returnData := by
    rw [← hu_PR]; exact PartialState.union_returnData_of_left_none h_P_rd
  have hp_cs : hp.callStack = hR.callStack := by
    rw [← hu_PR]; exact PartialState.union_callStack_of_left_none h_P_cs
  -- Disjointness of the two post reg singletons (keys r0 ≠ rAddr).
  have hd_post : (PartialState.singletonReg .r0 vNew).Disjoint
      (PartialState.singletonReg rAddr addrV) := by
    refine ⟨fun r => ?_, fun a => Or.inl (PartialState.singletonReg_mem a),
            Or.inl PartialState.singletonReg_pc,
            Or.inl PartialState.singletonReg_returnData,
            Or.inl PartialState.singletonReg_callStack⟩
    by_cases hr : r = .r0
    · right; rw [hr]; exact PartialState.singletonReg_regs_other (Ne.symm hAddr)
    · left; exact PartialState.singletonReg_regs_other hr
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_, ?_⟩
  · rw [hexec_pc, hpc]
  · exact hexec_exit
  · exact hexec_cu
  · refine ⟨((PartialState.singletonReg .r0 vNew).union
              (PartialState.singletonReg rAddr addrV)).union hR, ?_,
            (PartialState.singletonReg .r0 vNew).union
              (PartialState.singletonReg rAddr addrV), hR, ?_, rfl,
            ⟨PartialState.singletonReg .r0 vNew,
             PartialState.singletonReg rAddr addrV, hd_post, rfl, rfl, rfl⟩, hRsat⟩
    · -- compat: (Pq.union hR) matches (executeFn fetch s 1)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro r v hvr
        by_cases hr0 : r = .r0
        · subst hr0
          rw [PartialState.union_regs_of_left_some
              (PartialState.union_regs_of_left_some
                PartialState.singletonReg_regs_self)] at hvr
          have hveq : v = vNew := (Option.some.inj hvr).symm
          rw [hveq, hexec_regs]
          exact RegFile.get_set_self _ _ _ (by decide : (.r0 : Reg) ≠ .r10)
        · by_cases hrA : r = rAddr
          · have hPq : ((PartialState.singletonReg .r0 vNew).union
                (PartialState.singletonReg rAddr addrV)).regs r = some addrV := by
              rw [hrA, PartialState.union_regs_of_left_none
                    (PartialState.singletonReg_regs_other hAddr)]
              exact PartialState.singletonReg_regs_self
            rw [PartialState.union_regs_of_left_some hPq] at hvr
            have hveq : v = addrV := (Option.some.inj hvr).symm
            rw [hveq, hexec_regs, hrA, RegFile.get_set_diff _ _ _ _ hAddr]
            exact hs_regs_rA
          · have hPqnone : ((PartialState.singletonReg .r0 vNew).union
                (PartialState.singletonReg rAddr addrV)).regs r = none := by
              rw [PartialState.union_regs_of_left_none
                    (PartialState.singletonReg_regs_other hr0)]
              exact PartialState.singletonReg_regs_other hrA
            rw [PartialState.union_regs_of_left_none hPqnone] at hvr
            rw [hexec_regs]
            show (s.regs.set .r0 vNew).get r = v
            rw [RegFile.get_set_diff _ _ _ _ hr0]
            have hpr : hp.regs r = hR.regs r := by
              have h_P_none : h_P.regs r = none := by
                rw [← hu_r0_rA,
                  PartialState.union_regs_of_left_none
                    (PartialState.singletonReg_regs_other hr0)]
                exact PartialState.singletonReg_regs_other hrA
              rw [← hu_PR,
                PartialState.union_regs_of_left_none h_P_none]
            exact hcr_regs r v (hpr ▸ hvr)
      · intro a v hva
        rw [PartialState.union_mem_of_left_none
            (by rw [PartialState.union_mem_of_left_none
                  (PartialState.singletonReg_mem a)]
                exact PartialState.singletonReg_mem a)] at hva
        rw [hexec_mem]
        exact hcm_mem a v ((hp_mem a).symm ▸ hva)
      · intro v hvp
        rw [PartialState.union_pc_of_left_none
            (by rw [PartialState.union_pc_of_left_none
                  PartialState.singletonReg_pc]
                exact PartialState.singletonReg_pc)] at hvp
        rw [hR_no_pc] at hvp; nomatch hvp
      · intro rd hva
        rw [PartialState.union_returnData_of_left_none
            (by rw [PartialState.union_returnData_of_left_none
                  PartialState.singletonReg_returnData]
                exact PartialState.singletonReg_returnData)] at hva
        rw [hexec_rd]
        exact hcm_rd rd (hp_rd ▸ hva)
      · intro cs hva
        rw [PartialState.union_callStack_of_left_none
            (by rw [PartialState.union_callStack_of_left_none
                  PartialState.singletonReg_callStack]
                exact PartialState.singletonReg_callStack)] at hva
        rw [hexec_cs]
        exact hcm_cs cs (hp_cs ▸ hva)
    · -- disjointness Pq ⊥ hR
      refine ⟨fun r => ?_, fun a => Or.inl ?_, Or.inl ?_, Or.inl ?_, Or.inl ?_⟩
      · by_cases hr0 : r = .r0
        · right; rw [hr0]; exact hR_no_r0
        · by_cases hrA : r = rAddr
          · right; rw [hrA]; exact hR_no_rA
          · left
            rw [PartialState.union_regs_of_left_none
                (PartialState.singletonReg_regs_other hr0)]
            exact PartialState.singletonReg_regs_other hrA
      · rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
        exact PartialState.singletonReg_mem a
      · rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
        exact PartialState.singletonReg_pc
      · rw [PartialState.union_returnData_of_left_none
            PartialState.singletonReg_returnData]
        exact PartialState.singletonReg_returnData
      · rw [PartialState.union_callStack_of_left_none
            PartialState.singletonReg_callStack]
        exact PartialState.singletonReg_callStack

/-! ## Region-checked variant: writes `r0`, reads a slice `[rAddr, rAddr+rLen)`

Audit H6. Variable-length companion of the fixed-slice helper: read length is
the runtime value of `rLen` (e.g. `sol_log_` reading `[r1, r1+r2)`), so the
precondition pins both `rAddr` and `rLen` (pairwise distinct from `.r0`), with
`rr = containsRange addrV lenV`. -/
theorem cuTripleWithinMem_syscall_writes_r0_reads_var
    (sc : Syscall) (vNew : Nat) (pc : Nat) (nCu : Nat)
    (rAddr rLen : Reg) (addrV lenV : Nat)
    (hAddr : rAddr ≠ .r0) (hLen : rLen ≠ .r0) (hAL : rAddr ≠ rLen)
    (h_step_regs : ∀ s : State, s.regs.get rAddr = addrV → s.regs.get rLen = lenV →
        s.regions.containsRange addrV lenV = true →
        (step (.call sc) s).regs = s.regs.set .r0 vNew)
    (h_step_mem  : ∀ s : State, s.regs.get rAddr = addrV → s.regs.get rLen = lenV →
        s.regions.containsRange addrV lenV = true →
        (step (.call sc) s).mem = s.mem)
    (h_step_pc   : ∀ s : State, (step (.call sc) s).pc = s.pc + 1)
    (h_step_exit : ∀ s : State, s.exitCode = none →
        s.regs.get rAddr = addrV → s.regs.get rLen = lenV →
        s.regions.containsRange addrV lenV = true →
        (step (.call sc) s).exitCode = none)
    (h_step_returnData :
      ∀ s : State, (step (.call sc) s).returnData = s.returnData)
    (h_step_callStack :
      ∀ s : State, (step (.call sc) s).callStack = s.callStack)
    (h_step_cu : ∀ s : State,
        (step (.call sc) s).cuConsumed ≤ s.cuConsumed + nCu) :
    ∀ r0Old, cuTripleWithinMem 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call sc))
      ((.r0 ↦ᵣ r0Old) ** (rAddr ↦ᵣ addrV) ** (rLen ↦ᵣ lenV))
      ((.r0 ↦ᵣ vNew) ** (rAddr ↦ᵣ addrV) ** (rLen ↦ᵣ lenV))
      (fun rt => rt.containsRange addrV lenV = true) := by
  intro r0Old R hRfree fetch hcr s hPR hpc hex hbud h_region
  obtain ⟨hp, hcompat, h_P, hR, hd_PR, hu_PR, h_P_sat, hRsat⟩ := hPR
  obtain ⟨h_r0, h_T1, hd_r0_T1, hu_r0_T1, h_r0_pred, h_T1_sat⟩ := h_P_sat
  obtain ⟨h_rA, h_rL, hd_rA_rL, hu_rA_rL, h_rA_pred, h_rL_pred⟩ := h_T1_sat
  rw [h_r0_pred] at hu_r0_T1
  rw [h_rA_pred, h_rL_pred] at hu_rA_rL
  rw [← hu_rA_rL] at hu_r0_T1
  clear h_r0_pred h_rA_pred h_rL_pred h_r0 h_rA h_rL hd_r0_T1 hd_rA_rL hu_rA_rL h_T1
  have hcr_regs := hcompat.regs
  have hcm_mem := hcompat.mem
  have hcm_rd  := hcompat.returnData
  have hcm_cs  := hcompat.callStack
  -- hu_r0_T1 : (r0 ∪ (rAddr ∪ rLen singletons)) = h_P. Climb values up through h_P.
  have h_P_regs_r0 : h_P.regs .r0 = some r0Old := by
    rw [← hu_r0_T1]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_regs_rA : h_P.regs rAddr = some addrV := by
    rw [← hu_r0_T1,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other hAddr),
        PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self]
  have h_P_regs_rL : h_P.regs rLen = some lenV := by
    rw [← hu_r0_T1,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other hLen),
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (Ne.symm hAL))]
    exact PartialState.singletonReg_regs_self
  have h_Pin_mem : ∀ a, ((PartialState.singletonReg rAddr addrV).union (PartialState.singletonReg rLen lenV)).mem a = none := by
    intro a; rw [      PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
    exact PartialState.singletonReg_mem a
  have h_Pin_rd : ((PartialState.singletonReg rAddr addrV).union (PartialState.singletonReg rLen lenV)).returnData = none := by
    rw [PartialState.union_returnData_of_left_none
        PartialState.singletonReg_returnData]
    exact PartialState.singletonReg_returnData
  have h_Pin_cs : ((PartialState.singletonReg rAddr addrV).union (PartialState.singletonReg rLen lenV)).callStack = none := by
    rw [PartialState.union_callStack_of_left_none
        PartialState.singletonReg_callStack]
    exact PartialState.singletonReg_callStack
  have h_Pin_pc : ((PartialState.singletonReg rAddr addrV).union (PartialState.singletonReg rLen lenV)).pc = none := by
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    exact PartialState.singletonReg_pc
  have h_P_mem : ∀ a, h_P.mem a = none := by
    intro a
    rw [← hu_r0_T1,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
    exact h_Pin_mem a
  have h_P_rd : h_P.returnData = none := by
    rw [← hu_r0_T1, PartialState.union_returnData_of_left_none
        PartialState.singletonReg_returnData]
    exact h_Pin_rd
  have h_P_cs : h_P.callStack = none := by
    rw [← hu_r0_T1, PartialState.union_callStack_of_left_none
        PartialState.singletonReg_callStack]
    exact h_Pin_cs
  have hp_regs_rA : hp.regs rAddr = some addrV := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_rA
  have hp_regs_rL : hp.regs rLen = some lenV := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_rL
  have hs_regs_rA : s.regs.get rAddr = addrV := hcr_regs rAddr addrV hp_regs_rA
  have hs_regs_rL : s.regs.get rLen = lenV := hcr_regs rLen lenV hp_regs_rL
  -- Fetch + per-field facts about (executeFn fetch s 1).
  have hfetch : fetch s.pc = some (.call sc) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hstep_eq : executeFn fetch s 1 = chargeCu (step (.call sc) s) := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch, executeFn_zero]
  have hexec_regs : (executeFn fetch s 1).regs = s.regs.set .r0 vNew := by
    rw [hstep_eq]; exact h_step_regs s hs_regs_rA hs_regs_rL h_region
  have hexec_mem : (executeFn fetch s 1).mem = s.mem := by
    rw [hstep_eq]; exact h_step_mem s hs_regs_rA hs_regs_rL h_region
  have hexec_pc : (executeFn fetch s 1).pc = s.pc + 1 := by
    rw [hstep_eq]; exact h_step_pc s
  have hexec_exit : (executeFn fetch s 1).exitCode = none := by
    rw [hstep_eq]; exact h_step_exit s hex hs_regs_rA hs_regs_rL h_region
  have hexec_rd : (executeFn fetch s 1).returnData = s.returnData := by
    rw [hstep_eq]; exact h_step_returnData s
  have hexec_cs : (executeFn fetch s 1).callStack = s.callStack := by
    rw [hstep_eq]; exact h_step_callStack s
  have hexec_cu : (executeFn fetch s 1).cuConsumed ≤ s.cuConsumed + 1 + nCu := by
    rw [hstep_eq]
    show (step (.call sc) s).cuConsumed + 1 ≤ s.cuConsumed + 1 + nCu
    have := h_step_cu s; omega
  -- h_R: r0, rAddr, rLen, pc absent.
  have hd_PR_regs := hd_PR.regs
  have hR_no_r0 : hR.regs .r0 = none := by
    rcases hd_PR_regs .r0 with h | h
    · rw [h_P_regs_r0] at h; nomatch h
    · exact h
  have hR_no_rA : hR.regs rAddr = none := by
    rcases hd_PR_regs rAddr with h | h
    · rw [h_P_regs_rA] at h; nomatch h
    · exact h
  have hR_no_rL : hR.regs rLen = none := by
    rcases hd_PR_regs rLen with h | h
    · rw [h_P_regs_rL] at h; nomatch h
    · exact h
  have hR_no_pc : hR.pc = none := hRfree _ hRsat
  have hp_mem : ∀ a, hp.mem a = hR.mem a := by
    intro a; rw [← hu_PR,
      PartialState.union_mem_of_left_none (h_P_mem a)]
  have hp_rd : hp.returnData = hR.returnData := by
    rw [← hu_PR]; exact PartialState.union_returnData_of_left_none h_P_rd
  have hp_cs : hp.callStack = hR.callStack := by
    rw [← hu_PR]; exact PartialState.union_callStack_of_left_none h_P_cs
  -- Post-state partial `r0 ** (rAddr ** rLen)` (precond shape); disjointness pieces.
  have hd_rA_rL_post : (PartialState.singletonReg rAddr addrV).Disjoint
      (PartialState.singletonReg rLen lenV) := by
    refine ⟨fun r => ?_, fun a => Or.inl (PartialState.singletonReg_mem a),
            Or.inl PartialState.singletonReg_pc,
            Or.inl PartialState.singletonReg_returnData,
            Or.inl PartialState.singletonReg_callStack⟩
    by_cases hr : r = rAddr
    · right; rw [hr]; exact PartialState.singletonReg_regs_other hAL
    · left; exact PartialState.singletonReg_regs_other hr
  have hQin_regs_none : ∀ r, r ≠ rAddr → r ≠ rLen → ((PartialState.singletonReg rAddr addrV).union (PartialState.singletonReg rLen lenV)).regs r = none := by
    intro r hrA hrL
    rw [ PartialState.union_regs_of_left_none
        (PartialState.singletonReg_regs_other hrA)]
    exact PartialState.singletonReg_regs_other hrL
  have hd_r0_Qin : (PartialState.singletonReg .r0 vNew).Disjoint ((PartialState.singletonReg rAddr addrV).union (PartialState.singletonReg rLen lenV)) := by
    refine ⟨fun r => ?_, fun a => Or.inl (PartialState.singletonReg_mem a),
            Or.inl PartialState.singletonReg_pc,
            Or.inl PartialState.singletonReg_returnData,
            Or.inl PartialState.singletonReg_callStack⟩
    by_cases hr : r = .r0
    · right; rw [hr]; exact hQin_regs_none .r0 (Ne.symm hAddr) (Ne.symm hLen)
    · left; exact PartialState.singletonReg_regs_other hr
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_, ?_⟩
  · rw [hexec_pc, hpc]
  · exact hexec_exit
  · exact hexec_cu
  · refine ⟨((PartialState.singletonReg .r0 vNew).union ((PartialState.singletonReg rAddr addrV).union (PartialState.singletonReg rLen lenV))).union hR, ?_,
            (PartialState.singletonReg .r0 vNew).union ((PartialState.singletonReg rAddr addrV).union (PartialState.singletonReg rLen lenV)), hR, ?_, rfl,
            ⟨PartialState.singletonReg .r0 vNew, ((PartialState.singletonReg rAddr addrV).union (PartialState.singletonReg rLen lenV)), hd_r0_Qin, rfl, rfl,
             ⟨PartialState.singletonReg rAddr addrV,
              PartialState.singletonReg rLen lenV, hd_rA_rL_post, rfl, rfl, rfl⟩⟩,
            hRsat⟩
    · -- compat: ((r0 ∪ ((PartialState.singletonReg rAddr addrV).union (PartialState.singletonReg rLen lenV))) ∪ hR) matches (executeFn fetch s 1)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro r v hvr
        by_cases hr0 : r = .r0
        · subst hr0
          rw [PartialState.union_regs_of_left_some
              (PartialState.union_regs_of_left_some
                PartialState.singletonReg_regs_self)] at hvr
          have hveq : v = vNew := (Option.some.inj hvr).symm
          rw [hveq, hexec_regs]
          exact RegFile.get_set_self _ _ _ (by decide : (.r0 : Reg) ≠ .r10)
        · by_cases hrA : r = rAddr
          · have hQ : ((PartialState.singletonReg .r0 vNew).union ((PartialState.singletonReg rAddr addrV).union (PartialState.singletonReg rLen lenV))).regs r = some addrV := by
              rw [PartialState.union_regs_of_left_none
                    (PartialState.singletonReg_regs_other hr0), hrA,
                  PartialState.union_regs_of_left_some
                    PartialState.singletonReg_regs_self]
            rw [PartialState.union_regs_of_left_some hQ] at hvr
            have hveq : v = addrV := (Option.some.inj hvr).symm
            rw [hveq, hexec_regs, hrA, RegFile.get_set_diff _ _ _ _ hAddr]
            exact hs_regs_rA
          · by_cases hrL : r = rLen
            · have hQ : ((PartialState.singletonReg .r0 vNew).union ((PartialState.singletonReg rAddr addrV).union (PartialState.singletonReg rLen lenV))).regs r = some lenV := by
                rw [PartialState.union_regs_of_left_none
                      (PartialState.singletonReg_regs_other hr0), hrL,
                    PartialState.union_regs_of_left_none
                      (PartialState.singletonReg_regs_other (Ne.symm hAL))]
                exact PartialState.singletonReg_regs_self
              rw [PartialState.union_regs_of_left_some hQ] at hvr
              have hveq : v = lenV := (Option.some.inj hvr).symm
              rw [hveq, hexec_regs, hrL, RegFile.get_set_diff _ _ _ _ hLen]
              exact hs_regs_rL
            · have hQnone : ((PartialState.singletonReg .r0 vNew).union ((PartialState.singletonReg rAddr addrV).union (PartialState.singletonReg rLen lenV))).regs r = none := by
                rw [PartialState.union_regs_of_left_none
                      (PartialState.singletonReg_regs_other hr0)]
                exact hQin_regs_none r hrA hrL
              rw [PartialState.union_regs_of_left_none hQnone] at hvr
              rw [hexec_regs]
              show (s.regs.set .r0 vNew).get r = v
              rw [RegFile.get_set_diff _ _ _ _ hr0]
              have hpr : hp.regs r = hR.regs r := by
                have h_P_none : h_P.regs r = none := by
                  rw [← hu_r0_T1,
                    PartialState.union_regs_of_left_none
                      (PartialState.singletonReg_regs_other hr0)]
                  exact hQin_regs_none r hrA hrL
                rw [← hu_PR, PartialState.union_regs_of_left_none h_P_none]
              exact hcr_regs r v (hpr ▸ hvr)
      · intro a v hva
        rw [PartialState.union_mem_of_left_none
            (by rw [PartialState.union_mem_of_left_none
                  (PartialState.singletonReg_mem a)]
                exact h_Pin_mem a)] at hva
        rw [hexec_mem]
        exact hcm_mem a v ((hp_mem a).symm ▸ hva)
      · intro v hvp
        rw [PartialState.union_pc_of_left_none
            (by rw [PartialState.union_pc_of_left_none
                  PartialState.singletonReg_pc]
                exact h_Pin_pc)] at hvp
        rw [hR_no_pc] at hvp; nomatch hvp
      · intro rd hva
        rw [PartialState.union_returnData_of_left_none
            (by rw [PartialState.union_returnData_of_left_none
                  PartialState.singletonReg_returnData]
                exact h_Pin_rd)] at hva
        rw [hexec_rd]
        exact hcm_rd rd (hp_rd ▸ hva)
      · intro cs hva
        rw [PartialState.union_callStack_of_left_none
            (by rw [PartialState.union_callStack_of_left_none
                  PartialState.singletonReg_callStack]
                exact h_Pin_cs)] at hva
        rw [hexec_cs]
        exact hcm_cs cs (hp_cs ▸ hva)
    · -- disjointness (r0 ∪ ((PartialState.singletonReg rAddr addrV).union (PartialState.singletonReg rLen lenV))) ⊥ hR
      refine ⟨fun r => ?_, fun a => Or.inl ?_, Or.inl ?_, Or.inl ?_, Or.inl ?_⟩
      · by_cases hr0 : r = .r0
        · right; rw [hr0]; exact hR_no_r0
        · by_cases hrA : r = rAddr
          · right; rw [hrA]; exact hR_no_rA
          · by_cases hrL : r = rLen
            · right; rw [hrL]; exact hR_no_rL
            · left
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hr0)]
              exact hQin_regs_none r hrA hrL
      · rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
        exact h_Pin_mem a
      · rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
        exact h_Pin_pc
      · rw [PartialState.union_returnData_of_left_none
            PartialState.singletonReg_returnData]
        exact h_Pin_rd
      · rw [PartialState.union_callStack_of_left_none
            PartialState.singletonReg_callStack]
        exact h_Pin_cs

/-! ## Generic syscall helper: writes a STATE-DEPENDENT value to `r0`

Like the r0-only helper but the new `r0` depends on State fields silent in
`PartialState` (e.g. `sol_remaining_compute_units` reads the CU meter), so the
SL post can only say "`r0` was written to SOME value" (the existential). Proof
is the fixed-value helper with `vNew := f s`; post witness `⟨f s, rfl⟩`. -/

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
(`Cpi.exec = { exitCode := some ERR_UNSUPPORTED_INSTRUCTION }`): `step` aborts
rather than fabricate a successful effect-free invoke (which a lift could
misread as "all account memory unchanged") since the real invoke's account
mutation / return data / privilege+signer+depth rules / failure are unmodeled.
Real CPI lives in `Runner.cpiCallNextState` (via `executeFnCpiWithFuel`,
exercised by diff_mollusk), which intercepts CPI before `step`, unaffected here.
So a lift reaching CPI proves an ABORT; these `*_aborts_spec`s state exactly
that. A future step-level CPI model agreeing with `cpiCallNextState` would
replace them with effectful posts. See docs/SOUNDNESS_AUDIT_* (C4/C5). -/

/-- Shared proof for the two CPI abort specs: any syscall whose `execSyscall`
    sets `exitCode := some ERR_UNSUPPORTED_INSTRUCTION` (witnessed by `hexit`)
    aborts from the empty precondition. The two public specs below instantiate
    this with `hexit := fun _ => rfl`. -/
private theorem call_cpi_syscall_aborts_spec (sc : Syscall)
    (hexit : ∀ s : State,
        (execSyscall sc s).exitCode = some ERR_UNSUPPORTED_INSTRUCTION)
    (pc : Nat) (nCu : Nat)
    (hCu : ∀ s : State,
        (step (.call sc) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleAbortsWithin 1 nCu pc
      (CodeReq.singleton pc (.call sc))
      emp ERR_UNSUPPORTED_INSTRUCTION := by
  intro R hRfree fetch hcr s hPR hpc hex hbud
  have hfetch : fetch s.pc = some (.call sc) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hstep_eq : executeFn fetch s 1 =
      chargeCu (step (.call sc) s) := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch, executeFn_zero]
  refine ⟨1, Nat.le_refl 1, ?_, ?_⟩
  · rw [hstep_eq]
    show (execSyscall sc s).exitCode = some ERR_UNSUPPORTED_INSTRUCTION
    exact hexit s
  · rw [hstep_eq]
    show (step (.call sc) s).cuConsumed + 1
      ≤ s.cuConsumed + 1 + nCu
    have := hCu s; omega

theorem call_sol_invoke_signed_aborts_spec (pc : Nat) (nCu : Nat)
    (hCu : ∀ s : State,
        (step (.call .sol_invoke_signed) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleAbortsWithin 1 nCu pc
      (CodeReq.singleton pc (.call .sol_invoke_signed))
      emp ERR_UNSUPPORTED_INSTRUCTION :=
  call_cpi_syscall_aborts_spec .sol_invoke_signed (fun _ => rfl) pc nCu hCu

theorem call_sol_invoke_signed_c_aborts_spec (pc : Nat) (nCu : Nat)
    (hCu : ∀ s : State,
        (step (.call .sol_invoke_signed_c) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleAbortsWithin 1 nCu pc
      (CodeReq.singleton pc (.call .sol_invoke_signed_c))
      emp ERR_UNSUPPORTED_INSTRUCTION :=
  call_cpi_syscall_aborts_spec .sol_invoke_signed_c (fun _ => rfl) pc nCu hCu

end SVM.SBPF
