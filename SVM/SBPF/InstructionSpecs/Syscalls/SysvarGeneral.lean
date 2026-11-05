import SVM.SBPF.InstructionSpecs.Syscalls.SysvarSpec
import SVM.SBPF.InstructionSpecs.Syscalls.MemOpsGeneral
import SVM.SBPF.InstructionSpecs.Syscalls.Log

/-! # Sysvar triples, for any environment (#105)

Each success triple states its environment as an `rr` clause, `rt.sysvars = env`.
The region table never changes (`executeFn_preserves_regions`), so that clause
composes like any other, and a triple about code that reads no sysvar already
holds for every environment.

`sol_get_sysvar`'s success triple for arbitrary `(offset, len)` is
`call_sol_get_sysvar_spec` in `Log.lean`. -/

namespace SVM.SBPF

open Memory

/-! ## Typed getters -/

/-- `Syscall` `sc` is a typed getter of `size` bytes aligned to `align`, which
    writes `encode` of the environment. -/
def IsTypedGetter (sc : Syscall) (align size : Nat) (encode : SysvarEnv → ByteArray) : Prop :=
  ∀ s, execSyscall sc s = Sysvar.execTyped align size (encode s.regions.sysvars) s

theorem isTypedGetter_clock : IsTypedGetter .sol_get_clock_sysvar 8 40 (·.clock.reprC) :=
  fun _ => rfl
theorem isTypedGetter_rent : IsTypedGetter .sol_get_rent_sysvar 8 24 (·.rent.reprC) :=
  fun _ => rfl
theorem isTypedGetter_epochSchedule :
    IsTypedGetter .sol_get_epoch_schedule_sysvar 8 40 (·.epochSchedule.reprC) := fun _ => rfl
theorem isTypedGetter_epochRewards :
    IsTypedGetter .sol_get_epoch_rewards_sysvar 16 96 (·.epochRewards.reprC) := fun _ => rfl
theorem isTypedGetter_lastRestartSlot :
    IsTypedGetter .sol_get_last_restart_slot 8 8 (·.lastRestartBytes) := fun _ => rfl

/-- `cuTripleWithin_syscall_writesR1Bytes` with its step facts conditional on the
    pinned `r1` and on `rr`. -/
private theorem writesR1Bytes_if
    (sc : Syscall) (bsNew : ByteArray) (pc nCu r1V : Nat) (rr : Memory.RegionTable → Prop)
    (h_step_regs : ∀ s : State, s.regs.r1 = r1V → rr s.regions →
        (step (.call sc) s).regs = s.regs.set .r0 0)
    (h_step_mem_in : ∀ s : State, s.regs.r1 = r1V → rr s.regions → ∀ i, i < bsNew.size →
        (step (.call sc) s).mem (s.regs.r1 + i) = (bsNew.get! i).toNat)
    (h_step_mem_out : ∀ s : State, s.regs.r1 = r1V → rr s.regions → ∀ a,
        (a < s.regs.r1 ∨ a ≥ s.regs.r1 + bsNew.size) →
        (step (.call sc) s).mem a = s.mem a)
    (h_step_pc : ∀ s : State, (step (.call sc) s).pc = s.pc + 1)
    (h_step_exit : ∀ s : State, s.regs.r1 = r1V → rr s.regions → s.exitCode = none →
        (step (.call sc) s).exitCode = none)
    (h_step_returnData : ∀ s : State, (step (.call sc) s).returnData = s.returnData)
    (h_step_callStack : ∀ s : State, (step (.call sc) s).callStack = s.callStack)
    (h_step_cu : ∀ s : State, (step (.call sc) s).cuConsumed ≤ s.cuConsumed + nCu) :
    ∀ r0Old (bsOld : ByteArray), bsOld.size = bsNew.size →
      cuTripleWithinMem 1 nCu pc (pc + 1)
        (CodeReq.singleton pc (.call sc))
        ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1V) ** (r1V ↦Bytes bsOld))
        ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ r1V) ** (r1V ↦Bytes bsNew))
        rr := by
  intro r0Old bsOld hbsSize R hRfree fetch hcr s hPR hpc hex hbud h_region
  let N : Nat := bsNew.size
  obtain ⟨hp, hcompat, h_P, h_R, hd_PR, hu_PR, h_P_sat, h_R_sat⟩ := hPR
  obtain ⟨h_r0, h_T1, hd_r0_T1, hu_r0_T1, h_r0_pred, h_T1_sat⟩ := h_P_sat
  obtain ⟨h_r1, h_b, hd_r1_b, hu_r1_b, h_r1_pred, h_b_pred⟩ := h_T1_sat
  rw [h_r0_pred] at hu_r0_T1 hd_r0_T1
  rw [h_r1_pred] at hu_r1_b hd_r1_b
  rw [h_b_pred] at hu_r1_b hd_r1_b
  clear h_r0_pred h_r1_pred h_b_pred h_r0 h_r1 h_b
  have hcr_regs := hcompat.regs
  have hcm_mem := hcompat.mem
  have h_T1_regs_r1 : h_T1.regs .r1 = some r1V := by
    rw [← hu_r1_b]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_regs_r0 : h_P.regs .r0 = some r0Old := by
    rw [← hu_r0_T1]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_regs_r1 : h_P.regs .r1 = some r1V := by
    rw [← hu_r0_T1,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r1 ≠ Reg.r0))]
    exact h_T1_regs_r1
  have h_P_mem_eq_b (a : Nat) :
      h_P.mem a = (PartialState.singletonMemBytes r1V bsOld).mem a := by
    rw [← hu_r0_T1,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _),
        ← hu_r1_b,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
  have hp_regs_r0 : hp.regs .r0 = some r0Old := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r0
  have hp_regs_r1 : hp.regs .r1 = some r1V := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r1
  have hs_regs_r0 : s.regs.get .r0 = r0Old := hcr_regs .r0 r0Old hp_regs_r0
  have hs_regs_r1 : s.regs.get .r1 = r1V := hcr_regs .r1 r1V hp_regs_r1
  have hs_r1_field : s.regs.r1 = r1V := hs_regs_r1
  have hfetch : fetch s.pc = some (.call sc) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hstep_eq : executeFn fetch s 1 = chargeCu (step (.call sc) s) := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch, executeFn_zero]
  have hexec_pc : (executeFn fetch s 1).pc = s.pc + 1 := by
    rw [hstep_eq]; exact h_step_pc s
  have hexec_exit : (executeFn fetch s 1).exitCode = none := by
    rw [hstep_eq]; exact h_step_exit s hs_r1_field h_region hex
  have hexec_cu : (executeFn fetch s 1).cuConsumed ≤ s.cuConsumed + 1 + nCu := by
    rw [hstep_eq]
    show (step (.call sc) s).cuConsumed + 1 ≤ s.cuConsumed + 1 + nCu
    have := h_step_cu s; omega
  have hexec_regs : (executeFn fetch s 1).regs = s.regs.set .r0 0 := by
    rw [hstep_eq]; exact h_step_regs s hs_r1_field h_region
  have hexec_mem_in (i : Nat) (hi : i < N) :
      (executeFn fetch s 1).mem (r1V + i) = (bsNew.get! i).toNat := by
    rw [hstep_eq, ← hs_r1_field]; exact h_step_mem_in s (by rw [hs_r1_field]) h_region i hi
  have hexec_mem_out (a : Nat) (h : a < r1V ∨ a ≥ r1V + N) :
      (executeFn fetch s 1).mem a = s.mem a := by
    rw [hstep_eq]; apply h_step_mem_out s hs_r1_field h_region a
    rw [hs_r1_field]; exact h
  have hd_PR_regs := hd_PR.regs
  have hd_PR_mem := hd_PR.mem
  have hd_PR_pc := hd_PR.pc
  have h_R_no_r0 : h_R.regs .r0 = none := by
    rcases hd_PR_regs .r0 with hl | hr
    · rw [h_P_regs_r0] at hl; nomatch hl
    · exact hr
  have h_R_no_r1 : h_R.regs .r1 = none := by
    rcases hd_PR_regs .r1 with hl | hr
    · rw [h_P_regs_r1] at hl; nomatch hl
    · exact hr
  have h_R_no_pc : h_R.pc = none := hRfree _ h_R_sat
  have h_R_no_mem_in (i : Nat) (hi : i < N) : h_R.mem (r1V + i) = none := by
    obtain ⟨v, hatom⟩ := PartialState.singletonMemBytes_mem_isSome r1V bsOld
      (r1V + i) ⟨Nat.le_add_right _ _, by rw [hbsSize]; show r1V + i < r1V + N; omega⟩
    have h_P_some : h_P.mem (r1V + i) = some v := by
      rw [h_P_mem_eq_b]; exact hatom
    rcases hd_PR_mem (r1V + i) with hl | hr
    · rw [h_P_some] at hl; nomatch hl
    · exact hr
  let h_r0_new : PartialState := PartialState.singletonReg .r0 0
  let h_r1_new : PartialState := PartialState.singletonReg .r1 r1V
  let h_b_new  : PartialState := PartialState.singletonMemBytes r1V bsNew
  let h_T1_new : PartialState := h_r1_new.union h_b_new
  let h_P_new  : PartialState := h_r0_new.union h_T1_new
  have h_bsNew_mem_in (j : Nat) (hj : j < N) :
      (PartialState.singletonMemBytes r1V bsNew).mem (r1V + j) =
        some (bsNew.get! j).toNat :=
    PartialState.singletonMemBytes_mem_at r1V bsNew j hj
  have h_bsNew_mem_outside (a : Nat) (h : a < r1V ∨ a ≥ r1V + N) :
      (PartialState.singletonMemBytes r1V bsNew).mem a = none :=
    PartialState.singletonMemBytes_mem_outside r1V bsNew a h
  have hd_r1_b_new : h_r1_new.Disjoint h_b_new := by
    refine ⟨fun r => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
    · right; exact PartialState.singletonMemBytes_regs r
    · left; exact PartialState.singletonReg_mem a
    · left; exact PartialState.singletonReg_pc
  have hd_r0_T1_new : h_r0_new.Disjoint h_T1_new := by
    refine ⟨fun r => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
    · by_cases hr0 : r = .r0
      · right
        show h_T1_new.regs r = none
        show ((PartialState.singletonReg .r1 r1V).union h_b_new).regs r = none
        rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other
              (hr0 ▸ (by decide : Reg.r0 ≠ Reg.r1)))]
        exact PartialState.singletonMemBytes_regs r
      · left; exact PartialState.singletonReg_regs_other hr0
    · left; exact PartialState.singletonReg_mem a
    · left; exact PartialState.singletonReg_pc
  have h_P_new_regs_r0 : h_P_new.regs .r0 = some 0 :=
    PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_new_regs_r1 : h_P_new.regs .r1 = some r1V := by
    show ((PartialState.singletonReg .r0 0).union h_T1_new).regs .r1 = some r1V
    rw [PartialState.union_regs_of_left_none
        (PartialState.singletonReg_regs_other (by decide : Reg.r1 ≠ Reg.r0))]
    show ((PartialState.singletonReg .r1 r1V).union h_b_new).regs .r1 = some r1V
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_new_regs_other (r : Reg) (h0 : r ≠ .r0) (h1 : r ≠ .r1) :
      h_P_new.regs r = none := by
    show ((PartialState.singletonReg .r0 0).union h_T1_new).regs r = none
    rw [PartialState.union_regs_of_left_none
        (PartialState.singletonReg_regs_other h0)]
    show ((PartialState.singletonReg .r1 r1V).union h_b_new).regs r = none
    rw [PartialState.union_regs_of_left_none
        (PartialState.singletonReg_regs_other h1)]
    exact PartialState.singletonMemBytes_regs r
  have h_P_new_mem_eq_b (a : Nat) : h_P_new.mem a = h_b_new.mem a := by
    show ((PartialState.singletonReg .r0 0).union h_T1_new).mem a = h_b_new.mem a
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    show ((PartialState.singletonReg .r1 r1V).union h_b_new).mem a = h_b_new.mem a
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
  have h_P_new_mem_outside (a : Nat) (h : a < r1V ∨ a ≥ r1V + N) :
      h_P_new.mem a = none := by
    rw [h_P_new_mem_eq_b]
    exact h_bsNew_mem_outside a h
  have h_P_new_mem_in (j : Nat) (hj : j < N) :
      h_P_new.mem (r1V + j) = some (bsNew.get! j).toNat := by
    rw [h_P_new_mem_eq_b]
    exact h_bsNew_mem_in j hj
  have h_P_new_pc : h_P_new.pc = none := by
    show ((PartialState.singletonReg .r0 0).union h_T1_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    show ((PartialState.singletonReg .r1 r1V).union h_b_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    exact PartialState.singletonMemBytes_pc
  have hd_PnewR : h_P_new.Disjoint h_R := by
    refine ⟨fun r => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
    · by_cases h0 : r = .r0
      · right; rw [h0]; exact h_R_no_r0
      by_cases h1 : r = .r1
      · right; rw [h1]; exact h_R_no_r1
      · left; exact h_P_new_regs_other r h0 h1
    · by_cases ha : r1V ≤ a ∧ a < r1V + N
      · right
        obtain ⟨h1, h2⟩ := ha
        have h_eq : a = r1V + (a - r1V) := by omega
        have h_lt : a - r1V < N := by omega
        rw [h_eq]; exact h_R_no_mem_in _ h_lt
      · left
        apply h_P_new_mem_outside
        rcases Nat.lt_or_ge a r1V with h | h
        · left; exact h
        · rcases Nat.lt_or_ge a (r1V + N) with h' | h'
          · exact absurd ⟨h, h'⟩ ha
          · right; exact h'
    · left; exact h_P_new_pc
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_, ?_⟩
  · rw [hexec_pc, hpc]
  · exact hexec_exit
  · exact hexec_cu
  · refine ⟨h_P_new.union h_R, ?_, h_P_new, h_R, hd_PnewR, rfl,
            ⟨h_r0_new, h_T1_new, hd_r0_T1_new, rfl, rfl,
             h_r1_new, h_b_new, hd_r1_b_new, rfl, rfl, rfl⟩,
            h_R_sat⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    -- regs
    · intro r vr hvr
      by_cases h0 : r = .r0
      · rw [h0] at hvr
        rw [PartialState.union_regs_of_left_some h_P_new_regs_r0] at hvr
        have hvr0 : vr = 0 := (Option.some.inj hvr).symm
        rw [h0, hexec_regs, hvr0]
        exact RegFile.get_set_self _ _ _ (by decide : (.r0 : Reg) ≠ .r10)
      by_cases h1 : r = .r1
      · rw [h1] at hvr
        rw [PartialState.union_regs_of_left_some h_P_new_regs_r1] at hvr
        have hvr1 : vr = r1V := (Option.some.inj hvr).symm
        rw [h1, hexec_regs, hvr1,
            RegFile.get_set_diff _ _ _ _ (by decide : (.r1 : Reg) ≠ .r0)]
        exact hs_regs_r1
      · rw [PartialState.union_regs_of_left_none
            (h_P_new_regs_other r h0 h1)] at hvr
        rw [hexec_regs, RegFile.get_set_diff _ _ _ _ h0]
        have h_P_none : h_P.regs r = none := by
          rcases hd_PR_regs r with hl | hr
          · exact hl
          · rw [hr] at hvr; nomatch hvr
        apply hcr_regs r vr
        rw [← hu_PR, PartialState.union_regs_of_left_none h_P_none]
        exact hvr
    -- mem
    · intro a vm hvm
      by_cases ha : r1V ≤ a ∧ a < r1V + N
      · obtain ⟨h1, h2⟩ := ha
        have h_eq : a = r1V + (a - r1V) := by omega
        have h_lt : a - r1V < N := by omega
        rw [h_eq] at hvm ⊢
        rw [PartialState.union_mem_of_left_some
            (h_P_new_mem_in _ h_lt)] at hvm
        have hvmEq : vm = (bsNew.get! (a - r1V)).toNat :=
          (Option.some.inj hvm).symm
        rw [hexec_mem_in _ h_lt, hvmEq]
      · have h_out : a < r1V ∨ a ≥ r1V + N := by
          rcases Nat.lt_or_ge a r1V with h | h
          · left; exact h
          · rcases Nat.lt_or_ge a (r1V + N) with h' | h'
            · exact absurd ⟨h, h'⟩ ha
            · right; exact h'
        rw [PartialState.union_mem_of_left_none
            (h_P_new_mem_outside a h_out)] at hvm
        rw [hexec_mem_out a h_out]
        have h_P_none : h_P.mem a = none := by
          rcases hd_PR_mem a with hl | hr
          · exact hl
          · rw [hr] at hvm; nomatch hvm
        apply hcm_mem a vm
        rw [← hu_PR, PartialState.union_mem_of_left_none h_P_none]
        exact hvm
    -- pc
    · intro vp hvp
      rw [PartialState.union_pc_of_left_none h_P_new_pc] at hvp
      rw [h_R_no_pc] at hvp
      nomatch hvp
    · intro rd hva
      have h_P_new_rd : h_P_new.returnData = none := by rfl
      rw [PartialState.union_returnData_of_left_none h_P_new_rd] at hva
      have h_P_rd : h_P.returnData = none := by
        rw [← hu_r0_T1, ← hu_r1_b]; rfl
      have hp_rd : hp.returnData = some rd := by
        rw [← hu_PR, PartialState.union_returnData_of_left_none h_P_rd]
        exact hva
      have hexec_rd : (executeFn fetch s 1).returnData = s.returnData := by
        rw [hstep_eq]; exact h_step_returnData s
      rw [hexec_rd]
      exact hcompat.returnData rd hp_rd
    · intro cs hva
      have h_P_new_cs : h_P_new.callStack = none := by rfl
      rw [PartialState.union_callStack_of_left_none h_P_new_cs] at hva
      have h_P_cs : h_P.callStack = none := by
        rw [← hu_r0_T1, ← hu_r1_b]; rfl
      have hp_cs : hp.callStack = some cs := by
        rw [← hu_PR, PartialState.union_callStack_of_left_none h_P_cs]
        exact hva
      have hexec_cs : (executeFn fetch s 1).callStack = s.callStack := by
        rw [hstep_eq]; exact h_step_callStack s
      rw [hexec_cs]
      exact hcompat.callStack cs hp_cs

/-- A typed getter writes the environment's sysvar over an aligned, writable
    output below the input region. -/
theorem call_typed_getter_spec {sc : Syscall} {align size : Nat} {encode : SysvarEnv → ByteArray}
    (hg : IsTypedGetter sc align size encode) (hsize : ∀ env, (encode env).size = size)
    (env : SysvarEnv) (r0Old out pc nCu : Nat) (old : ByteArray) (hOld : old.size = size)
    (hAlign : out % align = 0) (hOut : out < Memory.INPUT_START)
    (hCu : ∀ s : State, (step (.call sc) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithinMem 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call sc))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ out) ** (out ↦Bytes old))
      ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ out) ** (out ↦Bytes encode env))
      (fun rt => rt.sysvars = env ∧ rt.containsWritable out size = true) := by
  have hok : ∀ s : State, s.regs.r1 = out →
      (s.regions.sysvars = env ∧ s.regions.containsWritable out size = true) →
      execSyscall sc s =
        { s with regs := s.regs.set .r0 0,
                 mem := fun a =>
                   if a ≥ s.regs.r1 ∧ a - s.regs.r1 < size then
                     ((encode env).get! (a - s.regs.r1)).toNat
                   else s.mem a } := by
    intro s h1 hr
    rw [hg s, hr.1]
    exact Sysvar.execTyped_ok _ _ _ s (by rw [h1]; exact hOut) (by rw [h1]; exact hr.2)
      (by rw [h1]; exact hAlign)
  have hstepRd : ∀ s : State, (execSyscall sc s).returnData = s.returnData := by
    intro s; rw [hg s]; simp only [Sysvar.execTyped, State.guardWrite, State.accessFault]
    repeat' split
    all_goals rfl
  have hstepCs : ∀ s : State, (execSyscall sc s).callStack = s.callStack := by
    intro s; rw [hg s]; simp only [Sysvar.execTyped, State.guardWrite, State.accessFault]
    repeat' split
    all_goals rfl
  refine writesR1Bytes_if sc (encode env) pc nCu out _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hCu r0Old old
    (by rw [hOld, hsize])
  · intro s h1 hr; simp only [step, hok s h1 hr]
  · intro s h1 hr i hi
    simp only [step, hok s h1 hr]
    rw [Mem_read_default, if_pos ⟨Nat.le_add_right _ _, by rw [hsize] at hi; omega⟩,
      show s.regs.r1 + i - s.regs.r1 = i by omega]
  · intro s h1 hr a ha
    simp only [step, hok s h1 hr]
    rw [hsize] at ha
    rw [Mem_read_default, if_neg (by omega)]
  · intro s; rfl
  · intro s h1 hr hex; simp only [step, hok s h1 hr]; exact hex
  · intro s; exact hstepRd s
  · intro s; exact hstepCs s

/-- The bytes of each sysvar at `out`, as the typed getter writes them. -/
abbrev clockIs (out : Nat) (env : SysvarEnv) : Assertion := out ↦Bytes env.clock.reprC
abbrev rentIs (out : Nat) (env : SysvarEnv) : Assertion := out ↦Bytes env.rent.reprC
abbrev epochScheduleIs (out : Nat) (env : SysvarEnv) : Assertion :=
  out ↦Bytes env.epochSchedule.reprC
abbrev epochRewardsIs (out : Nat) (env : SysvarEnv) : Assertion :=
  out ↦Bytes env.epochRewards.reprC
abbrev lastRestartSlotIs (out : Nat) (env : SysvarEnv) : Assertion :=
  out ↦Bytes env.lastRestartBytes

theorem call_sol_get_clock_sysvar_spec (env : SysvarEnv) (r0Old out pc nCu : Nat)
    (old : ByteArray) (hOld : old.size = 40) (hAlign : out % 8 = 0)
    (hOut : out < Memory.INPUT_START)
    (hCu : ∀ s : State,
      (step (.call .sol_get_clock_sysvar) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithinMem 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_get_clock_sysvar))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ out) ** (out ↦Bytes old))
      ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ out) ** clockIs out env)
      (fun rt => rt.sysvars = env ∧ rt.containsWritable out 40 = true) :=
  call_typed_getter_spec isTypedGetter_clock (fun e => e.clock.reprC_size) env r0Old out pc nCu
    old hOld hAlign hOut hCu

theorem call_sol_get_rent_sysvar_spec (env : SysvarEnv) (r0Old out pc nCu : Nat)
    (old : ByteArray) (hOld : old.size = 24) (hAlign : out % 8 = 0)
    (hOut : out < Memory.INPUT_START)
    (hCu : ∀ s : State,
      (step (.call .sol_get_rent_sysvar) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithinMem 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_get_rent_sysvar))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ out) ** (out ↦Bytes old))
      ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ out) ** rentIs out env)
      (fun rt => rt.sysvars = env ∧ rt.containsWritable out 24 = true) :=
  call_typed_getter_spec isTypedGetter_rent (fun e => e.rent.reprC_size) env r0Old out pc nCu
    old hOld hAlign hOut hCu

theorem call_sol_get_epoch_schedule_sysvar_spec (env : SysvarEnv) (r0Old out pc nCu : Nat)
    (old : ByteArray) (hOld : old.size = 40) (hAlign : out % 8 = 0)
    (hOut : out < Memory.INPUT_START)
    (hCu : ∀ s : State,
      (step (.call .sol_get_epoch_schedule_sysvar) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithinMem 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_get_epoch_schedule_sysvar))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ out) ** (out ↦Bytes old))
      ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ out) ** epochScheduleIs out env)
      (fun rt => rt.sysvars = env ∧ rt.containsWritable out 40 = true) :=
  call_typed_getter_spec isTypedGetter_epochSchedule (fun e => e.epochSchedule.reprC_size)
    env r0Old out pc nCu old hOld hAlign hOut hCu

theorem call_sol_get_epoch_rewards_sysvar_spec (env : SysvarEnv) (r0Old out pc nCu : Nat)
    (old : ByteArray) (hOld : old.size = 96) (hAlign : out % 16 = 0)
    (hOut : out < Memory.INPUT_START)
    (hCu : ∀ s : State,
      (step (.call .sol_get_epoch_rewards_sysvar) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithinMem 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_get_epoch_rewards_sysvar))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ out) ** (out ↦Bytes old))
      ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ out) ** epochRewardsIs out env)
      (fun rt => rt.sysvars = env ∧ rt.containsWritable out 96 = true) :=
  call_typed_getter_spec isTypedGetter_epochRewards (fun e => e.epochRewards.reprC_size)
    env r0Old out pc nCu old hOld hAlign hOut hCu

theorem call_sol_get_last_restart_slot_spec (env : SysvarEnv) (r0Old out pc nCu : Nat)
    (old : ByteArray) (hOld : old.size = 8) (hAlign : out % 8 = 0)
    (hOut : out < Memory.INPUT_START)
    (hCu : ∀ s : State,
      (step (.call .sol_get_last_restart_slot) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithinMem 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_get_last_restart_slot))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ out) ** (out ↦Bytes old))
      ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ out) ** lastRestartSlotIs out env)
      (fun rt => rt.sysvars = env ∧ rt.containsWritable out 8 = true) :=
  call_typed_getter_spec isTypedGetter_lastRestartSlot (fun e => e.lastRestartBytes_size)
    env r0Old out pc nCu old hOld hAlign hOut hCu

/-! ## Typed getter faults -/

private theorem r1_get {r1V : Nat} {R : Assertion} {s : State}
    (h : ((.r1 ↦ᵣ r1V) ** R).holdsFor s) : s.regs.r1 = r1V :=
  regIs_sepConj_get h

/-- A typed getter's output in the input region faults. -/
theorem call_typed_getter_input_faults_spec {sc : Syscall} {align size : Nat}
    {encode : SysvarEnv → ByteArray} (hg : IsTypedGetter sc align size encode)
    (r1V pc nCu : Nat) (hIn : Memory.INPUT_START ≤ r1V)
    (hCu : ∀ s : State, (step (.call sc) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleFaultsWithinMem 1 nCu pc (CodeReq.singleton pc (.call sc))
      (.r1 ↦ᵣ r1V) (fun _ => True) .accessViolation :=
  cuTripleFaultsWithinMem_syscall _ pc nCu _ _ _ (fun s => s.regs.r1 = r1V)
    (fun _ _ h => r1_get h)
    (fun s h1 _ => by
      rw [hg s]
      have := Sysvar.execTyped_faults_input align size (encode s.regions.sysvars) s
        (by rw [h1]; exact hIn)
      exact ⟨this.2, this.1⟩) hCu

/-- A typed getter's output outside a writable region faults. -/
theorem call_typed_getter_oob_faults_spec {sc : Syscall} {align size : Nat}
    {encode : SysvarEnv → ByteArray} (hg : IsTypedGetter sc align size encode)
    (r1V pc nCu : Nat) (hSize : size ≠ 0)
    (hCu : ∀ s : State, (step (.call sc) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleFaultsWithinMem 1 nCu pc (CodeReq.singleton pc (.call sc))
      (.r1 ↦ᵣ r1V) (fun rt => rt.containsWritable r1V size = false) .accessViolation :=
  cuTripleFaultsWithinMem_syscall _ pc nCu _ _ _ (fun s => s.regs.r1 = r1V)
    (fun _ _ h => r1_get h)
    (fun s h1 hr => by
      rw [hg s]
      have := Sysvar.execTyped_faults_oob align size (encode s.regions.sysvars) s hSize
        (by rw [h1]; exact hr)
      exact ⟨this.2, this.1⟩) hCu

/-- A typed getter's writable but unaligned output faults. -/
theorem call_typed_getter_unaligned_faults_spec {sc : Syscall} {align size : Nat}
    {encode : SysvarEnv → ByteArray} (hg : IsTypedGetter sc align size encode)
    (r1V pc nCu : Nat) (hIn : r1V < Memory.INPUT_START) (hAlign : r1V % align ≠ 0)
    (hCu : ∀ s : State, (step (.call sc) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleFaultsWithinMem 1 nCu pc (CodeReq.singleton pc (.call sc))
      (.r1 ↦ᵣ r1V) (fun rt => rt.containsWritable r1V size = true) .unalignedPointer :=
  cuTripleFaultsWithinMem_syscall _ pc nCu _ _ _ (fun s => s.regs.r1 = r1V)
    (fun _ _ h => r1_get h)
    (fun s h1 hr => by
      rw [hg s]
      have := Sysvar.execTyped_faults_unaligned align size (encode s.regions.sysvars) s
        (by rw [h1]; exact hIn) (by rw [h1]; exact hr) (by rw [h1]; exact hAlign)
      exact ⟨this.2, this.1⟩) hCu

/-! ## Syscalls that only set `r0` -/

/-- `r0`'s value changes and nothing else `X` can see does, so `X` still holds. -/
theorem r0_update_holdsFor {a b : Nat} {X : Assertion} {s s' : State}
    (h : ((.r0 ↦ᵣ a) ** X).holdsFor s) (hX : X.pcFree)
    (hregs : s'.regs = s.regs.set .r0 b) (hmem : s'.mem = s.mem)
    (hrd : s'.returnData = s.returnData) (hcs : s'.callStack = s.callStack) :
    ((.r0 ↦ᵣ b) ** X).holdsFor s' := by
  obtain ⟨hh, hc, h1, h2, hd, hu, hP, hXs⟩ := h
  subst hP
  subst hu
  have h2r0 : h2.regs .r0 = none := by
    rcases hd.regs .r0 with h | h
    · rw [PartialState.singletonReg_regs_self] at h; nomatch h
    · exact h
  have h2pc : h2.pc = none := hX _ hXs
  refine ⟨(PartialState.singletonReg .r0 b).union h2, ?_, _, h2, ?_, rfl, rfl, hXs⟩
  · refine ⟨fun r v hv => ?_, fun x v hv => ?_, fun v hv => ?_, fun rd hv => ?_, fun cs hv => ?_⟩
    · by_cases hr : r = .r0
      · subst hr
        rw [PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self] at hv
        rw [hregs, ← Option.some.inj hv]
        exact RegFile.get_set_self _ _ _ (by decide)
      · rw [PartialState.union_regs_of_left_none (PartialState.singletonReg_regs_other hr)] at hv
        rw [hregs, RegFile.get_set_diff _ _ _ _ hr]
        apply hc.regs r v
        rw [PartialState.union_regs_of_left_none (PartialState.singletonReg_regs_other hr)]
        exact hv
    · rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)] at hv
      rw [hmem]
      apply hc.mem x v
      rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
      exact hv
    · rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc, h2pc] at hv
      nomatch hv
    · rw [hrd]; exact hc.returnData rd (by
        rw [PartialState.union_returnData_of_left_none rfl] at hv ⊢; exact hv)
    · rw [hcs]; exact hc.callStack cs (by
        rw [PartialState.union_callStack_of_left_none rfl] at hv ⊢; exact hv)
  · refine ⟨fun r => ?_, fun x => Or.inl (PartialState.singletonReg_mem x),
      Or.inl PartialState.singletonReg_pc, Or.inl rfl, Or.inl rfl⟩
    by_cases hr : r = .r0
    · subst hr; exact Or.inr h2r0
    · exact Or.inl (PartialState.singletonReg_regs_other hr)

/-- A syscall that, on every state `P` and `rr` admit, sets `r0` to `vNew` and
    leaves what `F` can see alone. -/
theorem cuTripleWithinMem_syscall_setR0
    (sc : Syscall) (pc nCu vNew r0Old : Nat) (F : Assertion) (hF : F.pcFree)
    (rr : Memory.RegionTable → Prop) (Q : State → Prop)
    (hQ : ∀ R s, (((.r0 ↦ᵣ r0Old) ** F) ** R).holdsFor s → rr s.regions → Q s)
    (hexec : ∀ s, Q s → execSyscall sc s = { s with regs := s.regs.set .r0 vNew })
    (hCu : ∀ s : State, (step (.call sc) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithinMem 1 nCu pc (pc + 1) (CodeReq.singleton pc (.call sc))
      ((.r0 ↦ᵣ r0Old) ** F) ((.r0 ↦ᵣ vNew) ** F) rr := by
  intro R hR fetch hcr s hPR hpc hex hbud h_region
  have hq := hQ R s hPR h_region
  have hfetch : fetch s.pc = some (.call sc) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hstep : executeFn fetch s 1 = chargeCu (step (.call sc) s) := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch, executeFn_zero]
  have hs : step (.call sc) s =
      { s with regs := s.regs.set .r0 vNew, pc := s.pc + 1,
               cuConsumed := s.cuConsumed + syscallCu sc s } := by
    simp only [step, hexec s hq]
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_, ?_⟩
  · rw [hstep, hs, hpc]; rfl
  · rw [hstep, hs]; exact hex
  · rw [hstep]
    show (step (.call sc) s).cuConsumed + 1 ≤ s.cuConsumed + 1 + nCu
    have := hCu s; omega
  · have ha := (holdsFor_sepConj_assoc).mp hPR
    have hpf : (F ** R).pcFree := pcFree_sepConj hF hR
    refine (holdsFor_sepConj_assoc).mpr (r0_update_holdsFor ha hpf ?_ ?_ ?_ ?_)
    all_goals rw [hstep, hs]; rfl

/-- `(a ↦Bytes32 bs) ** R` pins those bytes of memory, and so `readBytes`. -/
theorem bytes32_sepConj_read {a : Nat} {bs : ByteArray} {R : Assertion} {s : State}
    (hsize : bs.size = 32) (h : ((a ↦Bytes32 bs) ** R).holdsFor s) :
    readBytes s.mem a 32 = bs := by
  obtain ⟨hp, hc, h1, h2, _, hu, hP, _⟩ := h
  apply readBytes_eq_of_match s.mem a 32 bs hsize
  intro i hi
  have hm : s.mem (a + i) = (bs.get! i).toNat := by
    apply hc.mem
    rw [← hu, hP]
    exact PartialState.union_mem_of_left_some (PartialState.singletonMem32Bytes_mem_at a bs i hi)
  rw [hm]
  exact Nat.mod_eq_of_lt (bs.get! i).toNat_lt

/-! ## `sol_get_epoch_stake` -/

/-- A null pointer returns the environment's total stake. -/
theorem call_sol_get_epoch_stake_total_spec (env : SysvarEnv) (r0Old pc nCu : Nat)
    (hCu : ∀ s : State, (step (.call .sol_get_epoch_stake) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithinMem 1 nCu pc (pc + 1) (CodeReq.singleton pc (.call .sol_get_epoch_stake))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ 0))
      ((.r0 ↦ᵣ env.totalStake % U64_MODULUS) ** (.r1 ↦ᵣ 0))
      (fun rt => rt.sysvars = env) :=
  cuTripleWithinMem_syscall_setR0 _ pc nCu _ r0Old (.r1 ↦ᵣ 0) (pcFree_regIs _ _) _
    (fun s => s.regs.r1 = 0 ∧ s.regions.sysvars = env)
    (fun R s h hr => ⟨by
      have h2 := (holdsFor_sepConj_assoc).mp h
      exact regIs_sepConj_get (sepConj_holdsFor_tail h2), hr⟩)
    (fun s ⟨h1, he⟩ => by
      rw [show execSyscall .sol_get_epoch_stake s = Sysvar.execEpochStake s from rfl,
        Sysvar.execEpochStake_null s h1, he])
    hCu

/-- A readable vote key returns its stake in the environment. -/
theorem call_sol_get_epoch_stake_vote_spec (env : SysvarEnv) (r0Old voteA pc nCu : Nat)
    (vote : ByteArray) (hSize : vote.size = 32) (hNull : voteA ≠ 0)
    (hCu : ∀ s : State, (step (.call .sol_get_epoch_stake) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithinMem 1 nCu pc (pc + 1) (CodeReq.singleton pc (.call .sol_get_epoch_stake))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ voteA) ** (voteA ↦Bytes32 vote))
      ((.r0 ↦ᵣ env.stakeOf vote % U64_MODULUS) ** (.r1 ↦ᵣ voteA) ** (voteA ↦Bytes32 vote))
      (fun rt => rt.sysvars = env ∧ rt.containsRange voteA 32 = true) :=
  cuTripleWithinMem_syscall_setR0 _ pc nCu _ r0Old ((.r1 ↦ᵣ voteA) ** (voteA ↦Bytes32 vote))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_memBytes32Is _ _)) _
    (fun s => s.regs.r1 = voteA ∧ readBytes s.mem voteA 32 = vote ∧
      s.regions.sysvars = env ∧ s.regions.containsRange voteA 32 = true)
    (fun R s h hr => by
      have h2 := sepConj_holdsFor_tail ((holdsFor_sepConj_assoc).mp h)
      have h3 := (holdsFor_sepConj_assoc).mp h2
      exact ⟨regIs_sepConj_get h3, bytes32_sepConj_read hSize (sepConj_holdsFor_tail h3),
        hr.1, hr.2⟩)
    (fun s ⟨h1, hb, he, hr⟩ => by
      rw [show execSyscall .sol_get_epoch_stake s = Sysvar.execEpochStake s from rfl,
        Sysvar.execEpochStake_vote s (by rw [h1]; exact hNull) (by rw [h1]; exact hr), h1, hb, he])
    hCu

/-- An unreadable vote key faults. -/
theorem call_sol_get_epoch_stake_oob_faults_spec (r1V pc nCu : Nat) (hNull : r1V ≠ 0)
    (hCu : ∀ s : State, (step (.call .sol_get_epoch_stake) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleFaultsWithinMem 1 nCu pc (CodeReq.singleton pc (.call .sol_get_epoch_stake))
      (.r1 ↦ᵣ r1V) (fun rt => rt.containsRange r1V 32 = false) .accessViolation :=
  cuTripleFaultsWithinMem_syscall _ pc nCu _ _ _ (fun s => s.regs.r1 = r1V)
    (fun _ _ h => r1_get h)
    (fun s h1 hr => by
      have := Sysvar.execEpochStake_faults s (by rw [h1]; exact hNull) (by rw [h1]; exact hr)
      exact ⟨this.2, this.1⟩) hCu

/-! ## `sol_get_sysvar`: in-band results and faults -/

/-- The registers and id `sol_get_sysvar`'s in-band results keep. -/
abbrev getSysvarArgs (idA outA offV lenV : Nat) (idBytes : ByteArray) : Assertion :=
  (.r1 ↦ᵣ idA) ** (.r2 ↦ᵣ outA) ** (.r3 ↦ᵣ offV) ** (.r4 ↦ᵣ lenV) ** (idA ↦Bytes32 idBytes)

private theorem getSysvarArgs_pcFree (idA outA offV lenV : Nat) (idBytes : ByteArray) :
    (getSysvarArgs idA outA offV lenV idBytes).pcFree :=
  pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _) (pcFree_sepConj
    (pcFree_regIs _ _) (pcFree_sepConj (pcFree_regIs _ _) (pcFree_memBytes32Is _ _))))

private theorem getSysvarArgs_ok {r0Old idA outA offV lenV : Nat} {idBytes : ByteArray}
    {R : Assertion} {s : State} (hSize : idBytes.size = 32)
    (h : (((.r0 ↦ᵣ r0Old) ** getSysvarArgs idA outA offV lenV idBytes) ** R).holdsFor s) :
    s.regs.r1 = idA ∧ s.regs.r2 = outA ∧ s.regs.r3 = offV ∧ s.regs.r4 = lenV ∧
      readBytes s.mem idA 32 = idBytes := by
  have h0 := sepConj_holdsFor_tail ((holdsFor_sepConj_assoc).mp h)
  have h1 := (holdsFor_sepConj_assoc).mp h0
  have h2 := (holdsFor_sepConj_assoc).mp (sepConj_holdsFor_tail h1)
  have h3 := (holdsFor_sepConj_assoc).mp (sepConj_holdsFor_tail h2)
  have h4 := (holdsFor_sepConj_assoc).mp (sepConj_holdsFor_tail h3)
  exact ⟨regIs_sepConj_get h1, regIs_sepConj_get h2, regIs_sepConj_get h3, regIs_sepConj_get h4,
    bytes32_sepConj_read hSize (sepConj_holdsFor_tail h4)⟩

/-- An id outside the environment's sysvars sets `r0 := 2` and writes nothing. -/
theorem call_sol_get_sysvar_not_found_spec (env : SysvarEnv) (r0Old idA outA offV lenV pc nCu : Nat)
    (idBytes : ByteArray) (hSize : idBytes.size = 32) (hId : env.bincode idBytes = none)
    (hOut : outA < Memory.INPUT_START) (hOffLen : offV + lenV < U64_MODULUS)
    (hOutLen : outA + lenV < U64_MODULUS)
    (hCu : ∀ s : State, (step (.call .sol_get_sysvar) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithinMem 1 nCu pc (pc + 1) (CodeReq.singleton pc (.call .sol_get_sysvar))
      ((.r0 ↦ᵣ r0Old) ** getSysvarArgs idA outA offV lenV idBytes)
      ((.r0 ↦ᵣ 2) ** getSysvarArgs idA outA offV lenV idBytes)
      (fun rt => (rt.sysvars = env ∧ (lenV = 0 ∨ rt.containsWritable outA lenV = true)) ∧
        rt.containsRange idA 32 = true) :=
  cuTripleWithinMem_syscall_setR0 _ pc nCu _ r0Old _ (getSysvarArgs_pcFree _ _ _ _ _) _
    (fun s => Misc.GetSysvarArgsOk s ∧ s.regions.sysvars.bincode (readBytes s.mem s.regs.r1 32) = none)
    (fun R s h hr => by
      obtain ⟨h1, h2, h3, h4, hb⟩ := getSysvarArgs_ok hSize h
      refine ⟨⟨by rw [h2]; exact hOut, by rw [h2, h4]; exact hr.1.2, by rw [h1]; exact hr.2,
        by rw [h2, h3, h4]; exact ⟨hOffLen, hOutLen⟩⟩, ?_⟩
      rw [h1, hb, hr.1.1]; exact hId)
    (fun s ⟨h, hid⟩ => Misc.execGetSysvar_notFound s h hid)
    hCu

/-- A window past the sysvar's end sets `r0 := 1` and writes nothing. -/
theorem call_sol_get_sysvar_out_of_range_spec (env : SysvarEnv)
    (r0Old idA outA offV lenV pc nCu : Nat) (idBytes buf : ByteArray)
    (hSize : idBytes.size = 32) (hId : env.bincode idBytes = some buf)
    (hOver : buf.size < offV + lenV)
    (hOut : outA < Memory.INPUT_START) (hOffLen : offV + lenV < U64_MODULUS)
    (hOutLen : outA + lenV < U64_MODULUS)
    (hCu : ∀ s : State, (step (.call .sol_get_sysvar) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithinMem 1 nCu pc (pc + 1) (CodeReq.singleton pc (.call .sol_get_sysvar))
      ((.r0 ↦ᵣ r0Old) ** getSysvarArgs idA outA offV lenV idBytes)
      ((.r0 ↦ᵣ 1) ** getSysvarArgs idA outA offV lenV idBytes)
      (fun rt => (rt.sysvars = env ∧ (lenV = 0 ∨ rt.containsWritable outA lenV = true)) ∧
        rt.containsRange idA 32 = true) :=
  cuTripleWithinMem_syscall_setR0 _ pc nCu _ r0Old _ (getSysvarArgs_pcFree _ _ _ _ _) _
    (fun s => Misc.GetSysvarArgsOk s ∧
      s.regions.sysvars.bincode (readBytes s.mem s.regs.r1 32) = some buf ∧
      s.regs.r3 + s.regs.r4 > buf.size)
    (fun R s h hr => by
      obtain ⟨h1, h2, h3, h4, hb⟩ := getSysvarArgs_ok hSize h
      refine ⟨⟨by rw [h2]; exact hOut, by rw [h2, h4]; exact hr.1.2, by rw [h1]; exact hr.2,
        by rw [h2, h3, h4]; exact ⟨hOffLen, hOutLen⟩⟩, ?_, by rw [h3, h4]; exact hOver⟩
      rw [h1, hb, hr.1.1]; exact hId)
    (fun s ⟨h, hid, hover⟩ => Misc.execGetSysvar_outOfRange s h buf hid hover)
    hCu

private theorem getSysvarRegs_get {idA outA lenV : Nat} {R : Assertion} {s : State}
    (h : (((.r1 ↦ᵣ idA) ** (.r2 ↦ᵣ outA) ** (.r4 ↦ᵣ lenV)) ** R).holdsFor s) :
    s.regs.r1 = idA ∧ s.regs.r2 = outA ∧ s.regs.r4 = lenV := by
  have h1 := (holdsFor_sepConj_assoc).mp h
  have h2 := (holdsFor_sepConj_assoc).mp (sepConj_holdsFor_tail h1)
  exact ⟨regIs_sepConj_get h1, regIs_sepConj_get h2,
    regIs_sepConj_get (sepConj_holdsFor_tail h2)⟩

/-- An output in the input region faults. -/
theorem call_sol_get_sysvar_input_faults_spec (idA outA lenV pc nCu : Nat)
    (hIn : Memory.INPUT_START ≤ outA)
    (hCu : ∀ s : State, (step (.call .sol_get_sysvar) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleFaultsWithinMem 1 nCu pc (CodeReq.singleton pc (.call .sol_get_sysvar))
      ((.r1 ↦ᵣ idA) ** (.r2 ↦ᵣ outA) ** (.r4 ↦ᵣ lenV)) (fun _ => True) .accessViolation :=
  cuTripleFaultsWithinMem_syscall _ pc nCu _ _ _ _ (fun _ _ h => getSysvarRegs_get h)
    (fun s ⟨_, h2, _⟩ _ => by
      have := Misc.execGetSysvar_faults_input s (by rw [h2]; exact hIn)
      exact ⟨this.2, this.1⟩) hCu

/-- A nonempty output outside a writable region faults. -/
theorem call_sol_get_sysvar_out_oob_faults_spec (idA outA lenV pc nCu : Nat)
    (hIn : outA < Memory.INPUT_START) (hLen : lenV ≠ 0)
    (hCu : ∀ s : State, (step (.call .sol_get_sysvar) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleFaultsWithinMem 1 nCu pc (CodeReq.singleton pc (.call .sol_get_sysvar))
      ((.r1 ↦ᵣ idA) ** (.r2 ↦ᵣ outA) ** (.r4 ↦ᵣ lenV))
      (fun rt => rt.containsWritable outA lenV = false) .accessViolation :=
  cuTripleFaultsWithinMem_syscall _ pc nCu _ _ _ _ (fun _ _ h => getSysvarRegs_get h)
    (fun s ⟨_, h2, h4⟩ hr => by
      have := Misc.execGetSysvar_faults_oob_out s (by rw [h2]; exact hIn) (by rw [h4]; exact hLen)
        (by rw [h2, h4]; exact hr)
      exact ⟨this.2, this.1⟩) hCu

/-- With the output fine, an unreadable id faults. -/
theorem call_sol_get_sysvar_id_oob_faults_spec (idA outA lenV pc nCu : Nat)
    (hIn : outA < Memory.INPUT_START)
    (hCu : ∀ s : State, (step (.call .sol_get_sysvar) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleFaultsWithinMem 1 nCu pc (CodeReq.singleton pc (.call .sol_get_sysvar))
      ((.r1 ↦ᵣ idA) ** (.r2 ↦ᵣ outA) ** (.r4 ↦ᵣ lenV))
      (fun rt => (lenV = 0 ∨ rt.containsWritable outA lenV = true) ∧
        rt.containsRange idA 32 = false) .accessViolation :=
  cuTripleFaultsWithinMem_syscall _ pc nCu _ _ _ _ (fun _ _ h => getSysvarRegs_get h)
    (fun s ⟨h1, h2, h4⟩ hr => by
      have := Misc.execGetSysvar_faults_oob_id s (by rw [h2]; exact hIn)
        (by rw [h2, h4]; exact hr.1) (by rw [h1]; exact hr.2)
      exact ⟨this.2, this.1⟩) hCu

end SVM.SBPF
