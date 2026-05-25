import SVM.SBPF.InstructionSpecs.Terminating

namespace SVM.SBPF

open Memory

/-! ## `call_local target` — push a frame, bump r10, jump (lift #3)

The instruction-level Hoare triple for sBPF's internal call. The
precondition owns r6..r10 (so their values are determinate for the
saved-frame) and `callStackIs cs`. The post: r6..r9 unchanged,
r10 bumped by `0x1000` (one V0 stack frame), and the new frame
pushed onto the call stack. PC moves to `target`. -/

theorem call_local_spec
    (target : Nat) (cs : List CallFrame)
    (r6V r7V r8V r9V r10V : Nat) (pc : Nat) :
    cuTripleWithin 1 pc target
      (CodeReq.singleton pc (.call_local target))
      ((.r6 ↦ᵣ r6V) ** (.r7 ↦ᵣ r7V) ** (.r8 ↦ᵣ r8V) **
        (.r9 ↦ᵣ r9V) ** (.r10 ↦ᵣ r10V) ** callStackIs cs)
      ((.r6 ↦ᵣ r6V) ** (.r7 ↦ᵣ r7V) ** (.r8 ↦ᵣ r8V) **
        (.r9 ↦ᵣ r9V) ** (.r10 ↦ᵣ (r10V + 0x1000)) **
        callStackIs (⟨pc + 1, r6V, r7V, r8V, r9V, r10V⟩ :: cs)) := by
  intro R hRfree fetch hcr s hPR hpc hex
  -- Phase 1: destructure 6-atom precondition.
  obtain ⟨hp, hcompat, h_P, h_R, hd_PR, hu_PR, h_P_sat, h_R_sat⟩ := hPR
  obtain ⟨h_r6, h_T1, hd_r6_T1, hu_r6_T1, h_r6_pred, h_T1_sat⟩ := h_P_sat
  obtain ⟨h_r7, h_T2, hd_r7_T2, hu_r7_T2, h_r7_pred, h_T2_sat⟩ := h_T1_sat
  obtain ⟨h_r8, h_T3, hd_r8_T3, hu_r8_T3, h_r8_pred, h_T3_sat⟩ := h_T2_sat
  obtain ⟨h_r9, h_T4, hd_r9_T4, hu_r9_T4, h_r9_pred, h_T4_sat⟩ := h_T3_sat
  obtain ⟨h_r10, h_cs, hd_r10_cs, hu_r10_cs, h_r10_pred, h_cs_pred⟩ := h_T4_sat
  rw [h_r6_pred] at hu_r6_T1 hd_r6_T1
  rw [h_r7_pred] at hu_r7_T2 hd_r7_T2
  rw [h_r8_pred] at hu_r8_T3 hd_r8_T3
  rw [h_r9_pred] at hu_r9_T4 hd_r9_T4
  rw [h_r10_pred] at hu_r10_cs hd_r10_cs
  rw [h_cs_pred] at hu_r10_cs hd_r10_cs
  clear h_r6_pred h_r7_pred h_r8_pred h_r9_pred h_r10_pred h_cs_pred
  clear h_r6 h_r7 h_r8 h_r9 h_r10 h_cs
  have hcr_regs := hcompat.regs
  have hcm_mem := hcompat.mem
  have hcm_cs := hcompat.callStack
  -- Phase 2: lift atoms through hp.
  have h_T4_cs : h_T4.callStack = some cs := by
    rw [← hu_r10_cs, PartialState.union_callStack_of_left_none
          PartialState.singletonReg_callStack]; rfl
  have h_T3_cs : h_T3.callStack = some cs := by
    rw [← hu_r9_T4, PartialState.union_callStack_of_left_none
          PartialState.singletonReg_callStack]; exact h_T4_cs
  have h_T2_cs : h_T2.callStack = some cs := by
    rw [← hu_r8_T3, PartialState.union_callStack_of_left_none
          PartialState.singletonReg_callStack]; exact h_T3_cs
  have h_T1_cs : h_T1.callStack = some cs := by
    rw [← hu_r7_T2, PartialState.union_callStack_of_left_none
          PartialState.singletonReg_callStack]; exact h_T2_cs
  have h_P_cs : h_P.callStack = some cs := by
    rw [← hu_r6_T1, PartialState.union_callStack_of_left_none
          PartialState.singletonReg_callStack]; exact h_T1_cs
  have hp_cs : hp.callStack = some cs := by
    rw [← hu_PR]; exact PartialState.union_callStack_of_left_some h_P_cs
  have hs_cs : s.callStack = cs := hcm_cs cs hp_cs
  have h_P_regs_r6 : h_P.regs .r6 = some r6V := by
    rw [← hu_r6_T1]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_T1_regs_r7 : h_T1.regs .r7 = some r7V := by
    rw [← hu_r7_T2]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_T2_regs_r8 : h_T2.regs .r8 = some r8V := by
    rw [← hu_r8_T3]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_T3_regs_r9 : h_T3.regs .r9 = some r9V := by
    rw [← hu_r9_T4]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_T4_regs_r10 : h_T4.regs .r10 = some r10V := by
    rw [← hu_r10_cs]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_regs_r7 : h_P.regs .r7 = some r7V := by
    rw [← hu_r6_T1, PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r7 ≠ Reg.r6))]
    exact h_T1_regs_r7
  have h_P_regs_r8 : h_P.regs .r8 = some r8V := by
    rw [← hu_r6_T1, PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r8 ≠ Reg.r6)),
        ← hu_r7_T2, PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r8 ≠ Reg.r7))]
    exact h_T2_regs_r8
  have h_P_regs_r9 : h_P.regs .r9 = some r9V := by
    rw [← hu_r6_T1, PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r9 ≠ Reg.r6)),
        ← hu_r7_T2, PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r9 ≠ Reg.r7)),
        ← hu_r8_T3, PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r9 ≠ Reg.r8))]
    exact h_T3_regs_r9
  have h_P_regs_r10 : h_P.regs .r10 = some r10V := by
    rw [← hu_r6_T1, PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r10 ≠ Reg.r6)),
        ← hu_r7_T2, PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r10 ≠ Reg.r7)),
        ← hu_r8_T3, PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r10 ≠ Reg.r8)),
        ← hu_r9_T4, PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r10 ≠ Reg.r9))]
    exact h_T4_regs_r10
  have hp_regs_r6 : hp.regs .r6 = some r6V := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r6
  have hp_regs_r7 : hp.regs .r7 = some r7V := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r7
  have hp_regs_r8 : hp.regs .r8 = some r8V := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r8
  have hp_regs_r9 : hp.regs .r9 = some r9V := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r9
  have hp_regs_r10 : hp.regs .r10 = some r10V := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r10
  have hs_regs_r6 : s.regs.r6 = r6V := hcr_regs .r6 r6V hp_regs_r6
  have hs_regs_r7 : s.regs.r7 = r7V := hcr_regs .r7 r7V hp_regs_r7
  have hs_regs_r8 : s.regs.r8 = r8V := hcr_regs .r8 r8V hp_regs_r8
  have hs_regs_r9 : s.regs.r9 = r9V := hcr_regs .r9 r9V hp_regs_r9
  have hs_regs_r10 : s.regs.r10 = r10V := hcr_regs .r10 r10V hp_regs_r10
  -- Phase 3: executeFn.
  have hfetch : fetch s.pc = some (.call_local target) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hstep_eq : executeFn fetch s 1 = step (.call_local target) s := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch, executeFn_zero]
  have hexec : executeFn fetch s 1 =
      { s with pc := target
               regs := { s.regs with r10 := s.regs.r10 + 0x1000 }
               callStack := ⟨s.pc + 1, s.regs.r6, s.regs.r7,
                             s.regs.r8, s.regs.r9, s.regs.r10⟩ :: s.callStack } := by
    rw [hstep_eq]; rfl
  -- Phase 4: hR non-overlap.
  have hd_PR_regs := hd_PR.regs
  have hd_PR_cs := hd_PR.callStack
  have h_R_no_r6 : h_R.regs .r6 = none := by
    rcases hd_PR_regs .r6 with hl | hr
    · rw [h_P_regs_r6] at hl; nomatch hl
    · exact hr
  have h_R_no_r7 : h_R.regs .r7 = none := by
    rcases hd_PR_regs .r7 with hl | hr
    · rw [h_P_regs_r7] at hl; nomatch hl
    · exact hr
  have h_R_no_r8 : h_R.regs .r8 = none := by
    rcases hd_PR_regs .r8 with hl | hr
    · rw [h_P_regs_r8] at hl; nomatch hl
    · exact hr
  have h_R_no_r9 : h_R.regs .r9 = none := by
    rcases hd_PR_regs .r9 with hl | hr
    · rw [h_P_regs_r9] at hl; nomatch hl
    · exact hr
  have h_R_no_r10 : h_R.regs .r10 = none := by
    rcases hd_PR_regs .r10 with hl | hr
    · rw [h_P_regs_r10] at hl; nomatch hl
    · exact hr
  have h_R_no_pc : h_R.pc = none := hRfree _ h_R_sat
  have h_R_no_cs : h_R.callStack = none := by
    rcases hd_PR_cs with hl | hr
    · rw [h_P_cs] at hl; nomatch hl
    · exact hr
  -- Phase 5: build post heap.
  let newFrame : CallFrame := ⟨pc + 1, r6V, r7V, r8V, r9V, r10V⟩
  let h_r6_new : PartialState := PartialState.singletonReg .r6 r6V
  let h_r7_new : PartialState := PartialState.singletonReg .r7 r7V
  let h_r8_new : PartialState := PartialState.singletonReg .r8 r8V
  let h_r9_new : PartialState := PartialState.singletonReg .r9 r9V
  let h_r10_new : PartialState := PartialState.singletonReg .r10 (r10V + 0x1000)
  let h_cs_new : PartialState :=
    PartialState.singletonCallStack (newFrame :: cs)
  let h_T4_new : PartialState := h_r10_new.union h_cs_new
  let h_T3_new : PartialState := h_r9_new.union h_T4_new
  let h_T2_new : PartialState := h_r8_new.union h_T3_new
  let h_T1_new : PartialState := h_r7_new.union h_T2_new
  let h_P_new : PartialState := h_r6_new.union h_T1_new
  -- Phase 6: inner disjointness (bottom-up).
  have hd_r10_cs_new : h_r10_new.Disjoint h_cs_new :=
    { regs := fun r => Or.inr (PartialState.singletonCallStack_regs r)
      mem  := fun a => Or.inl (PartialState.singletonReg_mem a)
      pc   := Or.inl PartialState.singletonReg_pc
      returnData := Or.inl PartialState.singletonReg_returnData
      callStack := Or.inl PartialState.singletonReg_callStack }
  have hd_r9_T4_new : h_r9_new.Disjoint h_T4_new := by
    refine
      { regs := fun r => ?_
        mem  := fun a => Or.inl (PartialState.singletonReg_mem a)
        pc   := Or.inl PartialState.singletonReg_pc
        returnData := Or.inl PartialState.singletonReg_returnData
        callStack := Or.inl PartialState.singletonReg_callStack }
    by_cases hr : r = .r9
    · right; rw [hr]
      show (h_r10_new.union h_cs_new).regs .r9 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r9 ≠ Reg.r10))]
      exact PartialState.singletonCallStack_regs .r9
    · left; exact PartialState.singletonReg_regs_other hr
  have hd_r8_T3_new : h_r8_new.Disjoint h_T3_new := by
    refine
      { regs := fun r => ?_
        mem  := fun a => Or.inl (PartialState.singletonReg_mem a)
        pc   := Or.inl PartialState.singletonReg_pc
        returnData := Or.inl PartialState.singletonReg_returnData
        callStack := Or.inl PartialState.singletonReg_callStack }
    by_cases hr : r = .r8
    · right; rw [hr]
      show (h_r9_new.union h_T4_new).regs .r8 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r8 ≠ Reg.r9))]
      show (h_r10_new.union h_cs_new).regs .r8 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r8 ≠ Reg.r10))]
      exact PartialState.singletonCallStack_regs .r8
    · left; exact PartialState.singletonReg_regs_other hr
  have hd_r7_T2_new : h_r7_new.Disjoint h_T2_new := by
    refine
      { regs := fun r => ?_
        mem  := fun a => Or.inl (PartialState.singletonReg_mem a)
        pc   := Or.inl PartialState.singletonReg_pc
        returnData := Or.inl PartialState.singletonReg_returnData
        callStack := Or.inl PartialState.singletonReg_callStack }
    by_cases hr : r = .r7
    · right; rw [hr]
      show (h_r8_new.union h_T3_new).regs .r7 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r7 ≠ Reg.r8))]
      show (h_r9_new.union h_T4_new).regs .r7 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r7 ≠ Reg.r9))]
      show (h_r10_new.union h_cs_new).regs .r7 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r7 ≠ Reg.r10))]
      exact PartialState.singletonCallStack_regs .r7
    · left; exact PartialState.singletonReg_regs_other hr
  have hd_r6_T1_new : h_r6_new.Disjoint h_T1_new := by
    refine
      { regs := fun r => ?_
        mem  := fun a => Or.inl (PartialState.singletonReg_mem a)
        pc   := Or.inl PartialState.singletonReg_pc
        returnData := Or.inl PartialState.singletonReg_returnData
        callStack := Or.inl PartialState.singletonReg_callStack }
    by_cases hr : r = .r6
    · right; rw [hr]
      show (h_r7_new.union h_T2_new).regs .r6 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r6 ≠ Reg.r7))]
      show (h_r8_new.union h_T3_new).regs .r6 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r6 ≠ Reg.r8))]
      show (h_r9_new.union h_T4_new).regs .r6 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r6 ≠ Reg.r9))]
      show (h_r10_new.union h_cs_new).regs .r6 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r6 ≠ Reg.r10))]
      exact PartialState.singletonCallStack_regs .r6
    · left; exact PartialState.singletonReg_regs_other hr
  -- Phase 7: per-field projections of h_P_new.
  have h_P_new_regs_r6 : h_P_new.regs .r6 = some r6V :=
    PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_new_regs_r7 : h_P_new.regs .r7 = some r7V := by
    show (h_r6_new.union h_T1_new).regs .r7 = some r7V
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r7 ≠ Reg.r6))]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_new_regs_r8 : h_P_new.regs .r8 = some r8V := by
    show (h_r6_new.union h_T1_new).regs .r8 = some r8V
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r8 ≠ Reg.r6))]
    show (h_r7_new.union h_T2_new).regs .r8 = some r8V
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r8 ≠ Reg.r7))]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_new_regs_r9 : h_P_new.regs .r9 = some r9V := by
    show (h_r6_new.union h_T1_new).regs .r9 = some r9V
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r9 ≠ Reg.r6))]
    show (h_r7_new.union h_T2_new).regs .r9 = some r9V
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r9 ≠ Reg.r7))]
    show (h_r8_new.union h_T3_new).regs .r9 = some r9V
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r9 ≠ Reg.r8))]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_new_regs_r10 : h_P_new.regs .r10 = some (r10V + 0x1000) := by
    show (h_r6_new.union h_T1_new).regs .r10 = some (r10V + 0x1000)
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r10 ≠ Reg.r6))]
    show (h_r7_new.union h_T2_new).regs .r10 = some (r10V + 0x1000)
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r10 ≠ Reg.r7))]
    show (h_r8_new.union h_T3_new).regs .r10 = some (r10V + 0x1000)
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r10 ≠ Reg.r8))]
    show (h_r9_new.union h_T4_new).regs .r10 = some (r10V + 0x1000)
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r10 ≠ Reg.r9))]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_new_regs_other (r : Reg)
      (h6 : r ≠ .r6) (h7 : r ≠ .r7) (h8 : r ≠ .r8) (h9 : r ≠ .r9) (h10 : r ≠ .r10) :
      h_P_new.regs r = none := by
    show (h_r6_new.union h_T1_new).regs r = none
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other h6)]
    show (h_r7_new.union h_T2_new).regs r = none
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other h7)]
    show (h_r8_new.union h_T3_new).regs r = none
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other h8)]
    show (h_r9_new.union h_T4_new).regs r = none
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other h9)]
    show (h_r10_new.union h_cs_new).regs r = none
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other h10)]
    exact PartialState.singletonCallStack_regs r
  have h_P_new_pc : h_P_new.pc = none := by rfl
  have h_P_new_cs : h_P_new.callStack = some (newFrame :: cs) := by
    show (h_r6_new.union h_T1_new).callStack = some (newFrame :: cs)
    rw [PartialState.union_callStack_of_left_none
          PartialState.singletonReg_callStack]
    show (h_r7_new.union h_T2_new).callStack = some (newFrame :: cs)
    rw [PartialState.union_callStack_of_left_none
          PartialState.singletonReg_callStack]
    show (h_r8_new.union h_T3_new).callStack = some (newFrame :: cs)
    rw [PartialState.union_callStack_of_left_none
          PartialState.singletonReg_callStack]
    show (h_r9_new.union h_T4_new).callStack = some (newFrame :: cs)
    rw [PartialState.union_callStack_of_left_none
          PartialState.singletonReg_callStack]
    show (h_r10_new.union h_cs_new).callStack = some (newFrame :: cs)
    rw [PartialState.union_callStack_of_left_none
          PartialState.singletonReg_callStack]
    rfl
  -- Phase 8: outer disjointness.
  have hd_PnewR : h_P_new.Disjoint h_R :=
    { regs := fun r => by
        by_cases h6 : r = .r6
        · right; rw [h6]; exact h_R_no_r6
        by_cases h7 : r = .r7
        · right; rw [h7]; exact h_R_no_r7
        by_cases h8 : r = .r8
        · right; rw [h8]; exact h_R_no_r8
        by_cases h9 : r = .r9
        · right; rw [h9]; exact h_R_no_r9
        by_cases h10 : r = .r10
        · right; rw [h10]; exact h_R_no_r10
        · left; exact h_P_new_regs_other r h6 h7 h8 h9 h10
      mem := fun a => Or.inl (by
        show (h_r6_new.union h_T1_new).mem a = none
        rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
        show (h_r7_new.union h_T2_new).mem a = none
        rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
        show (h_r8_new.union h_T3_new).mem a = none
        rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
        show (h_r9_new.union h_T4_new).mem a = none
        rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
        show (h_r10_new.union h_cs_new).mem a = none
        rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
        exact PartialState.singletonCallStack_mem a)
      pc := Or.inl h_P_new_pc
      returnData := Or.inl (by
        show (h_r6_new.union h_T1_new).returnData = none
        rw [PartialState.union_returnData_of_left_none
              PartialState.singletonReg_returnData]
        show (h_r7_new.union h_T2_new).returnData = none
        rw [PartialState.union_returnData_of_left_none
              PartialState.singletonReg_returnData]
        show (h_r8_new.union h_T3_new).returnData = none
        rw [PartialState.union_returnData_of_left_none
              PartialState.singletonReg_returnData]
        show (h_r9_new.union h_T4_new).returnData = none
        rw [PartialState.union_returnData_of_left_none
              PartialState.singletonReg_returnData]
        show (h_r10_new.union h_cs_new).returnData = none
        rw [PartialState.union_returnData_of_left_none
              PartialState.singletonReg_returnData]
        exact PartialState.singletonCallStack_returnData)
      callStack := Or.inr h_R_no_cs }
  -- Phase 9: assemble.
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_⟩
  · rw [hexec]
  · rw [hexec]; exact hex
  · refine ⟨h_P_new.union h_R, ?_, h_P_new, h_R, hd_PnewR, rfl,
            ⟨h_r6_new, h_T1_new, hd_r6_T1_new, rfl, rfl,
             h_r7_new, h_T2_new, hd_r7_T2_new, rfl, rfl,
             h_r8_new, h_T3_new, hd_r8_T3_new, rfl, rfl,
             h_r9_new, h_T4_new, hd_r9_T4_new, rfl, rfl,
             h_r10_new, h_cs_new, hd_r10_cs_new, rfl, rfl, rfl⟩,
            h_R_sat⟩
    refine { regs := ?_, mem := ?_, pc := ?_, returnData := ?_, callStack := ?_ }
    · intro r v hvr
      by_cases h6 : r = .r6
      · rw [h6] at hvr
        rw [PartialState.union_regs_of_left_some h_P_new_regs_r6] at hvr
        have : v = r6V := (Option.some.inj hvr).symm
        rw [h6, hexec, this]
        show ({ s.regs with r10 := s.regs.r10 + 0x1000 }).get .r6 = r6V
        exact hs_regs_r6
      by_cases h7 : r = .r7
      · rw [h7] at hvr
        rw [PartialState.union_regs_of_left_some h_P_new_regs_r7] at hvr
        have : v = r7V := (Option.some.inj hvr).symm
        rw [h7, hexec, this]; exact hs_regs_r7
      by_cases h8 : r = .r8
      · rw [h8] at hvr
        rw [PartialState.union_regs_of_left_some h_P_new_regs_r8] at hvr
        have : v = r8V := (Option.some.inj hvr).symm
        rw [h8, hexec, this]; exact hs_regs_r8
      by_cases h9 : r = .r9
      · rw [h9] at hvr
        rw [PartialState.union_regs_of_left_some h_P_new_regs_r9] at hvr
        have : v = r9V := (Option.some.inj hvr).symm
        rw [h9, hexec, this]; exact hs_regs_r9
      by_cases h10 : r = .r10
      · rw [h10] at hvr
        rw [PartialState.union_regs_of_left_some h_P_new_regs_r10] at hvr
        have : v = r10V + 0x1000 := (Option.some.inj hvr).symm
        rw [h10, hexec, this]
        show ({ s.regs with r10 := s.regs.r10 + 0x1000 }).get .r10 = r10V + 0x1000
        rw [show RegFile.get { s.regs with r10 := s.regs.r10 + 0x1000 } .r10
              = s.regs.r10 + 0x1000 from rfl, hs_regs_r10]
      · rw [PartialState.union_regs_of_left_none
              (h_P_new_regs_other r h6 h7 h8 h9 h10)] at hvr
        rw [hexec]
        have h_get_eq :
            ({ s.regs with r10 := s.regs.r10 + 0x1000 }).get r = s.regs.get r := by
          cases r <;> first | rfl | (exfalso; first | exact h6 rfl | exact h7 rfl |
                                       exact h8 rfl | exact h9 rfl | exact h10 rfl)
        rw [h_get_eq]
        have h_P_none : h_P.regs r = none := by
          rcases hd_PR_regs r with hl | hr
          · exact hl
          · rw [hr] at hvr; nomatch hvr
        apply hcr_regs r v
        rw [← hu_PR, PartialState.union_regs_of_left_none h_P_none]
        exact hvr
    · intro a v hva
      have h_P_new_mem : h_P_new.mem a = none := by
        show (h_r6_new.union h_T1_new).mem a = none
        rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
        show (h_r7_new.union h_T2_new).mem a = none
        rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
        show (h_r8_new.union h_T3_new).mem a = none
        rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
        show (h_r9_new.union h_T4_new).mem a = none
        rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
        show (h_r10_new.union h_cs_new).mem a = none
        rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
        exact PartialState.singletonCallStack_mem a
      rw [PartialState.union_mem_of_left_none h_P_new_mem] at hva
      rw [hexec]
      show s.mem a = v
      have h_P_none : h_P.mem a = none := by
        rcases hd_PR.mem a with hl | hr
        · exact hl
        · rw [hr] at hva; nomatch hva
      apply hcm_mem a v
      rw [← hu_PR, PartialState.union_mem_of_left_none h_P_none]
      exact hva
    · intro v hvp
      rw [PartialState.union_pc_of_left_none h_P_new_pc] at hvp
      rw [h_R_no_pc] at hvp
      nomatch hvp
    · intro rd hva
      have h_P_new_rd : h_P_new.returnData = none := by
        show (h_r6_new.union h_T1_new).returnData = none
        rw [PartialState.union_returnData_of_left_none
              PartialState.singletonReg_returnData]
        show (h_r7_new.union h_T2_new).returnData = none
        rw [PartialState.union_returnData_of_left_none
              PartialState.singletonReg_returnData]
        show (h_r8_new.union h_T3_new).returnData = none
        rw [PartialState.union_returnData_of_left_none
              PartialState.singletonReg_returnData]
        show (h_r9_new.union h_T4_new).returnData = none
        rw [PartialState.union_returnData_of_left_none
              PartialState.singletonReg_returnData]
        show (h_r10_new.union h_cs_new).returnData = none
        rw [PartialState.union_returnData_of_left_none
              PartialState.singletonReg_returnData]
        exact PartialState.singletonCallStack_returnData
      rw [PartialState.union_returnData_of_left_none h_P_new_rd] at hva
      rw [hexec]
      show s.returnData = rd
      have h_P_rd_none : h_P.returnData = none := by
        rw [← hu_r6_T1, ← hu_r7_T2, ← hu_r8_T3, ← hu_r9_T4, ← hu_r10_cs]; rfl
      apply hcompat.returnData rd
      rw [← hu_PR, PartialState.union_returnData_of_left_none h_P_rd_none]
      exact hva
    · intro csq hva
      rw [PartialState.union_callStack_of_left_some h_P_new_cs] at hva
      have hcs_eq : csq = newFrame :: cs := (Option.some.inj hva).symm
      rw [hexec, hcs_eq]
      show ({ retPc := s.pc + 1, savedR6 := s.regs.r6, savedR7 := s.regs.r7,
              savedR8 := s.regs.r8, savedR9 := s.regs.r9, savedR10 := s.regs.r10
            } : CallFrame) :: s.callStack = newFrame :: cs
      show ({ retPc := s.pc + 1, savedR6 := s.regs.r6, savedR7 := s.regs.r7,
              savedR8 := s.regs.r8, savedR9 := s.regs.r9, savedR10 := s.regs.r10
            } : CallFrame) :: s.callStack
            = ⟨pc + 1, r6V, r7V, r8V, r9V, r10V⟩ :: cs
      rw [hpc, hs_regs_r6, hs_regs_r7, hs_regs_r8, hs_regs_r9, hs_regs_r10, hs_cs]

/-! ## `.exit` (non-empty callStack) — pop frame, restore r6..r10 (lift #3)

The dual of `call_local`: the precondition owns r6..r10 (whatever the
callee left them as) and the call stack with at least one frame.
The post: r6..r10 restored to the saved values from the top frame,
the stack popped, PC moves to the frame's return PC. The empty-stack
case (program termination) is covered by `exit_aborts_spec` above. -/

theorem exit_pops_spec (frame : CallFrame) (cs : List CallFrame)
    (r6Old r7Old r8Old r9Old r10Old : Nat) (pc : Nat) :
    cuTripleWithin 1 pc frame.retPc
      (CodeReq.singleton pc .exit)
      ((.r6 ↦ᵣ r6Old) ** (.r7 ↦ᵣ r7Old) ** (.r8 ↦ᵣ r8Old) **
        (.r9 ↦ᵣ r9Old) ** (.r10 ↦ᵣ r10Old) ** callStackIs (frame :: cs))
      ((.r6 ↦ᵣ frame.savedR6) ** (.r7 ↦ᵣ frame.savedR7) **
        (.r8 ↦ᵣ frame.savedR8) ** (.r9 ↦ᵣ frame.savedR9) **
        (.r10 ↦ᵣ frame.savedR10) ** callStackIs cs) := by
  intro R hRfree fetch hcr s hPR hpc hex
  -- Phase 1: destructure 6-atom precondition.
  obtain ⟨hp, hcompat, h_P, h_R, hd_PR, hu_PR, h_P_sat, h_R_sat⟩ := hPR
  obtain ⟨h_r6, h_T1, hd_r6_T1, hu_r6_T1, h_r6_pred, h_T1_sat⟩ := h_P_sat
  obtain ⟨h_r7, h_T2, hd_r7_T2, hu_r7_T2, h_r7_pred, h_T2_sat⟩ := h_T1_sat
  obtain ⟨h_r8, h_T3, hd_r8_T3, hu_r8_T3, h_r8_pred, h_T3_sat⟩ := h_T2_sat
  obtain ⟨h_r9, h_T4, hd_r9_T4, hu_r9_T4, h_r9_pred, h_T4_sat⟩ := h_T3_sat
  obtain ⟨h_r10, h_cs, hd_r10_cs, hu_r10_cs, h_r10_pred, h_cs_pred⟩ := h_T4_sat
  rw [h_r6_pred] at hu_r6_T1 hd_r6_T1
  rw [h_r7_pred] at hu_r7_T2 hd_r7_T2
  rw [h_r8_pred] at hu_r8_T3 hd_r8_T3
  rw [h_r9_pred] at hu_r9_T4 hd_r9_T4
  rw [h_r10_pred] at hu_r10_cs hd_r10_cs
  rw [h_cs_pred] at hu_r10_cs hd_r10_cs
  clear h_r6_pred h_r7_pred h_r8_pred h_r9_pred h_r10_pred h_cs_pred
  clear h_r6 h_r7 h_r8 h_r9 h_r10 h_cs
  have hcr_regs := hcompat.regs
  have hcm_mem := hcompat.mem
  have hcm_cs := hcompat.callStack
  -- Phase 2: lift atoms through hp.
  have h_T4_cs : h_T4.callStack = some (frame :: cs) := by
    rw [← hu_r10_cs, PartialState.union_callStack_of_left_none
          PartialState.singletonReg_callStack]; rfl
  have h_T3_cs : h_T3.callStack = some (frame :: cs) := by
    rw [← hu_r9_T4, PartialState.union_callStack_of_left_none
          PartialState.singletonReg_callStack]; exact h_T4_cs
  have h_T2_cs : h_T2.callStack = some (frame :: cs) := by
    rw [← hu_r8_T3, PartialState.union_callStack_of_left_none
          PartialState.singletonReg_callStack]; exact h_T3_cs
  have h_T1_cs : h_T1.callStack = some (frame :: cs) := by
    rw [← hu_r7_T2, PartialState.union_callStack_of_left_none
          PartialState.singletonReg_callStack]; exact h_T2_cs
  have h_P_cs : h_P.callStack = some (frame :: cs) := by
    rw [← hu_r6_T1, PartialState.union_callStack_of_left_none
          PartialState.singletonReg_callStack]; exact h_T1_cs
  have hp_cs : hp.callStack = some (frame :: cs) := by
    rw [← hu_PR]; exact PartialState.union_callStack_of_left_some h_P_cs
  have hs_cs : s.callStack = frame :: cs := hcm_cs (frame :: cs) hp_cs
  have h_P_regs_r6 : h_P.regs .r6 = some r6Old := by
    rw [← hu_r6_T1]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_T1_regs_r7 : h_T1.regs .r7 = some r7Old := by
    rw [← hu_r7_T2]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_T2_regs_r8 : h_T2.regs .r8 = some r8Old := by
    rw [← hu_r8_T3]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_T3_regs_r9 : h_T3.regs .r9 = some r9Old := by
    rw [← hu_r9_T4]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_T4_regs_r10 : h_T4.regs .r10 = some r10Old := by
    rw [← hu_r10_cs]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_regs_r7 : h_P.regs .r7 = some r7Old := by
    rw [← hu_r6_T1, PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r7 ≠ Reg.r6))]
    exact h_T1_regs_r7
  have h_P_regs_r8 : h_P.regs .r8 = some r8Old := by
    rw [← hu_r6_T1, PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r8 ≠ Reg.r6)),
        ← hu_r7_T2, PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r8 ≠ Reg.r7))]
    exact h_T2_regs_r8
  have h_P_regs_r9 : h_P.regs .r9 = some r9Old := by
    rw [← hu_r6_T1, PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r9 ≠ Reg.r6)),
        ← hu_r7_T2, PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r9 ≠ Reg.r7)),
        ← hu_r8_T3, PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r9 ≠ Reg.r8))]
    exact h_T3_regs_r9
  have h_P_regs_r10 : h_P.regs .r10 = some r10Old := by
    rw [← hu_r6_T1, PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r10 ≠ Reg.r6)),
        ← hu_r7_T2, PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r10 ≠ Reg.r7)),
        ← hu_r8_T3, PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r10 ≠ Reg.r8)),
        ← hu_r9_T4, PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r10 ≠ Reg.r9))]
    exact h_T4_regs_r10
  -- Phase 3: executeFn.
  have hfetch : fetch s.pc = some .exit := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hstep_eq : executeFn fetch s 1 = step .exit s := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch, executeFn_zero]
  -- Show the non-empty branch of the match runs.
  have hexec : executeFn fetch s 1 =
      { s with pc := frame.retPc
               regs := { s.regs with
                         r6 := frame.savedR6, r7 := frame.savedR7,
                         r8 := frame.savedR8, r9 := frame.savedR9,
                         r10 := frame.savedR10 }
               callStack := cs } := by
    rw [hstep_eq]
    show (match s.callStack with
          | frame :: rest =>
              { s with pc := frame.retPc
                       regs := { s.regs with
                                 r6 := frame.savedR6, r7 := frame.savedR7,
                                 r8 := frame.savedR8, r9 := frame.savedR9,
                                 r10 := frame.savedR10 }
                       callStack := rest }
          | [] => { s with exitCode := some (s.regs.get .r0) })
        = _
    rw [hs_cs]
  -- Phase 4: hR non-overlap.
  have hd_PR_regs := hd_PR.regs
  have hd_PR_cs := hd_PR.callStack
  have h_R_no_r6 : h_R.regs .r6 = none := by
    rcases hd_PR_regs .r6 with hl | hr
    · rw [h_P_regs_r6] at hl; nomatch hl
    · exact hr
  have h_R_no_r7 : h_R.regs .r7 = none := by
    rcases hd_PR_regs .r7 with hl | hr
    · rw [h_P_regs_r7] at hl; nomatch hl
    · exact hr
  have h_R_no_r8 : h_R.regs .r8 = none := by
    rcases hd_PR_regs .r8 with hl | hr
    · rw [h_P_regs_r8] at hl; nomatch hl
    · exact hr
  have h_R_no_r9 : h_R.regs .r9 = none := by
    rcases hd_PR_regs .r9 with hl | hr
    · rw [h_P_regs_r9] at hl; nomatch hl
    · exact hr
  have h_R_no_r10 : h_R.regs .r10 = none := by
    rcases hd_PR_regs .r10 with hl | hr
    · rw [h_P_regs_r10] at hl; nomatch hl
    · exact hr
  have h_R_no_pc : h_R.pc = none := hRfree _ h_R_sat
  have h_R_no_cs : h_R.callStack = none := by
    rcases hd_PR_cs with hl | hr
    · rw [h_P_cs] at hl; nomatch hl
    · exact hr
  -- Phase 5: build post heap (each reg gets the saved value).
  let h_r6_new : PartialState := PartialState.singletonReg .r6 frame.savedR6
  let h_r7_new : PartialState := PartialState.singletonReg .r7 frame.savedR7
  let h_r8_new : PartialState := PartialState.singletonReg .r8 frame.savedR8
  let h_r9_new : PartialState := PartialState.singletonReg .r9 frame.savedR9
  let h_r10_new : PartialState := PartialState.singletonReg .r10 frame.savedR10
  let h_cs_new : PartialState := PartialState.singletonCallStack cs
  let h_T4_new : PartialState := h_r10_new.union h_cs_new
  let h_T3_new : PartialState := h_r9_new.union h_T4_new
  let h_T2_new : PartialState := h_r8_new.union h_T3_new
  let h_T1_new : PartialState := h_r7_new.union h_T2_new
  let h_P_new : PartialState := h_r6_new.union h_T1_new
  -- Phase 6: inner disjointness.
  have hd_r10_cs_new : h_r10_new.Disjoint h_cs_new :=
    { regs := fun r => Or.inr (PartialState.singletonCallStack_regs r)
      mem  := fun a => Or.inl (PartialState.singletonReg_mem a)
      pc   := Or.inl PartialState.singletonReg_pc
      returnData := Or.inl PartialState.singletonReg_returnData
      callStack := Or.inl PartialState.singletonReg_callStack }
  have hd_r9_T4_new : h_r9_new.Disjoint h_T4_new := by
    refine
      { regs := fun r => ?_
        mem  := fun a => Or.inl (PartialState.singletonReg_mem a)
        pc   := Or.inl PartialState.singletonReg_pc
        returnData := Or.inl PartialState.singletonReg_returnData
        callStack := Or.inl PartialState.singletonReg_callStack }
    by_cases hr : r = .r9
    · right; rw [hr]
      show (h_r10_new.union h_cs_new).regs .r9 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r9 ≠ Reg.r10))]
      exact PartialState.singletonCallStack_regs .r9
    · left; exact PartialState.singletonReg_regs_other hr
  have hd_r8_T3_new : h_r8_new.Disjoint h_T3_new := by
    refine
      { regs := fun r => ?_
        mem  := fun a => Or.inl (PartialState.singletonReg_mem a)
        pc   := Or.inl PartialState.singletonReg_pc
        returnData := Or.inl PartialState.singletonReg_returnData
        callStack := Or.inl PartialState.singletonReg_callStack }
    by_cases hr : r = .r8
    · right; rw [hr]
      show (h_r9_new.union h_T4_new).regs .r8 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r8 ≠ Reg.r9))]
      show (h_r10_new.union h_cs_new).regs .r8 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r8 ≠ Reg.r10))]
      exact PartialState.singletonCallStack_regs .r8
    · left; exact PartialState.singletonReg_regs_other hr
  have hd_r7_T2_new : h_r7_new.Disjoint h_T2_new := by
    refine
      { regs := fun r => ?_
        mem  := fun a => Or.inl (PartialState.singletonReg_mem a)
        pc   := Or.inl PartialState.singletonReg_pc
        returnData := Or.inl PartialState.singletonReg_returnData
        callStack := Or.inl PartialState.singletonReg_callStack }
    by_cases hr : r = .r7
    · right; rw [hr]
      show (h_r8_new.union h_T3_new).regs .r7 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r7 ≠ Reg.r8))]
      show (h_r9_new.union h_T4_new).regs .r7 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r7 ≠ Reg.r9))]
      show (h_r10_new.union h_cs_new).regs .r7 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r7 ≠ Reg.r10))]
      exact PartialState.singletonCallStack_regs .r7
    · left; exact PartialState.singletonReg_regs_other hr
  have hd_r6_T1_new : h_r6_new.Disjoint h_T1_new := by
    refine
      { regs := fun r => ?_
        mem  := fun a => Or.inl (PartialState.singletonReg_mem a)
        pc   := Or.inl PartialState.singletonReg_pc
        returnData := Or.inl PartialState.singletonReg_returnData
        callStack := Or.inl PartialState.singletonReg_callStack }
    by_cases hr : r = .r6
    · right; rw [hr]
      show (h_r7_new.union h_T2_new).regs .r6 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r6 ≠ Reg.r7))]
      show (h_r8_new.union h_T3_new).regs .r6 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r6 ≠ Reg.r8))]
      show (h_r9_new.union h_T4_new).regs .r6 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r6 ≠ Reg.r9))]
      show (h_r10_new.union h_cs_new).regs .r6 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r6 ≠ Reg.r10))]
      exact PartialState.singletonCallStack_regs .r6
    · left; exact PartialState.singletonReg_regs_other hr
  -- Phase 7: per-field projections of h_P_new.
  have h_P_new_regs_r6 : h_P_new.regs .r6 = some frame.savedR6 :=
    PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_new_regs_r7 : h_P_new.regs .r7 = some frame.savedR7 := by
    show (h_r6_new.union h_T1_new).regs .r7 = some frame.savedR7
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r7 ≠ Reg.r6))]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_new_regs_r8 : h_P_new.regs .r8 = some frame.savedR8 := by
    show (h_r6_new.union h_T1_new).regs .r8 = some frame.savedR8
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r8 ≠ Reg.r6))]
    show (h_r7_new.union h_T2_new).regs .r8 = some frame.savedR8
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r8 ≠ Reg.r7))]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_new_regs_r9 : h_P_new.regs .r9 = some frame.savedR9 := by
    show (h_r6_new.union h_T1_new).regs .r9 = some frame.savedR9
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r9 ≠ Reg.r6))]
    show (h_r7_new.union h_T2_new).regs .r9 = some frame.savedR9
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r9 ≠ Reg.r7))]
    show (h_r8_new.union h_T3_new).regs .r9 = some frame.savedR9
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r9 ≠ Reg.r8))]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_new_regs_r10 : h_P_new.regs .r10 = some frame.savedR10 := by
    show (h_r6_new.union h_T1_new).regs .r10 = some frame.savedR10
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r10 ≠ Reg.r6))]
    show (h_r7_new.union h_T2_new).regs .r10 = some frame.savedR10
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r10 ≠ Reg.r7))]
    show (h_r8_new.union h_T3_new).regs .r10 = some frame.savedR10
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r10 ≠ Reg.r8))]
    show (h_r9_new.union h_T4_new).regs .r10 = some frame.savedR10
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r10 ≠ Reg.r9))]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_new_regs_other (r : Reg)
      (h6 : r ≠ .r6) (h7 : r ≠ .r7) (h8 : r ≠ .r8) (h9 : r ≠ .r9) (h10 : r ≠ .r10) :
      h_P_new.regs r = none := by
    show (h_r6_new.union h_T1_new).regs r = none
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other h6)]
    show (h_r7_new.union h_T2_new).regs r = none
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other h7)]
    show (h_r8_new.union h_T3_new).regs r = none
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other h8)]
    show (h_r9_new.union h_T4_new).regs r = none
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other h9)]
    show (h_r10_new.union h_cs_new).regs r = none
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other h10)]
    exact PartialState.singletonCallStack_regs r
  have h_P_new_pc : h_P_new.pc = none := by rfl
  have h_P_new_cs : h_P_new.callStack = some cs := by
    show (h_r6_new.union h_T1_new).callStack = some cs
    rw [PartialState.union_callStack_of_left_none
          PartialState.singletonReg_callStack]
    show (h_r7_new.union h_T2_new).callStack = some cs
    rw [PartialState.union_callStack_of_left_none
          PartialState.singletonReg_callStack]
    show (h_r8_new.union h_T3_new).callStack = some cs
    rw [PartialState.union_callStack_of_left_none
          PartialState.singletonReg_callStack]
    show (h_r9_new.union h_T4_new).callStack = some cs
    rw [PartialState.union_callStack_of_left_none
          PartialState.singletonReg_callStack]
    show (h_r10_new.union h_cs_new).callStack = some cs
    rw [PartialState.union_callStack_of_left_none
          PartialState.singletonReg_callStack]
    rfl
  -- Phase 8: outer disjointness.
  have hd_PnewR : h_P_new.Disjoint h_R :=
    { regs := fun r => by
        by_cases h6 : r = .r6
        · right; rw [h6]; exact h_R_no_r6
        by_cases h7 : r = .r7
        · right; rw [h7]; exact h_R_no_r7
        by_cases h8 : r = .r8
        · right; rw [h8]; exact h_R_no_r8
        by_cases h9 : r = .r9
        · right; rw [h9]; exact h_R_no_r9
        by_cases h10 : r = .r10
        · right; rw [h10]; exact h_R_no_r10
        · left; exact h_P_new_regs_other r h6 h7 h8 h9 h10
      mem := fun a => Or.inl (by
        show (h_r6_new.union h_T1_new).mem a = none
        rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
        show (h_r7_new.union h_T2_new).mem a = none
        rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
        show (h_r8_new.union h_T3_new).mem a = none
        rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
        show (h_r9_new.union h_T4_new).mem a = none
        rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
        show (h_r10_new.union h_cs_new).mem a = none
        rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
        exact PartialState.singletonCallStack_mem a)
      pc := Or.inl h_P_new_pc
      returnData := Or.inl (by
        show (h_r6_new.union h_T1_new).returnData = none
        rw [PartialState.union_returnData_of_left_none
              PartialState.singletonReg_returnData]
        show (h_r7_new.union h_T2_new).returnData = none
        rw [PartialState.union_returnData_of_left_none
              PartialState.singletonReg_returnData]
        show (h_r8_new.union h_T3_new).returnData = none
        rw [PartialState.union_returnData_of_left_none
              PartialState.singletonReg_returnData]
        show (h_r9_new.union h_T4_new).returnData = none
        rw [PartialState.union_returnData_of_left_none
              PartialState.singletonReg_returnData]
        show (h_r10_new.union h_cs_new).returnData = none
        rw [PartialState.union_returnData_of_left_none
              PartialState.singletonReg_returnData]
        exact PartialState.singletonCallStack_returnData)
      callStack := Or.inr h_R_no_cs }
  -- Phase 9: assemble.
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_⟩
  · rw [hexec]
  · rw [hexec]; exact hex
  · refine ⟨h_P_new.union h_R, ?_, h_P_new, h_R, hd_PnewR, rfl,
            ⟨h_r6_new, h_T1_new, hd_r6_T1_new, rfl, rfl,
             h_r7_new, h_T2_new, hd_r7_T2_new, rfl, rfl,
             h_r8_new, h_T3_new, hd_r8_T3_new, rfl, rfl,
             h_r9_new, h_T4_new, hd_r9_T4_new, rfl, rfl,
             h_r10_new, h_cs_new, hd_r10_cs_new, rfl, rfl, rfl⟩,
            h_R_sat⟩
    refine { regs := ?_, mem := ?_, pc := ?_, returnData := ?_, callStack := ?_ }
    · intro r v hvr
      by_cases h6 : r = .r6
      · rw [h6] at hvr
        rw [PartialState.union_regs_of_left_some h_P_new_regs_r6] at hvr
        have : v = frame.savedR6 := (Option.some.inj hvr).symm
        rw [h6, hexec, this]; rfl
      by_cases h7 : r = .r7
      · rw [h7] at hvr
        rw [PartialState.union_regs_of_left_some h_P_new_regs_r7] at hvr
        have : v = frame.savedR7 := (Option.some.inj hvr).symm
        rw [h7, hexec, this]; rfl
      by_cases h8 : r = .r8
      · rw [h8] at hvr
        rw [PartialState.union_regs_of_left_some h_P_new_regs_r8] at hvr
        have : v = frame.savedR8 := (Option.some.inj hvr).symm
        rw [h8, hexec, this]; rfl
      by_cases h9 : r = .r9
      · rw [h9] at hvr
        rw [PartialState.union_regs_of_left_some h_P_new_regs_r9] at hvr
        have : v = frame.savedR9 := (Option.some.inj hvr).symm
        rw [h9, hexec, this]; rfl
      by_cases h10 : r = .r10
      · rw [h10] at hvr
        rw [PartialState.union_regs_of_left_some h_P_new_regs_r10] at hvr
        have : v = frame.savedR10 := (Option.some.inj hvr).symm
        rw [h10, hexec, this]; rfl
      · rw [PartialState.union_regs_of_left_none
              (h_P_new_regs_other r h6 h7 h8 h9 h10)] at hvr
        rw [hexec]
        have h_get_eq :
            ({ s.regs with r6 := frame.savedR6, r7 := frame.savedR7,
                           r8 := frame.savedR8, r9 := frame.savedR9,
                           r10 := frame.savedR10 }).get r = s.regs.get r := by
          cases r <;> first | rfl | (exfalso; first | exact h6 rfl | exact h7 rfl |
                                       exact h8 rfl | exact h9 rfl | exact h10 rfl)
        rw [h_get_eq]
        have h_P_none : h_P.regs r = none := by
          rcases hd_PR_regs r with hl | hr
          · exact hl
          · rw [hr] at hvr; nomatch hvr
        apply hcr_regs r v
        rw [← hu_PR, PartialState.union_regs_of_left_none h_P_none]
        exact hvr
    · intro a v hva
      have h_P_new_mem : h_P_new.mem a = none := by
        show (h_r6_new.union h_T1_new).mem a = none
        rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
        show (h_r7_new.union h_T2_new).mem a = none
        rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
        show (h_r8_new.union h_T3_new).mem a = none
        rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
        show (h_r9_new.union h_T4_new).mem a = none
        rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
        show (h_r10_new.union h_cs_new).mem a = none
        rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
        exact PartialState.singletonCallStack_mem a
      rw [PartialState.union_mem_of_left_none h_P_new_mem] at hva
      rw [hexec]
      show s.mem a = v
      have h_P_none : h_P.mem a = none := by
        rcases hd_PR.mem a with hl | hr
        · exact hl
        · rw [hr] at hva; nomatch hva
      apply hcm_mem a v
      rw [← hu_PR, PartialState.union_mem_of_left_none h_P_none]
      exact hva
    · intro v hvp
      rw [PartialState.union_pc_of_left_none h_P_new_pc] at hvp
      rw [h_R_no_pc] at hvp
      nomatch hvp
    · intro rd hva
      have h_P_new_rd : h_P_new.returnData = none := by
        show (h_r6_new.union h_T1_new).returnData = none
        rw [PartialState.union_returnData_of_left_none
              PartialState.singletonReg_returnData]
        show (h_r7_new.union h_T2_new).returnData = none
        rw [PartialState.union_returnData_of_left_none
              PartialState.singletonReg_returnData]
        show (h_r8_new.union h_T3_new).returnData = none
        rw [PartialState.union_returnData_of_left_none
              PartialState.singletonReg_returnData]
        show (h_r9_new.union h_T4_new).returnData = none
        rw [PartialState.union_returnData_of_left_none
              PartialState.singletonReg_returnData]
        show (h_r10_new.union h_cs_new).returnData = none
        rw [PartialState.union_returnData_of_left_none
              PartialState.singletonReg_returnData]
        exact PartialState.singletonCallStack_returnData
      rw [PartialState.union_returnData_of_left_none h_P_new_rd] at hva
      rw [hexec]
      show s.returnData = rd
      have h_P_rd_none : h_P.returnData = none := by
        rw [← hu_r6_T1, ← hu_r7_T2, ← hu_r8_T3, ← hu_r9_T4, ← hu_r10_cs]; rfl
      apply hcompat.returnData rd
      rw [← hu_PR, PartialState.union_returnData_of_left_none h_P_rd_none]
      exact hva
    · intro csq hva
      rw [PartialState.union_callStack_of_left_some h_P_new_cs] at hva
      have hcs_eq : csq = cs := (Option.some.inj hva).symm
      rw [hexec, hcs_eq]


end SVM.SBPF
