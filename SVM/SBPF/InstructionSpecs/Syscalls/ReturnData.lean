import SVM.SBPF.InstructionSpecs.Syscalls.Log

namespace SVM.SBPF

open Memory

/-! ## Syscall: `sol_set_return_data` (refined via `returnDataIs`)

`sol_set_return_data(ptr, len)`: replace `State.returnData` with the
slice `[r1..r1+r2)`, set `r0 := 0`. With lift #2's `returnData` SL
atom, the spec owns the input memory range and the returnData buffer:
the post-state's returnData is exactly the input bytes. -/

theorem call_sol_set_return_data_spec
    (r0Old r1V r2V : Nat) (rdOld bsIn : ByteArray) (pc : Nat) (nCu : Nat)
    (hSize : bsIn.size = r2V)
    (hLen : r2V ≤ MAX_RETURN_DATA)
    (hCu : ∀ s : State,
        (step (.call .sol_set_return_data) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_set_return_data))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) **
        (r1V ↦Bytes bsIn) ** returnDataIs rdOld)
      ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) **
        (r1V ↦Bytes bsIn) ** returnDataIs bsIn) := by
  intro R hRfree fetch hcr s hPR hpc hex hbud
  -- ==== Phase 1: destructure the 5-atom layered precondition. ====
  obtain ⟨hp, hcompat, h_P, h_R, hd_PR, hu_PR, h_P_sat, h_R_sat⟩ := hPR
  obtain ⟨h_r0, h_T1, hd_r0_T1, hu_r0_T1, h_r0_pred, h_T1_sat⟩ := h_P_sat
  obtain ⟨h_r1, h_T2, hd_r1_T2, hu_r1_T2, h_r1_pred, h_T2_sat⟩ := h_T1_sat
  obtain ⟨h_r2, h_T3, hd_r2_T3, hu_r2_T3, h_r2_pred, h_T3_sat⟩ := h_T2_sat
  obtain ⟨h_b, h_rd, hd_b_rd, hu_b_rd, h_b_pred, h_rd_pred⟩ := h_T3_sat
  rw [h_r0_pred] at hu_r0_T1 hd_r0_T1
  rw [h_r1_pred] at hu_r1_T2 hd_r1_T2
  rw [h_r2_pred] at hu_r2_T3 hd_r2_T3
  rw [h_b_pred] at hu_b_rd hd_b_rd
  rw [h_rd_pred] at hu_b_rd hd_b_rd
  clear h_r0_pred h_r1_pred h_r2_pred h_b_pred h_rd_pred
  clear h_r0 h_r1 h_r2 h_b h_rd
  have hcr_regs := hcompat.regs
  have hcm_mem := hcompat.mem
  have hcm_rd := hcompat.returnData
  -- ==== Phase 2: lift atom projections through hp. ====
  -- returnData: singletonReturnData rdOld is in h_b_rd's right half.
  have h_T3_rd : h_T3.returnData = some rdOld := by
    rw [← hu_b_rd]
    rw [PartialState.union_returnData_of_left_none
          PartialState.singletonMemBytes_returnData]
    rfl
  have h_T2_rd : h_T2.returnData = some rdOld := by
    rw [← hu_r2_T3,
        PartialState.union_returnData_of_left_none
          PartialState.singletonReg_returnData]
    exact h_T3_rd
  have h_T1_rd : h_T1.returnData = some rdOld := by
    rw [← hu_r1_T2,
        PartialState.union_returnData_of_left_none
          PartialState.singletonReg_returnData]
    exact h_T2_rd
  have h_P_rd : h_P.returnData = some rdOld := by
    rw [← hu_r0_T1,
        PartialState.union_returnData_of_left_none
          PartialState.singletonReg_returnData]
    exact h_T1_rd
  have hp_rd : hp.returnData = some rdOld := by
    rw [← hu_PR]; exact PartialState.union_returnData_of_left_some h_P_rd
  have hs_rd : s.returnData = rdOld := hcm_rd rdOld hp_rd
  -- regs r0, r1, r2.
  have h_P_regs_r0 : h_P.regs .r0 = some r0Old := by
    rw [← hu_r0_T1]
    exact PartialState.union_regs_of_left_some
      PartialState.singletonReg_regs_self
  have h_T1_regs_r1 : h_T1.regs .r1 = some r1V := by
    rw [← hu_r1_T2]
    exact PartialState.union_regs_of_left_some
      PartialState.singletonReg_regs_self
  have h_T2_regs_r2 : h_T2.regs .r2 = some r2V := by
    rw [← hu_r2_T3]
    exact PartialState.union_regs_of_left_some
      PartialState.singletonReg_regs_self
  have h_P_regs_r1 : h_P.regs .r1 = some r1V := by
    rw [← hu_r0_T1,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r1 ≠ Reg.r0))]
    exact h_T1_regs_r1
  have h_P_regs_r2 : h_P.regs .r2 = some r2V := by
    rw [← hu_r0_T1,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r2 ≠ Reg.r0)),
        ← hu_r1_T2,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r2 ≠ Reg.r1))]
    exact h_T2_regs_r2
  have hp_regs_r0 : hp.regs .r0 = some r0Old := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r0
  have hp_regs_r1 : hp.regs .r1 = some r1V := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r1
  have hp_regs_r2 : hp.regs .r2 = some r2V := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r2
  have hs_regs_r0 : s.regs.get .r0 = r0Old := hcr_regs .r0 r0Old hp_regs_r0
  have hs_regs_r1 : s.regs.get .r1 = r1V := hcr_regs .r1 r1V hp_regs_r1
  have hs_regs_r2 : s.regs.get .r2 = r2V := hcr_regs .r2 r2V hp_regs_r2
  have hs_r1_field : s.regs.r1 = r1V := hs_regs_r1
  have hs_r2_field : s.regs.r2 = r2V := hs_regs_r2
  -- Memory bytes at r1V match bsIn.
  have h_T3_mem (i : Nat) (hi : i < r2V) :
      h_T3.mem (r1V + i) = some (bsIn.get! i).toNat := by
    rw [← hu_b_rd]
    apply PartialState.union_mem_of_left_some
    have h_lt : i < bsIn.size := by rw [hSize]; exact hi
    exact PartialState.singletonMemBytes_mem_at r1V bsIn i h_lt
  have h_P_mem (i : Nat) (hi : i < r2V) :
      h_P.mem (r1V + i) = some (bsIn.get! i).toNat := by
    rw [← hu_r0_T1,
        PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (r1V + i)),
        ← hu_r1_T2,
        PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (r1V + i)),
        ← hu_r2_T3,
        PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (r1V + i))]
    exact h_T3_mem i hi
  have hp_mem (i : Nat) (hi : i < r2V) :
      hp.mem (r1V + i) = some (bsIn.get! i).toNat := by
    rw [← hu_PR]; exact PartialState.union_mem_of_left_some (h_P_mem i hi)
  have hs_mem (i : Nat) (hi : i < r2V) :
      s.mem (r1V + i) = (bsIn.get! i).toNat :=
    hcm_mem (r1V + i) _ (hp_mem i hi)
  -- ==== Phase 3: readBytes s.mem r1V r2V = bsIn. ====
  have h_readBytes : readBytes s.mem r1V r2V = bsIn := by
    apply readBytes_eq_of_match s.mem r1V r2V bsIn hSize
    intro i hi
    rw [hs_mem i hi]
    -- (bsIn.get! i).toNat % 256 = (bsIn.get! i).toNat
    -- since the UInt8 value is < 256.
    exact Nat.mod_eq_of_lt (bsIn.get! i).toNat_lt
  -- ==== Phase 4: executeFn produces the expected post state. ====
  have hfetch : fetch s.pc = some (.call .sol_set_return_data) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hexec : executeFn fetch s 1 =
      chargeCu { s with regs := s.regs.set .r0 0
                        returnData := bsIn
                        returnDataProgId := s.progIdBytes
                        pc := s.pc + 1
                        cuConsumed := s.cuConsumed
                          + syscallCu .sol_set_return_data s } := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch, executeFn_zero]
    show chargeCu ({ ReturnData.execSet s with
            pc := s.pc + 1
            cuConsumed := (ReturnData.execSet s).cuConsumed
                          + syscallCu .sol_set_return_data s }) = _
    -- len = r2V ≤ MAX_RETURN_DATA, so execSet takes the success branch.
    have hnotbig : ¬ (s.regs.r2 > MAX_RETURN_DATA) := by rw [hs_r2_field]; omega
    simp only [ReturnData.execSet, if_neg hnotbig]
    -- Both sides have the same record fields; the readBytes call needs
    -- s.regs.r1 = r1V, s.regs.r2 = r2V, and h_readBytes.
    rw [hs_r1_field, hs_r2_field, h_readBytes]
  -- ==== Phase 5: facts about hR. ====
  have hd_PR_regs := hd_PR.regs
  have hd_PR_mem := hd_PR.mem
  have hd_PR_rd := hd_PR.returnData
  have h_R_no_r0 : h_R.regs .r0 = none := by
    rcases hd_PR_regs .r0 with hl | hr
    · rw [h_P_regs_r0] at hl; nomatch hl
    · exact hr
  have h_R_no_r1 : h_R.regs .r1 = none := by
    rcases hd_PR_regs .r1 with hl | hr
    · rw [h_P_regs_r1] at hl; nomatch hl
    · exact hr
  have h_R_no_r2 : h_R.regs .r2 = none := by
    rcases hd_PR_regs .r2 with hl | hr
    · rw [h_P_regs_r2] at hl; nomatch hl
    · exact hr
  have h_R_no_pc : h_R.pc = none := hRfree _ h_R_sat
  have h_R_no_rd : h_R.returnData = none := by
    rcases hd_PR_rd with hl | hr
    · rw [h_P_rd] at hl; nomatch hl
    · exact hr
  have h_R_no_mem_in (i : Nat) (hi : i < r2V) :
      h_R.mem (r1V + i) = none := by
    rcases hd_PR_mem (r1V + i) with hl | hr
    · rw [h_P_mem i hi] at hl; nomatch hl
    · exact hr
  -- ==== Phase 6: build the post heap. ====
  -- New atoms (post-state).
  let h_r0_new : PartialState := PartialState.singletonReg .r0 0
  let h_r1_new : PartialState := PartialState.singletonReg .r1 r1V
  let h_r2_new : PartialState := PartialState.singletonReg .r2 r2V
  let h_b_new : PartialState := PartialState.singletonMemBytes r1V bsIn
  let h_rd_new : PartialState := PartialState.singletonReturnData bsIn
  let h_T3_new : PartialState := h_b_new.union h_rd_new
  let h_T2_new : PartialState := h_r2_new.union h_T3_new
  let h_T1_new : PartialState := h_r1_new.union h_T2_new
  let h_P_new : PartialState := h_r0_new.union h_T1_new
  -- Inner disjointness facts.
  have hd_b_rd_new : h_b_new.Disjoint h_rd_new :=
    { regs := fun r => Or.inl (PartialState.singletonMemBytes_regs r)
      mem  := fun a => Or.inr (PartialState.singletonReturnData_mem a)
      pc   := Or.inl PartialState.singletonMemBytes_pc
      returnData := Or.inl PartialState.singletonMemBytes_returnData
      callStack := Or.inl PartialState.singletonMemBytes_callStack }
  have hd_r2_T3_new : h_r2_new.Disjoint h_T3_new := by
    refine
      { regs := fun r => ?_
        mem  := fun a => Or.inl (PartialState.singletonReg_mem a)
        pc   := Or.inl PartialState.singletonReg_pc
        returnData := Or.inl PartialState.singletonReg_returnData
        callStack := Or.inl PartialState.singletonReg_callStack }
    by_cases hr : r = .r2
    · right; rw [hr]
      show ((PartialState.singletonMemBytes r1V bsIn).union
              (PartialState.singletonReturnData bsIn)).regs .r2 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonMemBytes_regs .r2)]
      exact PartialState.singletonReturnData_regs .r2
    · left; exact PartialState.singletonReg_regs_other hr
  have hd_r1_T2_new : h_r1_new.Disjoint h_T2_new := by
    refine
      { regs := fun r => ?_
        mem  := fun a => Or.inl (PartialState.singletonReg_mem a)
        pc   := Or.inl PartialState.singletonReg_pc
        returnData := Or.inl PartialState.singletonReg_returnData
        callStack := Or.inl PartialState.singletonReg_callStack }
    by_cases hr : r = .r1
    · right; rw [hr]
      show (h_r2_new.union h_T3_new).regs .r1 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r1 ≠ Reg.r2))]
      show ((PartialState.singletonMemBytes r1V bsIn).union
              (PartialState.singletonReturnData bsIn)).regs .r1 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonMemBytes_regs .r1)]
      exact PartialState.singletonReturnData_regs .r1
    · left; exact PartialState.singletonReg_regs_other hr
  have hd_r0_T1_new : h_r0_new.Disjoint h_T1_new := by
    refine
      { regs := fun r => ?_
        mem  := fun a => Or.inl (PartialState.singletonReg_mem a)
        pc   := Or.inl PartialState.singletonReg_pc
        returnData := Or.inl PartialState.singletonReg_returnData
        callStack := Or.inl PartialState.singletonReg_callStack }
    by_cases hr : r = .r0
    · right; rw [hr]
      show (h_r1_new.union h_T2_new).regs .r0 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r0 ≠ Reg.r1))]
      show (h_r2_new.union h_T3_new).regs .r0 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r0 ≠ Reg.r2))]
      show ((PartialState.singletonMemBytes r1V bsIn).union
              (PartialState.singletonReturnData bsIn)).regs .r0 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonMemBytes_regs .r0)]
      exact PartialState.singletonReturnData_regs .r0
    · left; exact PartialState.singletonReg_regs_other hr
  -- Per-field projections of h_P_new.
  have h_P_new_regs_r0 : h_P_new.regs .r0 = some 0 := by
    show (h_r0_new.union h_T1_new).regs .r0 = some 0
    exact PartialState.union_regs_of_left_some
      PartialState.singletonReg_regs_self
  have h_P_new_regs_r1 : h_P_new.regs .r1 = some r1V := by
    show (h_r0_new.union h_T1_new).regs .r1 = some r1V
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r1 ≠ Reg.r0))]
    show (h_r1_new.union h_T2_new).regs .r1 = some r1V
    exact PartialState.union_regs_of_left_some
      PartialState.singletonReg_regs_self
  have h_P_new_regs_r2 : h_P_new.regs .r2 = some r2V := by
    show (h_r0_new.union h_T1_new).regs .r2 = some r2V
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r2 ≠ Reg.r0))]
    show (h_r1_new.union h_T2_new).regs .r2 = some r2V
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r2 ≠ Reg.r1))]
    show (h_r2_new.union h_T3_new).regs .r2 = some r2V
    exact PartialState.union_regs_of_left_some
      PartialState.singletonReg_regs_self
  have h_P_new_regs_other (r : Reg)
      (h0 : r ≠ .r0) (h1 : r ≠ .r1) (h2 : r ≠ .r2) :
      h_P_new.regs r = none := by
    show (h_r0_new.union h_T1_new).regs r = none
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other h0)]
    show (h_r1_new.union h_T2_new).regs r = none
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other h1)]
    show (h_r2_new.union h_T3_new).regs r = none
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other h2)]
    show ((PartialState.singletonMemBytes r1V bsIn).union
            (PartialState.singletonReturnData bsIn)).regs r = none
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonMemBytes_regs r)]
    exact PartialState.singletonReturnData_regs r
  have h_P_new_mem_in (i : Nat) (hi : i < r2V) :
      h_P_new.mem (r1V + i) = some (bsIn.get! i).toNat := by
    show (h_r0_new.union h_T1_new).mem (r1V + i) = some (bsIn.get! i).toNat
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (r1V + i))]
    show (h_r1_new.union h_T2_new).mem (r1V + i) = some (bsIn.get! i).toNat
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (r1V + i))]
    show (h_r2_new.union h_T3_new).mem (r1V + i) = some (bsIn.get! i).toNat
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (r1V + i))]
    show ((PartialState.singletonMemBytes r1V bsIn).union
            (PartialState.singletonReturnData bsIn)).mem (r1V + i)
            = some (bsIn.get! i).toNat
    apply PartialState.union_mem_of_left_some
    have h_lt : i < bsIn.size := by rw [hSize]; exact hi
    exact PartialState.singletonMemBytes_mem_at r1V bsIn i h_lt
  have h_P_new_mem_out (a : Nat) (h : a < r1V ∨ a ≥ r1V + r2V) :
      h_P_new.mem a = none := by
    show (h_r0_new.union h_T1_new).mem a = none
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem a)]
    show (h_r1_new.union h_T2_new).mem a = none
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem a)]
    show (h_r2_new.union h_T3_new).mem a = none
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem a)]
    show ((PartialState.singletonMemBytes r1V bsIn).union
            (PartialState.singletonReturnData bsIn)).mem a = none
    have hbs : a < r1V ∨ a ≥ r1V + bsIn.size := by rw [hSize]; exact h
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonMemBytes_mem_outside r1V bsIn a hbs)]
    exact PartialState.singletonReturnData_mem a
  have h_P_new_pc : h_P_new.pc = none := by
    show (h_r0_new.union h_T1_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    show (h_r1_new.union h_T2_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    show (h_r2_new.union h_T3_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    show ((PartialState.singletonMemBytes r1V bsIn).union
            (PartialState.singletonReturnData bsIn)).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonMemBytes_pc]
    exact PartialState.singletonReturnData_pc
  have h_P_new_rd : h_P_new.returnData = some bsIn := by
    show (h_r0_new.union h_T1_new).returnData = some bsIn
    rw [PartialState.union_returnData_of_left_none
          PartialState.singletonReg_returnData]
    show (h_r1_new.union h_T2_new).returnData = some bsIn
    rw [PartialState.union_returnData_of_left_none
          PartialState.singletonReg_returnData]
    show (h_r2_new.union h_T3_new).returnData = some bsIn
    rw [PartialState.union_returnData_of_left_none
          PartialState.singletonReg_returnData]
    show ((PartialState.singletonMemBytes r1V bsIn).union
            (PartialState.singletonReturnData bsIn)).returnData = some bsIn
    rw [PartialState.union_returnData_of_left_none
          PartialState.singletonMemBytes_returnData]
    rfl
  -- ==== Phase 7: outer disjointness h_P_new ⫫ h_R. ====
  have h_P_new_cs : h_P_new.callStack = none := by
    show ((PartialState.singletonReg .r0 0).union
            ((PartialState.singletonReg .r1 r1V).union
              ((PartialState.singletonReg .r2 r2V).union
                ((PartialState.singletonMemBytes r1V bsIn).union
                  (PartialState.singletonReturnData bsIn))))).callStack = none
    simp
  have h_P_cs_pre : h_P.callStack = none := by
    rw [← hu_r0_T1, ← hu_r1_T2, ← hu_r2_T3, ← hu_b_rd]
    simp
  have hd_PnewR : h_P_new.Disjoint h_R :=
    { regs := fun r => by
        by_cases h0 : r = .r0
        · right; rw [h0]; exact h_R_no_r0
        by_cases h1 : r = .r1
        · right; rw [h1]; exact h_R_no_r1
        by_cases h2 : r = .r2
        · right; rw [h2]; exact h_R_no_r2
        · left; exact h_P_new_regs_other r h0 h1 h2
      mem := fun a => by
        by_cases ha : r1V ≤ a ∧ a < r1V + r2V
        · right
          obtain ⟨hlo, hhi⟩ := ha
          have h_eq : a = r1V + (a - r1V) := by omega
          have h_lt : a - r1V < r2V := by omega
          rw [h_eq]; exact h_R_no_mem_in _ h_lt
        · left
          apply h_P_new_mem_out
          rcases Nat.lt_or_ge a r1V with h | h
          · left; exact h
          · rcases Nat.lt_or_ge a (r1V + r2V) with h' | h'
            · exact absurd ⟨h, h'⟩ ha
            · right; exact h'
      pc := Or.inl h_P_new_pc
      returnData := Or.inr h_R_no_rd
      callStack := Or.inl h_P_new_cs }
  -- ^ Above is the hd_PnewR Disjoint construction for sol_set_return_data.
  -- ==== Phase 8: assemble the witness for (Q ** R).holdsFor. ====
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_, ?_⟩
  · rw [hexec]; show s.pc + 1 = pc + 1; rw [hpc]
  · rw [hexec]; exact hex
  · -- CU bound: executeFn fetch s 1 = chargeCu (step (.call .sol_set_return_data) s),
    -- and hCu provides the bound for step (pre-chargeCu).
    have hstep : executeFn fetch s 1 =
        chargeCu (step (.call .sol_set_return_data) s) := by
      rw [show (1 : Nat) = 0 + 1 from rfl,
          executeFn_step fetch s 0 _ hex (by omega) hfetch, executeFn_zero]
    rw [hstep]
    show (step (.call .sol_set_return_data) s).cuConsumed + 1
        ≤ s.cuConsumed + 1 + nCu
    have := hCu s; omega
  · refine ⟨h_P_new.union h_R, ?_, h_P_new, h_R, hd_PnewR, rfl,
            ⟨h_r0_new, h_T1_new, hd_r0_T1_new, rfl, rfl,
             h_r1_new, h_T2_new, hd_r1_T2_new, rfl, rfl,
             h_r2_new, h_T3_new, hd_r2_T3_new, rfl, rfl,
             h_b_new, h_rd_new, hd_b_rd_new, rfl, rfl, rfl⟩,
            h_R_sat⟩
    -- CompatibleWith (h_P_new ⊎ h_R) (executeFn fetch s 1).
    refine
      { regs := ?_, mem := ?_, pc := ?_, returnData := ?_, callStack := ?_ }
    · intro r v hvr
      by_cases h0 : r = .r0
      · rw [h0] at hvr
        rw [PartialState.union_regs_of_left_some h_P_new_regs_r0] at hvr
        have hv0 : v = 0 := (Option.some.inj hvr).symm
        rw [h0, hexec, hv0]
        show (s.regs.set .r0 0).get .r0 = 0
        exact RegFile.get_set_self _ _ _ (by decide : (.r0 : Reg) ≠ .r10)
      by_cases h1 : r = .r1
      · rw [h1] at hvr
        rw [PartialState.union_regs_of_left_some h_P_new_regs_r1] at hvr
        have hv1 : v = r1V := (Option.some.inj hvr).symm
        rw [h1, hexec, hv1]
        show (s.regs.set .r0 0).get .r1 = r1V
        rw [RegFile.get_set_diff _ _ _ _ (by decide : (.r1 : Reg) ≠ .r0)]
        exact hs_regs_r1
      by_cases h2 : r = .r2
      · rw [h2] at hvr
        rw [PartialState.union_regs_of_left_some h_P_new_regs_r2] at hvr
        have hv2 : v = r2V := (Option.some.inj hvr).symm
        rw [h2, hexec, hv2]
        show (s.regs.set .r0 0).get .r2 = r2V
        rw [RegFile.get_set_diff _ _ _ _ (by decide : (.r2 : Reg) ≠ .r0)]
        exact hs_regs_r2
      · rw [PartialState.union_regs_of_left_none
              (h_P_new_regs_other r h0 h1 h2)] at hvr
        rw [hexec]
        show (s.regs.set .r0 0).get r = v
        rw [RegFile.get_set_diff _ _ _ _ h0]
        have h_P_none : h_P.regs r = none := by
          rcases hd_PR_regs r with hl | hr
          · exact hl
          · rw [hr] at hvr; nomatch hvr
        apply hcr_regs r v
        rw [← hu_PR, PartialState.union_regs_of_left_none h_P_none]
        exact hvr
    · intro a v hva
      by_cases ha : r1V ≤ a ∧ a < r1V + r2V
      · obtain ⟨hlo, hhi⟩ := ha
        have h_eq : a = r1V + (a - r1V) := by omega
        have h_lt : a - r1V < r2V := by omega
        rw [h_eq] at hva ⊢
        rw [PartialState.union_mem_of_left_some
              (h_P_new_mem_in _ h_lt)] at hva
        have hveq : v = (bsIn.get! (a - r1V)).toNat :=
          (Option.some.inj hva).symm
        rw [hexec, hveq]
        show s.mem (r1V + (a - r1V)) = (bsIn.get! (a - r1V)).toNat
        exact hs_mem _ h_lt
      · have h_out : a < r1V ∨ a ≥ r1V + r2V := by
          rcases Nat.lt_or_ge a r1V with h | h
          · left; exact h
          · rcases Nat.lt_or_ge a (r1V + r2V) with h' | h'
            · exact absurd ⟨h, h'⟩ ha
            · right; exact h'
        rw [PartialState.union_mem_of_left_none
              (h_P_new_mem_out a h_out)] at hva
        rw [hexec]
        show s.mem a = v
        have h_P_none : h_P.mem a = none := by
          rcases hd_PR_mem a with hl | hr
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
      rw [PartialState.union_returnData_of_left_some h_P_new_rd] at hva
      have hrd_eq : rd = bsIn := (Option.some.inj hva).symm
      rw [hexec, hrd_eq]; rfl
    · intro cs hva
      rw [PartialState.union_callStack_of_left_none h_P_new_cs] at hva
      have hp_cs : hp.callStack = some cs := by
        rw [← hu_PR, PartialState.union_callStack_of_left_none h_P_cs_pre]
        exact hva
      rw [hexec]
      exact hcompat.callStack cs hp_cs

/-! ## Syscall: `sol_get_return_data` (refined via `returnDataIs`)

`sol_get_return_data(out, maxLen, pubkeyOut)`: copies up to `maxLen`
bytes of returnData to `*out`, writes the SETTER's 32-byte program id
(`State.returnDataProgId`) to `*pubkeyOut`, returns the ACTUAL data
length in `r0`. With lift #2, the spec owns both output buffers and
`returnDataIs` (read-only); the post-state has `r0 = rd.size`, the
buffers overwritten, returnData unchanged.

H7: `returnDataProgId` is SILENT in `PartialState` (like the CU meter
fields), so the SL-level post cannot pin the pubkey bytes — the honest
spec is existential over the 32 bytes written to `*pubkeyOut`. Pinning
the setter id would need a `PartialState` lift of `returnDataProgId`
(deferred; the diff suite pins the value cross-engine instead). The
pre-H7 spec claimed 32 ZERO bytes — false on chain.

This is the **exact-fit case**: `rd.size = maxLen`, and `hNonEmpty`
requires the buffer non-empty so the copy branch is taken (agave
writes NOTHING when `min(maxLen, len) = 0`; a copyLen-0 spec would
have a different frame, all-buffers-unchanged). The `h_disj`
hypothesis captures that the output and pubkey buffers don't overlap;
implicit in the sepConj precondition but accepted as an explicit
hypothesis here to keep the proof tractable (deriving non-overlap
from sepConj is ~150 LoC of pointwise contradiction). -/

theorem call_sol_get_return_data_spec
    (r0Old outA maxLen pkA : Nat)
    (rd bsOut pkOld : ByteArray) (pc : Nat) (nCu : Nat)
    (hRdSize : rd.size = maxLen)
    (hOutSize : bsOut.size = maxLen)
    (_hPkSize : pkOld.size = 32)
    (hNonEmpty : 0 < rd.size)
    (h_disj : outA + maxLen ≤ pkA ∨ pkA + 32 ≤ outA)
    (hCu : ∀ s : State,
        (step (.call .sol_get_return_data) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_get_return_data))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ outA) ** (.r2 ↦ᵣ maxLen) ** (.r3 ↦ᵣ pkA) **
        (outA ↦Bytes bsOut) ** (pkA ↦Bytes32 pkOld) ** returnDataIs rd)
      (fun h => ∃ pkNew : ByteArray,
        ((.r0 ↦ᵣ rd.size) ** (.r1 ↦ᵣ outA) ** (.r2 ↦ᵣ maxLen) ** (.r3 ↦ᵣ pkA) **
          (outA ↦Bytes rd) ** (pkA ↦Bytes32 pkNew) **
          returnDataIs rd) h) := by
  intro R hRfree fetch hcr s hPR hpc hex hbud
  -- ==== Phase 1: destructure the 7-atom precondition. ====
  obtain ⟨hp, hcompat, h_P, h_R, hd_PR, hu_PR, h_P_sat, h_R_sat⟩ := hPR
  obtain ⟨h_r0, h_T1, hd_r0_T1, hu_r0_T1, h_r0_pred, h_T1_sat⟩ := h_P_sat
  obtain ⟨h_r1, h_T2, hd_r1_T2, hu_r1_T2, h_r1_pred, h_T2_sat⟩ := h_T1_sat
  obtain ⟨h_r2, h_T3, hd_r2_T3, hu_r2_T3, h_r2_pred, h_T3_sat⟩ := h_T2_sat
  obtain ⟨h_r3, h_T4, hd_r3_T4, hu_r3_T4, h_r3_pred, h_T4_sat⟩ := h_T3_sat
  obtain ⟨h_out, h_T5, hd_out_T5, hu_out_T5, h_out_pred, h_T5_sat⟩ := h_T4_sat
  obtain ⟨h_pk, h_rd, hd_pk_rd, hu_pk_rd, h_pk_pred, h_rd_pred⟩ := h_T5_sat
  rw [h_r0_pred] at hu_r0_T1 hd_r0_T1
  rw [h_r1_pred] at hu_r1_T2 hd_r1_T2
  rw [h_r2_pred] at hu_r2_T3 hd_r2_T3
  rw [h_r3_pred] at hu_r3_T4 hd_r3_T4
  rw [h_out_pred] at hu_out_T5 hd_out_T5
  rw [h_pk_pred] at hu_pk_rd hd_pk_rd
  rw [h_rd_pred] at hu_pk_rd hd_pk_rd
  clear h_r0_pred h_r1_pred h_r2_pred h_r3_pred h_out_pred h_pk_pred h_rd_pred
  clear h_r0 h_r1 h_r2 h_r3 h_out h_pk h_rd
  have hcr_regs := hcompat.regs
  have hcm_mem := hcompat.mem
  have hcm_rd := hcompat.returnData
  -- ==== Phase 2: range-disjointness corollaries from h_disj. ====
  have h_pk_out_disj (i : Nat) (hi : i < 32) :
      pkA + i < outA ∨ pkA + i ≥ outA + maxLen := by
    rcases h_disj with h | h
    · right; omega
    · left; omega
  have h_out_pk_disj (i : Nat) (hi : i < maxLen) :
      outA + i < pkA ∨ outA + i ≥ pkA + 32 := by
    rcases h_disj with h | h
    · left; omega
    · right; omega
  -- ==== Phase 3: lift atom projections through hp. ====
  have h_T5_rd : h_T5.returnData = some rd := by
    rw [← hu_pk_rd,
        PartialState.union_returnData_of_left_none
          PartialState.singletonMem32Bytes_returnData]
    rfl
  have h_T4_rd : h_T4.returnData = some rd := by
    rw [← hu_out_T5,
        PartialState.union_returnData_of_left_none
          PartialState.singletonMemBytes_returnData]
    exact h_T5_rd
  have h_T3_rd : h_T3.returnData = some rd := by
    rw [← hu_r3_T4,
        PartialState.union_returnData_of_left_none
          PartialState.singletonReg_returnData]
    exact h_T4_rd
  have h_T2_rd : h_T2.returnData = some rd := by
    rw [← hu_r2_T3,
        PartialState.union_returnData_of_left_none
          PartialState.singletonReg_returnData]
    exact h_T3_rd
  have h_T1_rd : h_T1.returnData = some rd := by
    rw [← hu_r1_T2,
        PartialState.union_returnData_of_left_none
          PartialState.singletonReg_returnData]
    exact h_T2_rd
  have h_P_rd : h_P.returnData = some rd := by
    rw [← hu_r0_T1,
        PartialState.union_returnData_of_left_none
          PartialState.singletonReg_returnData]
    exact h_T1_rd
  have hp_rd : hp.returnData = some rd := by
    rw [← hu_PR]; exact PartialState.union_returnData_of_left_some h_P_rd
  have hs_rd : s.returnData = rd := hcm_rd rd hp_rd
  have h_P_regs_r0 : h_P.regs .r0 = some r0Old := by
    rw [← hu_r0_T1]
    exact PartialState.union_regs_of_left_some
      PartialState.singletonReg_regs_self
  have h_T1_regs_r1 : h_T1.regs .r1 = some outA := by
    rw [← hu_r1_T2]
    exact PartialState.union_regs_of_left_some
      PartialState.singletonReg_regs_self
  have h_T2_regs_r2 : h_T2.regs .r2 = some maxLen := by
    rw [← hu_r2_T3]
    exact PartialState.union_regs_of_left_some
      PartialState.singletonReg_regs_self
  have h_T3_regs_r3 : h_T3.regs .r3 = some pkA := by
    rw [← hu_r3_T4]
    exact PartialState.union_regs_of_left_some
      PartialState.singletonReg_regs_self
  have h_P_regs_r1 : h_P.regs .r1 = some outA := by
    rw [← hu_r0_T1,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r1 ≠ Reg.r0))]
    exact h_T1_regs_r1
  have h_P_regs_r2 : h_P.regs .r2 = some maxLen := by
    rw [← hu_r0_T1,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r2 ≠ Reg.r0)),
        ← hu_r1_T2,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r2 ≠ Reg.r1))]
    exact h_T2_regs_r2
  have h_P_regs_r3 : h_P.regs .r3 = some pkA := by
    rw [← hu_r0_T1,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r3 ≠ Reg.r0)),
        ← hu_r1_T2,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r3 ≠ Reg.r1)),
        ← hu_r2_T3,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r3 ≠ Reg.r2))]
    exact h_T3_regs_r3
  have hp_regs_r0 : hp.regs .r0 = some r0Old := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r0
  have hp_regs_r1 : hp.regs .r1 = some outA := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r1
  have hp_regs_r2 : hp.regs .r2 = some maxLen := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r2
  have hp_regs_r3 : hp.regs .r3 = some pkA := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r3
  have hs_regs_r0 : s.regs.get .r0 = r0Old := hcr_regs .r0 r0Old hp_regs_r0
  have hs_regs_r1 : s.regs.get .r1 = outA := hcr_regs .r1 outA hp_regs_r1
  have hs_regs_r2 : s.regs.get .r2 = maxLen := hcr_regs .r2 maxLen hp_regs_r2
  have hs_regs_r3 : s.regs.get .r3 = pkA := hcr_regs .r3 pkA hp_regs_r3
  have hs_r1_field : s.regs.r1 = outA := hs_regs_r1
  have hs_r2_field : s.regs.r2 = maxLen := hs_regs_r2
  have hs_r3_field : s.regs.r3 = pkA := hs_regs_r3
  have h_P_mem_out (i : Nat) (hi : i < bsOut.size) :
      h_P.mem (outA + i) = some (bsOut.get! i).toNat := by
    rw [← hu_r0_T1,
        PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (outA + i)),
        ← hu_r1_T2,
        PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (outA + i)),
        ← hu_r2_T3,
        PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (outA + i)),
        ← hu_r3_T4,
        PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (outA + i)),
        ← hu_out_T5]
    exact PartialState.union_mem_of_left_some
      (PartialState.singletonMemBytes_mem_at outA bsOut i hi)
  have h_P_mem_pk (i : Nat) (hi : i < 32) :
      h_P.mem (pkA + i) = some (pkOld.get! i).toNat := by
    have h_pk_out_no : pkA + i < outA ∨ pkA + i ≥ outA + bsOut.size := by
      rcases h_pk_out_disj i hi with h | h
      · left; exact h
      · right; rw [hOutSize]; exact h
    rw [← hu_r0_T1,
        PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (pkA + i)),
        ← hu_r1_T2,
        PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (pkA + i)),
        ← hu_r2_T3,
        PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (pkA + i)),
        ← hu_r3_T4,
        PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (pkA + i)),
        ← hu_out_T5,
        PartialState.union_mem_of_left_none
          (PartialState.singletonMemBytes_mem_outside outA bsOut (pkA + i) h_pk_out_no),
        ← hu_pk_rd]
    exact PartialState.union_mem_of_left_some
      (PartialState.singletonMem32Bytes_mem_at pkA pkOld i hi)
  -- ==== Phase 4: executeFn produces the expected post state. ====
  have hfetch : fetch s.pc = some (.call .sol_get_return_data) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hstep_eq : executeFn fetch s 1 =
      chargeCu (step (.call .sol_get_return_data) s) := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch, executeFn_zero]
  have h_copyLen : (if rd.size ≤ maxLen then rd.size else maxLen) = rd.size := by
    rw [if_pos (by rw [hRdSize]; exact Nat.le_refl _)]
  -- The copy length is non-zero (hNonEmpty), so `execGet` takes the
  -- write branch, not the agave `length == 0` no-op branch.
  have h_copy_ne :
      ¬ ((if s.returnData.size ≤ s.regs.r2
            then s.returnData.size else s.regs.r2) = 0) := by
    rw [hs_rd, hs_r2_field, h_copyLen]
    omega
  have hexec_regs : (executeFn fetch s 1).regs = s.regs.set .r0 rd.size := by
    rw [hstep_eq]; show ((ReturnData.execGet s).regs) = s.regs.set .r0 rd.size
    simp only [ReturnData.execGet]
    simp only [if_neg h_copy_ne]
    simp only [hs_rd]
  have hexec_pc : (executeFn fetch s 1).pc = s.pc + 1 := by
    rw [hstep_eq]; rfl
  have hexec_exit : (executeFn fetch s 1).exitCode = none := by
    rw [hstep_eq]; show (ReturnData.execGet s).exitCode = none
    simp only [ReturnData.execGet]
    split <;> split <;> exact hex
  have hexec_rd : (executeFn fetch s 1).returnData = s.returnData := by
    rw [hstep_eq]; show (ReturnData.execGet s).returnData = s.returnData
    simp only [ReturnData.execGet]
    split <;> split <;> rfl
  have hexec_mem_at_out (i : Nat) (hi : i < rd.size) :
      (executeFn fetch s 1).mem (outA + i) = (rd.get! i).toNat := by
    rw [hstep_eq]
    show ((ReturnData.execGet s).mem) (outA + i) = (rd.get! i).toNat
    simp only [ReturnData.execGet]
    simp only [if_neg h_copy_ne]
    rw [Mem_read_default, hs_r1_field, hs_r3_field, hs_r2_field, hs_rd, h_copyLen]
    rw [if_pos ⟨Nat.le_add_right _ _, by omega⟩,
        show outA + i - outA = i from by omega]
  have hexec_mem_at_pk (i : Nat) (hi : i < 32) :
      (executeFn fetch s 1).mem (pkA + i)
        = (s.returnDataProgId.get! i).toNat := by
    rw [hstep_eq]
    show ((ReturnData.execGet s).mem) (pkA + i)
        = (s.returnDataProgId.get! i).toNat
    simp only [ReturnData.execGet]
    simp only [if_neg h_copy_ne]
    rw [Mem_read_default, hs_r1_field, hs_r3_field, hs_r2_field, hs_rd, h_copyLen]
    rw [if_neg, if_pos ⟨Nat.le_add_right _ _, by omega⟩,
        show pkA + i - pkA = i from by omega]
    rintro ⟨h1, h2⟩
    rcases h_pk_out_disj i hi with h | h
    · omega
    · have : rd.size ≤ maxLen := by rw [hRdSize]; exact Nat.le_refl _
      omega
  have hexec_mem_outside (a : Nat)
      (h_out_addr : a < outA ∨ a ≥ outA + maxLen)
      (h_pk_addr : a < pkA ∨ a ≥ pkA + 32) :
      (executeFn fetch s 1).mem a = s.mem a := by
    rw [hstep_eq]
    show ((ReturnData.execGet s).mem) a = s.mem a
    simp only [ReturnData.execGet]
    simp only [if_neg h_copy_ne]
    rw [Mem_read_default, hs_r1_field, hs_r3_field, hs_r2_field, hs_rd, h_copyLen]
    rw [if_neg, if_neg]
    · rintro ⟨h1, h2⟩
      rcases h_pk_addr with h | h <;> omega
    · rintro ⟨h1, h2⟩
      rcases h_out_addr with h | h
      · omega
      · have : rd.size ≤ maxLen := by rw [hRdSize]; exact Nat.le_refl _
        omega
  -- ==== Phase 5: hR non-overlap facts. ====
  have hd_PR_regs := hd_PR.regs
  have hd_PR_mem := hd_PR.mem
  have hd_PR_rd := hd_PR.returnData
  have h_R_no_r0 : h_R.regs .r0 = none := by
    rcases hd_PR_regs .r0 with hl | hr
    · rw [h_P_regs_r0] at hl; nomatch hl
    · exact hr
  have h_R_no_r1 : h_R.regs .r1 = none := by
    rcases hd_PR_regs .r1 with hl | hr
    · rw [h_P_regs_r1] at hl; nomatch hl
    · exact hr
  have h_R_no_r2 : h_R.regs .r2 = none := by
    rcases hd_PR_regs .r2 with hl | hr
    · rw [h_P_regs_r2] at hl; nomatch hl
    · exact hr
  have h_R_no_r3 : h_R.regs .r3 = none := by
    rcases hd_PR_regs .r3 with hl | hr
    · rw [h_P_regs_r3] at hl; nomatch hl
    · exact hr
  have h_R_no_pc : h_R.pc = none := hRfree _ h_R_sat
  have h_R_no_rd : h_R.returnData = none := by
    rcases hd_PR_rd with hl | hr
    · rw [h_P_rd] at hl; nomatch hl
    · exact hr
  have h_R_no_mem_out (i : Nat) (hi : i < bsOut.size) :
      h_R.mem (outA + i) = none := by
    rcases hd_PR_mem (outA + i) with hl | hr
    · rw [h_P_mem_out i hi] at hl; nomatch hl
    · exact hr
  have h_R_no_mem_pk (i : Nat) (hi : i < 32) :
      h_R.mem (pkA + i) = none := by
    rcases hd_PR_mem (pkA + i) with hl | hr
    · rw [h_P_mem_pk i hi] at hl; nomatch hl
    · exact hr
  -- ==== Phase 6: build the post heap. ====
  let h_r0_new : PartialState := PartialState.singletonReg .r0 rd.size
  let h_r1_new : PartialState := PartialState.singletonReg .r1 outA
  let h_r2_new : PartialState := PartialState.singletonReg .r2 maxLen
  let h_r3_new : PartialState := PartialState.singletonReg .r3 pkA
  let h_out_new : PartialState := PartialState.singletonMemBytes outA rd
  let h_pk_new : PartialState :=
    -- The pubkey-out buffer's post value is the setter id carried by
    -- the CONCRETE state (`s.returnDataProgId`, silent in
    -- PartialState) — it becomes the witness of the existential post.
    PartialState.singletonMem32Bytes pkA s.returnDataProgId
  let h_rd_new : PartialState := PartialState.singletonReturnData rd
  let h_T5_new : PartialState := h_pk_new.union h_rd_new
  let h_T4_new : PartialState := h_out_new.union h_T5_new
  let h_T3_new : PartialState := h_r3_new.union h_T4_new
  let h_T2_new : PartialState := h_r2_new.union h_T3_new
  let h_T1_new : PartialState := h_r1_new.union h_T2_new
  let h_P_new : PartialState := h_r0_new.union h_T1_new
  have hd_pk_rd_new : h_pk_new.Disjoint h_rd_new :=
    { regs := fun r => Or.inl (PartialState.singletonMem32Bytes_regs r)
      mem  := fun a => Or.inr (PartialState.singletonReturnData_mem a)
      pc   := Or.inl PartialState.singletonMem32Bytes_pc
      returnData := Or.inl PartialState.singletonMem32Bytes_returnData
      callStack := Or.inl PartialState.singletonMem32Bytes_callStack }
  have hd_out_T5_new : h_out_new.Disjoint h_T5_new :=
    { regs := fun r => Or.inl (PartialState.singletonMemBytes_regs r)
      mem  := fun a => by
        by_cases ha : outA ≤ a ∧ a < outA + rd.size
        · right
          obtain ⟨h_lo, h_hi⟩ := ha
          show (h_pk_new.union h_rd_new).mem a = none
          rw [PartialState.union_mem_of_left_none]
          · exact PartialState.singletonReturnData_mem a
          · apply PartialState.singletonMem32Bytes_mem_outside
            have h_lt_max : a - outA < maxLen := by rw [← hRdSize]; omega
            rcases h_out_pk_disj (a - outA) h_lt_max with h | h
            · left; omega
            · right; omega
        · left
          apply PartialState.singletonMemBytes_mem_outside
          rcases Nat.lt_or_ge a outA with h' | h'
          · left; exact h'
          · rcases Nat.lt_or_ge a (outA + rd.size) with h'' | h''
            · exact absurd ⟨h', h''⟩ ha
            · right; exact h''
      pc   := Or.inl PartialState.singletonMemBytes_pc
      returnData := Or.inl PartialState.singletonMemBytes_returnData
      callStack := Or.inl PartialState.singletonMemBytes_callStack }
  have hd_r3_T4_new : h_r3_new.Disjoint h_T4_new := by
    refine
      { regs := fun r => ?_
        mem  := fun a => Or.inl (PartialState.singletonReg_mem a)
        pc   := Or.inl PartialState.singletonReg_pc
        returnData := Or.inl PartialState.singletonReg_returnData
        callStack := Or.inl PartialState.singletonReg_callStack }
    by_cases hr : r = .r3
    · right; rw [hr]
      show (h_out_new.union h_T5_new).regs .r3 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonMemBytes_regs .r3)]
      show (h_pk_new.union h_rd_new).regs .r3 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonMem32Bytes_regs .r3)]
      exact PartialState.singletonReturnData_regs .r3
    · left; exact PartialState.singletonReg_regs_other hr
  have hd_r2_T3_new : h_r2_new.Disjoint h_T3_new := by
    refine
      { regs := fun r => ?_
        mem  := fun a => Or.inl (PartialState.singletonReg_mem a)
        pc   := Or.inl PartialState.singletonReg_pc
        returnData := Or.inl PartialState.singletonReg_returnData
        callStack := Or.inl PartialState.singletonReg_callStack }
    by_cases hr : r = .r2
    · right; rw [hr]
      show (h_r3_new.union h_T4_new).regs .r2 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r2 ≠ Reg.r3))]
      show (h_out_new.union h_T5_new).regs .r2 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonMemBytes_regs .r2)]
      show (h_pk_new.union h_rd_new).regs .r2 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonMem32Bytes_regs .r2)]
      exact PartialState.singletonReturnData_regs .r2
    · left; exact PartialState.singletonReg_regs_other hr
  have hd_r1_T2_new : h_r1_new.Disjoint h_T2_new := by
    refine
      { regs := fun r => ?_
        mem  := fun a => Or.inl (PartialState.singletonReg_mem a)
        pc   := Or.inl PartialState.singletonReg_pc
        returnData := Or.inl PartialState.singletonReg_returnData
        callStack := Or.inl PartialState.singletonReg_callStack }
    by_cases hr : r = .r1
    · right; rw [hr]
      show (h_r2_new.union h_T3_new).regs .r1 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r1 ≠ Reg.r2))]
      show (h_r3_new.union h_T4_new).regs .r1 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r1 ≠ Reg.r3))]
      show (h_out_new.union h_T5_new).regs .r1 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonMemBytes_regs .r1)]
      show (h_pk_new.union h_rd_new).regs .r1 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonMem32Bytes_regs .r1)]
      exact PartialState.singletonReturnData_regs .r1
    · left; exact PartialState.singletonReg_regs_other hr
  have hd_r0_T1_new : h_r0_new.Disjoint h_T1_new := by
    refine
      { regs := fun r => ?_
        mem  := fun a => Or.inl (PartialState.singletonReg_mem a)
        pc   := Or.inl PartialState.singletonReg_pc
        returnData := Or.inl PartialState.singletonReg_returnData
        callStack := Or.inl PartialState.singletonReg_callStack }
    by_cases hr : r = .r0
    · right; rw [hr]
      show (h_r1_new.union h_T2_new).regs .r0 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r0 ≠ Reg.r1))]
      show (h_r2_new.union h_T3_new).regs .r0 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r0 ≠ Reg.r2))]
      show (h_r3_new.union h_T4_new).regs .r0 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r0 ≠ Reg.r3))]
      show (h_out_new.union h_T5_new).regs .r0 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonMemBytes_regs .r0)]
      show (h_pk_new.union h_rd_new).regs .r0 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonMem32Bytes_regs .r0)]
      exact PartialState.singletonReturnData_regs .r0
    · left; exact PartialState.singletonReg_regs_other hr
  have h_P_new_regs_r0 : h_P_new.regs .r0 = some rd.size := by
    show (h_r0_new.union h_T1_new).regs .r0 = some rd.size
    exact PartialState.union_regs_of_left_some
      PartialState.singletonReg_regs_self
  have h_P_new_regs_r1 : h_P_new.regs .r1 = some outA := by
    show (h_r0_new.union h_T1_new).regs .r1 = some outA
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r1 ≠ Reg.r0))]
    show (h_r1_new.union h_T2_new).regs .r1 = some outA
    exact PartialState.union_regs_of_left_some
      PartialState.singletonReg_regs_self
  have h_P_new_regs_r2 : h_P_new.regs .r2 = some maxLen := by
    show (h_r0_new.union h_T1_new).regs .r2 = some maxLen
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r2 ≠ Reg.r0))]
    show (h_r1_new.union h_T2_new).regs .r2 = some maxLen
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r2 ≠ Reg.r1))]
    show (h_r2_new.union h_T3_new).regs .r2 = some maxLen
    exact PartialState.union_regs_of_left_some
      PartialState.singletonReg_regs_self
  have h_P_new_regs_r3 : h_P_new.regs .r3 = some pkA := by
    show (h_r0_new.union h_T1_new).regs .r3 = some pkA
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r3 ≠ Reg.r0))]
    show (h_r1_new.union h_T2_new).regs .r3 = some pkA
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r3 ≠ Reg.r1))]
    show (h_r2_new.union h_T3_new).regs .r3 = some pkA
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r3 ≠ Reg.r2))]
    show (h_r3_new.union h_T4_new).regs .r3 = some pkA
    exact PartialState.union_regs_of_left_some
      PartialState.singletonReg_regs_self
  have h_P_new_regs_other (r : Reg)
      (h0 : r ≠ .r0) (h1 : r ≠ .r1) (h2 : r ≠ .r2) (h3 : r ≠ .r3) :
      h_P_new.regs r = none := by
    show (h_r0_new.union h_T1_new).regs r = none
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other h0)]
    show (h_r1_new.union h_T2_new).regs r = none
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other h1)]
    show (h_r2_new.union h_T3_new).regs r = none
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other h2)]
    show (h_r3_new.union h_T4_new).regs r = none
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other h3)]
    show (h_out_new.union h_T5_new).regs r = none
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonMemBytes_regs r)]
    show (h_pk_new.union h_rd_new).regs r = none
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonMem32Bytes_regs r)]
    exact PartialState.singletonReturnData_regs r
  have h_P_new_mem_at_out (i : Nat) (hi : i < rd.size) :
      h_P_new.mem (outA + i) = some (rd.get! i).toNat := by
    show (h_r0_new.union h_T1_new).mem (outA + i) = some (rd.get! i).toNat
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (outA + i))]
    show (h_r1_new.union h_T2_new).mem (outA + i) = some (rd.get! i).toNat
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (outA + i))]
    show (h_r2_new.union h_T3_new).mem (outA + i) = some (rd.get! i).toNat
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (outA + i))]
    show (h_r3_new.union h_T4_new).mem (outA + i) = some (rd.get! i).toNat
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (outA + i))]
    show (h_out_new.union h_T5_new).mem (outA + i) = some (rd.get! i).toNat
    apply PartialState.union_mem_of_left_some
    exact PartialState.singletonMemBytes_mem_at outA rd i hi
  have h_P_new_mem_at_pk (i : Nat) (hi : i < 32) :
      h_P_new.mem (pkA + i) = some (s.returnDataProgId.get! i).toNat := by
    have h_pk_outside_out : pkA + i < outA ∨ pkA + i ≥ outA + rd.size := by
      rcases h_pk_out_disj i hi with h | h
      · left; exact h
      · right; rw [hRdSize]; exact h
    show (h_r0_new.union h_T1_new).mem (pkA + i)
        = some (s.returnDataProgId.get! i).toNat
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (pkA + i))]
    show (h_r1_new.union h_T2_new).mem (pkA + i)
        = some (s.returnDataProgId.get! i).toNat
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (pkA + i))]
    show (h_r2_new.union h_T3_new).mem (pkA + i)
        = some (s.returnDataProgId.get! i).toNat
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (pkA + i))]
    show (h_r3_new.union h_T4_new).mem (pkA + i)
        = some (s.returnDataProgId.get! i).toNat
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (pkA + i))]
    show (h_out_new.union h_T5_new).mem (pkA + i)
        = some (s.returnDataProgId.get! i).toNat
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonMemBytes_mem_outside outA rd (pkA + i) h_pk_outside_out)]
    show (h_pk_new.union h_rd_new).mem (pkA + i)
        = some (s.returnDataProgId.get! i).toNat
    apply PartialState.union_mem_of_left_some
    exact PartialState.singletonMem32Bytes_mem_at pkA s.returnDataProgId i hi
  have h_P_new_mem_outside (a : Nat)
      (h_out_addr : a < outA ∨ a ≥ outA + rd.size)
      (h_pk_addr : a < pkA ∨ a ≥ pkA + 32) :
      h_P_new.mem a = none := by
    show (h_r0_new.union h_T1_new).mem a = none
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
    show (h_r1_new.union h_T2_new).mem a = none
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
    show (h_r2_new.union h_T3_new).mem a = none
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
    show (h_r3_new.union h_T4_new).mem a = none
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
    show (h_out_new.union h_T5_new).mem a = none
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonMemBytes_mem_outside outA rd a h_out_addr)]
    show (h_pk_new.union h_rd_new).mem a = none
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonMem32Bytes_mem_outside pkA s.returnDataProgId a h_pk_addr)]
    exact PartialState.singletonReturnData_mem a
  have h_P_new_pc : h_P_new.pc = none := by
    show (h_r0_new.union h_T1_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    show (h_r1_new.union h_T2_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    show (h_r2_new.union h_T3_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    show (h_r3_new.union h_T4_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    show (h_out_new.union h_T5_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonMemBytes_pc]
    show (h_pk_new.union h_rd_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonMem32Bytes_pc]
    exact PartialState.singletonReturnData_pc
  have h_P_new_rd : h_P_new.returnData = some rd := by
    show (h_r0_new.union h_T1_new).returnData = some rd
    rw [PartialState.union_returnData_of_left_none PartialState.singletonReg_returnData]
    show (h_r1_new.union h_T2_new).returnData = some rd
    rw [PartialState.union_returnData_of_left_none PartialState.singletonReg_returnData]
    show (h_r2_new.union h_T3_new).returnData = some rd
    rw [PartialState.union_returnData_of_left_none PartialState.singletonReg_returnData]
    show (h_r3_new.union h_T4_new).returnData = some rd
    rw [PartialState.union_returnData_of_left_none PartialState.singletonReg_returnData]
    show (h_out_new.union h_T5_new).returnData = some rd
    rw [PartialState.union_returnData_of_left_none PartialState.singletonMemBytes_returnData]
    show (h_pk_new.union h_rd_new).returnData = some rd
    rw [PartialState.union_returnData_of_left_none PartialState.singletonMem32Bytes_returnData]
    rfl
  have h_P_new_cs : h_P_new.callStack = none := by rfl
  have h_P_cs_pre : h_P.callStack = none := by
    rw [← hu_r0_T1, ← hu_r1_T2, ← hu_r2_T3, ← hu_r3_T4, ← hu_out_T5, ← hu_pk_rd]
    rfl
  -- ==== Phase 7: outer disjointness h_P_new ⫫ h_R. ====
  have hd_PnewR : h_P_new.Disjoint h_R :=
    { regs := fun r => by
        by_cases h0 : r = .r0
        · right; rw [h0]; exact h_R_no_r0
        by_cases h1 : r = .r1
        · right; rw [h1]; exact h_R_no_r1
        by_cases h2 : r = .r2
        · right; rw [h2]; exact h_R_no_r2
        by_cases h3 : r = .r3
        · right; rw [h3]; exact h_R_no_r3
        · left; exact h_P_new_regs_other r h0 h1 h2 h3
      mem := fun a => by
        by_cases ha : outA ≤ a ∧ a < outA + rd.size
        · right
          obtain ⟨h_lo, h_hi⟩ := ha
          have h_eq : a = outA + (a - outA) := by omega
          have h_lt : a - outA < rd.size := by omega
          have h_lt_bsOut : a - outA < bsOut.size := by rw [hOutSize, ← hRdSize]; exact h_lt
          rw [h_eq]; exact h_R_no_mem_out _ h_lt_bsOut
        · by_cases hb : pkA ≤ a ∧ a < pkA + 32
          · right
            obtain ⟨h_lo, h_hi⟩ := hb
            have h_eq : a = pkA + (a - pkA) := by omega
            have h_lt : a - pkA < 32 := by omega
            rw [h_eq]; exact h_R_no_mem_pk _ h_lt
          · left
            apply h_P_new_mem_outside
            · rcases Nat.lt_or_ge a outA with h | h
              · left; exact h
              · rcases Nat.lt_or_ge a (outA + rd.size) with h' | h'
                · exact absurd ⟨h, h'⟩ ha
                · right; exact h'
            · rcases Nat.lt_or_ge a pkA with h | h
              · left; exact h
              · rcases Nat.lt_or_ge a (pkA + 32) with h' | h'
                · exact absurd ⟨h, h'⟩ hb
                · right; exact h'
      pc := Or.inl h_P_new_pc
      returnData := Or.inr h_R_no_rd
      callStack := Or.inl h_P_new_cs }
  -- ==== Phase 8: assemble the witness. ====
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_, ?_⟩
  · rw [hexec_pc, hpc]
  · exact hexec_exit
  · rw [hstep_eq]
    show (step (.call .sol_get_return_data) s).cuConsumed + 1
        ≤ s.cuConsumed + 1 + nCu
    have := hCu s; omega
  · -- The existential post is witnessed by the concrete state's setter
    -- id: `pkNew := s.returnDataProgId` (h_pk_new is built over it).
    refine ⟨h_P_new.union h_R, ?_, h_P_new, h_R, hd_PnewR, rfl,
            ⟨s.returnDataProgId,
             h_r0_new, h_T1_new, hd_r0_T1_new, rfl, rfl,
             h_r1_new, h_T2_new, hd_r1_T2_new, rfl, rfl,
             h_r2_new, h_T3_new, hd_r2_T3_new, rfl, rfl,
             h_r3_new, h_T4_new, hd_r3_T4_new, rfl, rfl,
             h_out_new, h_T5_new, hd_out_T5_new, rfl, rfl,
             h_pk_new, h_rd_new, hd_pk_rd_new, rfl, rfl, rfl⟩,
            h_R_sat⟩
    refine
      { regs := ?_, mem := ?_, pc := ?_, returnData := ?_, callStack := ?_ }
    · intro r v hvr
      by_cases h0 : r = .r0
      · rw [h0] at hvr
        rw [PartialState.union_regs_of_left_some h_P_new_regs_r0] at hvr
        have hv0 : v = rd.size := (Option.some.inj hvr).symm
        rw [h0, hexec_regs, hv0]
        exact RegFile.get_set_self _ _ _ (by decide : (.r0 : Reg) ≠ .r10)
      by_cases h1 : r = .r1
      · rw [h1] at hvr
        rw [PartialState.union_regs_of_left_some h_P_new_regs_r1] at hvr
        have hv1 : v = outA := (Option.some.inj hvr).symm
        rw [h1, hexec_regs, hv1,
            RegFile.get_set_diff _ _ _ _ (by decide : (.r1 : Reg) ≠ .r0)]
        exact hs_regs_r1
      by_cases h2 : r = .r2
      · rw [h2] at hvr
        rw [PartialState.union_regs_of_left_some h_P_new_regs_r2] at hvr
        have hv2 : v = maxLen := (Option.some.inj hvr).symm
        rw [h2, hexec_regs, hv2,
            RegFile.get_set_diff _ _ _ _ (by decide : (.r2 : Reg) ≠ .r0)]
        exact hs_regs_r2
      by_cases h3 : r = .r3
      · rw [h3] at hvr
        rw [PartialState.union_regs_of_left_some h_P_new_regs_r3] at hvr
        have hv3 : v = pkA := (Option.some.inj hvr).symm
        rw [h3, hexec_regs, hv3,
            RegFile.get_set_diff _ _ _ _ (by decide : (.r3 : Reg) ≠ .r0)]
        exact hs_regs_r3
      · rw [PartialState.union_regs_of_left_none
              (h_P_new_regs_other r h0 h1 h2 h3)] at hvr
        rw [hexec_regs, RegFile.get_set_diff _ _ _ _ h0]
        have h_P_none : h_P.regs r = none := by
          rcases hd_PR_regs r with hl | hr
          · exact hl
          · rw [hr] at hvr; nomatch hvr
        apply hcr_regs r v
        rw [← hu_PR, PartialState.union_regs_of_left_none h_P_none]
        exact hvr
    · intro a v hva
      by_cases ha : outA ≤ a ∧ a < outA + rd.size
      · obtain ⟨h_lo, h_hi⟩ := ha
        have h_eq : a = outA + (a - outA) := by omega
        have h_lt : a - outA < rd.size := by omega
        rw [h_eq] at hva ⊢
        rw [PartialState.union_mem_of_left_some
              (h_P_new_mem_at_out _ h_lt)] at hva
        have hveq : v = (rd.get! (a - outA)).toNat := (Option.some.inj hva).symm
        rw [hexec_mem_at_out _ h_lt, hveq]
      · by_cases hb : pkA ≤ a ∧ a < pkA + 32
        · obtain ⟨h_lo, h_hi⟩ := hb
          have h_eq : a = pkA + (a - pkA) := by omega
          have h_lt : a - pkA < 32 := by omega
          rw [h_eq] at hva ⊢
          rw [PartialState.union_mem_of_left_some
                (h_P_new_mem_at_pk _ h_lt)] at hva
          have hveq : v = (s.returnDataProgId.get! (a - pkA)).toNat :=
            (Option.some.inj hva).symm
          rw [hexec_mem_at_pk _ h_lt, hveq]
        · have h_out_addr : a < outA ∨ a ≥ outA + rd.size := by
            rcases Nat.lt_or_ge a outA with h | h
            · left; exact h
            · rcases Nat.lt_or_ge a (outA + rd.size) with h' | h'
              · exact absurd ⟨h, h'⟩ ha
              · right; exact h'
          have h_pk_addr : a < pkA ∨ a ≥ pkA + 32 := by
            rcases Nat.lt_or_ge a pkA with h | h
            · left; exact h
            · rcases Nat.lt_or_ge a (pkA + 32) with h' | h'
              · exact absurd ⟨h, h'⟩ hb
              · right; exact h'
          have h_out_max : a < outA ∨ a ≥ outA + maxLen := by
            rcases h_out_addr with h | h
            · left; exact h
            · right; rw [← hRdSize]; exact h
          rw [PartialState.union_mem_of_left_none
                (h_P_new_mem_outside a h_out_addr h_pk_addr)] at hva
          rw [hexec_mem_outside a h_out_max h_pk_addr]
          have h_P_none : h_P.mem a = none := by
            rcases hd_PR_mem a with hl | hr
            · exact hl
            · rw [hr] at hva; nomatch hva
          apply hcm_mem a v
          rw [← hu_PR, PartialState.union_mem_of_left_none h_P_none]
          exact hva
    · intro v hvp
      rw [PartialState.union_pc_of_left_none h_P_new_pc] at hvp
      rw [h_R_no_pc] at hvp
      nomatch hvp
    · intro rdq hva
      rw [PartialState.union_returnData_of_left_some h_P_new_rd] at hva
      have hrd_eq : rdq = rd := (Option.some.inj hva).symm
      rw [hexec_rd, hs_rd, hrd_eq]
    · intro cs hva
      rw [PartialState.union_callStack_of_left_none h_P_new_cs] at hva
      have hp_cs : hp.callStack = some cs := by
        rw [← hu_PR, PartialState.union_callStack_of_left_none h_P_cs_pre]
        exact hva
      have hexec_cs : (executeFn fetch s 1).callStack = s.callStack := by
        rw [hstep_eq]
        show (ReturnData.execGet s).callStack = s.callStack
        simp only [ReturnData.execGet]
        split <;> split <;> rfl
      rw [hexec_cs]
      exact hcompat.callStack cs hp_cs

/-! ## Silent-syscall helper: `cuTripleWithin_syscall_silent`

For syscalls whose `step` is a no-op on `PartialState` (regs, mem, pc
all match modulo `pc + 1`). The spec is `emp ↓ emp` — the syscall
advances pc by 1 and consumes fuel/CU but doesn't observably touch
any SL-tracked resource. Composed with the frame rule, it transports
any pc-free assertion through the call. -/

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

H7: `execRemainingComputeUnits` writes the REAL remaining compute budget
to `r0` (`cuBudget − (cuConsumed + 1 + Misc.cu)`, H5 total metering).
The meter fields (`cuBudget`/`cuConsumed`) are SILENT in `PartialState`,
so the SL-level postcondition cannot pin the value — the honest spec is
existential: `r0` was overwritten with SOME value. A lift can therefore
no longer prove "`r0` preserved" across this syscall (which would be
false on chain), but also cannot claim to know the returned budget. -/

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
