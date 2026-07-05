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
  (r0_writer_obligations
    (cuTripleWithin_syscall_writes_r0_fn .sol_remaining_compute_units
      (fun s => s.cuBudget - (s.cuConsumed + 1 + Misc.cu)) pc nCu)
    Misc.execRemainingComputeUnits)
    hCu

/-! ## Syscall: `sol_set_return_data` — H6 region check + returnData write

`sol_set_return_data(ptr, len)` reads the input slice `[r1V, r1V+r2V)` and
COPIES it into `State.returnData` (`ReturnData.execSet`), setting `r0 := 0`.
Memory is unchanged; the only SL-tracked write is to the framed `↦ReturnData`
atom (the log helper's silent-returnData obligation is FALSE here).

This is the first triple that OWNS the `returnData` atom in pre AND post: P
carries `↦ReturnData rdOld`, the post flips it to the input blob. The
`readBytes`↔blob bridge (`readBytes_eq_of_match`) pins the post buffer to the
owned `↦Bytes inputBlob`. The length guard `r2V ≤ MAX_RETURN_DATA` (H7) clears
the `ReturnDataTooLarge` branch; `rr = containsRange r1V r2V` clears the H6
`guardRead`. `returnDataProgId` is silent in `PartialState`. -/

theorem call_sol_set_return_data_spec
    (r0Old r1V r2V pc nCu : Nat) (inputBlob rdOld : ByteArray)
    (hsize : inputBlob.size = r2V)
    (hlen : r2V ≤ MAX_RETURN_DATA)
    (hCu : ∀ s : State,
        (step (.call .sol_set_return_data) s).cuConsumed ≤ s.cuConsumed + nCu) :
    -- H6: the input slice `[r1V, r1V + r2V)` must be in a mapped region.
    cuTripleWithinMem 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_set_return_data))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V)
       ** (r1V ↦Bytes inputBlob) ** (↦ReturnData rdOld))
      ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V)
       ** (r1V ↦Bytes inputBlob) ** (↦ReturnData inputBlob))
      (fun rt => rt.containsRange r1V r2V = true) := by
  intro R hRfree fetch hcr s hPR hpc hex hbud h_region
  obtain ⟨hp, hcompat, h_P, h_R, hd_PR, hu_PR, h_P_sat, h_R_sat⟩ := hPR
  obtain ⟨h_r0, h_T1, hd_r0_T1, hu_r0_T1, h_r0_pred, h_T1_sat⟩ := h_P_sat
  obtain ⟨h_r1, h_T2, hd_r1_T2, hu_r1_T2, h_r1_pred, h_T2_sat⟩ := h_T1_sat
  obtain ⟨h_r2, h_T3, hd_r2_T3, hu_r2_T3, h_r2_pred, h_T3_sat⟩ := h_T2_sat
  obtain ⟨h_blob, h_rd, hd_blob_rd, hu_blob_rd, h_blob_pred, h_rd_pred⟩ := h_T3_sat
  rw [h_r0_pred] at hu_r0_T1
  rw [h_r1_pred] at hu_r1_T2
  rw [h_r2_pred] at hu_r2_T3
  rw [h_blob_pred] at hu_blob_rd
  rw [h_rd_pred] at hu_blob_rd
  clear h_r0_pred h_r1_pred h_r2_pred h_blob_pred h_rd_pred
        h_r0 h_r1 h_r2 h_blob h_rd
        hd_r0_T1 hd_r1_T2 hd_r2_T3 hd_blob_rd
  have hcr_regs := hcompat.regs
  have hcm_mem := hcompat.mem
  have hd_PR_regs := hd_PR.regs
  have hd_PR_mem := hd_PR.mem
  -- Climb register/mem/returnData values up to `h_P`.
  have h_P_regs_r0 : h_P.regs .r0 = some r0Old := by
    rw [← hu_r0_T1]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_regs_r1 : h_P.regs .r1 = some r1V := by
    rw [← hu_r0_T1,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r1 ≠ Reg.r0)),
        ← hu_r1_T2]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_regs_r2 : h_P.regs .r2 = some r2V := by
    rw [← hu_r0_T1,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r2 ≠ Reg.r0)),
        ← hu_r1_T2,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r2 ≠ Reg.r1)),
        ← hu_r2_T3]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_mem_blob (i : Nat) (hi : i < r2V) :
      h_P.mem (r1V + i) = some (inputBlob.get! i).toNat := by
    have hlt : i < inputBlob.size := by rw [hsize]; exact hi
    rw [← hu_r0_T1,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _),
        ← hu_r1_T2,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _),
        ← hu_r2_T3,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _),
        ← hu_blob_rd]
    exact PartialState.union_mem_of_left_some
      (PartialState.singletonMemBytes_mem_at r1V inputBlob i hlt)
  have h_P_returnData : h_P.returnData = some rdOld := by
    rw [← hu_r0_T1,
        PartialState.union_returnData_of_left_none PartialState.singletonReg_returnData,
        ← hu_r1_T2,
        PartialState.union_returnData_of_left_none PartialState.singletonReg_returnData,
        ← hu_r2_T3,
        PartialState.union_returnData_of_left_none PartialState.singletonReg_returnData,
        ← hu_blob_rd,
        PartialState.union_returnData_of_left_none PartialState.singletonMemBytes_returnData]
    exact PartialState.singletonReturnData_returnData_self
  have h_P_cs_pre : h_P.callStack = none := by
    rw [← hu_r0_T1,
        PartialState.union_callStack_of_left_none PartialState.singletonReg_callStack,
        ← hu_r1_T2,
        PartialState.union_callStack_of_left_none PartialState.singletonReg_callStack,
        ← hu_r2_T3,
        PartialState.union_callStack_of_left_none PartialState.singletonReg_callStack,
        ← hu_blob_rd,
        PartialState.union_callStack_of_left_none PartialState.singletonMemBytes_callStack]
    exact PartialState.singletonReturnData_callStack
  -- Lift to `hp`, then to `s` via compat.
  have hp_regs_r0 : hp.regs .r0 = some r0Old := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r0
  have hp_regs_r1 : hp.regs .r1 = some r1V := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r1
  have hp_regs_r2 : hp.regs .r2 = some r2V := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r2
  have hs_regs_r1 : s.regs.get .r1 = r1V := hcr_regs .r1 r1V hp_regs_r1
  have hs_regs_r2 : s.regs.get .r2 = r2V := hcr_regs .r2 r2V hp_regs_r2
  have hs_r1_field : s.regs.r1 = r1V := hs_regs_r1
  have hs_r2_field : s.regs.r2 = r2V := hs_regs_r2
  have hp_mem_blob (i : Nat) (hi : i < r2V) :
      hp.mem (r1V + i) = some (inputBlob.get! i).toNat := by
    rw [← hu_PR]; exact PartialState.union_mem_of_left_some (h_P_mem_blob i hi)
  have hs_mem_blob (i : Nat) (hi : i < r2V) :
      s.mem (r1V + i) = (inputBlob.get! i).toNat := hcm_mem _ _ (hp_mem_blob i hi)
  -- The `readBytes`↔blob bridge: the input slice recovers `inputBlob`.
  have h_readBytes : readBytes s.mem r1V r2V = inputBlob := by
    apply readBytes_eq_of_match s.mem r1V r2V inputBlob hsize
    intro i hi
    rw [hs_mem_blob i hi]
    exact Nat.mod_eq_of_lt (inputBlob.get! i).toNat_lt
  -- Branch dischargers (in `execSet`'s check order: length limit, then guardRead).
  have hr2le : s.regs.r2 ≤ MAX_RETURN_DATA := by rw [hs_r2_field]; exact hlen
  have hcontains : s.regions.containsRange s.regs.r1 s.regs.r2 = true := by
    rw [hs_r1_field, hs_r2_field]; exact h_region
  have hfetch : fetch s.pc = some (.call .sol_set_return_data) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hstep_eq : executeFn fetch s 1 =
      chargeCu (step (.call .sol_set_return_data) s) := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch, executeFn_zero]
  have hexec_regs : (executeFn fetch s 1).regs = s.regs.set .r0 0 := by
    rw [hstep_eq]
    show (ReturnData.execSet s).regs = s.regs.set .r0 0
    simp only [ReturnData.execSet, State.guardRead,
      if_neg (Nat.not_lt.mpr hr2le), if_pos (Or.inr hcontains)]
  have hexec_mem : (executeFn fetch s 1).mem = s.mem := by
    rw [hstep_eq]
    show (ReturnData.execSet s).mem = s.mem
    simp only [ReturnData.execSet, State.guardRead,
      if_neg (Nat.not_lt.mpr hr2le), if_pos (Or.inr hcontains)]
  have hexec_pc : (executeFn fetch s 1).pc = s.pc + 1 := by
    rw [hstep_eq]; rfl
  have hexec_exit : (executeFn fetch s 1).exitCode = none := by
    rw [hstep_eq]
    show (ReturnData.execSet s).exitCode = none
    simp only [ReturnData.execSet, State.guardRead,
      if_neg (Nat.not_lt.mpr hr2le), if_pos (Or.inr hcontains)]
    exact hex
  have hexec_rd : (executeFn fetch s 1).returnData = inputBlob := by
    rw [hstep_eq]
    show (ReturnData.execSet s).returnData = inputBlob
    simp only [ReturnData.execSet, State.guardRead,
      if_neg (Nat.not_lt.mpr hr2le), if_pos (Or.inr hcontains)]
    rw [hs_r1_field, hs_r2_field]; exact h_readBytes
  have hexec_cs : (executeFn fetch s 1).callStack = s.callStack := by
    rw [hstep_eq]
    show (ReturnData.execSet s).callStack = s.callStack
    simp only [ReturnData.execSet, State.guardRead,
      if_neg (Nat.not_lt.mpr hr2le), if_pos (Or.inr hcontains)]
  have hexec_cu : (executeFn fetch s 1).cuConsumed ≤ s.cuConsumed + 1 + nCu := by
    rw [hstep_eq]
    show (step (.call .sol_set_return_data) s).cuConsumed + 1 ≤ s.cuConsumed + 1 + nCu
    have := hCu s; omega
  -- Frame facts: `h_R` owns none of P's atoms.
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
    rcases hd_PR.returnData with hl | hr
    · rw [h_P_returnData] at hl; nomatch hl
    · exact hr
  have h_R_no_mem_blob (i : Nat) (hi : i < r2V) : h_R.mem (r1V + i) = none := by
    rcases hd_PR_mem (r1V + i) with hl | hr
    · rw [h_P_mem_blob i hi] at hl; nomatch hl
    · exact hr
  -- Build the post heap.
  let h_r0_new : PartialState := PartialState.singletonReg .r0 0
  let h_r1_new : PartialState := PartialState.singletonReg .r1 r1V
  let h_r2_new : PartialState := PartialState.singletonReg .r2 r2V
  let h_blob_new : PartialState := PartialState.singletonMemBytes r1V inputBlob
  let h_rd_new : PartialState := PartialState.singletonReturnData inputBlob
  let h_T3_new : PartialState := h_blob_new.union h_rd_new
  let h_T2_new : PartialState := h_r2_new.union h_T3_new
  let h_T1_new : PartialState := h_r1_new.union h_T2_new
  let h_P_new : PartialState := h_r0_new.union h_T1_new
  have hd_blob_rd_new : h_blob_new.Disjoint h_rd_new :=
    { regs := fun r => Or.inl (PartialState.singletonMemBytes_regs r)
      mem  := fun a => Or.inr (PartialState.singletonReturnData_mem a)
      pc   := Or.inl PartialState.singletonMemBytes_pc
      returnData := Or.inl PartialState.singletonMemBytes_returnData
      callStack := Or.inl PartialState.singletonMemBytes_callStack }
  have hd_r2_T3_new : h_r2_new.Disjoint h_T3_new := by
    refine ⟨fun r => ?_, fun a => Or.inl (PartialState.singletonReg_mem a),
            Or.inl PartialState.singletonReg_pc,
            Or.inl PartialState.singletonReg_returnData,
            Or.inl PartialState.singletonReg_callStack⟩
    by_cases hr : r = .r2
    · right; rw [hr]
      show (h_blob_new.union h_rd_new).regs .r2 = none
      rw [PartialState.union_regs_of_left_none (PartialState.singletonMemBytes_regs .r2)]
      exact PartialState.singletonReturnData_regs .r2
    · left; exact PartialState.singletonReg_regs_other hr
  have hd_r1_T2_new : h_r1_new.Disjoint h_T2_new := by
    refine ⟨fun r => ?_, fun a => Or.inl (PartialState.singletonReg_mem a),
            Or.inl PartialState.singletonReg_pc,
            Or.inl PartialState.singletonReg_returnData,
            Or.inl PartialState.singletonReg_callStack⟩
    by_cases hr : r = .r1
    · right; rw [hr]
      show (h_r2_new.union h_T3_new).regs .r1 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r1 ≠ Reg.r2))]
      show (h_blob_new.union h_rd_new).regs .r1 = none
      rw [PartialState.union_regs_of_left_none (PartialState.singletonMemBytes_regs .r1)]
      exact PartialState.singletonReturnData_regs .r1
    · left; exact PartialState.singletonReg_regs_other hr
  have hd_r0_T1_new : h_r0_new.Disjoint h_T1_new := by
    refine ⟨fun r => ?_, fun a => Or.inl (PartialState.singletonReg_mem a),
            Or.inl PartialState.singletonReg_pc,
            Or.inl PartialState.singletonReg_returnData,
            Or.inl PartialState.singletonReg_callStack⟩
    by_cases hr : r = .r0
    · right; rw [hr]
      show (h_r1_new.union h_T2_new).regs .r0 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r0 ≠ Reg.r1))]
      show (h_r2_new.union h_T3_new).regs .r0 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r0 ≠ Reg.r2))]
      show (h_blob_new.union h_rd_new).regs .r0 = none
      rw [PartialState.union_regs_of_left_none (PartialState.singletonMemBytes_regs .r0)]
      exact PartialState.singletonReturnData_regs .r0
    · left; exact PartialState.singletonReg_regs_other hr
  -- Project `h_P_new`.
  have h_P_new_regs_r0 : h_P_new.regs .r0 = some 0 :=
    PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_new_regs_r1 : h_P_new.regs .r1 = some r1V := by
    show (h_r0_new.union h_T1_new).regs .r1 = some r1V
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r1 ≠ Reg.r0))]
    show (h_r1_new.union h_T2_new).regs .r1 = some r1V
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_new_regs_r2 : h_P_new.regs .r2 = some r2V := by
    show (h_r0_new.union h_T1_new).regs .r2 = some r2V
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r2 ≠ Reg.r0))]
    show (h_r1_new.union h_T2_new).regs .r2 = some r2V
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r2 ≠ Reg.r1))]
    show (h_r2_new.union h_T3_new).regs .r2 = some r2V
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_new_regs_other (r : Reg)
      (h0 : r ≠ .r0) (h1 : r ≠ .r1) (h2 : r ≠ .r2) :
      h_P_new.regs r = none := by
    show (h_r0_new.union h_T1_new).regs r = none
    rw [PartialState.union_regs_of_left_none (PartialState.singletonReg_regs_other h0)]
    show (h_r1_new.union h_T2_new).regs r = none
    rw [PartialState.union_regs_of_left_none (PartialState.singletonReg_regs_other h1)]
    show (h_r2_new.union h_T3_new).regs r = none
    rw [PartialState.union_regs_of_left_none (PartialState.singletonReg_regs_other h2)]
    show (h_blob_new.union h_rd_new).regs r = none
    rw [PartialState.union_regs_of_left_none (PartialState.singletonMemBytes_regs r)]
    exact PartialState.singletonReturnData_regs r
  have h_P_new_mem_at_blob (i : Nat) (hi : i < r2V) :
      h_P_new.mem (r1V + i) = some (inputBlob.get! i).toNat := by
    have hlt : i < inputBlob.size := by rw [hsize]; exact hi
    show (h_r0_new.union h_T1_new).mem (r1V + i) = _
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    show (h_r1_new.union h_T2_new).mem (r1V + i) = _
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    show (h_r2_new.union h_T3_new).mem (r1V + i) = _
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    show (h_blob_new.union h_rd_new).mem (r1V + i) = _
    exact PartialState.union_mem_of_left_some
      (PartialState.singletonMemBytes_mem_at r1V inputBlob i hlt)
  have h_P_new_mem_outside (a : Nat) (h : a < r1V ∨ a ≥ r1V + r2V) :
      h_P_new.mem a = none := by
    have hsz : a < r1V ∨ a ≥ r1V + inputBlob.size := by rw [hsize]; exact h
    show (h_r0_new.union h_T1_new).mem a = none
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
    show (h_r1_new.union h_T2_new).mem a = none
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
    show (h_r2_new.union h_T3_new).mem a = none
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
    show (h_blob_new.union h_rd_new).mem a = none
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonMemBytes_mem_outside r1V inputBlob a hsz)]
    exact PartialState.singletonReturnData_mem a
  have h_P_new_returnData : h_P_new.returnData = some inputBlob := by
    show (h_r0_new.union h_T1_new).returnData = some inputBlob
    rw [PartialState.union_returnData_of_left_none PartialState.singletonReg_returnData]
    show (h_r1_new.union h_T2_new).returnData = some inputBlob
    rw [PartialState.union_returnData_of_left_none PartialState.singletonReg_returnData]
    show (h_r2_new.union h_T3_new).returnData = some inputBlob
    rw [PartialState.union_returnData_of_left_none PartialState.singletonReg_returnData]
    show (h_blob_new.union h_rd_new).returnData = some inputBlob
    rw [PartialState.union_returnData_of_left_none PartialState.singletonMemBytes_returnData]
    exact PartialState.singletonReturnData_returnData_self
  have h_P_new_pc : h_P_new.pc = none := by
    show (h_r0_new.union h_T1_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    show (h_r1_new.union h_T2_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    show (h_r2_new.union h_T3_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    show (h_blob_new.union h_rd_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonMemBytes_pc]
    exact PartialState.singletonReturnData_pc
  have h_P_new_cs : h_P_new.callStack = none := by
    show (h_r0_new.union h_T1_new).callStack = none
    rw [PartialState.union_callStack_of_left_none PartialState.singletonReg_callStack]
    show (h_r1_new.union h_T2_new).callStack = none
    rw [PartialState.union_callStack_of_left_none PartialState.singletonReg_callStack]
    show (h_r2_new.union h_T3_new).callStack = none
    rw [PartialState.union_callStack_of_left_none PartialState.singletonReg_callStack]
    show (h_blob_new.union h_rd_new).callStack = none
    rw [PartialState.union_callStack_of_left_none PartialState.singletonMemBytes_callStack]
    exact PartialState.singletonReturnData_callStack
  -- Outer disjointness `h_P_new ⫫ h_R`.
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
          have heq : a = r1V + (a - r1V) := by omega
          have hlt : a - r1V < r2V := by omega
          rw [heq]; exact h_R_no_mem_blob _ hlt
        · left
          apply h_P_new_mem_outside
          rcases Nat.lt_or_ge a r1V with h | h
          · left; exact h
          · rcases Nat.lt_or_ge a (r1V + r2V) with h' | h'
            · exact absurd ⟨h, h'⟩ ha
            · right; exact h'
      pc := Or.inl h_P_new_pc
      returnData := Or.inr h_R_no_rd
      callStack := Or.inl h_P_new_cs }
  refine ⟨1, Nat.le_refl 1, ?_, hexec_exit, hexec_cu, ?_⟩
  · rw [hexec_pc, hpc]
  · refine ⟨h_P_new.union h_R, ?_, h_P_new, h_R, hd_PnewR, rfl,
            ⟨h_r0_new, h_T1_new, hd_r0_T1_new, rfl, rfl,
             h_r1_new, h_T2_new, hd_r1_T2_new, rfl, rfl,
             h_r2_new, h_T3_new, hd_r2_T3_new, rfl, rfl,
             h_blob_new, h_rd_new, hd_blob_rd_new, rfl, rfl, rfl⟩,
            h_R_sat⟩
    refine { regs := ?_, mem := ?_, pc := ?_, returnData := ?_, callStack := ?_ }
    · intro r v hvr
      by_cases h0 : r = .r0
      · rw [h0] at hvr
        rw [PartialState.union_regs_of_left_some h_P_new_regs_r0] at hvr
        have hv0 : v = 0 := (Option.some.inj hvr).symm
        rw [h0, hexec_regs, hv0]
        exact RegFile.get_set_self _ _ _ (by decide : (.r0 : Reg) ≠ .r10)
      by_cases h1 : r = .r1
      · rw [h1] at hvr
        rw [PartialState.union_regs_of_left_some h_P_new_regs_r1] at hvr
        have hv1 : v = r1V := (Option.some.inj hvr).symm
        rw [h1, hexec_regs, hv1,
            RegFile.get_set_diff _ _ _ _ (by decide : (.r1 : Reg) ≠ .r0)]
        exact hs_regs_r1
      by_cases h2 : r = .r2
      · rw [h2] at hvr
        rw [PartialState.union_regs_of_left_some h_P_new_regs_r2] at hvr
        have hv2 : v = r2V := (Option.some.inj hvr).symm
        rw [h2, hexec_regs, hv2,
            RegFile.get_set_diff _ _ _ _ (by decide : (.r2 : Reg) ≠ .r0)]
        exact hs_regs_r2
      · rw [PartialState.union_regs_of_left_none
              (h_P_new_regs_other r h0 h1 h2)] at hvr
        rw [hexec_regs, RegFile.get_set_diff _ _ _ _ h0]
        have h_P_none : h_P.regs r = none := by
          rcases hd_PR_regs r with hl | hr
          · exact hl
          · rw [hr] at hvr; nomatch hvr
        apply hcr_regs r v
        rw [← hu_PR, PartialState.union_regs_of_left_none h_P_none]
        exact hvr
    · intro a v hva
      rw [hexec_mem]
      by_cases ha : r1V ≤ a ∧ a < r1V + r2V
      · obtain ⟨hlo, hhi⟩ := ha
        have heq : a = r1V + (a - r1V) := by omega
        have hlt : a - r1V < r2V := by omega
        rw [heq] at hva ⊢
        rw [PartialState.union_mem_of_left_some (h_P_new_mem_at_blob _ hlt)] at hva
        have hveq : v = (inputBlob.get! (a - r1V)).toNat := (Option.some.inj hva).symm
        rw [hveq]; exact hs_mem_blob _ hlt
      · have h_out : a < r1V ∨ a ≥ r1V + r2V := by
          rcases Nat.lt_or_ge a r1V with h | h
          · left; exact h
          · rcases Nat.lt_or_ge a (r1V + r2V) with h' | h'
            · exact absurd ⟨h, h'⟩ ha
            · right; exact h'
        rw [PartialState.union_mem_of_left_none (h_P_new_mem_outside a h_out)] at hva
        have h_P_none : h_P.mem a = none := by
          rcases hd_PR_mem a with hl | hr
          · exact hl
          · rw [hr] at hva; nomatch hva
        apply hcm_mem a v
        rw [← hu_PR, PartialState.union_mem_of_left_none h_P_none]
        exact hva
    · intro v hvp
      rw [PartialState.union_pc_of_left_none h_P_new_pc] at hvp
      rw [h_R_no_pc] at hvp; nomatch hvp
    · intro rd hva
      rw [PartialState.union_returnData_of_left_some h_P_new_returnData] at hva
      rw [hexec_rd]
      exact Option.some.inj hva
    · intro cs hva
      rw [PartialState.union_callStack_of_left_none h_P_new_cs] at hva
      have hp_cs : hp.callStack = some cs := by
        rw [← hu_PR, PartialState.union_callStack_of_left_none h_P_cs_pre]
        exact hva
      rw [hexec_cs]
      exact hcompat.callStack cs hp_cs



/-! ## H6 OOB-fault triple — `sol_set_return_data` (register-sized region)

The first two-register region in the OOB family: the guarded input slice is
`[r1, r1+r2)`, so the pre pins BOTH `r1` and `r2` and the region requirement
mentions both values. The `r2V` side conditions (≤ cap, ≠ 0) are theorem
hypotheses — the emitter instantiates them at the traced literal via
`by decide`. -/
theorem call_sol_set_return_data_faults_oob_spec (r1V r2V : Nat)
    (hle : r2V ≤ MAX_RETURN_DATA) (hne : r2V ≠ 0) (pc : Nat) (nCu : Nat)
    (hCu : ∀ s : State,
        (step (.call .sol_set_return_data) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleFaultsWithinMem 1 nCu pc
      (CodeReq.singleton pc (.call .sol_set_return_data))
      ((.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V))
      (fun rt => rt.containsRange r1V r2V = false)
      .accessViolation := by
  intro R hRfree fetch hcr s hPR hpc hex hbud h_region
  obtain ⟨hp, hcompat, h_P, h_R, hd_PR, hu_PR, h_P_sat, h_R_sat⟩ := hPR
  obtain ⟨h_r1, h_r2, hd_r1_r2, hu_r1_r2, h_r1_pred, h_r2_pred⟩ := h_P_sat
  rw [h_r1_pred] at hu_r1_r2
  rw [h_r2_pred] at hu_r1_r2
  have hcr_regs := hcompat.regs
  have h_P_regs_r1 : h_P.regs .r1 = some r1V := by
    rw [← hu_r1_r2]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_regs_r2 : h_P.regs .r2 = some r2V := by
    rw [← hu_r1_r2,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r2 ≠ Reg.r1))]
    exact PartialState.singletonReg_regs_self
  have hp_regs_r1 : hp.regs .r1 = some r1V := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r1
  have hp_regs_r2 : hp.regs .r2 = some r2V := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r2
  have hr1 : s.regs.r1 = r1V := hcr_regs .r1 r1V hp_regs_r1
  have hr2 : s.regs.r2 = r2V := hcr_regs .r2 r2V hp_regs_r2
  have hoob : s.regions.containsRange s.regs.r1 s.regs.r2 = false := by
    rw [hr1, hr2]; exact h_region
  have hle' : s.regs.r2 ≤ MAX_RETURN_DATA := by rw [hr2]; exact hle
  have hne' : s.regs.r2 ≠ 0 := by rw [hr2]; exact hne
  have hfetch : fetch s.pc = some (.call .sol_set_return_data) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hstep_eq : executeFn fetch s 1
      = chargeCu (step (.call .sol_set_return_data) s) := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch, executeFn_zero]
  have hexec : executeFn fetch s 1 =
      chargeCu { (ReturnData.execSet s) with
                 pc := s.pc + 1
                 cuConsumed := (ReturnData.execSet s).cuConsumed
                   + syscallCu .sol_set_return_data s } := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch, executeFn_zero]
    simp only [step, execSyscall]
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_⟩
  · rw [hexec]
    show (ReturnData.execSet s).exitCode = some VmError.accessViolation.toSentinel
    exact ReturnData.execSet_faults_oob_exitCode s hle' hne' hoob
  · rw [hexec]
    show (ReturnData.execSet s).vmError = some .accessViolation
    exact ReturnData.execSet_faults_oob s hle' hne' hoob
  · rw [hstep_eq]
    show (step (.call .sol_set_return_data) s).cuConsumed + 1
      ≤ s.cuConsumed + 1 + nCu
    have := hCu s; omega

end SVM.SBPF
