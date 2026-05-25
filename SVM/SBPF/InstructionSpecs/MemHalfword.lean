import SVM.SBPF.InstructionSpecs.MemDwordLoad

namespace SVM.SBPF

open Memory

/-! ## Memory loads/stores — halfword width

Narrower-width analog of dword specs. Two bytes (`u16`) instead of
eight, so mem compat case-analysis is 3-way (2 in-range + outside)
vs dword's 9-way. -/

/-- `ldx .half dst src off`: load 16-bit value at `[src + off]` into `dst`. -/
theorem ldxh_spec
    (dst src : Reg) (off : Int) (vOldDst baseAddr v : Nat) (pc : Nat)
    (hne : dst ≠ .r10) (hv : v < 2 ^ 16) :
    cuTripleWithinMem 1 pc (pc + 1)
      (CodeReq.singleton pc (.ldx .half dst src off))
      ((dst ↦ᵣ vOldDst) ** (src ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr off ↦U16 v))
      ((dst ↦ᵣ v) ** (src ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr off ↦U16 v))
      (fun rt => rt.containsRange (effectiveAddr baseAddr off) 2 = true) := by
  intro R hRfree fetch hcr s hPR hpc hex h_region
  obtain ⟨hp, hcompat, h_P, h_R, hd_PR, hu_PR, h_P_sat, h_R_sat⟩ := hPR
  obtain ⟨h_dst, h_SM, hd_dst_SM, hu_dst_SM, h_dst_pred, h_SM_sat⟩ := h_P_sat
  obtain ⟨h_src, h_mem, hd_src_mem, hu_src_mem, h_src_pred, h_mem_pred⟩ := h_SM_sat
  rw [h_src_pred] at hu_src_mem hd_src_mem
  rw [h_mem_pred] at hu_src_mem hd_src_mem
  rw [h_dst_pred] at hu_dst_SM hd_dst_SM
  clear h_src_pred h_mem_pred h_dst_pred h_src h_mem h_dst
  have hcr_regs := hcompat.regs
  have hcm_mem := hcompat.mem
  have hne_dst_src : dst ≠ src := by
    have hd_dst_SM_regs := hd_dst_SM.regs
    intro habs
    rcases hd_dst_SM_regs dst with hl | hr
    · rw [PartialState.singletonReg_regs_self] at hl; nomatch hl
    · rw [← hu_src_mem] at hr
      have : ((PartialState.singletonReg src baseAddr).union
              (PartialState.singletonMemU16 (effectiveAddr baseAddr off) v)).regs dst
              = some baseAddr := by
        rw [habs]
        exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
      rw [this] at hr; nomatch hr
  have h_SM_regs_src : h_SM.regs src = some baseAddr := by
    rw [← hu_src_mem]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_SM_mem_0 :
      h_SM.mem (effectiveAddr baseAddr off) = some (v % 256) := by
    rw [← hu_src_mem,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact PartialState.singletonMemU16_mem_0 _ _
  have h_SM_mem_1 :
      h_SM.mem (effectiveAddr baseAddr off + 1) = some (v / 0x100 % 256) := by
    rw [← hu_src_mem,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact PartialState.singletonMemU16_mem_1 _ _
  have h_P_regs_dst : h_P.regs dst = some vOldDst := by
    rw [← hu_dst_SM]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_regs_src : h_P.regs src = some baseAddr := by
    rw [← hu_dst_SM,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other hne_dst_src.symm)]
    exact h_SM_regs_src
  have h_P_mem_0 : h_P.mem (effectiveAddr baseAddr off) = some (v % 256) := by
    rw [← hu_dst_SM,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact h_SM_mem_0
  have h_P_mem_1 :
      h_P.mem (effectiveAddr baseAddr off + 1) = some (v / 0x100 % 256) := by
    rw [← hu_dst_SM,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact h_SM_mem_1
  have hp_regs_dst : hp.regs dst = some vOldDst := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_dst
  have hp_regs_src : hp.regs src = some baseAddr := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_src
  have hp_mem_0 : hp.mem (effectiveAddr baseAddr off) = some (v % 256) := by
    rw [← hu_PR]; exact PartialState.union_mem_of_left_some h_P_mem_0
  have hp_mem_1 : hp.mem (effectiveAddr baseAddr off + 1) = some (v / 0x100 % 256) := by
    rw [← hu_PR]; exact PartialState.union_mem_of_left_some h_P_mem_1
  have hs_regs_src : s.regs.get src = baseAddr := hcr_regs src baseAddr hp_regs_src
  have hs_mem_0 : s.mem (effectiveAddr baseAddr off) = v % 256 :=
    hcm_mem _ _ hp_mem_0
  have hs_mem_1 : s.mem (effectiveAddr baseAddr off + 1) = v / 0x100 % 256 :=
    hcm_mem _ _ hp_mem_1
  have h_readU16 : Memory.readU16 s.mem (effectiveAddr baseAddr off) = v :=
    readU16_eq_of_bytes_match hv hs_mem_0 hs_mem_1
  have hfetch : fetch s.pc = some (.ldx .half dst src off) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hexec : executeFn fetch s 1 =
      { s with regs := s.regs.set dst v, pc := s.pc + 1 } := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch,
        executeFn_zero]
    simp only [step, hs_regs_src, Width.bytes, if_pos h_region,
               Memory.readByWidth, h_readU16]
  have hd_PR_regs := hd_PR.regs
  have hd_PR_mem := hd_PR.mem
  have h_R_no_dst : h_R.regs dst = none := by
    rcases hd_PR_regs dst with hl | hr
    · rw [h_P_regs_dst] at hl; nomatch hl
    · exact hr
  have h_R_no_src : h_R.regs src = none := by
    rcases hd_PR_regs src with hl | hr
    · rw [h_P_regs_src] at hl; nomatch hl
    · exact hr
  have h_R_no_mem_0 : h_R.mem (effectiveAddr baseAddr off) = none := by
    rcases hd_PR_mem _ with hl | hr
    · rw [h_P_mem_0] at hl; nomatch hl
    · exact hr
  have h_R_no_mem_1 : h_R.mem (effectiveAddr baseAddr off + 1) = none := by
    rcases hd_PR_mem _ with hl | hr
    · rw [h_P_mem_1] at hl; nomatch hl
    · exact hr
  have h_R_no_pc : h_R.pc = none := hRfree _ h_R_sat
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_⟩
  · rw [hexec]; show s.pc + 1 = pc + 1; rw [hpc]
  · rw [hexec]; exact hex
  · rw [hexec]
    refine ⟨_, ?_,
            (PartialState.singletonReg dst v).union
              ((PartialState.singletonReg src baseAddr).union
                (PartialState.singletonMemU16 (effectiveAddr baseAddr off) v)),
            h_R, ?_, rfl,
            ⟨PartialState.singletonReg dst v,
             (PartialState.singletonReg src baseAddr).union
              (PartialState.singletonMemU16 (effectiveAddr baseAddr off) v),
             ?_, rfl, rfl,
             ⟨PartialState.singletonReg src baseAddr,
              PartialState.singletonMemU16 (effectiveAddr baseAddr off) v,
              hd_src_mem, rfl, rfl, rfl⟩⟩,
            h_R_sat⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro r vr hvr
        show (s.regs.set dst v).get r = vr
        by_cases hrdst : r = dst
        · rw [hrdst] at hvr
          have h_inner :
              ((PartialState.singletonReg dst v).union
                ((PartialState.singletonReg src baseAddr).union
                  (PartialState.singletonMemU16 (effectiveAddr baseAddr off) v))).regs dst
              = some v :=
            PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
          rw [PartialState.union_regs_of_left_some h_inner] at hvr
          have : vr = v := (Option.some.inj hvr).symm
          rw [hrdst, this]
          exact RegFile.get_set_self _ _ _ hne
        · rw [RegFile.get_set_diff _ _ _ _ hrdst]
          by_cases hrsrc : r = src
          · rw [hrsrc] at hvr
            have h_inner :
                ((PartialState.singletonReg dst v).union
                  ((PartialState.singletonReg src baseAddr).union
                    (PartialState.singletonMemU16 (effectiveAddr baseAddr off) v))).regs src
                = some baseAddr := by
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hne_dst_src.symm)]
              exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
            rw [PartialState.union_regs_of_left_some h_inner] at hvr
            have : vr = baseAddr := (Option.some.inj hvr).symm
            rw [hrsrc, this]
            exact hcr_regs src baseAddr hp_regs_src
          · have h_outer_h1_none :
                ((PartialState.singletonReg dst v).union
                  ((PartialState.singletonReg src baseAddr).union
                    (PartialState.singletonMemU16 (effectiveAddr baseAddr off) v))).regs r
                = none := by
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrdst)]
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrsrc)]
              exact PartialState.singletonMemU16_regs r
            rw [PartialState.union_regs_of_left_none h_outer_h1_none] at hvr
            apply hcr_regs r vr
            have h_P_none : h_P.regs r = none := by
              rw [← hu_dst_SM]
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrdst)]
              rw [← hu_src_mem]
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrsrc)]
              exact PartialState.singletonMemU16_regs r
            rw [← hu_PR]
            rw [PartialState.union_regs_of_left_none h_P_none]
            exact hvr
      · intro a vm hvm
        show s.mem a = vm
        by_cases ha0 : a = effectiveAddr baseAddr off
        · rw [ha0] at hvm ⊢
          have h_inner :
              ((PartialState.singletonReg dst v).union
                ((PartialState.singletonReg src baseAddr).union
                  (PartialState.singletonMemU16 (effectiveAddr baseAddr off) v))).mem
                  (effectiveAddr baseAddr off) = some (v % 256) := by
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            exact PartialState.singletonMemU16_mem_0 _ _
          rw [PartialState.union_mem_of_left_some h_inner] at hvm
          have : vm = v % 256 := (Option.some.inj hvm).symm
          rw [this]; exact hs_mem_0
        · by_cases ha1 : a = effectiveAddr baseAddr off + 1
          · rw [ha1] at hvm ⊢
            have h_inner :
                ((PartialState.singletonReg dst v).union
                  ((PartialState.singletonReg src baseAddr).union
                    (PartialState.singletonMemU16 (effectiveAddr baseAddr off) v))).mem
                    (effectiveAddr baseAddr off + 1) = some (v / 0x100 % 256) := by
              rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
              rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
              exact PartialState.singletonMemU16_mem_1 _ _
            rw [PartialState.union_mem_of_left_some h_inner] at hvm
            have : vm = v / 0x100 % 256 := (Option.some.inj hvm).symm
            rw [this]; exact hs_mem_1
          · have h_outer_none :
                ((PartialState.singletonReg dst v).union
                  ((PartialState.singletonReg src baseAddr).union
                    (PartialState.singletonMemU16 (effectiveAddr baseAddr off) v))).mem a
                = none := by
              rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
              rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
              exact PartialState.singletonMemU16_mem_outside _ _ a (by omega)
            rw [PartialState.union_mem_of_left_none h_outer_none] at hvm
            apply hcm_mem a vm
            have h_P_none : h_P.mem a = none := by
              rw [← hu_dst_SM]
              rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
              rw [← hu_src_mem]
              rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
              exact PartialState.singletonMemU16_mem_outside _ _ a (by omega)
            rw [← hu_PR]
            rw [PartialState.union_mem_of_left_none h_P_none]
            exact hvm
      · intro vp hvp
        have h_outer_pc :
            ((PartialState.singletonReg dst v).union
              ((PartialState.singletonReg src baseAddr).union
                (PartialState.singletonMemU16 (effectiveAddr baseAddr off) v))).pc = none := by
          rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
          rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
          exact PartialState.singletonMemU16_pc
        rw [PartialState.union_pc_of_left_none h_outer_pc] at hvp
        rw [h_R_no_pc] at hvp
        nomatch hvp
      · intro rd hva
        first
        | exact hcompat.returnData rd hva
        | (rw [PartialState.union_returnData_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.returnData rd
             (by rw [
                    ← hu_PR,
                    ← hu_dst_SM,
                    ← hu_src_mem,
                    PartialState.union_returnData_of_left_none (by first | rfl | simp)]
                 exact hva))
        | (rw [PartialState.union_returnData_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.returnData rd
             (by rw [
                    ← hu_PR,
                    ← hu_dst_SM,
                    ← hu_src_mem,
                    PartialState.union_returnData_of_left_none (by first | rfl | simp)]
                 exact hva))
        | (rw [PartialState.union_returnData_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.returnData rd (by rw [← hu_PR]; exact hva))
      · intro cs hva
        first
        | exact hcompat.callStack cs hva
        | (rw [PartialState.union_callStack_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.callStack cs
             (by rw [
                    ← hu_PR,
                    ← hu_dst_SM,
                    ← hu_src_mem,
                    PartialState.union_callStack_of_left_none (by first | rfl | simp)]
                 exact hva))
        | (rw [PartialState.union_callStack_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.callStack cs
             (by rw [
                    ← hu_PR,
                    ← hu_dst_SM,
                    ← hu_src_mem,
                    PartialState.union_callStack_of_left_none (by first | rfl | simp)]
                 exact hva))
        | (rw [PartialState.union_callStack_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.callStack cs (by rw [← hu_PR]; exact hva))
    · refine ⟨?_, ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
      · intro r
        by_cases hrdst : r = dst
        · rw [hrdst]; right; exact h_R_no_dst
        · by_cases hrsrc : r = src
          · rw [hrsrc]; right; exact h_R_no_src
          · left
            rw [PartialState.union_regs_of_left_none
                (PartialState.singletonReg_regs_other hrdst)]
            rw [PartialState.union_regs_of_left_none
                (PartialState.singletonReg_regs_other hrsrc)]
            exact PartialState.singletonMemU16_regs r
      · intro a
        by_cases ha0 : a = effectiveAddr baseAddr off
        · rw [ha0]; right; exact h_R_no_mem_0
        · by_cases ha1 : a = effectiveAddr baseAddr off + 1
          · rw [ha1]; right; exact h_R_no_mem_1
          · left
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            exact PartialState.singletonMemU16_mem_outside _ _ a (by omega)
      · left
        rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
        rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
        exact PartialState.singletonMemU16_pc
    · refine ⟨fun r => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
      · by_cases hrdst : r = dst
        · right
          rw [hrdst,
              PartialState.union_regs_of_left_none
                (PartialState.singletonReg_regs_other hne_dst_src)]
          exact PartialState.singletonMemU16_regs dst
        · left; exact PartialState.singletonReg_regs_other hrdst
      · left; exact PartialState.singletonReg_mem a
      · left; exact PartialState.singletonReg_pc

/-- `stx .half baseReg off valReg`: write valReg's low 16 bits at `[baseReg + off]`. -/
theorem stxh_spec
    (baseReg valReg : Reg) (off : Int)
    (baseAddr vSrc oldV : Nat) (pc : Nat) :
    cuTripleWithinMem 1 pc (pc + 1)
      (CodeReq.singleton pc (.stx .half baseReg off valReg))
      ((baseReg ↦ᵣ baseAddr) ** (valReg ↦ᵣ vSrc) **
        (effectiveAddr baseAddr off ↦U16 oldV))
      ((baseReg ↦ᵣ baseAddr) ** (valReg ↦ᵣ vSrc) **
        (effectiveAddr baseAddr off ↦U16 vSrc))
      (fun rt => rt.containsWritable (effectiveAddr baseAddr off) 2 = true) := by
  intro R hRfree fetch hcr s hPR hpc hex h_region
  obtain ⟨hp, hcompat, h_P, h_R, hd_PR, hu_PR, h_P_sat, h_R_sat⟩ := hPR
  obtain ⟨h_base, h_VM, hd_base_VM, hu_base_VM, h_base_pred, h_VM_sat⟩ := h_P_sat
  obtain ⟨h_val, h_mem, hd_val_mem, hu_val_mem, h_val_pred, h_mem_pred⟩ := h_VM_sat
  rw [h_val_pred] at hu_val_mem hd_val_mem
  rw [h_mem_pred] at hu_val_mem hd_val_mem
  rw [h_base_pred] at hu_base_VM hd_base_VM
  clear h_val_pred h_mem_pred h_base_pred h_val h_mem h_base
  have hcr_regs := hcompat.regs
  have hcm_mem := hcompat.mem
  have hne_base_val : baseReg ≠ valReg := by
    have hd_base_VM_regs := hd_base_VM.regs
    intro habs
    rcases hd_base_VM_regs baseReg with hl | hr
    · rw [PartialState.singletonReg_regs_self] at hl; nomatch hl
    · rw [← hu_val_mem] at hr
      have : ((PartialState.singletonReg valReg vSrc).union
              (PartialState.singletonMemU16 (effectiveAddr baseAddr off) oldV)).regs baseReg
              = some vSrc := by
        rw [habs]
        exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
      rw [this] at hr; nomatch hr
  have h_VM_regs_val : h_VM.regs valReg = some vSrc := by
    rw [← hu_val_mem]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_VM_mem_0 :
      h_VM.mem (effectiveAddr baseAddr off) = some (oldV % 256) := by
    rw [← hu_val_mem,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact PartialState.singletonMemU16_mem_0 _ _
  have h_VM_mem_1 :
      h_VM.mem (effectiveAddr baseAddr off + 1) = some (oldV / 0x100 % 256) := by
    rw [← hu_val_mem,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact PartialState.singletonMemU16_mem_1 _ _
  have h_P_regs_base : h_P.regs baseReg = some baseAddr := by
    rw [← hu_base_VM]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_regs_val : h_P.regs valReg = some vSrc := by
    rw [← hu_base_VM,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other hne_base_val.symm)]
    exact h_VM_regs_val
  have h_P_mem_0 :
      h_P.mem (effectiveAddr baseAddr off) = some (oldV % 256) := by
    rw [← hu_base_VM,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact h_VM_mem_0
  have h_P_mem_1 :
      h_P.mem (effectiveAddr baseAddr off + 1) = some (oldV / 0x100 % 256) := by
    rw [← hu_base_VM,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact h_VM_mem_1
  have hp_regs_base : hp.regs baseReg = some baseAddr := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_base
  have hp_regs_val : hp.regs valReg = some vSrc := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_val
  have hs_regs_base : s.regs.get baseReg = baseAddr :=
    hcr_regs baseReg baseAddr hp_regs_base
  have hs_regs_val : s.regs.get valReg = vSrc := hcr_regs valReg vSrc hp_regs_val
  have hfetch : fetch s.pc = some (.stx .half baseReg off valReg) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hexec : executeFn fetch s 1 =
      { s with mem := Memory.writeU16 s.mem (effectiveAddr baseAddr off) (vSrc % 2 ^ 16),
               pc := s.pc + 1 } := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch,
        executeFn_zero]
    simp only [step, hs_regs_base, Width.bytes, if_pos h_region,
               Memory.writeByWidth, hs_regs_val]
  have hd_PR_regs := hd_PR.regs
  have hd_PR_mem := hd_PR.mem
  have h_R_no_base : h_R.regs baseReg = none := by
    rcases hd_PR_regs baseReg with hl | hr
    · rw [h_P_regs_base] at hl; nomatch hl
    · exact hr
  have h_R_no_val : h_R.regs valReg = none := by
    rcases hd_PR_regs valReg with hl | hr
    · rw [h_P_regs_val] at hl; nomatch hl
    · exact hr
  have h_R_no_mem_0 : h_R.mem (effectiveAddr baseAddr off) = none := by
    rcases hd_PR_mem _ with hl | hr
    · rw [h_P_mem_0] at hl; nomatch hl
    · exact hr
  have h_R_no_mem_1 : h_R.mem (effectiveAddr baseAddr off + 1) = none := by
    rcases hd_PR_mem _ with hl | hr
    · rw [h_P_mem_1] at hl; nomatch hl
    · exact hr
  have h_R_no_pc : h_R.pc = none := hRfree _ h_R_sat
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_⟩
  · rw [hexec]; show s.pc + 1 = pc + 1; rw [hpc]
  · rw [hexec]; exact hex
  · rw [hexec]
    refine ⟨_, ?_,
            (PartialState.singletonReg baseReg baseAddr).union
              ((PartialState.singletonReg valReg vSrc).union
                (PartialState.singletonMemU16 (effectiveAddr baseAddr off) vSrc)),
            h_R, ?_, rfl,
            ⟨PartialState.singletonReg baseReg baseAddr,
             (PartialState.singletonReg valReg vSrc).union
              (PartialState.singletonMemU16 (effectiveAddr baseAddr off) vSrc),
             ?_, rfl, rfl,
             ⟨PartialState.singletonReg valReg vSrc,
              PartialState.singletonMemU16 (effectiveAddr baseAddr off) vSrc,
              ?_, rfl, rfl, rfl⟩⟩,
            h_R_sat⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro r vr hvr
        show s.regs.get r = vr
        by_cases hrbase : r = baseReg
        · rw [hrbase] at hvr
          have h_inner :
              ((PartialState.singletonReg baseReg baseAddr).union
                ((PartialState.singletonReg valReg vSrc).union
                  (PartialState.singletonMemU16 (effectiveAddr baseAddr off) vSrc))).regs baseReg
              = some baseAddr :=
            PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
          rw [PartialState.union_regs_of_left_some h_inner] at hvr
          have : vr = baseAddr := (Option.some.inj hvr).symm
          rw [hrbase, this]; exact hs_regs_base
        · by_cases hrval : r = valReg
          · rw [hrval] at hvr
            have h_inner :
                ((PartialState.singletonReg baseReg baseAddr).union
                  ((PartialState.singletonReg valReg vSrc).union
                    (PartialState.singletonMemU16 (effectiveAddr baseAddr off) vSrc))).regs valReg
                = some vSrc := by
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hne_base_val.symm)]
              exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
            rw [PartialState.union_regs_of_left_some h_inner] at hvr
            have : vr = vSrc := (Option.some.inj hvr).symm
            rw [hrval, this]; exact hs_regs_val
          · have h_outer_h1_none :
                ((PartialState.singletonReg baseReg baseAddr).union
                  ((PartialState.singletonReg valReg vSrc).union
                    (PartialState.singletonMemU16 (effectiveAddr baseAddr off) vSrc))).regs r
                = none := by
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrbase)]
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrval)]
              exact PartialState.singletonMemU16_regs r
            rw [PartialState.union_regs_of_left_none h_outer_h1_none] at hvr
            apply hcr_regs r vr
            have h_P_none : h_P.regs r = none := by
              rw [← hu_base_VM]
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrbase)]
              rw [← hu_val_mem]
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrval)]
              exact PartialState.singletonMemU16_regs r
            rw [← hu_PR]
            rw [PartialState.union_regs_of_left_none h_P_none]
            exact hvr
      · intro a vm hvm
        show (Memory.writeU16 s.mem (effectiveAddr baseAddr off) (vSrc % 2 ^ 16)) a = vm
        by_cases ha0 : a = effectiveAddr baseAddr off
        · rw [ha0] at hvm ⊢
          have h_inner :
              ((PartialState.singletonReg baseReg baseAddr).union
                ((PartialState.singletonReg valReg vSrc).union
                  (PartialState.singletonMemU16 (effectiveAddr baseAddr off) vSrc))).mem
                  (effectiveAddr baseAddr off) = some (vSrc % 256) := by
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            exact PartialState.singletonMemU16_mem_0 _ _
          rw [PartialState.union_mem_of_left_some h_inner] at hvm
          have : vm = vSrc % 256 := (Option.some.inj hvm).symm
          rw [this]
          unfold Memory.writeU16
          simp
        · by_cases ha1 : a = effectiveAddr baseAddr off + 1
          · rw [ha1] at hvm ⊢
            have h_inner :
                ((PartialState.singletonReg baseReg baseAddr).union
                  ((PartialState.singletonReg valReg vSrc).union
                    (PartialState.singletonMemU16 (effectiveAddr baseAddr off) vSrc))).mem
                    (effectiveAddr baseAddr off + 1) = some (vSrc / 0x100 % 256) := by
              rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
              rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
              exact PartialState.singletonMemU16_mem_1 _ _
            rw [PartialState.union_mem_of_left_some h_inner] at hvm
            have : vm = vSrc / 0x100 % 256 := (Option.some.inj hvm).symm
            rw [this]
            unfold Memory.writeU16
            simp [show effectiveAddr baseAddr off + 1 ≠ effectiveAddr baseAddr off from by omega]
            omega
          · have h_outer_none :
                ((PartialState.singletonReg baseReg baseAddr).union
                  ((PartialState.singletonReg valReg vSrc).union
                    (PartialState.singletonMemU16 (effectiveAddr baseAddr off) vSrc))).mem a
                = none := by
              rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
              rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
              exact PartialState.singletonMemU16_mem_outside _ _ a (by omega)
            rw [PartialState.union_mem_of_left_none h_outer_none] at hvm
            unfold Memory.writeU16
            simp only [Memory.Mem.read_put]
            rw [if_neg ha0, if_neg ha1]
            apply hcm_mem a vm
            have h_P_none : h_P.mem a = none := by
              rw [← hu_base_VM]
              rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
              rw [← hu_val_mem]
              rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
              exact PartialState.singletonMemU16_mem_outside _ _ a (by omega)
            rw [← hu_PR]
            rw [PartialState.union_mem_of_left_none h_P_none]
            exact hvm
      · intro vp hvp
        have h_outer_pc :
            ((PartialState.singletonReg baseReg baseAddr).union
              ((PartialState.singletonReg valReg vSrc).union
                (PartialState.singletonMemU16 (effectiveAddr baseAddr off) vSrc))).pc = none := by
          rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
          rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
          exact PartialState.singletonMemU16_pc
        rw [PartialState.union_pc_of_left_none h_outer_pc] at hvp
        rw [h_R_no_pc] at hvp
        nomatch hvp
      · intro rd hva
        first
        | exact hcompat.returnData rd hva
        | (rw [PartialState.union_returnData_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.returnData rd
             (by rw [
                    ← hu_PR,
                    ← hu_base_VM,
                    ← hu_val_mem,
                    PartialState.union_returnData_of_left_none (by first | rfl | simp)]
                 exact hva))
        | (rw [PartialState.union_returnData_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.returnData rd
             (by rw [
                    ← hu_PR,
                    ← hu_base_VM,
                    ← hu_val_mem,
                    PartialState.union_returnData_of_left_none (by first | rfl | simp)]
                 exact hva))
        | (rw [PartialState.union_returnData_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.returnData rd (by rw [← hu_PR]; exact hva))
      · intro cs hva
        first
        | exact hcompat.callStack cs hva
        | (rw [PartialState.union_callStack_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.callStack cs
             (by rw [
                    ← hu_PR,
                    ← hu_base_VM,
                    ← hu_val_mem,
                    PartialState.union_callStack_of_left_none (by first | rfl | simp)]
                 exact hva))
        | (rw [PartialState.union_callStack_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.callStack cs
             (by rw [
                    ← hu_PR,
                    ← hu_base_VM,
                    ← hu_val_mem,
                    PartialState.union_callStack_of_left_none (by first | rfl | simp)]
                 exact hva))
        | (rw [PartialState.union_callStack_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.callStack cs (by rw [← hu_PR]; exact hva))
    · refine ⟨?_, ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
      · intro r
        by_cases hrbase : r = baseReg
        · rw [hrbase]; right; exact h_R_no_base
        · by_cases hrval : r = valReg
          · rw [hrval]; right; exact h_R_no_val
          · left
            rw [PartialState.union_regs_of_left_none
                (PartialState.singletonReg_regs_other hrbase)]
            rw [PartialState.union_regs_of_left_none
                (PartialState.singletonReg_regs_other hrval)]
            exact PartialState.singletonMemU16_regs r
      · intro a
        by_cases ha0 : a = effectiveAddr baseAddr off
        · rw [ha0]; right; exact h_R_no_mem_0
        · by_cases ha1 : a = effectiveAddr baseAddr off + 1
          · rw [ha1]; right; exact h_R_no_mem_1
          · left
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            exact PartialState.singletonMemU16_mem_outside _ _ a (by omega)
      · left
        rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
        rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
        exact PartialState.singletonMemU16_pc
    · refine ⟨fun r => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
      · by_cases hrbase : r = baseReg
        · right
          rw [hrbase,
              PartialState.union_regs_of_left_none
                (PartialState.singletonReg_regs_other hne_base_val)]
          exact PartialState.singletonMemU16_regs baseReg
        · left; exact PartialState.singletonReg_regs_other hrbase
      · left; exact PartialState.singletonReg_mem a
      · left; exact PartialState.singletonReg_pc
    · refine ⟨fun r => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
      · right; exact PartialState.singletonMemU16_regs r
      · left; exact PartialState.singletonReg_mem a
      · left; exact PartialState.singletonReg_pc


end SVM.SBPF
