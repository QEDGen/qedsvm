import SVM.SBPF.InstructionSpecs.Syscalls.Mem
import SVM.SBPF.InstructionSpecs.Syscalls.MemOpsSpec

/-! # General memop specs (#103)

Separation-logic forms of the functional specs in `MemOpsSpec.lean`:

* window triples `call_sol_mem{move,cpy}_window_spec`, which own one `↦Bytes`
  atom covering both ranges, so source and destination may alias (memmove) or
  share a buffer (memcpy); the disjoint two-atom triples in `Mem.lean` remain
  for the lifts;
* one `cuTripleFaultsWithinMem` per failure direction, built by
  `cuTripleFaultsWithinMem_syscall`;
* memcmp's written result as a comparison at the first differing byte. -/

namespace SVM.SBPF

open Memory

theorem memcmpFold_eq_firstDiff (p1 p2 : ByteArray) (n : Nat) :
    memcmpFold p1 p2 n =
      MemOps.firstDiff (fun i => (p1.get! i).toNat) (fun i => (p2.get! i).toNat) n := rfl

theorem memcmpResultU32_eq (p1 p2 : ByteArray) (n : Nat) :
    memcmpResultU32 p1 p2 n = MemOps.cmpU32 (memcmpFold p1 p2 n) := rfl

/-- Byte form for `memcmpFold`: equal inputs compare `0`. -/
theorem memcmpFold_eq_zero (p1 p2 : ByteArray) (n : Nat)
    (h : ∀ j, j < n → p1.get! j = p2.get! j) : memcmpFold p1 p2 n = 0 :=
  MemOps.firstDiff_eq_zero _ _ n fun j hj => congrArg UInt8.toNat (h j hj)

/-- Byte form for `memcmpFold`: the first differing byte decides. -/
theorem memcmpFold_eq_of_first (p1 p2 : ByteArray) (n i : Nat) (hin : i < n)
    (hpre : ∀ j, j < i → p1.get! j = p2.get! j) (hne : p1.get! i ≠ p2.get! i) :
    memcmpFold p1 p2 n = ((p1.get! i).toNat : Int) - ((p2.get! i).toNat : Int) :=
  MemOps.firstDiff_eq_of_first _ _ n i hin (fun j hj => congrArg UInt8.toNat (hpre j hj))
    (fun h => hne (UInt8.toNat_inj.mp h))

/-- The written u32 at the first differing byte: the difference when
    non-negative, else its two's-complement encoding. -/
theorem memcmpResultU32_of_first (p1 p2 : ByteArray) (n i : Nat) (hin : i < n)
    (hpre : ∀ j, j < i → p1.get! j = p2.get! j) (hne : p1.get! i ≠ p2.get! i) :
    memcmpResultU32 p1 p2 n =
      if (p2.get! i).toNat ≤ (p1.get! i).toNat then (p1.get! i).toNat - (p2.get! i).toNat
      else U32_MODULUS - ((p2.get! i).toNat - (p1.get! i).toNat) := by
  rw [memcmpResultU32_eq, memcmpFold_eq_of_first p1 p2 n i hin hpre hne, MemOps.cmpU32]
  split <;> split <;> omega

theorem memcmpResultU32_of_eq (p1 p2 : ByteArray) (n : Nat)
    (h : ∀ j, j < n → p1.get! j = p2.get! j) : memcmpResultU32 p1 p2 n = 0 := by
  rw [memcmpResultU32_eq, memcmpFold_eq_zero p1 p2 n h]; rfl

/-! ## Window triples: alias-capable memmove and same-buffer memcpy -/

/-- Window form of the copy and set triples: one `↦Bytes` atom at `base` owns
    every byte the syscall may read or write, so `src` and `dst` can alias
    inside it. The step obligations see the old window bytes, which is what an
    overlapping move reads. -/
theorem cuTripleWithin_syscall_writesWindow
    (sc : Syscall) (pc nCu r1V r2V r3V base : Nat) (bsOld bsNew : ByteArray)
    (hbsSize : bsOld.size = bsNew.size) (rr : Memory.RegionTable → Prop)
    (h_step_regs : ∀ s : State, s.regs.r1 = r1V → s.regs.r2 = r2V → s.regs.r3 = r3V →
        rr s.regions → (step (.call sc) s).regs = s.regs.set .r0 0)
    (h_step_mem_in : ∀ s : State, s.regs.r1 = r1V → s.regs.r2 = r2V → s.regs.r3 = r3V →
        rr s.regions →
        (∀ j, j < bsOld.size → s.mem (base + j) = (bsOld.get! j).toNat) →
        ∀ i, i < bsNew.size → (step (.call sc) s).mem (base + i) = (bsNew.get! i).toNat)
    (h_step_mem_out : ∀ s : State, s.regs.r1 = r1V → s.regs.r2 = r2V → s.regs.r3 = r3V →
        rr s.regions → ∀ a, (a < base ∨ a ≥ base + bsNew.size) →
        (step (.call sc) s).mem a = s.mem a)
    (h_step_pc : ∀ s : State, (step (.call sc) s).pc = s.pc + 1)
    (h_step_exit : ∀ s : State, s.exitCode = none →
        s.regs.r1 = r1V → s.regs.r2 = r2V → s.regs.r3 = r3V →
        rr s.regions → (step (.call sc) s).exitCode = none)
    (h_step_returnData : ∀ s : State, (step (.call sc) s).returnData = s.returnData)
    (h_step_callStack : ∀ s : State, (step (.call sc) s).callStack = s.callStack)
    (h_step_cu : ∀ s : State, (step (.call sc) s).cuConsumed ≤ s.cuConsumed + nCu) :
    ∀ r0Old,
      cuTripleWithinMem 1 nCu pc (pc + 1)
        (CodeReq.singleton pc (.call sc))
        ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V)
         ** (base ↦Bytes bsOld))
        ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V)
         ** (base ↦Bytes bsNew))
        rr := by
  intro r0Old R hRfree fetch hcr s hPR hpc hex hbud h_region
  let N : Nat := bsNew.size
  obtain ⟨hp, hcompat, h_P, h_R, hd_PR, hu_PR, h_P_sat, h_R_sat⟩ := hPR
  obtain ⟨h_r0, h_T1, hd_r0_T1, hu_r0_T1, h_r0_pred, h_T1_sat⟩ := h_P_sat
  obtain ⟨h_r1, h_T2, hd_r1_T2, hu_r1_T2, h_r1_pred, h_T2_sat⟩ := h_T1_sat
  obtain ⟨h_r2, h_T3, hd_r2_T3, hu_r2_T3, h_r2_pred, h_T3_sat⟩ := h_T2_sat
  obtain ⟨h_r3, h_b,  hd_r3_b,  hu_r3_b,  h_r3_pred, h_b_pred⟩ := h_T3_sat
  rw [h_r0_pred] at hu_r0_T1 hd_r0_T1
  rw [h_r1_pred] at hu_r1_T2 hd_r1_T2
  rw [h_r2_pred] at hu_r2_T3 hd_r2_T3
  rw [h_r3_pred] at hu_r3_b hd_r3_b
  rw [h_b_pred]  at hu_r3_b hd_r3_b
  clear h_r0_pred h_r1_pred h_r2_pred h_r3_pred h_b_pred
        h_r0 h_r1 h_r2 h_r3 h_b
  have hcr_regs := hcompat.regs
  have hcm_mem := hcompat.mem
  have h_T3_regs_r3 : h_T3.regs .r3 = some r3V := by
    rw [← hu_r3_b]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_T2_regs_r2 : h_T2.regs .r2 = some r2V := by
    rw [← hu_r2_T3]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_T2_regs_r3 : h_T2.regs .r3 = some r3V := by
    rw [← hu_r2_T3,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r3 ≠ Reg.r2))]
    exact h_T3_regs_r3
  have h_T1_regs_r1 : h_T1.regs .r1 = some r1V := by
    rw [← hu_r1_T2]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_T1_regs_r2 : h_T1.regs .r2 = some r2V := by
    rw [← hu_r1_T2,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r2 ≠ Reg.r1))]
    exact h_T2_regs_r2
  have h_T1_regs_r3 : h_T1.regs .r3 = some r3V := by
    rw [← hu_r1_T2,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r3 ≠ Reg.r1))]
    exact h_T2_regs_r3
  have h_P_regs_r0 : h_P.regs .r0 = some r0Old := by
    rw [← hu_r0_T1]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_regs_r1 : h_P.regs .r1 = some r1V := by
    rw [← hu_r0_T1,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r1 ≠ Reg.r0))]
    exact h_T1_regs_r1
  have h_P_regs_r2 : h_P.regs .r2 = some r2V := by
    rw [← hu_r0_T1,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r2 ≠ Reg.r0))]
    exact h_T1_regs_r2
  have h_P_regs_r3 : h_P.regs .r3 = some r3V := by
    rw [← hu_r0_T1,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r3 ≠ Reg.r0))]
    exact h_T1_regs_r3
  have h_P_mem_eq_b (a : Nat) :
      h_P.mem a = (PartialState.singletonMemBytes base bsOld).mem a := by
    rw [← hu_r0_T1,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _),
        ← hu_r1_T2,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _),
        ← hu_r2_T3,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _),
        ← hu_r3_b,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
  have hp_regs_r0 : hp.regs .r0 = some r0Old := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r0
  have hp_regs_r1 : hp.regs .r1 = some r1V := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r1
  have hp_regs_r2 : hp.regs .r2 = some r2V := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r2
  have hp_regs_r3 : hp.regs .r3 = some r3V := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r3
  have hs_regs_r0 : s.regs.get .r0 = r0Old := hcr_regs .r0 r0Old hp_regs_r0
  have hs_regs_r1 : s.regs.get .r1 = r1V := hcr_regs .r1 r1V hp_regs_r1
  have hs_regs_r2 : s.regs.get .r2 = r2V := hcr_regs .r2 r2V hp_regs_r2
  have hs_regs_r3 : s.regs.get .r3 = r3V := hcr_regs .r3 r3V hp_regs_r3
  have hs_r1_field : s.regs.r1 = r1V := hs_regs_r1
  have hs_r2_field : s.regs.r2 = r2V := hs_regs_r2
  have hs_r3_field : s.regs.r3 = r3V := hs_regs_r3
  -- The old window bytes, for the in-window obligation.
  have hold : ∀ j, j < bsOld.size → s.mem (base + j) = (bsOld.get! j).toNat := by
    intro j hj
    apply hcm_mem
    rw [← hu_PR]
    refine PartialState.union_mem_of_left_some ?_
    rw [h_P_mem_eq_b]
    exact PartialState.singletonMemBytes_mem_at base bsOld j hj
  have hfetch : fetch s.pc = some (.call sc) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hstep_eq : executeFn fetch s 1 = chargeCu (step (.call sc) s) := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch, executeFn_zero]
  have hexec_pc : (executeFn fetch s 1).pc = s.pc + 1 := by
    rw [hstep_eq]; exact h_step_pc s
  have hexec_exit : (executeFn fetch s 1).exitCode = none := by
    rw [hstep_eq]; exact h_step_exit s hex hs_r1_field hs_r2_field hs_r3_field h_region
  have hexec_cu : (executeFn fetch s 1).cuConsumed ≤ s.cuConsumed + 1 + nCu := by
    rw [hstep_eq]
    show (step (.call sc) s).cuConsumed + 1 ≤ s.cuConsumed + 1 + nCu
    have := h_step_cu s; omega
  have hexec_regs : (executeFn fetch s 1).regs = s.regs.set .r0 0 := by
    rw [hstep_eq]; exact h_step_regs s hs_r1_field hs_r2_field hs_r3_field h_region
  have hexec_mem_in (i : Nat) (hi : i < N) :
      (executeFn fetch s 1).mem (base + i) = (bsNew.get! i).toNat := by
    rw [hstep_eq]
    exact h_step_mem_in s hs_r1_field hs_r2_field hs_r3_field h_region hold i hi
  have hexec_mem_out (a : Nat) (h : a < base ∨ a ≥ base + N) :
      (executeFn fetch s 1).mem a = s.mem a := by
    rw [hstep_eq]
    exact h_step_mem_out s hs_r1_field hs_r2_field hs_r3_field h_region a h
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
  have h_R_no_r2 : h_R.regs .r2 = none := by
    rcases hd_PR_regs .r2 with hl | hr
    · rw [h_P_regs_r2] at hl; nomatch hl
    · exact hr
  have h_R_no_r3 : h_R.regs .r3 = none := by
    rcases hd_PR_regs .r3 with hl | hr
    · rw [h_P_regs_r3] at hl; nomatch hl
    · exact hr
  have h_R_no_pc : h_R.pc = none := hRfree _ h_R_sat
  have h_R_no_mem_in (i : Nat) (hi : i < N) : h_R.mem (base + i) = none := by
    obtain ⟨v, hatom⟩ := PartialState.singletonMemBytes_mem_isSome base bsOld
      (base + i) ⟨Nat.le_add_right _ _, by rw [hbsSize]; show base + i < base + N; omega⟩
    have h_P_some : h_P.mem (base + i) = some v := by
      rw [h_P_mem_eq_b]; exact hatom
    rcases hd_PR_mem (base + i) with hl | hr
    · rw [h_P_some] at hl; nomatch hl
    · exact hr
  let h_r0_new : PartialState := PartialState.singletonReg .r0 0
  let h_r1_new : PartialState := PartialState.singletonReg .r1 r1V
  let h_r2_new : PartialState := PartialState.singletonReg .r2 r2V
  let h_r3_new : PartialState := PartialState.singletonReg .r3 r3V
  let h_b_new  : PartialState := PartialState.singletonMemBytes base bsNew
  let h_T3_new : PartialState := h_r3_new.union h_b_new
  let h_T2_new : PartialState := h_r2_new.union h_T3_new
  let h_T1_new : PartialState := h_r1_new.union h_T2_new
  let h_P_new  : PartialState := h_r0_new.union h_T1_new
  have h_bsNew_mem_in (j : Nat) (hj : j < N) :
      (PartialState.singletonMemBytes base bsNew).mem (base + j) =
        some (bsNew.get! j).toNat :=
    PartialState.singletonMemBytes_mem_at base bsNew j hj
  have h_bsNew_mem_outside (a : Nat) (h : a < base ∨ a ≥ base + N) :
      (PartialState.singletonMemBytes base bsNew).mem a = none :=
    PartialState.singletonMemBytes_mem_outside base bsNew a h
  -- Inner disjointness: r3 ⊥ b.
  have hd_r3_b_new : h_r3_new.Disjoint h_b_new := by
    refine ⟨fun r => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
    · right; exact PartialState.singletonMemBytes_regs r
    · left; exact PartialState.singletonReg_mem a
    · left; exact PartialState.singletonReg_pc
  -- r2 ⊥ (r3 ∪ b)
  have hd_r2_T3_new : h_r2_new.Disjoint h_T3_new := by
    refine ⟨fun r => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
    · by_cases hr2 : r = .r2
      · right
        show h_T3_new.regs r = none
        show ((PartialState.singletonReg .r3 r3V).union h_b_new).regs r = none
        rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other
              (hr2 ▸ (by decide : Reg.r2 ≠ Reg.r3)))]
        exact PartialState.singletonMemBytes_regs r
      · left; exact PartialState.singletonReg_regs_other hr2
    · left; exact PartialState.singletonReg_mem a
    · left; exact PartialState.singletonReg_pc
  -- r1 ⊥ (r2 ∪ r3 ∪ b)
  have hd_r1_T2_new : h_r1_new.Disjoint h_T2_new := by
    refine ⟨fun r => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
    · by_cases hr1 : r = .r1
      · right
        show h_T2_new.regs r = none
        show ((PartialState.singletonReg .r2 r2V).union h_T3_new).regs r = none
        rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other
              (hr1 ▸ (by decide : Reg.r1 ≠ Reg.r2)))]
        show ((PartialState.singletonReg .r3 r3V).union h_b_new).regs r = none
        rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other
              (hr1 ▸ (by decide : Reg.r1 ≠ Reg.r3)))]
        exact PartialState.singletonMemBytes_regs r
      · left; exact PartialState.singletonReg_regs_other hr1
    · left; exact PartialState.singletonReg_mem a
    · left; exact PartialState.singletonReg_pc
  -- r0 ⊥ (r1 ∪ r2 ∪ r3 ∪ b)
  have hd_r0_T1_new : h_r0_new.Disjoint h_T1_new := by
    refine ⟨fun r => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
    · by_cases hr0 : r = .r0
      · right
        show h_T1_new.regs r = none
        show ((PartialState.singletonReg .r1 r1V).union h_T2_new).regs r = none
        rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other
              (hr0 ▸ (by decide : Reg.r0 ≠ Reg.r1)))]
        show ((PartialState.singletonReg .r2 r2V).union h_T3_new).regs r = none
        rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other
              (hr0 ▸ (by decide : Reg.r0 ≠ Reg.r2)))]
        show ((PartialState.singletonReg .r3 r3V).union h_b_new).regs r = none
        rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other
              (hr0 ▸ (by decide : Reg.r0 ≠ Reg.r3)))]
        exact PartialState.singletonMemBytes_regs r
      · left; exact PartialState.singletonReg_regs_other hr0
    · left; exact PartialState.singletonReg_mem a
    · left; exact PartialState.singletonReg_pc
  -- Project h_P_new.regs onto specific registers
  have h_P_new_regs_r0 : h_P_new.regs .r0 = some 0 :=
    PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_new_regs_r1 : h_P_new.regs .r1 = some r1V := by
    show ((PartialState.singletonReg .r0 0).union h_T1_new).regs .r1 = some r1V
    rw [PartialState.union_regs_of_left_none
        (PartialState.singletonReg_regs_other (by decide : Reg.r1 ≠ Reg.r0))]
    show ((PartialState.singletonReg .r1 r1V).union h_T2_new).regs .r1 = some r1V
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_new_regs_r2 : h_P_new.regs .r2 = some r2V := by
    show ((PartialState.singletonReg .r0 0).union h_T1_new).regs .r2 = some r2V
    rw [PartialState.union_regs_of_left_none
        (PartialState.singletonReg_regs_other (by decide : Reg.r2 ≠ Reg.r0))]
    show ((PartialState.singletonReg .r1 r1V).union h_T2_new).regs .r2 = some r2V
    rw [PartialState.union_regs_of_left_none
        (PartialState.singletonReg_regs_other (by decide : Reg.r2 ≠ Reg.r1))]
    show ((PartialState.singletonReg .r2 r2V).union h_T3_new).regs .r2 = some r2V
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_new_regs_r3 : h_P_new.regs .r3 = some r3V := by
    show ((PartialState.singletonReg .r0 0).union h_T1_new).regs .r3 = some r3V
    rw [PartialState.union_regs_of_left_none
        (PartialState.singletonReg_regs_other (by decide : Reg.r3 ≠ Reg.r0))]
    show ((PartialState.singletonReg .r1 r1V).union h_T2_new).regs .r3 = some r3V
    rw [PartialState.union_regs_of_left_none
        (PartialState.singletonReg_regs_other (by decide : Reg.r3 ≠ Reg.r1))]
    show ((PartialState.singletonReg .r2 r2V).union h_T3_new).regs .r3 = some r3V
    rw [PartialState.union_regs_of_left_none
        (PartialState.singletonReg_regs_other (by decide : Reg.r3 ≠ Reg.r2))]
    show ((PartialState.singletonReg .r3 r3V).union h_b_new).regs .r3 = some r3V
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_new_regs_other (r : Reg)
      (h0 : r ≠ .r0) (h1 : r ≠ .r1) (h2 : r ≠ .r2) (h3 : r ≠ .r3) :
      h_P_new.regs r = none := by
    show ((PartialState.singletonReg .r0 0).union h_T1_new).regs r = none
    rw [PartialState.union_regs_of_left_none
        (PartialState.singletonReg_regs_other h0)]
    show ((PartialState.singletonReg .r1 r1V).union h_T2_new).regs r = none
    rw [PartialState.union_regs_of_left_none
        (PartialState.singletonReg_regs_other h1)]
    show ((PartialState.singletonReg .r2 r2V).union h_T3_new).regs r = none
    rw [PartialState.union_regs_of_left_none
        (PartialState.singletonReg_regs_other h2)]
    show ((PartialState.singletonReg .r3 r3V).union h_b_new).regs r = none
    rw [PartialState.union_regs_of_left_none
        (PartialState.singletonReg_regs_other h3)]
    exact PartialState.singletonMemBytes_regs r
  -- Project h_P_new.mem
  have h_P_new_mem_eq_b (a : Nat) : h_P_new.mem a = h_b_new.mem a := by
    show ((PartialState.singletonReg .r0 0).union h_T1_new).mem a = h_b_new.mem a
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    show ((PartialState.singletonReg .r1 r1V).union h_T2_new).mem a = h_b_new.mem a
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    show ((PartialState.singletonReg .r2 r2V).union h_T3_new).mem a = h_b_new.mem a
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    show ((PartialState.singletonReg .r3 r3V).union h_b_new).mem a = h_b_new.mem a
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
  have h_P_new_mem_outside (a : Nat) (h : a < base ∨ a ≥ base + N) :
      h_P_new.mem a = none := by
    rw [h_P_new_mem_eq_b]
    exact h_bsNew_mem_outside a h
  have h_P_new_mem_in (j : Nat) (hj : j < N) :
      h_P_new.mem (base + j) = some (bsNew.get! j).toNat := by
    rw [h_P_new_mem_eq_b]
    exact h_bsNew_mem_in j hj
  have h_P_new_pc : h_P_new.pc = none := by
    show ((PartialState.singletonReg .r0 0).union h_T1_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    show ((PartialState.singletonReg .r1 r1V).union h_T2_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    show ((PartialState.singletonReg .r2 r2V).union h_T3_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    show ((PartialState.singletonReg .r3 r3V).union h_b_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    exact PartialState.singletonMemBytes_pc
  have hd_PnewR : h_P_new.Disjoint h_R := by
    refine ⟨fun r => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
    · by_cases h0 : r = .r0
      · right; rw [h0]; exact h_R_no_r0
      by_cases h1 : r = .r1
      · right; rw [h1]; exact h_R_no_r1
      by_cases h2 : r = .r2
      · right; rw [h2]; exact h_R_no_r2
      by_cases h3 : r = .r3
      · right; rw [h3]; exact h_R_no_r3
      · left; exact h_P_new_regs_other r h0 h1 h2 h3
    · by_cases ha : base ≤ a ∧ a < base + N
      · right
        obtain ⟨h1, h2⟩ := ha
        have h_eq : a = base + (a - base) := by omega
        have h_lt : a - base < N := by omega
        rw [h_eq]; exact h_R_no_mem_in _ h_lt
      · left
        apply h_P_new_mem_outside
        rcases Nat.lt_or_ge a base with h | h
        · left; exact h
        · rcases Nat.lt_or_ge a (base + N) with h' | h'
          · exact absurd ⟨h, h'⟩ ha
          · right; exact h'
    · left; exact h_P_new_pc
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_, ?_⟩
  · rw [hexec_pc, hpc]
  · exact hexec_exit
  · exact hexec_cu
  · refine ⟨h_P_new.union h_R, ?_, h_P_new, h_R, hd_PnewR, rfl,
            ⟨h_r0_new, h_T1_new, hd_r0_T1_new, rfl, rfl,
             h_r1_new, h_T2_new, hd_r1_T2_new, rfl, rfl,
             h_r2_new, h_T3_new, hd_r2_T3_new, rfl, rfl,
             h_r3_new, h_b_new,  hd_r3_b_new,  rfl, rfl, rfl⟩,
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
      by_cases h2 : r = .r2
      · rw [h2] at hvr
        rw [PartialState.union_regs_of_left_some h_P_new_regs_r2] at hvr
        have hvr2 : vr = r2V := (Option.some.inj hvr).symm
        rw [h2, hexec_regs, hvr2,
            RegFile.get_set_diff _ _ _ _ (by decide : (.r2 : Reg) ≠ .r0)]
        exact hs_regs_r2
      by_cases h3 : r = .r3
      · rw [h3] at hvr
        rw [PartialState.union_regs_of_left_some h_P_new_regs_r3] at hvr
        have hvr3 : vr = r3V := (Option.some.inj hvr).symm
        rw [h3, hexec_regs, hvr3,
            RegFile.get_set_diff _ _ _ _ (by decide : (.r3 : Reg) ≠ .r0)]
        exact hs_regs_r3
      · rw [PartialState.union_regs_of_left_none
            (h_P_new_regs_other r h0 h1 h2 h3)] at hvr
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
      by_cases ha : base ≤ a ∧ a < base + N
      · obtain ⟨h1, h2⟩ := ha
        have h_eq : a = base + (a - base) := by omega
        have h_lt : a - base < N := by omega
        rw [h_eq] at hvm ⊢
        rw [PartialState.union_mem_of_left_some
            (h_P_new_mem_in _ h_lt)] at hvm
        have hvmEq : vm = (bsNew.get! (a - base)).toNat :=
          (Option.some.inj hvm).symm
        rw [hexec_mem_in _ h_lt, hvmEq]
      · have h_out : a < base ∨ a ≥ base + N := by
          rcases Nat.lt_or_ge a base with h | h
          · left; exact h
          · rcases Nat.lt_or_ge a (base + N) with h' | h'
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
        rw [← hu_r0_T1, ← hu_r1_T2, ← hu_r2_T3, ← hu_r3_b]; rfl
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
        rw [← hu_r0_T1, ← hu_r1_T2, ← hu_r2_T3, ← hu_r3_b]; rfl
      have hp_cs : hp.callStack = some cs := by
        rw [← hu_PR, PartialState.union_callStack_of_left_none h_P_cs]
        exact hva
      have hexec_cs : (executeFn fetch s 1).callStack = s.callStack := by
        rw [hstep_eq]; exact h_step_callStack s
      rw [hexec_cs]
      exact hcompat.callStack cs hp_cs

/-- The window after moving `n` bytes from offset `so` to offset `dO`,
    reading every source byte from the original window. -/
def moveBytes (w : ByteArray) (dO so n : Nat) : ByteArray :=
  ⟨(Array.range w.size).map fun i =>
    if dO ≤ i ∧ i - dO < n then w.get! (so + (i - dO)) else w.get! i⟩

@[simp] theorem moveBytes_size (w : ByteArray) (dO so n : Nat) :
    (moveBytes w dO so n).size = w.size := by
  show ((Array.range w.size).map _).size = w.size
  simp

theorem moveBytes_get! (w : ByteArray) (dO so n i : Nat) (hi : i < w.size) :
    (moveBytes w dO so n).get! i =
      if dO ≤ i ∧ i - dO < n then w.get! (so + (i - dO)) else w.get! i := by
  show ((Array.range w.size).map _)[i]! = _
  rw [getElem!_pos _ _ (by simpa using hi)]
  simp

/-- Shared proof of the two window triples. -/
private theorem call_window_syscall_spec
    (sc : Syscall) (isMove : Bool)
    (hexec : ∀ s, execSyscall sc s =
      if isMove then MemOps.execMove s else MemOps.execCopy s)
    (r0Old base dO so n pc nCu : Nat) (w : ByteArray)
    (hd : dO + n ≤ w.size) (hs : so + n ≤ w.size)
    (hno : isMove = true ∨ MemOps.nonoverlapping (base + so) (base + dO) n = true)
    (hCu : ∀ s : State, (step (.call sc) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithinMem 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call sc))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ base + dO) ** (.r2 ↦ᵣ base + so) ** (.r3 ↦ᵣ n)
       ** (base ↦Bytes w))
      ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ base + dO) ** (.r2 ↦ᵣ base + so) ** (.r3 ↦ᵣ n)
       ** (base ↦Bytes moveBytes w dO so n))
      (fun rt => rt.containsRange (base + so) n = true ∧
                 rt.containsWritable (base + dO) n = true) := by
  have hmove : ∀ s : State, s.regs.r1 = base + dO → s.regs.r2 = base + so → s.regs.r3 = n →
      execSyscall sc s = MemOps.execMove s := by
    intro s h1 h2 h3
    rw [hexec]
    cases isMove
    · rcases hno with h | h
      · nomatch h
      · rw [← h1, ← h2, ← h3] at h
        exact MemOps.execCopy_ok s h
    · rfl
  have hok : ∀ s : State, s.regs.r1 = base + dO → s.regs.r2 = base + so → s.regs.r3 = n →
      (s.regions.containsRange (base + so) n = true ∧
        s.regions.containsWritable (base + dO) n = true) →
      execSyscall sc s =
        { s with regs := s.regs.set .r0 0,
                 mem := MemOps.moveMem s.mem (base + dO) (base + so) n } := by
    intro s h1 h2 h3 hr
    rw [hmove s h1 h2 h3, MemOps.execMove_ok s (by rw [h2, h3]; exact Or.inr hr.1)
      (by rw [h1, h3]; exact Or.inr hr.2), h1, h2, h3]
  refine cuTripleWithin_syscall_writesWindow sc pc nCu (base + dO) (base + so) n base
    w (moveBytes w dO so n) (moveBytes_size w dO so n).symm _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hCu r0Old
  · intro s h1 h2 h3 hr
    simp only [step, hok s h1 h2 h3 hr]
  · intro s h1 h2 h3 hr hold i hi
    rw [moveBytes_size] at hi
    simp only [step, hok s h1 h2 h3 hr]
    rw [moveBytes_get! w dO so n i hi]
    by_cases hin : dO ≤ i ∧ i - dO < n
    · rw [if_pos hin, show base + i = base + dO + (i - dO) by omega,
        MemOps.moveMem_in _ _ _ _ _ hin.2,
        show base + so + (i - dO) = base + (so + (i - dO)) by omega,
        hold _ (by omega)]
      exact Nat.mod_eq_of_lt (UInt8.toNat_lt _)
    · rw [if_neg hin, MemOps.moveMem_out _ _ _ _ _ (by omega), hold i hi]
  · intro s h1 h2 h3 hr a ha
    rw [moveBytes_size] at ha
    simp only [step, hok s h1 h2 h3 hr]
    exact MemOps.moveMem_out _ _ _ _ _ (by omega)
  · intro s; rfl
  · intro s hex h1 h2 h3 hr
    simp only [step, hok s h1 h2 h3 hr]
    exact hex
  · intro s
    simp only [step, hexec]
    cases isMove <;>
      simp only [Bool.false_eq_true, if_false, if_true, MemOps.execCopy, MemOps.execMove,
        State.guardRead, State.guardWrite, State.accessFault] <;>
      (repeat' split) <;> rfl
  · intro s
    simp only [step, hexec]
    cases isMove <;>
      simp only [Bool.false_eq_true, if_false, if_true, MemOps.execCopy, MemOps.execMove,
        State.guardRead, State.guardWrite, State.accessFault] <;>
      (repeat' split) <;> rfl

/-- `sol_memmove` inside one buffer `w` at `base`, any offsets: the ranges
    `[dO, dO+n)` and `[so, so+n)` may overlap in either direction. -/
theorem call_sol_memmove_window_spec
    (r0Old base dO so n pc nCu : Nat) (w : ByteArray)
    (hd : dO + n ≤ w.size) (hs : so + n ≤ w.size)
    (hCu : ∀ s : State, (step (.call .sol_memmove) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithinMem 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_memmove))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ base + dO) ** (.r2 ↦ᵣ base + so) ** (.r3 ↦ᵣ n)
       ** (base ↦Bytes w))
      ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ base + dO) ** (.r2 ↦ᵣ base + so) ** (.r3 ↦ᵣ n)
       ** (base ↦Bytes moveBytes w dO so n))
      (fun rt => rt.containsRange (base + so) n = true ∧
                 rt.containsWritable (base + dO) n = true) :=
  call_window_syscall_spec .sol_memmove true (fun _ => rfl)
    r0Old base dO so n pc nCu w hd hs (Or.inl rfl) hCu

/-- `sol_memcpy` between disjoint ranges of one buffer. Overlapping ranges
    fault instead (`call_sol_memcpy_overlap_faults_spec`). -/
theorem call_sol_memcpy_window_spec
    (r0Old base dO so n pc nCu : Nat) (w : ByteArray)
    (hd : dO + n ≤ w.size) (hs : so + n ≤ w.size)
    (hno : so + n ≤ dO ∨ dO + n ≤ so)
    (hCu : ∀ s : State, (step (.call .sol_memcpy) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithinMem 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_memcpy))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ base + dO) ** (.r2 ↦ᵣ base + so) ** (.r3 ↦ᵣ n)
       ** (base ↦Bytes w))
      ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ base + dO) ** (.r2 ↦ᵣ base + so) ** (.r3 ↦ᵣ n)
       ** (base ↦Bytes moveBytes w dO so n))
      (fun rt => rt.containsRange (base + so) n = true ∧
                 rt.containsWritable (base + dO) n = true) :=
  call_window_syscall_spec .sol_memcpy false (fun _ => rfl)
    r0Old base dO so n pc nCu w hd hs
    (Or.inr ((MemOps.nonoverlapping_iff _ _ _).mpr (by omega))) hCu

/-! ## Fault triples -/

/-- `(r ↦ᵣ v) ** Q` pins register `r` of any state it holds for. -/
theorem regIs_sepConj_get {r : Reg} {v : Nat} {Q : Assertion} {s : State}
    (h : ((r ↦ᵣ v) ** Q).holdsFor s) : s.regs.get r = v := by
  obtain ⟨hp, hc, h1, h2, _, hu, hP, _⟩ := h
  apply hc.regs r v
  rw [← hu, hP]
  exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self

/-- The tail of a `**` holds whenever the whole does. -/
theorem sepConj_holdsFor_tail {P Q : Assertion} {s : State}
    (h : (P ** Q).holdsFor s) : Q.holdsFor s := by
  obtain ⟨hh, hc, h1, h2, hd, hu, _, hQ⟩ := h
  refine ⟨h2, ?_, hQ⟩
  subst hu
  refine ⟨fun r v hv => hc.regs r v ?_, fun a v hv => hc.mem a v ?_, fun v hv => hc.pc v ?_,
    fun rd hv => hc.returnData rd ?_, fun cs hv => hc.callStack cs ?_⟩
  · rcases hd.regs r with h | h
    · rw [PartialState.union_regs_of_left_none h]; exact hv
    · rw [h] at hv; nomatch hv
  · rcases hd.mem a with h | h
    · rw [PartialState.union_mem_of_left_none h]; exact hv
    · rw [h] at hv; nomatch hv
  · rcases hd.pc with h | h
    · rw [PartialState.union_pc_of_left_none h]; exact hv
    · rw [h] at hv; nomatch hv
  · rcases hd.returnData with h | h
    · rw [PartialState.union_returnData_of_left_none h]; exact hv
    · rw [h] at hv; nomatch hv
  · rcases hd.callStack with h | h
    · rw [PartialState.union_callStack_of_left_none h]; exact hv
    · rw [h] at hv; nomatch hv

/-- Any syscall that faults with `e` on every state its precondition pins
    (`Q`) and its region requirement admits. -/
theorem cuTripleFaultsWithinMem_syscall
    (sc : Syscall) (pc nCu : Nat) (P : Assertion) (rr : Memory.RegionTable → Prop)
    (e : VmError) (Q : State → Prop)
    (hQ : ∀ R s, (P ** R).holdsFor s → Q s)
    (hf : ∀ s, Q s → rr s.regions →
      (execSyscall sc s).exitCode = some e.toSentinel ∧ (execSyscall sc s).vmError = some e)
    (hCu : ∀ s : State, (step (.call sc) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleFaultsWithinMem 1 nCu pc (CodeReq.singleton pc (.call sc)) P rr e := by
  intro R _ fetch hcr s hPR hpc hex hbud h_region
  have hfetch : fetch s.pc = some (.call sc) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hstep_eq : executeFn fetch s 1 = chargeCu (step (.call sc) s) := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch, executeFn_zero]
  obtain ⟨h1, h2⟩ := hf s (hQ R s hPR) h_region
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_⟩
  · rw [hstep_eq]; exact h1
  · rw [hstep_eq]; exact h2
  · rw [hstep_eq]
    show (step (.call sc) s).cuConsumed + 1 ≤ s.cuConsumed + 1 + nCu
    have := hCu s; omega

/-- Register precondition of a three-argument memop. -/
abbrev memopRegs3 (r1V r2V r3V : Nat) : Assertion :=
  (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V)

theorem memopRegs3_get {r1V r2V r3V : Nat} {R : Assertion} {s : State}
    (h : (memopRegs3 r1V r2V r3V ** R).holdsFor s) :
    s.regs.r1 = r1V ∧ s.regs.r2 = r2V ∧ s.regs.r3 = r3V := by
  have h := (holdsFor_sepConj_assoc).mp h
  have h' := sepConj_holdsFor_tail h
  have h' := (holdsFor_sepConj_assoc).mp h'
  exact ⟨regIs_sepConj_get h, regIs_sepConj_get h', regIs_sepConj_get (sepConj_holdsFor_tail h')⟩

/-- Overlapping memcpy faults `copyOverlapping`, whatever the regions. -/
theorem call_sol_memcpy_overlap_faults_spec (r1V r2V r3V pc nCu : Nat)
    (hov : MemOps.nonoverlapping r2V r1V r3V = false)
    (hCu : ∀ s : State, (step (.call .sol_memcpy) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleFaultsWithinMem 1 nCu pc (CodeReq.singleton pc (.call .sol_memcpy))
      (memopRegs3 r1V r2V r3V) (fun _ => True) .copyOverlapping :=
  cuTripleFaultsWithinMem_syscall _ pc nCu _ _ _ _ (fun _ _ h => memopRegs3_get h)
    (fun s ⟨h1, h2, h3⟩ _ => by
      rw [show execSyscall .sol_memcpy s = MemOps.execCopy s from rfl,
        MemOps.execCopy_overlap s (by rw [h1, h2, h3]; exact hov)]
      exact ⟨rfl, rfl⟩) hCu

/-- Non-overlapping memcpy with a nonempty slice out of region. -/
theorem call_sol_memcpy_oob_faults_spec (r1V r2V r3V pc nCu : Nat) (hn : r3V ≠ 0)
    (hno : MemOps.nonoverlapping r2V r1V r3V = true)
    (hCu : ∀ s : State, (step (.call .sol_memcpy) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleFaultsWithinMem 1 nCu pc (CodeReq.singleton pc (.call .sol_memcpy))
      (memopRegs3 r1V r2V r3V)
      (fun rt => rt.containsRange r2V r3V = false ∨ rt.containsWritable r1V r3V = false)
      .accessViolation :=
  cuTripleFaultsWithinMem_syscall _ pc nCu _ _ _ _ (fun _ _ h => memopRegs3_get h)
    (fun s ⟨h1, h2, h3⟩ hr => by
      rw [show execSyscall .sol_memcpy s = MemOps.execCopy s from rfl,
        MemOps.execCopy_ok s (by rw [h1, h2, h3]; exact hno),
        MemOps.execMove_fault s (by rw [h3]; exact hn) (by rw [h1, h2, h3]; exact hr)]
      exact ⟨rfl, rfl⟩) hCu

theorem call_sol_memmove_oob_faults_spec (r1V r2V r3V pc nCu : Nat) (hn : r3V ≠ 0)
    (hCu : ∀ s : State, (step (.call .sol_memmove) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleFaultsWithinMem 1 nCu pc (CodeReq.singleton pc (.call .sol_memmove))
      (memopRegs3 r1V r2V r3V)
      (fun rt => rt.containsRange r2V r3V = false ∨ rt.containsWritable r1V r3V = false)
      .accessViolation :=
  cuTripleFaultsWithinMem_syscall _ pc nCu _ _ _ _ (fun _ _ h => memopRegs3_get h)
    (fun s ⟨h1, h2, h3⟩ hr => by
      rw [show execSyscall .sol_memmove s = MemOps.execMove s from rfl,
        MemOps.execMove_fault s (by rw [h3]; exact hn) (by rw [h1, h2, h3]; exact hr)]
      exact ⟨rfl, rfl⟩) hCu

theorem call_sol_memset_oob_faults_spec (r1V r2V r3V pc nCu : Nat) (hn : r3V ≠ 0)
    (hCu : ∀ s : State, (step (.call .sol_memset) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleFaultsWithinMem 1 nCu pc (CodeReq.singleton pc (.call .sol_memset))
      (memopRegs3 r1V r2V r3V)
      (fun rt => rt.containsWritable r1V r3V = false) .accessViolation :=
  cuTripleFaultsWithinMem_syscall _ pc nCu _ _ _ _ (fun _ _ h => memopRegs3_get h)
    (fun s ⟨h1, _, h3⟩ hr => by
      rw [show execSyscall .sol_memset s = MemOps.execSet s from rfl,
        MemOps.execSet_fault s (by rw [h3]; exact hn) (by rw [h1, h3]; exact hr)]
      exact ⟨rfl, rfl⟩) hCu

/-- Register precondition of memcmp. -/
abbrev memopRegs4 (r1V r2V r3V r4V : Nat) : Assertion :=
  (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V) ** (.r4 ↦ᵣ r4V)

theorem memopRegs4_get {r1V r2V r3V r4V : Nat} {R : Assertion} {s : State}
    (h : (memopRegs4 r1V r2V r3V r4V ** R).holdsFor s) :
    s.regs.r1 = r1V ∧ s.regs.r2 = r2V ∧ s.regs.r3 = r3V ∧ s.regs.r4 = r4V := by
  have h := (holdsFor_sepConj_assoc).mp h
  have h2 := (holdsFor_sepConj_assoc).mp (sepConj_holdsFor_tail h)
  have h3 := (holdsFor_sepConj_assoc).mp (sepConj_holdsFor_tail h2)
  exact ⟨regIs_sepConj_get h, regIs_sepConj_get h2, regIs_sepConj_get h3,
    regIs_sepConj_get (sepConj_holdsFor_tail h3)⟩

/-- memcmp with an input or the result out of region (the result is checked
    even for `n = 0`). -/
theorem call_sol_memcmp_oob_faults_spec (r1V r2V r3V r4V pc nCu : Nat)
    (hCu : ∀ s : State, (step (.call .sol_memcmp) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleFaultsWithinMem 1 nCu pc (CodeReq.singleton pc (.call .sol_memcmp))
      (memopRegs4 r1V r2V r3V r4V)
      (fun rt => (r3V ≠ 0 ∧ rt.containsRange r1V r3V = false) ∨
                 (r3V ≠ 0 ∧ rt.containsRange r2V r3V = false) ∨
                 rt.containsWritable r4V 4 = false)
      .accessViolation :=
  cuTripleFaultsWithinMem_syscall _ pc nCu _ _ _ _ (fun _ _ h => memopRegs4_get h)
    (fun s ⟨h1, h2, h3, h4⟩ hr => by
      rw [show execSyscall .sol_memcmp s = MemOps.execCmp s from rfl,
        MemOps.execCmp_fault s (by rw [h1, h2, h3, h4]; exact hr)]
      exact ⟨rfl, rfl⟩) hCu

/-- memcmp with in-region inputs and a writable but unaligned result. -/
theorem call_sol_memcmp_unaligned_faults_spec (r1V r2V r3V r4V pc nCu : Nat)
    (halign : r4V % 4 ≠ 0)
    (hCu : ∀ s : State, (step (.call .sol_memcmp) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleFaultsWithinMem 1 nCu pc (CodeReq.singleton pc (.call .sol_memcmp))
      (memopRegs4 r1V r2V r3V r4V)
      (fun rt => (r3V = 0 ∨ rt.containsRange r1V r3V = true) ∧
                 (r3V = 0 ∨ rt.containsRange r2V r3V = true) ∧
                 rt.containsWritable r4V 4 = true)
      .unalignedPointer :=
  cuTripleFaultsWithinMem_syscall _ pc nCu _ _ _ _ (fun _ _ h => memopRegs4_get h)
    (fun s ⟨h1, h2, h3, h4⟩ ⟨g1, g2, g3⟩ => by
      rw [show execSyscall .sol_memcmp s = MemOps.execCmp s from rfl,
        MemOps.execCmp_unaligned s (by rw [h1, h3]; exact g1) (by rw [h2, h3]; exact g2)
          (by rw [h4]; exact g3) (by rw [h4]; exact halign)]
      exact ⟨rfl, rfl⟩) hCu

end SVM.SBPF
