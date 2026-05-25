import SVM.SBPF.InstructionSpecs.Preamble

namespace SVM.SBPF

open Memory

/-! ## Generic 1-register write spec

The pattern of "instruction reads dst (current value `vOld`), writes
`vNew`, increments PC, takes 1 step" covers every register-only ALU
instruction with an immediate source: `mov64 dst (.imm _)`, `add64 dst
(.imm _)`, `sub64 dst (.imm _)`, `neg64 dst`, `and64/or64/xor64/lsh64/
rsh64 dst (.imm _)`, and their 32-bit variants. Capturing the proof
shape once collapses each such per-instruction spec to a two-line
characterization of how `step` behaves on that opcode. -/

theorem cuTripleWithin_1reg_write
    (dst : Reg) (vOld vNew : Nat) (pc : Nat) (insn : Insn)
    (hne : dst ≠ .r10)
    (h_step : ∀ s : State, s.regs.get dst = vOld →
        step insn s = { s with regs := s.regs.set dst vNew, pc := s.pc + 1 }) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc insn)
      (dst ↦ᵣ vOld)
      (dst ↦ᵣ vNew) := by
  intro R hRfree fetch hcr s hPR hpc hex
  obtain ⟨hp, hcompat, h1, hR, hd, hu, hreg, hRsat⟩ := hPR
  rw [hreg] at hu hd
  clear hreg h1
  have hcr_regs := hcompat.regs
  have hcm_mem := hcompat.mem
  have hd_regs := hd.regs
  have hfetch : fetch s.pc = some insn := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hp_regs_dst : hp.regs dst = some vOld := by
    rw [← hu]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have hs_regs_dst : s.regs.get dst = vOld := hcr_regs dst vOld hp_regs_dst
  have hexec : executeFn fetch s 1 =
      { s with regs := s.regs.set dst vNew, pc := s.pc + 1 } := by
    have hstep := h_step s hs_regs_dst
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 insn hex hfetch,
        executeFn_zero, hstep]
  have hR_no_dst : hR.regs dst = none := by
    rcases hd_regs dst with h | h
    · rw [PartialState.singletonReg_regs_self] at h; nomatch h
    · exact h
  have hR_no_pc : hR.pc = none := hRfree _ hRsat
  have hp_regs_other : ∀ r, r ≠ dst → hp.regs r = hR.regs r := by
    intro r hr; rw [← hu]
    exact PartialState.union_regs_of_left_none
      (PartialState.singletonReg_regs_other hr)
  have hp_mem : ∀ a, hp.mem a = hR.mem a := by
    intro a; rw [← hu]
    exact PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_⟩
  · rw [hexec]; show s.pc + 1 = pc + 1; rw [hpc]
  · rw [hexec]; exact hex
  · rw [hexec]
    refine ⟨(PartialState.singletonReg dst vNew).union hR, ?_,
            PartialState.singletonReg dst vNew, hR, ?_, rfl, rfl, hRsat⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro r v hvr
        by_cases hr : r = dst
        · rw [hr] at hvr
          rw [PartialState.union_regs_of_left_some
              PartialState.singletonReg_regs_self] at hvr
          have hveq : v = vNew := (Option.some.inj hvr).symm
          rw [hr, hveq]
          show (s.regs.set dst vNew).get dst = vNew
          exact RegFile.get_set_self _ _ _ hne
        · rw [PartialState.union_regs_of_left_none
              (PartialState.singletonReg_regs_other hr)] at hvr
          show (s.regs.set dst vNew).get r = v
          rw [RegFile.get_set_diff _ _ _ _ hr]
          exact hcr_regs r v ((hp_regs_other r hr).symm ▸ hvr)
      · intro a v hva
        rw [PartialState.union_mem_of_left_none
            (PartialState.singletonReg_mem _)] at hva
        show s.mem a = v
        exact hcm_mem a v ((hp_mem a).symm ▸ hva)
      · intro v hvp
        rw [PartialState.union_pc_of_left_none
            PartialState.singletonReg_pc] at hvp
        rw [hR_no_pc] at hvp
        nomatch hvp
      · intro rd hva
        first
        | exact hcompat.returnData rd hva
        | (rw [PartialState.union_returnData_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.returnData rd
             (by rw [
                    ← hu,
                    PartialState.union_returnData_of_left_none (by first | rfl | simp)]
                 exact hva))
        | (rw [PartialState.union_returnData_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.returnData rd
             (by rw [
                    ← hu,
                    PartialState.union_returnData_of_left_none (by first | rfl | simp)]
                 exact hva))
        | (rw [PartialState.union_returnData_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.returnData rd (by rw [← hu]; exact hva))
      · intro cs hva
        first
        | exact hcompat.callStack cs hva
        | (rw [PartialState.union_callStack_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.callStack cs
             (by rw [
                    ← hu,
                    PartialState.union_callStack_of_left_none (by first | rfl | simp)]
                 exact hva))
        | (rw [PartialState.union_callStack_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.callStack cs
             (by rw [
                    ← hu,
                    PartialState.union_callStack_of_left_none (by first | rfl | simp)]
                 exact hva))
        | (rw [PartialState.union_callStack_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.callStack cs (by rw [← hu]; exact hva))
    · refine ⟨?_, ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
      · intro r
        by_cases hr : r = dst
        · rw [hr]; right; exact hR_no_dst
        · left; exact PartialState.singletonReg_regs_other hr
      · intro a; left; exact PartialState.singletonReg_mem a
      · left; exact PartialState.singletonReg_pc

/-! ## `mov64 dst (.imm imm)` — load immediate

The simplest possible triple: writes a constant to a destination register,
overwriting whatever was there. Excludes the read-only frame pointer
(r10), whose writes are silently dropped by the runtime. -/

theorem mov64_imm_spec (dst : Reg) (imm : Int) (vOld : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.mov64 dst (.imm imm)))
      (dst ↦ᵣ vOld)
      (dst ↦ᵣ toU64 imm) := by
  intro R hRfree fetch hcr s hPR hpc hex
  -- 1. Destructure (dst ↦ᵣ vOld) ** R for state s.
  obtain ⟨hp, hcompat, h1, hR, hd, hu, hreg, hRsat⟩ := hPR
  -- hreg : h1 = singletonReg dst vOld  →  rewrite h1 throughout.
  rw [hreg] at hu hd
  clear hreg h1
  have hcr_regs := hcompat.regs
  have hcm_mem := hcompat.mem
  have hd_regs := hd.regs
  -- 2. Fetch resolves to the mov64 instruction at PC.
  have hfetch : fetch s.pc = some (.mov64 dst (.imm imm)) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  -- 3. Single-step executeFn.
  have hexec : executeFn fetch s 1 =
      { s with regs := s.regs.set dst (toU64 imm), pc := s.pc + 1 } := by
    simp [executeFn, step, hex, hfetch]
  -- 4. hR doesn't own dst.
  have hR_no_dst : hR.regs dst = none := by
    rcases hd_regs dst with h | h
    · rw [PartialState.singletonReg_regs_self] at h
      simp at h
    · exact h
  -- 5. hR.pc = none (R is pc-free).
  have hR_no_pc : hR.pc = none := hRfree _ hRsat
  -- 6. hp's projections in terms of hR (with dst as the only special address).
  have hp_regs_dst : hp.regs dst = some vOld := by
    rw [← hu]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have hp_regs_other : ∀ r, r ≠ dst → hp.regs r = hR.regs r := by
    intro r hr
    rw [← hu]
    exact PartialState.union_regs_of_left_none
      (PartialState.singletonReg_regs_other hr)
  have hp_mem : ∀ a, hp.mem a = hR.mem a := by
    intro a
    rw [← hu]
    exact PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)
  -- 7. Build the witness for the post.
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_⟩
  · -- s'.pc = pc + 1
    rw [hexec]
    show s.pc + 1 = pc + 1
    rw [hpc]
  · -- s'.exitCode = none
    rw [hexec]; exact hex
  · -- ((dst ↦ᵣ toU64 imm) ** R).holdsFor s'
    rw [hexec]
    refine ⟨(PartialState.singletonReg dst (toU64 imm)).union hR, ?_,
            PartialState.singletonReg dst (toU64 imm), hR, ?_, rfl, rfl, hRsat⟩
    · -- Compatibility of the new partial state with s'.
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · -- regs
        intro r v hvr
        by_cases hr : r = dst
        · rw [hr] at hvr
          rw [PartialState.union_regs_of_left_some
              PartialState.singletonReg_regs_self] at hvr
          have hveq : v = toU64 imm := (Option.some.inj hvr).symm
          rw [hr, hveq]
          show (s.regs.set dst (toU64 imm)).get dst = toU64 imm
          exact RegFile.get_set_self _ _ _ hne
        · rw [PartialState.union_regs_of_left_none
              (PartialState.singletonReg_regs_other hr)] at hvr
          show (s.regs.set dst (toU64 imm)).get r = v
          rw [RegFile.get_set_diff _ _ _ _ hr]
          exact hcr_regs r v ((hp_regs_other r hr).symm ▸ hvr)
      · -- mem
        intro a v hva
        rw [PartialState.union_mem_of_left_none
            (PartialState.singletonReg_mem _)] at hva
        show s.mem a = v
        exact hcm_mem a v ((hp_mem a).symm ▸ hva)
      · -- pc
        intro v hvp
        rw [PartialState.union_pc_of_left_none
            PartialState.singletonReg_pc] at hvp
        rw [hR_no_pc] at hvp
        simp at hvp
      · intro rd hva
        first
        | exact hcompat.returnData rd hva
        | (rw [PartialState.union_returnData_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.returnData rd
             (by rw [
                    ← hu,
                    PartialState.union_returnData_of_left_none (by first | rfl | simp)]
                 exact hva))
        | (rw [PartialState.union_returnData_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.returnData rd
             (by rw [
                    ← hu,
                    PartialState.union_returnData_of_left_none (by first | rfl | simp)]
                 exact hva))
        | (rw [PartialState.union_returnData_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.returnData rd (by rw [← hu]; exact hva))
      · intro cs hva
        first
        | exact hcompat.callStack cs hva
        | (rw [PartialState.union_callStack_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.callStack cs
             (by rw [
                    ← hu,
                    PartialState.union_callStack_of_left_none (by first | rfl | simp)]
                 exact hva))
        | (rw [PartialState.union_callStack_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.callStack cs
             (by rw [
                    ← hu,
                    PartialState.union_callStack_of_left_none (by first | rfl | simp)]
                 exact hva))
        | (rw [PartialState.union_callStack_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.callStack cs (by rw [← hu]; exact hva))
    · -- Disjointness: singletonReg dst (toU64 imm) is disjoint from hR.
      refine ⟨?_, ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
      · intro r
        by_cases hr : r = dst
        · rw [hr]; right; exact hR_no_dst
        · left; exact PartialState.singletonReg_regs_other hr
      · intro a; left; exact PartialState.singletonReg_mem a
      · left; exact PartialState.singletonReg_pc

/-! ## `mov64 dst (.reg src)` — register copy (manual proof of pattern)

Two-atom precondition: we own both registers. After the step, the
source's value lives in both. `dst ≠ src` falls out of the sepConj
disjointness in the precondition (no extra hypothesis needed).

This was the original first-principles proof — kept in-tree as a
methodology exemplar showing what `cuTripleWithin_2reg_write`
expands to. The concise derived form lives below as
`mov64_reg_spec`; the manual form here is `mov64_reg_spec_manual`. -/

theorem mov64_reg_spec_manual (dst src : Reg) (vOld v : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.mov64 dst (.reg src)))
      ((dst ↦ᵣ vOld) ** (src ↦ᵣ v))
      ((dst ↦ᵣ v) ** (src ↦ᵣ v)) := by
  intro R hRfree fetch hcr s hPR hpc hex
  -- 1. Destructure the precondition layers.
  obtain ⟨hp, hcompat, hPQ, hR, hd_PQR, hu_PQR, hPQ_pred, hR_sat⟩ := hPR
  obtain ⟨h_dst, h_src, hd_dst_src, hu_PQ, h_dst_eq, h_src_eq⟩ := hPQ_pred
  rw [h_dst_eq] at hu_PQ hd_dst_src
  rw [h_src_eq] at hu_PQ hd_dst_src
  clear h_dst_eq h_src_eq h_dst h_src
  have hcr_regs := hcompat.regs
  have hcm_mem := hcompat.mem
  have hd_PQR_regs := hd_PQR.regs
  -- 2. dst ≠ src from inner disjointness.
  have hne_dst_src : dst ≠ src := by
    have hd_inner_regs := hd_dst_src.regs
    intro habs
    rcases hd_inner_regs dst with h | h
    · rw [PartialState.singletonReg_regs_self] at h; nomatch h
    · rw [habs, PartialState.singletonReg_regs_self] at h; nomatch h
  -- 3. Reshape hu_PQ to get explicit hp decomposition.
  have hp_eq : ((PartialState.singletonReg dst vOld).union
                (PartialState.singletonReg src v)).union hR = hp := by
    rw [hu_PQ]; exact hu_PQR
  -- 4. Extract register values from compat.
  have hp_regs_dst : hp.regs dst = some vOld := by
    rw [← hp_eq]
    apply PartialState.union_regs_of_left_some
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have hp_regs_src : hp.regs src = some v := by
    rw [← hp_eq]
    apply PartialState.union_regs_of_left_some
    rw [PartialState.union_regs_of_left_none
        (PartialState.singletonReg_regs_other hne_dst_src.symm)]
    exact PartialState.singletonReg_regs_self
  have hs_regs_src : s.regs.get src = v := hcr_regs src v hp_regs_src
  -- 5. hR doesn't own dst, src, or pc.
  have hR_no_dst : hR.regs dst = none := by
    rcases hd_PQR_regs dst with h | h
    · rw [← hu_PQ] at h
      rw [PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self] at h
      nomatch h
    · exact h
  have hR_no_src : hR.regs src = none := by
    rcases hd_PQR_regs src with h | h
    · rw [← hu_PQ] at h
      rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other hne_dst_src.symm)] at h
      rw [PartialState.singletonReg_regs_self] at h
      nomatch h
    · exact h
  have hR_no_pc : hR.pc = none := hRfree _ hR_sat
  -- 6. Fetch and step.
  have hfetch : fetch s.pc = some (.mov64 dst (.reg src)) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hexec : executeFn fetch s 1 =
      { s with regs := s.regs.set dst v, pc := s.pc + 1 } := by
    have h0 : executeFn fetch s 1 =
        { s with regs := s.regs.set dst (s.regs.get src), pc := s.pc + 1 } := by
      simp [executeFn, step, hex, hfetch]
    rw [h0, hs_regs_src]
  -- 7. hp's mem = hR's mem (neither singletonReg owns memory).
  have hp_mem : ∀ a, hp.mem a = hR.mem a := by
    intro a
    rw [← hp_eq]
    rw [PartialState.union_mem_of_left_none
        (PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a))]
  -- 8. Build the post.
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_⟩
  · rw [hexec]; show s.pc + 1 = pc + 1; rw [hpc]
  · rw [hexec]; exact hex
  · rw [hexec]
    refine ⟨((PartialState.singletonReg dst v).union
              (PartialState.singletonReg src v)).union hR, ?_,
            (PartialState.singletonReg dst v).union
              (PartialState.singletonReg src v),
            hR, ?_, rfl,
            ⟨PartialState.singletonReg dst v, PartialState.singletonReg src v,
             ?_, rfl, rfl, rfl⟩,
            hR_sat⟩
    · -- Compatibility.
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro r vr hvr
        by_cases hrdst : r = dst
        · -- r = dst: inner union picks (singletonReg dst v).regs dst = some v.
          have hinner_dst :
              ((PartialState.singletonReg dst v).union
                (PartialState.singletonReg src v)).regs dst = some v :=
            PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
          rw [hrdst] at hvr
          rw [PartialState.union_regs_of_left_some hinner_dst] at hvr
          have hveq : vr = v := (Option.some.inj hvr).symm
          rw [hrdst, hveq]
          show (s.regs.set dst v).get dst = v
          exact RegFile.get_set_self _ _ _ hne
        · by_cases hrsrc : r = src
          · -- r = src: inner union falls through to (singletonReg src v).regs src = some v.
            have hinner_src :
                ((PartialState.singletonReg dst v).union
                  (PartialState.singletonReg src v)).regs src = some v := by
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hne_dst_src.symm)]
              exact PartialState.singletonReg_regs_self
            rw [hrsrc] at hvr
            rw [PartialState.union_regs_of_left_some hinner_src] at hvr
            have hveq : vr = v := (Option.some.inj hvr).symm
            rw [hrsrc, hveq]
            show (s.regs.set dst v).get src = v
            rw [RegFile.get_set_diff _ _ _ _ hne_dst_src.symm]
            exact hs_regs_src
          · -- r owned by hR (or none): both inner singletons return none, outer falls through.
            have hinner_none_new :
                ((PartialState.singletonReg dst v).union
                  (PartialState.singletonReg src v)).regs r = none := by
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrdst)]
              exact PartialState.singletonReg_regs_other hrsrc
            have hinner_none_old :
                ((PartialState.singletonReg dst vOld).union
                  (PartialState.singletonReg src v)).regs r = none := by
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrdst)]
              exact PartialState.singletonReg_regs_other hrsrc
            rw [PartialState.union_regs_of_left_none hinner_none_new] at hvr
            show (s.regs.set dst v).get r = vr
            rw [RegFile.get_set_diff _ _ _ _ hrdst]
            apply hcr_regs r vr
            rw [← hp_eq]
            rw [PartialState.union_regs_of_left_none hinner_none_old]
            exact hvr
      · intro a vm hvm
        rw [PartialState.union_mem_of_left_none
            (PartialState.union_mem_of_left_none
              (PartialState.singletonReg_mem _))] at hvm
        show s.mem a = vm
        exact hcm_mem a vm ((hp_mem a).symm ▸ hvm)
      · intro vp hvp
        rw [PartialState.union_pc_of_left_none
            (PartialState.union_pc_of_left_none
              PartialState.singletonReg_pc)] at hvp
        rw [hR_no_pc] at hvp
        nomatch hvp
      · intro rd hva
        first
        | exact hcompat.returnData rd hva
        | (rw [PartialState.union_returnData_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.returnData rd
             (by rw [
                    ← hu_PQR,
                    ← hu_PQ,
                    PartialState.union_returnData_of_left_none (by first | rfl | simp)]
                 exact hva))
        | (rw [PartialState.union_returnData_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.returnData rd
             (by rw [
                    ← hu_PQR,
                    ← hu_PQ,
                    PartialState.union_returnData_of_left_none (by first | rfl | simp)]
                 exact hva))
        | (rw [PartialState.union_returnData_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.returnData rd (by rw [← hu_PQR]; exact hva))
      · intro cs hva
        first
        | exact hcompat.callStack cs hva
        | (rw [PartialState.union_callStack_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.callStack cs
             (by rw [
                    ← hu_PQR,
                    ← hu_PQ,
                    PartialState.union_callStack_of_left_none (by first | rfl | simp)]
                 exact hva))
        | (rw [PartialState.union_callStack_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.callStack cs
             (by rw [
                    ← hu_PQR,
                    ← hu_PQ,
                    PartialState.union_callStack_of_left_none (by first | rfl | simp)]
                 exact hva))
        | (rw [PartialState.union_callStack_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.callStack cs (by rw [← hu_PQR]; exact hva))
    · -- (singletonReg dst v ⊎ singletonReg src v).Disjoint hR
      refine ⟨?_, ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
      · intro r
        by_cases hrdst : r = dst
        · rw [hrdst]; right; exact hR_no_dst
        · by_cases hrsrc : r = src
          · rw [hrsrc]; right; exact hR_no_src
          · left
            rw [PartialState.union_regs_of_left_none
                (PartialState.singletonReg_regs_other hrdst)]
            exact PartialState.singletonReg_regs_other hrsrc
      · intro a; left
        rw [PartialState.union_mem_of_left_none
            (PartialState.singletonReg_mem _)]
        exact PartialState.singletonReg_mem _
      · left
        rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
        exact PartialState.singletonReg_pc
    · -- (singletonReg dst v).Disjoint (singletonReg src v)
      refine ⟨?_, ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
      · intro r
        by_cases hrdst : r = dst
        · rw [hrdst]; right; exact PartialState.singletonReg_regs_other hne_dst_src
        · left; exact PartialState.singletonReg_regs_other hrdst
      · intro a; left; exact PartialState.singletonReg_mem _
      · left; exact PartialState.singletonReg_pc

/-! ## ALU-with-immediate ops via the 1-reg-write helper

These are each two lines: the spec statement and a `simp [step, hdst]`
proof that `step` produces the expected state given the precondition. -/

/-- `add64 dst, imm`: wrapping 64-bit add with immediate. -/
theorem add64_imm_spec (dst : Reg) (imm : Int) (vOld : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.add64 dst (.imm imm)))
      (dst ↦ᵣ vOld)
      (dst ↦ᵣ wrapAdd vOld (toU64 imm)) :=
  cuTripleWithin_1reg_write dst vOld (wrapAdd vOld (toU64 imm)) pc
    (.add64 dst (.imm imm)) hne
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-- `sub64 dst, imm`: wrapping 64-bit subtract with immediate. -/
theorem sub64_imm_spec (dst : Reg) (imm : Int) (vOld : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.sub64 dst (.imm imm)))
      (dst ↦ᵣ vOld)
      (dst ↦ᵣ wrapSub vOld (toU64 imm)) :=
  cuTripleWithin_1reg_write dst vOld (wrapSub vOld (toU64 imm)) pc
    (.sub64 dst (.imm imm)) hne
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-- `mul64 dst, imm`: wrapping 64-bit multiply with immediate. -/
theorem mul64_imm_spec (dst : Reg) (imm : Int) (vOld : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.mul64 dst (.imm imm)))
      (dst ↦ᵣ vOld)
      (dst ↦ᵣ wrapMul vOld (toU64 imm)) :=
  cuTripleWithin_1reg_write dst vOld (wrapMul vOld (toU64 imm)) pc
    (.mul64 dst (.imm imm)) hne
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-- `neg64 dst`: wrapping 64-bit negation. -/
theorem neg64_spec (dst : Reg) (vOld : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.neg64 dst))
      (dst ↦ᵣ vOld)
      (dst ↦ᵣ wrapNeg vOld) :=
  cuTripleWithin_1reg_write dst vOld (wrapNeg vOld) pc (.neg64 dst) hne
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-- `and64 dst, imm`: bitwise AND with immediate (truncated to 64 bits). -/
theorem and64_imm_spec (dst : Reg) (imm : Int) (vOld : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.and64 dst (.imm imm)))
      (dst ↦ᵣ vOld)
      (dst ↦ᵣ ((vOld &&& toU64 imm) % U64_MODULUS)) :=
  cuTripleWithin_1reg_write dst vOld ((vOld &&& toU64 imm) % U64_MODULUS) pc
    (.and64 dst (.imm imm)) hne
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-- `or64 dst, imm`: bitwise OR with immediate (truncated to 64 bits). -/
theorem or64_imm_spec (dst : Reg) (imm : Int) (vOld : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.or64 dst (.imm imm)))
      (dst ↦ᵣ vOld)
      (dst ↦ᵣ ((vOld ||| toU64 imm) % U64_MODULUS)) :=
  cuTripleWithin_1reg_write dst vOld ((vOld ||| toU64 imm) % U64_MODULUS) pc
    (.or64 dst (.imm imm)) hne
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-- `xor64 dst, imm`: bitwise XOR with immediate (truncated to 64 bits). -/
theorem xor64_imm_spec (dst : Reg) (imm : Int) (vOld : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.xor64 dst (.imm imm)))
      (dst ↦ᵣ vOld)
      (dst ↦ᵣ ((vOld ^^^ toU64 imm) % U64_MODULUS)) :=
  cuTripleWithin_1reg_write dst vOld ((vOld ^^^ toU64 imm) % U64_MODULUS) pc
    (.xor64 dst (.imm imm)) hne
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-- `lsh64 dst, imm`: logical left shift by immediate (modulo 64), 64-bit truncated. -/
theorem lsh64_imm_spec (dst : Reg) (imm : Int) (vOld : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.lsh64 dst (.imm imm)))
      (dst ↦ᵣ vOld)
      (dst ↦ᵣ ((vOld <<< (toU64 imm % 64)) % U64_MODULUS)) :=
  cuTripleWithin_1reg_write dst vOld ((vOld <<< (toU64 imm % 64)) % U64_MODULUS) pc
    (.lsh64 dst (.imm imm)) hne
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-- `rsh64 dst, imm`: logical right shift by immediate (modulo 64). -/
theorem rsh64_imm_spec (dst : Reg) (imm : Int) (vOld : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.rsh64 dst (.imm imm)))
      (dst ↦ᵣ vOld)
      (dst ↦ᵣ (vOld >>> (toU64 imm % 64))) :=
  cuTripleWithin_1reg_write dst vOld (vOld >>> (toU64 imm % 64)) pc
    (.rsh64 dst (.imm imm)) hne
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-- `lddw dst, imm`: load 64-bit immediate. Semantically identical to
    `mov64 dst (.imm imm)` in our model (the binary encoding occupies two
    instruction slots; we abstract that away). -/
theorem lddw_spec (dst : Reg) (imm : Int) (vOld : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.lddw dst imm))
      (dst ↦ᵣ vOld)
      (dst ↦ᵣ toU64 imm) :=
  cuTripleWithin_1reg_write dst vOld (toU64 imm) pc (.lddw dst imm) hne
    (fun _ _ => by simp only [step])

/-! ## Generic 2-register-read, 1-register-write spec

The reg-source analogue of `cuTripleWithin_1reg_write`: instruction
reads `dst` (current value `vOld`) and `src` (value `v`), writes
`vNew` to `dst`, leaves `src` and memory unchanged, increments PC,
takes one step. Covers every register-source ALU instruction:
`add64/sub64/mul64/and64/or64/xor64/lsh64/rsh64/arsh64 dst (.reg src)`
and their 32-bit variants. `dst ≠ src` falls out of the precondition's
inner disjointness — no extra hypothesis required. -/

theorem cuTripleWithin_2reg_write
    (dst src : Reg) (vOld v vNew : Nat) (pc : Nat) (insn : Insn)
    (hne : dst ≠ .r10)
    (h_step : ∀ s : State, s.regs.get dst = vOld → s.regs.get src = v →
        step insn s = { s with regs := s.regs.set dst vNew, pc := s.pc + 1 }) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc insn)
      ((dst ↦ᵣ vOld) ** (src ↦ᵣ v))
      ((dst ↦ᵣ vNew) ** (src ↦ᵣ v)) := by
  intro R hRfree fetch hcr s hPR hpc hex
  obtain ⟨hp, hcompat, hPQ, hR, hd_PQR, hu_PQR, hPQ_pred, hR_sat⟩ := hPR
  obtain ⟨h_dst, h_src, hd_dst_src, hu_PQ, h_dst_eq, h_src_eq⟩ := hPQ_pred
  rw [h_dst_eq] at hu_PQ hd_dst_src
  rw [h_src_eq] at hu_PQ hd_dst_src
  clear h_dst_eq h_src_eq h_dst h_src
  have hcr_regs := hcompat.regs
  have hcm_mem := hcompat.mem
  have hd_PQR_regs := hd_PQR.regs
  have hne_dst_src : dst ≠ src := by
    have hd_inner_regs := hd_dst_src.regs
    intro habs
    rcases hd_inner_regs dst with h | h
    · rw [PartialState.singletonReg_regs_self] at h; nomatch h
    · rw [habs, PartialState.singletonReg_regs_self] at h; nomatch h
  have hp_eq : ((PartialState.singletonReg dst vOld).union
                (PartialState.singletonReg src v)).union hR = hp := by
    rw [hu_PQ]; exact hu_PQR
  have hp_regs_dst : hp.regs dst = some vOld := by
    rw [← hp_eq]
    apply PartialState.union_regs_of_left_some
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have hp_regs_src : hp.regs src = some v := by
    rw [← hp_eq]
    apply PartialState.union_regs_of_left_some
    rw [PartialState.union_regs_of_left_none
        (PartialState.singletonReg_regs_other hne_dst_src.symm)]
    exact PartialState.singletonReg_regs_self
  have hs_regs_dst : s.regs.get dst = vOld := hcr_regs dst vOld hp_regs_dst
  have hs_regs_src : s.regs.get src = v    := hcr_regs src v    hp_regs_src
  have hR_no_dst : hR.regs dst = none := by
    rcases hd_PQR_regs dst with h | h
    · rw [← hu_PQ] at h
      rw [PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self] at h
      nomatch h
    · exact h
  have hR_no_src : hR.regs src = none := by
    rcases hd_PQR_regs src with h | h
    · rw [← hu_PQ] at h
      rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other hne_dst_src.symm)] at h
      rw [PartialState.singletonReg_regs_self] at h
      nomatch h
    · exact h
  have hR_no_pc : hR.pc = none := hRfree _ hR_sat
  have hfetch : fetch s.pc = some insn := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hexec : executeFn fetch s 1 =
      { s with regs := s.regs.set dst vNew, pc := s.pc + 1 } := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 insn hex hfetch,
        executeFn_zero, h_step s hs_regs_dst hs_regs_src]
  have hp_mem : ∀ a, hp.mem a = hR.mem a := by
    intro a
    rw [← hp_eq]
    rw [PartialState.union_mem_of_left_none
        (PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a))]
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_⟩
  · rw [hexec]; show s.pc + 1 = pc + 1; rw [hpc]
  · rw [hexec]; exact hex
  · rw [hexec]
    refine ⟨((PartialState.singletonReg dst vNew).union
              (PartialState.singletonReg src v)).union hR, ?_,
            (PartialState.singletonReg dst vNew).union
              (PartialState.singletonReg src v),
            hR, ?_, rfl,
            ⟨PartialState.singletonReg dst vNew, PartialState.singletonReg src v,
             ?_, rfl, rfl, rfl⟩,
            hR_sat⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro r vr hvr
        by_cases hrdst : r = dst
        · have hinner_dst :
              ((PartialState.singletonReg dst vNew).union
                (PartialState.singletonReg src v)).regs dst = some vNew :=
            PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
          rw [hrdst] at hvr
          rw [PartialState.union_regs_of_left_some hinner_dst] at hvr
          have hveq : vr = vNew := (Option.some.inj hvr).symm
          rw [hrdst, hveq]
          show (s.regs.set dst vNew).get dst = vNew
          exact RegFile.get_set_self _ _ _ hne
        · by_cases hrsrc : r = src
          · have hinner_src :
                ((PartialState.singletonReg dst vNew).union
                  (PartialState.singletonReg src v)).regs src = some v := by
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hne_dst_src.symm)]
              exact PartialState.singletonReg_regs_self
            rw [hrsrc] at hvr
            rw [PartialState.union_regs_of_left_some hinner_src] at hvr
            have hveq : vr = v := (Option.some.inj hvr).symm
            rw [hrsrc, hveq]
            show (s.regs.set dst vNew).get src = v
            rw [RegFile.get_set_diff _ _ _ _ hne_dst_src.symm]
            exact hs_regs_src
          · have hinner_none_new :
                ((PartialState.singletonReg dst vNew).union
                  (PartialState.singletonReg src v)).regs r = none := by
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrdst)]
              exact PartialState.singletonReg_regs_other hrsrc
            have hinner_none_old :
                ((PartialState.singletonReg dst vOld).union
                  (PartialState.singletonReg src v)).regs r = none := by
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrdst)]
              exact PartialState.singletonReg_regs_other hrsrc
            rw [PartialState.union_regs_of_left_none hinner_none_new] at hvr
            show (s.regs.set dst vNew).get r = vr
            rw [RegFile.get_set_diff _ _ _ _ hrdst]
            apply hcr_regs r vr
            rw [← hp_eq]
            rw [PartialState.union_regs_of_left_none hinner_none_old]
            exact hvr
      · intro a vm hvm
        rw [PartialState.union_mem_of_left_none
            (PartialState.union_mem_of_left_none
              (PartialState.singletonReg_mem _))] at hvm
        show s.mem a = vm
        exact hcm_mem a vm ((hp_mem a).symm ▸ hvm)
      · intro vp hvp
        rw [PartialState.union_pc_of_left_none
            (PartialState.union_pc_of_left_none
              PartialState.singletonReg_pc)] at hvp
        rw [hR_no_pc] at hvp
        nomatch hvp
      · intro rd hva
        first
        | exact hcompat.returnData rd hva
        | (rw [PartialState.union_returnData_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.returnData rd
             (by rw [
                    ← hu_PQR,
                    ← hu_PQ,
                    PartialState.union_returnData_of_left_none (by first | rfl | simp)]
                 exact hva))
        | (rw [PartialState.union_returnData_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.returnData rd
             (by rw [
                    ← hu_PQR,
                    ← hu_PQ,
                    PartialState.union_returnData_of_left_none (by first | rfl | simp)]
                 exact hva))
        | (rw [PartialState.union_returnData_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.returnData rd (by rw [← hu_PQR]; exact hva))
      · intro cs hva
        first
        | exact hcompat.callStack cs hva
        | (rw [PartialState.union_callStack_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.callStack cs
             (by rw [
                    ← hu_PQR,
                    ← hu_PQ,
                    PartialState.union_callStack_of_left_none (by first | rfl | simp)]
                 exact hva))
        | (rw [PartialState.union_callStack_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.callStack cs
             (by rw [
                    ← hu_PQR,
                    ← hu_PQ,
                    PartialState.union_callStack_of_left_none (by first | rfl | simp)]
                 exact hva))
        | (rw [PartialState.union_callStack_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.callStack cs (by rw [← hu_PQR]; exact hva))
    · refine ⟨?_, ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
      · intro r
        by_cases hrdst : r = dst
        · rw [hrdst]; right; exact hR_no_dst
        · by_cases hrsrc : r = src
          · rw [hrsrc]; right; exact hR_no_src
          · left
            rw [PartialState.union_regs_of_left_none
                (PartialState.singletonReg_regs_other hrdst)]
            exact PartialState.singletonReg_regs_other hrsrc
      · intro a; left
        rw [PartialState.union_mem_of_left_none
            (PartialState.singletonReg_mem _)]
        exact PartialState.singletonReg_mem _
      · left
        rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
        exact PartialState.singletonReg_pc
    · refine ⟨?_, ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
      · intro r
        by_cases hrdst : r = dst
        · rw [hrdst]; right; exact PartialState.singletonReg_regs_other hne_dst_src
        · left; exact PartialState.singletonReg_regs_other hrdst
      · intro a; left; exact PartialState.singletonReg_mem _
      · left; exact PartialState.singletonReg_pc

/-! ## 64-bit ALU reg-source specs via the 2-reg-write helper

Reg-source counterparts of the `*_imm_spec` family above. Each is a
single-line `cuTripleWithin_2reg_write` invocation whose only payload
is showing `step` reduces to the expected `set dst vNew` form.

`mov64_reg_spec` leads the section because it's the simplest reg-source
spec — it ignores `vOld` entirely and just copies `v` into `dst`. -/

/-- `mov64 dst, src`: register copy. Derived form of
    `mov64_reg_spec_manual`. -/
theorem mov64_reg_spec (dst src : Reg) (vOld v : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.mov64 dst (.reg src)))
      ((dst ↦ᵣ vOld) ** (src ↦ᵣ v))
      ((dst ↦ᵣ v) ** (src ↦ᵣ v)) :=
  cuTripleWithin_2reg_write dst src vOld v v pc (.mov64 dst (.reg src)) hne
    (fun _ _ hsrc => by simp only [step, resolveSrc]; rw [hsrc])

/-- `add64 dst, src`: wrapping 64-bit add of two registers. -/
theorem add64_reg_spec (dst src : Reg) (vOld v : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.add64 dst (.reg src)))
      ((dst ↦ᵣ vOld) ** (src ↦ᵣ v))
      ((dst ↦ᵣ wrapAdd vOld v) ** (src ↦ᵣ v)) :=
  cuTripleWithin_2reg_write dst src vOld v (wrapAdd vOld v) pc
    (.add64 dst (.reg src)) hne
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-- `sub64 dst, src`: wrapping 64-bit subtract of two registers. -/
theorem sub64_reg_spec (dst src : Reg) (vOld v : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.sub64 dst (.reg src)))
      ((dst ↦ᵣ vOld) ** (src ↦ᵣ v))
      ((dst ↦ᵣ wrapSub vOld v) ** (src ↦ᵣ v)) :=
  cuTripleWithin_2reg_write dst src vOld v (wrapSub vOld v) pc
    (.sub64 dst (.reg src)) hne
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-- `mul64 dst, src`: wrapping 64-bit multiply of two registers. -/
theorem mul64_reg_spec (dst src : Reg) (vOld v : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.mul64 dst (.reg src)))
      ((dst ↦ᵣ vOld) ** (src ↦ᵣ v))
      ((dst ↦ᵣ wrapMul vOld v) ** (src ↦ᵣ v)) :=
  cuTripleWithin_2reg_write dst src vOld v (wrapMul vOld v) pc
    (.mul64 dst (.reg src)) hne
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-- `and64 dst, src`: bitwise AND of two registers (mod U64_MODULUS). -/
theorem and64_reg_spec (dst src : Reg) (vOld v : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.and64 dst (.reg src)))
      ((dst ↦ᵣ vOld) ** (src ↦ᵣ v))
      ((dst ↦ᵣ ((vOld &&& v) % U64_MODULUS)) ** (src ↦ᵣ v)) :=
  cuTripleWithin_2reg_write dst src vOld v ((vOld &&& v) % U64_MODULUS) pc
    (.and64 dst (.reg src)) hne
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-- `or64 dst, src`: bitwise OR of two registers (mod U64_MODULUS). -/
theorem or64_reg_spec (dst src : Reg) (vOld v : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.or64 dst (.reg src)))
      ((dst ↦ᵣ vOld) ** (src ↦ᵣ v))
      ((dst ↦ᵣ ((vOld ||| v) % U64_MODULUS)) ** (src ↦ᵣ v)) :=
  cuTripleWithin_2reg_write dst src vOld v ((vOld ||| v) % U64_MODULUS) pc
    (.or64 dst (.reg src)) hne
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-- `xor64 dst, src`: bitwise XOR of two registers (mod U64_MODULUS). -/
theorem xor64_reg_spec (dst src : Reg) (vOld v : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.xor64 dst (.reg src)))
      ((dst ↦ᵣ vOld) ** (src ↦ᵣ v))
      ((dst ↦ᵣ ((vOld ^^^ v) % U64_MODULUS)) ** (src ↦ᵣ v)) :=
  cuTripleWithin_2reg_write dst src vOld v ((vOld ^^^ v) % U64_MODULUS) pc
    (.xor64 dst (.reg src)) hne
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-- `lsh64 dst, src`: left shift by (src mod 64), truncated to 64 bits. -/
theorem lsh64_reg_spec (dst src : Reg) (vOld v : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.lsh64 dst (.reg src)))
      ((dst ↦ᵣ vOld) ** (src ↦ᵣ v))
      ((dst ↦ᵣ ((vOld <<< (v % 64)) % U64_MODULUS)) ** (src ↦ᵣ v)) :=
  cuTripleWithin_2reg_write dst src vOld v ((vOld <<< (v % 64)) % U64_MODULUS) pc
    (.lsh64 dst (.reg src)) hne
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-- `rsh64 dst, src`: logical right shift by (src mod 64). -/
theorem rsh64_reg_spec (dst src : Reg) (vOld v : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.rsh64 dst (.reg src)))
      ((dst ↦ᵣ vOld) ** (src ↦ᵣ v))
      ((dst ↦ᵣ (vOld >>> (v % 64))) ** (src ↦ᵣ v)) :=
  cuTripleWithin_2reg_write dst src vOld v (vOld >>> (v % 64)) pc
    (.rsh64 dst (.reg src)) hne
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-! ## arsh64 — arithmetic right shift

Sign-extending right shift: if the high bit of `vOld` is set
(`vOld ≥ U64_MODULUS / 2`), the shifted-out bits are filled with 1s
in the new high bits. The post-value is exactly what `step .arsh64`
computes — packaged into a `let` so the spec reads with the
expression close to the definition site. -/

/-- `arsh64 dst, imm`: arithmetic right shift by (imm mod 64). -/
theorem arsh64_imm_spec (dst : Reg) (imm : Int) (vOld : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.arsh64 dst (.imm imm)))
      (dst ↦ᵣ vOld)
      (dst ↦ᵣ
        (let shift := toU64 imm % 64
         if vOld < U64_MODULUS / 2 then vOld >>> shift
         else let shifted := vOld >>> shift
              let highBits := (U64_MODULUS - 1) - (U64_MODULUS / (2 ^ shift) - 1)
              (shifted ||| highBits) % U64_MODULUS)) :=
  cuTripleWithin_1reg_write dst vOld _ pc (.arsh64 dst (.imm imm)) hne
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-- `arsh64 dst, src`: arithmetic right shift by (src mod 64). -/
theorem arsh64_reg_spec (dst src : Reg) (vOld v : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.arsh64 dst (.reg src)))
      ((dst ↦ᵣ vOld) ** (src ↦ᵣ v))
      ((dst ↦ᵣ
        (let shift := v % 64
         if vOld < U64_MODULUS / 2 then vOld >>> shift
         else let shifted := vOld >>> shift
              let highBits := (U64_MODULUS - 1) - (U64_MODULUS / (2 ^ shift) - 1)
              (shifted ||| highBits) % U64_MODULUS)) ** (src ↦ᵣ v)) :=
  cuTripleWithin_2reg_write dst src vOld v _ pc (.arsh64 dst (.reg src)) hne
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-! ## 32-bit ALU ops via the 1-reg-write helper

Same pattern, but the new value is computed mod `U32_MODULUS` (the 32-bit
result is zero-extended to 64 bits). -/

/-- `mov32 dst, imm`: load 32-bit immediate (zero-extended to 64 bits). -/
theorem mov32_imm_spec (dst : Reg) (imm : Int) (vOld : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.mov32 dst (.imm imm)))
      (dst ↦ᵣ vOld)
      (dst ↦ᵣ (toU64 imm % U32_MODULUS)) :=
  cuTripleWithin_1reg_write dst vOld (toU64 imm % U32_MODULUS) pc
    (.mov32 dst (.imm imm)) hne
    (fun _ _ => by simp only [step, resolveSrc])

/-- `add32 dst, imm`: wrapping 32-bit add with immediate. -/
theorem add32_imm_spec (dst : Reg) (imm : Int) (vOld : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.add32 dst (.imm imm)))
      (dst ↦ᵣ vOld)
      (dst ↦ᵣ wrapAdd32 vOld (toU64 imm)) :=
  cuTripleWithin_1reg_write dst vOld (wrapAdd32 vOld (toU64 imm)) pc
    (.add32 dst (.imm imm)) hne
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-- `sub32 dst, imm`: wrapping 32-bit subtract with immediate. -/
theorem sub32_imm_spec (dst : Reg) (imm : Int) (vOld : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.sub32 dst (.imm imm)))
      (dst ↦ᵣ vOld)
      (dst ↦ᵣ wrapSub32 vOld (toU64 imm)) :=
  cuTripleWithin_1reg_write dst vOld (wrapSub32 vOld (toU64 imm)) pc
    (.sub32 dst (.imm imm)) hne
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-- `mul32 dst, imm`: wrapping 32-bit multiply with immediate. -/
theorem mul32_imm_spec (dst : Reg) (imm : Int) (vOld : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.mul32 dst (.imm imm)))
      (dst ↦ᵣ vOld)
      (dst ↦ᵣ wrapMul32 vOld (toU64 imm)) :=
  cuTripleWithin_1reg_write dst vOld (wrapMul32 vOld (toU64 imm)) pc
    (.mul32 dst (.imm imm)) hne
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-- `neg32 dst`: wrapping 32-bit negation. -/
theorem neg32_spec (dst : Reg) (vOld : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.neg32 dst))
      (dst ↦ᵣ vOld)
      (dst ↦ᵣ wrapNeg32 vOld) :=
  cuTripleWithin_1reg_write dst vOld (wrapNeg32 vOld) pc (.neg32 dst) hne
    (fun _ hdst => by simp only [step]; rw [hdst])

/-- `and32 dst, imm`: bitwise AND with immediate (mod U32_MODULUS). -/
theorem and32_imm_spec (dst : Reg) (imm : Int) (vOld : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.and32 dst (.imm imm)))
      (dst ↦ᵣ vOld)
      (dst ↦ᵣ ((vOld &&& toU64 imm) % U32_MODULUS)) :=
  cuTripleWithin_1reg_write dst vOld ((vOld &&& toU64 imm) % U32_MODULUS) pc
    (.and32 dst (.imm imm)) hne
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-- `or32 dst, imm`: bitwise OR with immediate (mod U32_MODULUS). -/
theorem or32_imm_spec (dst : Reg) (imm : Int) (vOld : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.or32 dst (.imm imm)))
      (dst ↦ᵣ vOld)
      (dst ↦ᵣ ((vOld ||| toU64 imm) % U32_MODULUS)) :=
  cuTripleWithin_1reg_write dst vOld ((vOld ||| toU64 imm) % U32_MODULUS) pc
    (.or32 dst (.imm imm)) hne
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-- `xor32 dst, imm`: bitwise XOR with immediate (mod U32_MODULUS). -/
theorem xor32_imm_spec (dst : Reg) (imm : Int) (vOld : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.xor32 dst (.imm imm)))
      (dst ↦ᵣ vOld)
      (dst ↦ᵣ ((vOld ^^^ toU64 imm) % U32_MODULUS)) :=
  cuTripleWithin_1reg_write dst vOld ((vOld ^^^ toU64 imm) % U32_MODULUS) pc
    (.xor32 dst (.imm imm)) hne
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-! ## 32-bit shifts via the 1-reg-write helper

Same pattern as the 64-bit shifts. `lsh32` and `rsh32` mask the
distance to 5 bits (mod 32); `rsh32` also masks the source to its
low 32 bits before shifting (matching `step`). -/

/-- `lsh32 dst, imm`: 32-bit left shift by (imm mod 32). -/
theorem lsh32_imm_spec (dst : Reg) (imm : Int) (vOld : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.lsh32 dst (.imm imm)))
      (dst ↦ᵣ vOld)
      (dst ↦ᵣ ((vOld <<< (toU64 imm % 32)) % U32_MODULUS)) :=
  cuTripleWithin_1reg_write dst vOld ((vOld <<< (toU64 imm % 32)) % U32_MODULUS) pc
    (.lsh32 dst (.imm imm)) hne
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-- `rsh32 dst, imm`: 32-bit logical right shift by (imm mod 32).
    Source is masked to its low 32 bits before shifting. -/
theorem rsh32_imm_spec (dst : Reg) (imm : Int) (vOld : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.rsh32 dst (.imm imm)))
      (dst ↦ᵣ vOld)
      (dst ↦ᵣ ((vOld % U32_MODULUS) >>> (toU64 imm % 32))) :=
  cuTripleWithin_1reg_write dst vOld ((vOld % U32_MODULUS) >>> (toU64 imm % 32)) pc
    (.rsh32 dst (.imm imm)) hne
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-- `arsh32 dst, imm`: 32-bit arithmetic right shift by (imm mod 32). -/
theorem arsh32_imm_spec (dst : Reg) (imm : Int) (vOld : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.arsh32 dst (.imm imm)))
      (dst ↦ᵣ vOld)
      (dst ↦ᵣ
        (let shift := toU64 imm % 32
         let a := vOld % U32_MODULUS
         if a < U32_MODULUS / 2 then a >>> shift
         else let shifted := a >>> shift
              let highBits := (U32_MODULUS - 1) - (U32_MODULUS / (2 ^ shift) - 1)
              (shifted ||| highBits) % U32_MODULUS)) :=
  cuTripleWithin_1reg_write dst vOld _ pc (.arsh32 dst (.imm imm)) hne
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-! ## 32-bit ALU reg-source specs via the 2-reg-write helper -/

/-- `mov32 dst, src`: zero-extended 32-bit register copy. -/
theorem mov32_reg_spec (dst src : Reg) (vOld v : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.mov32 dst (.reg src)))
      ((dst ↦ᵣ vOld) ** (src ↦ᵣ v))
      ((dst ↦ᵣ (v % U32_MODULUS)) ** (src ↦ᵣ v)) :=
  cuTripleWithin_2reg_write dst src vOld v (v % U32_MODULUS) pc
    (.mov32 dst (.reg src)) hne
    (fun _ _ hsrc => by simp only [step, resolveSrc]; rw [hsrc])

/-- `add32 dst, src`: wrapping 32-bit add of two registers. -/
theorem add32_reg_spec (dst src : Reg) (vOld v : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.add32 dst (.reg src)))
      ((dst ↦ᵣ vOld) ** (src ↦ᵣ v))
      ((dst ↦ᵣ wrapAdd32 vOld v) ** (src ↦ᵣ v)) :=
  cuTripleWithin_2reg_write dst src vOld v (wrapAdd32 vOld v) pc
    (.add32 dst (.reg src)) hne
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-- `sub32 dst, src`: wrapping 32-bit subtract of two registers. -/
theorem sub32_reg_spec (dst src : Reg) (vOld v : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.sub32 dst (.reg src)))
      ((dst ↦ᵣ vOld) ** (src ↦ᵣ v))
      ((dst ↦ᵣ wrapSub32 vOld v) ** (src ↦ᵣ v)) :=
  cuTripleWithin_2reg_write dst src vOld v (wrapSub32 vOld v) pc
    (.sub32 dst (.reg src)) hne
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-- `mul32 dst, src`: wrapping 32-bit multiply of two registers. -/
theorem mul32_reg_spec (dst src : Reg) (vOld v : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.mul32 dst (.reg src)))
      ((dst ↦ᵣ vOld) ** (src ↦ᵣ v))
      ((dst ↦ᵣ wrapMul32 vOld v) ** (src ↦ᵣ v)) :=
  cuTripleWithin_2reg_write dst src vOld v (wrapMul32 vOld v) pc
    (.mul32 dst (.reg src)) hne
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-- `and32 dst, src`: bitwise AND of two registers (mod U32_MODULUS). -/
theorem and32_reg_spec (dst src : Reg) (vOld v : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.and32 dst (.reg src)))
      ((dst ↦ᵣ vOld) ** (src ↦ᵣ v))
      ((dst ↦ᵣ ((vOld &&& v) % U32_MODULUS)) ** (src ↦ᵣ v)) :=
  cuTripleWithin_2reg_write dst src vOld v ((vOld &&& v) % U32_MODULUS) pc
    (.and32 dst (.reg src)) hne
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-- `or32 dst, src`: bitwise OR of two registers (mod U32_MODULUS). -/
theorem or32_reg_spec (dst src : Reg) (vOld v : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.or32 dst (.reg src)))
      ((dst ↦ᵣ vOld) ** (src ↦ᵣ v))
      ((dst ↦ᵣ ((vOld ||| v) % U32_MODULUS)) ** (src ↦ᵣ v)) :=
  cuTripleWithin_2reg_write dst src vOld v ((vOld ||| v) % U32_MODULUS) pc
    (.or32 dst (.reg src)) hne
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-- `xor32 dst, src`: bitwise XOR of two registers (mod U32_MODULUS). -/
theorem xor32_reg_spec (dst src : Reg) (vOld v : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.xor32 dst (.reg src)))
      ((dst ↦ᵣ vOld) ** (src ↦ᵣ v))
      ((dst ↦ᵣ ((vOld ^^^ v) % U32_MODULUS)) ** (src ↦ᵣ v)) :=
  cuTripleWithin_2reg_write dst src vOld v ((vOld ^^^ v) % U32_MODULUS) pc
    (.xor32 dst (.reg src)) hne
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-- `lsh32 dst, src`: 32-bit left shift by (src mod 32). -/
theorem lsh32_reg_spec (dst src : Reg) (vOld v : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.lsh32 dst (.reg src)))
      ((dst ↦ᵣ vOld) ** (src ↦ᵣ v))
      ((dst ↦ᵣ ((vOld <<< (v % 32)) % U32_MODULUS)) ** (src ↦ᵣ v)) :=
  cuTripleWithin_2reg_write dst src vOld v ((vOld <<< (v % 32)) % U32_MODULUS) pc
    (.lsh32 dst (.reg src)) hne
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-- `rsh32 dst, src`: 32-bit logical right shift by (src mod 32). -/
theorem rsh32_reg_spec (dst src : Reg) (vOld v : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.rsh32 dst (.reg src)))
      ((dst ↦ᵣ vOld) ** (src ↦ᵣ v))
      ((dst ↦ᵣ ((vOld % U32_MODULUS) >>> (v % 32))) ** (src ↦ᵣ v)) :=
  cuTripleWithin_2reg_write dst src vOld v ((vOld % U32_MODULUS) >>> (v % 32)) pc
    (.rsh32 dst (.reg src)) hne
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-- `arsh32 dst, src`: 32-bit arithmetic right shift by (src mod 32). -/
theorem arsh32_reg_spec (dst src : Reg) (vOld v : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.arsh32 dst (.reg src)))
      ((dst ↦ᵣ vOld) ** (src ↦ᵣ v))
      ((dst ↦ᵣ
        (let shift := v % 32
         let a := vOld % U32_MODULUS
         if a < U32_MODULUS / 2 then a >>> shift
         else let shifted := a >>> shift
              let highBits := (U32_MODULUS - 1) - (U32_MODULUS / (2 ^ shift) - 1)
              (shifted ||| highBits) % U32_MODULUS)) ** (src ↦ᵣ v)) :=
  cuTripleWithin_2reg_write dst src vOld v _ pc (.arsh32 dst (.reg src)) hne
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-! ## div / mod (64-bit and 32-bit)

Both `div` and `mod` short-circuit to `ERR_DIVIDE_BY_ZERO` when the
resolved divisor is zero. The triple captures the success branch:
each spec takes a `hnz : ... ≠ 0` hypothesis so the if-then-else in
`step` reduces to the else arm. 32-bit variants charge `b` after
masking to its low 32 bits (matching `step .div32`/`step .mod32`),
so the non-zero hypothesis is on `... % U32_MODULUS`. -/

/-- `div64 dst, imm`: 64-bit unsigned division (success path). -/
theorem div64_imm_spec (dst : Reg) (imm : Int) (vOld : Nat) (pc : Nat)
    (hne : dst ≠ .r10) (hnz : toU64 imm ≠ 0) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.div64 dst (.imm imm)))
      (dst ↦ᵣ vOld)
      (dst ↦ᵣ ((vOld / toU64 imm) % U64_MODULUS)) :=
  cuTripleWithin_1reg_write dst vOld ((vOld / toU64 imm) % U64_MODULUS) pc
    (.div64 dst (.imm imm)) hne
    (fun _ hdst => by simp only [step, resolveSrc, if_neg hnz]; rw [hdst])

/-- `div64 dst, src`: 64-bit unsigned division of two registers (success path). -/
theorem div64_reg_spec (dst src : Reg) (vOld v : Nat) (pc : Nat)
    (hne : dst ≠ .r10) (hnz : v ≠ 0) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.div64 dst (.reg src)))
      ((dst ↦ᵣ vOld) ** (src ↦ᵣ v))
      ((dst ↦ᵣ ((vOld / v) % U64_MODULUS)) ** (src ↦ᵣ v)) :=
  cuTripleWithin_2reg_write dst src vOld v ((vOld / v) % U64_MODULUS) pc
    (.div64 dst (.reg src)) hne
    (fun _ hdst hsrc => by
      simp only [step, resolveSrc]
      rw [hsrc, if_neg hnz, hdst])

/-- `mod64 dst, imm`: 64-bit modulo with immediate (success path). -/
theorem mod64_imm_spec (dst : Reg) (imm : Int) (vOld : Nat) (pc : Nat)
    (hne : dst ≠ .r10) (hnz : toU64 imm ≠ 0) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.mod64 dst (.imm imm)))
      (dst ↦ᵣ vOld)
      (dst ↦ᵣ (vOld % toU64 imm)) :=
  cuTripleWithin_1reg_write dst vOld (vOld % toU64 imm) pc
    (.mod64 dst (.imm imm)) hne
    (fun _ hdst => by simp only [step, resolveSrc, if_neg hnz]; rw [hdst])

/-- `mod64 dst, src`: 64-bit modulo of two registers (success path). -/
theorem mod64_reg_spec (dst src : Reg) (vOld v : Nat) (pc : Nat)
    (hne : dst ≠ .r10) (hnz : v ≠ 0) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.mod64 dst (.reg src)))
      ((dst ↦ᵣ vOld) ** (src ↦ᵣ v))
      ((dst ↦ᵣ (vOld % v)) ** (src ↦ᵣ v)) :=
  cuTripleWithin_2reg_write dst src vOld v (vOld % v) pc
    (.mod64 dst (.reg src)) hne
    (fun _ hdst hsrc => by
      simp only [step, resolveSrc]
      rw [hsrc, if_neg hnz, hdst])

/-- `div32 dst, imm`: 32-bit unsigned division (success path).
    Both operand and divisor are masked to their low 32 bits. -/
theorem div32_imm_spec (dst : Reg) (imm : Int) (vOld : Nat) (pc : Nat)
    (hne : dst ≠ .r10) (hnz : toU64 imm % U32_MODULUS ≠ 0) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.div32 dst (.imm imm)))
      (dst ↦ᵣ vOld)
      (dst ↦ᵣ ((vOld % U32_MODULUS / (toU64 imm % U32_MODULUS)) % U32_MODULUS)) :=
  cuTripleWithin_1reg_write dst vOld
    ((vOld % U32_MODULUS / (toU64 imm % U32_MODULUS)) % U32_MODULUS) pc
    (.div32 dst (.imm imm)) hne
    (fun _ hdst => by simp only [step, resolveSrc, if_neg hnz]; rw [hdst])

/-- `div32 dst, src`: 32-bit unsigned division of two registers (success path). -/
theorem div32_reg_spec (dst src : Reg) (vOld v : Nat) (pc : Nat)
    (hne : dst ≠ .r10) (hnz : v % U32_MODULUS ≠ 0) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.div32 dst (.reg src)))
      ((dst ↦ᵣ vOld) ** (src ↦ᵣ v))
      ((dst ↦ᵣ ((vOld % U32_MODULUS / (v % U32_MODULUS)) % U32_MODULUS)) ** (src ↦ᵣ v)) :=
  cuTripleWithin_2reg_write dst src vOld v
    ((vOld % U32_MODULUS / (v % U32_MODULUS)) % U32_MODULUS) pc
    (.div32 dst (.reg src)) hne
    (fun _ hdst hsrc => by
      simp only [step, resolveSrc]
      rw [hsrc, if_neg hnz, hdst])

/-- `mod32 dst, imm`: 32-bit modulo with immediate (success path). -/
theorem mod32_imm_spec (dst : Reg) (imm : Int) (vOld : Nat) (pc : Nat)
    (hne : dst ≠ .r10) (hnz : toU64 imm % U32_MODULUS ≠ 0) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.mod32 dst (.imm imm)))
      (dst ↦ᵣ vOld)
      (dst ↦ᵣ (vOld % U32_MODULUS % (toU64 imm % U32_MODULUS))) :=
  cuTripleWithin_1reg_write dst vOld
    (vOld % U32_MODULUS % (toU64 imm % U32_MODULUS)) pc
    (.mod32 dst (.imm imm)) hne
    (fun _ hdst => by simp only [step, resolveSrc, if_neg hnz]; rw [hdst])

/-- `mod32 dst, src`: 32-bit modulo of two registers (success path). -/
theorem mod32_reg_spec (dst src : Reg) (vOld v : Nat) (pc : Nat)
    (hne : dst ≠ .r10) (hnz : v % U32_MODULUS ≠ 0) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.mod32 dst (.reg src)))
      ((dst ↦ᵣ vOld) ** (src ↦ᵣ v))
      ((dst ↦ᵣ (vOld % U32_MODULUS % (v % U32_MODULUS))) ** (src ↦ᵣ v)) :=
  cuTripleWithin_2reg_write dst src vOld v
    (vOld % U32_MODULUS % (v % U32_MODULUS)) pc
    (.mod32 dst (.reg src)) hne
    (fun _ hdst hsrc => by
      simp only [step, resolveSrc]
      rw [hsrc, if_neg hnz, hdst])


end SVM.SBPF
