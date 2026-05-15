/-
  Per-instruction separation-logic Hoare triples for sBPF.

  Each spec is `cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc insn) P Q`:
  one compute unit per instruction (in this layer — true CU pricing will
  scale this in a later phase), code requirement pinning the instruction at
  `pc`, and a separation-logic pre/post over the resources the instruction
  reads and writes.

  This file currently proves only the simplest cases — pure-ALU 64-bit moves
  — from first principles, as a methodology proof-of-concept. The pattern
  generalizes via to-be-built `generic_*_spec` helpers (Phase A / B).
-/

import Svm.SBPF.CPSSpec

namespace Svm.SBPF

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
  obtain ⟨hcr_regs, hcm_mem, _⟩ := hcompat
  obtain ⟨hd_regs, _, _⟩ := hd
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
    · refine ⟨?_, ?_, ?_⟩
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
    · refine ⟨?_, ?_, ?_⟩
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
  obtain ⟨hcr_regs, hcm_mem, _hcp_pc⟩ := hcompat
  obtain ⟨hd_regs, _hd_mem, _hd_pc⟩ := hd
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
      refine ⟨?_, ?_, ?_⟩
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
    · -- Disjointness: singletonReg dst (toU64 imm) is disjoint from hR.
      refine ⟨?_, ?_, ?_⟩
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
  obtain ⟨hcr_regs, hcm_mem, _hcp_pc⟩ := hcompat
  obtain ⟨hd_PQR_regs, _, _⟩ := hd_PQR
  -- 2. dst ≠ src from inner disjointness.
  have hne_dst_src : dst ≠ src := by
    obtain ⟨hd_inner_regs, _, _⟩ := hd_dst_src
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
      refine ⟨?_, ?_, ?_⟩
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
    · -- (singletonReg dst v ⊎ singletonReg src v).Disjoint hR
      refine ⟨?_, ?_, ?_⟩
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
      refine ⟨?_, ?_, ?_⟩
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
  obtain ⟨hcr_regs, hcm_mem, _⟩ := hcompat
  obtain ⟨hd_PQR_regs, _, _⟩ := hd_PQR
  have hne_dst_src : dst ≠ src := by
    obtain ⟨hd_inner_regs, _, _⟩ := hd_dst_src
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
    · refine ⟨?_, ?_, ?_⟩
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
    · refine ⟨?_, ?_, ?_⟩
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
    · refine ⟨?_, ?_, ?_⟩
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

/-! ## Conditional-jump helpers

Conditional jumps read one or two registers and modify only the PC.
The precondition and postcondition are identical (the read registers
keep their values); the exit PC depends on the runtime condition,
which the caller supplies as a `Decidable Prop`. The condition is
already evaluated in the spec's exit-PC term, so callers
case-split externally (`by_cases hc : cond`) and propagate the right
exit through the macro composition. -/

/-- Generic 1-register-read conditional jump: instruction reads `dst`
    (value `vDst`), tests `cond`, jumps to `target` if true and falls
    through to `pc + 1` otherwise. Registers and memory unchanged. -/
theorem cuTripleWithin_1reg_cjump
    (dst : Reg) (vDst : Nat) (pc target : Nat) (insn : Insn)
    (cond : Prop) [Decidable cond]
    (h_step : ∀ s : State, s.regs.get dst = vDst →
        step insn s = { s with pc := if cond then target else s.pc + 1 }) :
    cuTripleWithin 1 pc (if cond then target else pc + 1)
      (CodeReq.singleton pc insn) (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) := by
  intro R hRfree fetch hcr s hPR hpc hex
  obtain ⟨hp, hcompat, h1, hR, hd, hu, hreg, hRsat⟩ := hPR
  rw [hreg] at hu hd
  clear hreg h1
  obtain ⟨hcr_regs, hcm_mem, _⟩ := hcompat
  have hp_regs_dst : hp.regs dst = some vDst := by
    rw [← hu]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have hs_regs_dst : s.regs.get dst = vDst := hcr_regs dst vDst hp_regs_dst
  have hR_no_pc : hR.pc = none := hRfree _ hRsat
  have hfetch : fetch s.pc = some insn := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hexec : executeFn fetch s 1 =
      { s with pc := if cond then target else s.pc + 1 } := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch,
        executeFn_zero, h_step s hs_regs_dst]
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_⟩
  · rw [hexec]
    show (if cond then target else s.pc + 1) = if cond then target else pc + 1
    rw [hpc]
  · rw [hexec]; exact hex
  · rw [hexec]
    refine ⟨(PartialState.singletonReg dst vDst).union hR, ?_,
            PartialState.singletonReg dst vDst, hR, hd, rfl, rfl, hRsat⟩
    refine ⟨?_, ?_, ?_⟩
    · intro r vr hvr
      have hp_vr : hp.regs r = some vr := hu ▸ hvr
      exact hcr_regs r vr hp_vr
    · intro a vm hvm
      have hp_vm : hp.mem a = some vm := hu ▸ hvm
      exact hcm_mem a vm hp_vm
    · intro vp hvp
      have hunion_pc_none :
          ((PartialState.singletonReg dst vDst).union hR).pc = none := by
        rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
        exact hR_no_pc
      rw [hunion_pc_none] at hvp
      nomatch hvp

/-- Generic 2-register-read conditional jump: instruction reads `dst`
    (value `vDst`) and `src` (value `vSrc`), tests `cond`, jumps. Same
    "regs/mem unchanged" shape. `dst ≠ src` falls out of disjointness. -/
theorem cuTripleWithin_2reg_cjump
    (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat) (insn : Insn)
    (cond : Prop) [Decidable cond]
    (h_step : ∀ s : State, s.regs.get dst = vDst → s.regs.get src = vSrc →
        step insn s = { s with pc := if cond then target else s.pc + 1 }) :
    cuTripleWithin 1 pc (if cond then target else pc + 1)
      (CodeReq.singleton pc insn)
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) := by
  intro R hRfree fetch hcr s hPR hpc hex
  obtain ⟨hp, hcompat, hPQ, hR, hd_PQR, hu_PQR, hPQ_pred, hR_sat⟩ := hPR
  obtain ⟨h_dst, h_src, hd_dst_src, hu_PQ, h_dst_eq, h_src_eq⟩ := hPQ_pred
  rw [h_dst_eq] at hu_PQ hd_dst_src
  rw [h_src_eq] at hu_PQ hd_dst_src
  clear h_dst_eq h_src_eq h_dst h_src
  obtain ⟨hcr_regs, hcm_mem, _⟩ := hcompat
  have hne_dst_src : dst ≠ src := by
    obtain ⟨hd_inner_regs, _, _⟩ := hd_dst_src
    intro habs
    rcases hd_inner_regs dst with h | h
    · rw [PartialState.singletonReg_regs_self] at h; nomatch h
    · rw [habs, PartialState.singletonReg_regs_self] at h; nomatch h
  have hp_eq : ((PartialState.singletonReg dst vDst).union
                (PartialState.singletonReg src vSrc)).union hR = hp := by
    rw [hu_PQ]; exact hu_PQR
  have hp_regs_dst : hp.regs dst = some vDst := by
    rw [← hp_eq]
    apply PartialState.union_regs_of_left_some
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have hp_regs_src : hp.regs src = some vSrc := by
    rw [← hp_eq]
    apply PartialState.union_regs_of_left_some
    rw [PartialState.union_regs_of_left_none
        (PartialState.singletonReg_regs_other hne_dst_src.symm)]
    exact PartialState.singletonReg_regs_self
  have hs_regs_dst : s.regs.get dst = vDst := hcr_regs dst vDst hp_regs_dst
  have hs_regs_src : s.regs.get src = vSrc := hcr_regs src vSrc hp_regs_src
  have hR_no_pc : hR.pc = none := hRfree _ hR_sat
  have hfetch : fetch s.pc = some insn := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hexec : executeFn fetch s 1 =
      { s with pc := if cond then target else s.pc + 1 } := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch,
        executeFn_zero, h_step s hs_regs_dst hs_regs_src]
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_⟩
  · rw [hexec]
    show (if cond then target else s.pc + 1) = if cond then target else pc + 1
    rw [hpc]
  · rw [hexec]; exact hex
  · rw [hexec]
    refine ⟨hp, ?_,
            (PartialState.singletonReg dst vDst).union
              (PartialState.singletonReg src vSrc),
            hR, ?_, hp_eq,
            ⟨PartialState.singletonReg dst vDst,
             PartialState.singletonReg src vSrc,
             ?_, rfl, rfl, rfl⟩,
            hR_sat⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro r vr hvr; exact hcr_regs r vr hvr
      · intro a vm hvm; exact hcm_mem a vm hvm
      · -- Show hp.pc = none, which is true since both inner singletons + hR are pc-free
        intro vp hvp
        have : hp.pc = none := by
          rw [← hp_eq]
          rw [PartialState.union_pc_of_left_none
              (PartialState.union_pc_of_left_none PartialState.singletonReg_pc)]
          exact hR_no_pc
        rw [this] at hvp
        nomatch hvp
    · -- Outer disjointness: (singletonReg dst vDst ⊎ singletonReg src vSrc) ⫫ hR
      -- Same as hd_PQR after the hu_PQ rewrite
      have : ((PartialState.singletonReg dst vDst).union
              (PartialState.singletonReg src vSrc)).Disjoint hR := hu_PQ ▸ hd_PQR
      exact this
    · -- Inner disjointness: singletonReg dst vDst ⫫ singletonReg src vSrc
      exact hd_dst_src

/-! ## Conditional-jump specs

Each spec captures both branches in one statement: the exit PC is
`if cond then target else pc + 1`, where `cond` is a `Decidable Prop`
expressed in terms of the operand values. Callers `by_cases hc : cond`
externally and propagate the right exit through macro composition.
Signed variants use `toSigned64` to interpret the 64-bit register
contents as two's complement. -/

-- imm-source --

/-- `jeq dst, imm, target`: jump if `dst = toU64 imm`. -/
theorem jeq_imm_spec (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat) :
    cuTripleWithin 1 pc (if vDst = toU64 imm then target else pc + 1)
      (CodeReq.singleton pc (.jeq dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) :=
  cuTripleWithin_1reg_cjump dst vDst pc target (.jeq dst (.imm imm) target)
    (vDst = toU64 imm)
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-- `jne dst, imm, target`: jump if `dst ≠ toU64 imm`. -/
theorem jne_imm_spec (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat) :
    cuTripleWithin 1 pc (if vDst ≠ toU64 imm then target else pc + 1)
      (CodeReq.singleton pc (.jne dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) :=
  cuTripleWithin_1reg_cjump dst vDst pc target (.jne dst (.imm imm) target)
    (vDst ≠ toU64 imm)
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-- `jgt dst, imm, target`: unsigned jump-greater-than. -/
theorem jgt_imm_spec (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat) :
    cuTripleWithin 1 pc (if vDst > toU64 imm then target else pc + 1)
      (CodeReq.singleton pc (.jgt dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) :=
  cuTripleWithin_1reg_cjump dst vDst pc target (.jgt dst (.imm imm) target)
    (vDst > toU64 imm)
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-- `jge dst, imm, target`: unsigned jump-greater-or-equal. -/
theorem jge_imm_spec (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat) :
    cuTripleWithin 1 pc (if vDst ≥ toU64 imm then target else pc + 1)
      (CodeReq.singleton pc (.jge dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) :=
  cuTripleWithin_1reg_cjump dst vDst pc target (.jge dst (.imm imm) target)
    (vDst ≥ toU64 imm)
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-- `jlt dst, imm, target`: unsigned jump-less-than. -/
theorem jlt_imm_spec (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat) :
    cuTripleWithin 1 pc (if vDst < toU64 imm then target else pc + 1)
      (CodeReq.singleton pc (.jlt dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) :=
  cuTripleWithin_1reg_cjump dst vDst pc target (.jlt dst (.imm imm) target)
    (vDst < toU64 imm)
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-- `jle dst, imm, target`: unsigned jump-less-or-equal. -/
theorem jle_imm_spec (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat) :
    cuTripleWithin 1 pc (if vDst ≤ toU64 imm then target else pc + 1)
      (CodeReq.singleton pc (.jle dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) :=
  cuTripleWithin_1reg_cjump dst vDst pc target (.jle dst (.imm imm) target)
    (vDst ≤ toU64 imm)
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-- `jsgt dst, imm, target`: signed jump-greater-than. -/
theorem jsgt_imm_spec (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat) :
    cuTripleWithin 1 pc
      (if toSigned64 vDst > toSigned64 (toU64 imm) then target else pc + 1)
      (CodeReq.singleton pc (.jsgt dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) :=
  cuTripleWithin_1reg_cjump dst vDst pc target (.jsgt dst (.imm imm) target)
    (toSigned64 vDst > toSigned64 (toU64 imm))
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-- `jsge dst, imm, target`: signed jump-greater-or-equal. -/
theorem jsge_imm_spec (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat) :
    cuTripleWithin 1 pc
      (if toSigned64 vDst ≥ toSigned64 (toU64 imm) then target else pc + 1)
      (CodeReq.singleton pc (.jsge dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) :=
  cuTripleWithin_1reg_cjump dst vDst pc target (.jsge dst (.imm imm) target)
    (toSigned64 vDst ≥ toSigned64 (toU64 imm))
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-- `jslt dst, imm, target`: signed jump-less-than. -/
theorem jslt_imm_spec (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat) :
    cuTripleWithin 1 pc
      (if toSigned64 vDst < toSigned64 (toU64 imm) then target else pc + 1)
      (CodeReq.singleton pc (.jslt dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) :=
  cuTripleWithin_1reg_cjump dst vDst pc target (.jslt dst (.imm imm) target)
    (toSigned64 vDst < toSigned64 (toU64 imm))
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-- `jsle dst, imm, target`: signed jump-less-or-equal. -/
theorem jsle_imm_spec (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat) :
    cuTripleWithin 1 pc
      (if toSigned64 vDst ≤ toSigned64 (toU64 imm) then target else pc + 1)
      (CodeReq.singleton pc (.jsle dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) :=
  cuTripleWithin_1reg_cjump dst vDst pc target (.jsle dst (.imm imm) target)
    (toSigned64 vDst ≤ toSigned64 (toU64 imm))
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-- `jset dst, imm, target`: jump if any bit-mask bit is set. -/
theorem jset_imm_spec (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat) :
    cuTripleWithin 1 pc
      (if vDst &&& toU64 imm ≠ 0 then target else pc + 1)
      (CodeReq.singleton pc (.jset dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) :=
  cuTripleWithin_1reg_cjump dst vDst pc target (.jset dst (.imm imm) target)
    (vDst &&& toU64 imm ≠ 0)
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

-- reg-source --

/-- `jeq dst, src, target`: jump if `dst = src`. -/
theorem jeq_reg_spec (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat) :
    cuTripleWithin 1 pc (if vDst = vSrc then target else pc + 1)
      (CodeReq.singleton pc (.jeq dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) :=
  cuTripleWithin_2reg_cjump dst src vDst vSrc pc target
    (.jeq dst (.reg src) target) (vDst = vSrc)
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-- `jne dst, src, target`: jump if `dst ≠ src`. -/
theorem jne_reg_spec (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat) :
    cuTripleWithin 1 pc (if vDst ≠ vSrc then target else pc + 1)
      (CodeReq.singleton pc (.jne dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) :=
  cuTripleWithin_2reg_cjump dst src vDst vSrc pc target
    (.jne dst (.reg src) target) (vDst ≠ vSrc)
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-- `jgt dst, src, target`: unsigned jump-greater-than. -/
theorem jgt_reg_spec (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat) :
    cuTripleWithin 1 pc (if vDst > vSrc then target else pc + 1)
      (CodeReq.singleton pc (.jgt dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) :=
  cuTripleWithin_2reg_cjump dst src vDst vSrc pc target
    (.jgt dst (.reg src) target) (vDst > vSrc)
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-- `jge dst, src, target`: unsigned jump-greater-or-equal. -/
theorem jge_reg_spec (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat) :
    cuTripleWithin 1 pc (if vDst ≥ vSrc then target else pc + 1)
      (CodeReq.singleton pc (.jge dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) :=
  cuTripleWithin_2reg_cjump dst src vDst vSrc pc target
    (.jge dst (.reg src) target) (vDst ≥ vSrc)
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-- `jlt dst, src, target`: unsigned jump-less-than. -/
theorem jlt_reg_spec (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat) :
    cuTripleWithin 1 pc (if vDst < vSrc then target else pc + 1)
      (CodeReq.singleton pc (.jlt dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) :=
  cuTripleWithin_2reg_cjump dst src vDst vSrc pc target
    (.jlt dst (.reg src) target) (vDst < vSrc)
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-- `jle dst, src, target`: unsigned jump-less-or-equal. -/
theorem jle_reg_spec (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat) :
    cuTripleWithin 1 pc (if vDst ≤ vSrc then target else pc + 1)
      (CodeReq.singleton pc (.jle dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) :=
  cuTripleWithin_2reg_cjump dst src vDst vSrc pc target
    (.jle dst (.reg src) target) (vDst ≤ vSrc)
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-- `jsgt dst, src, target`: signed jump-greater-than. -/
theorem jsgt_reg_spec (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat) :
    cuTripleWithin 1 pc
      (if toSigned64 vDst > toSigned64 vSrc then target else pc + 1)
      (CodeReq.singleton pc (.jsgt dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) :=
  cuTripleWithin_2reg_cjump dst src vDst vSrc pc target
    (.jsgt dst (.reg src) target) (toSigned64 vDst > toSigned64 vSrc)
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-- `jsge dst, src, target`: signed jump-greater-or-equal. -/
theorem jsge_reg_spec (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat) :
    cuTripleWithin 1 pc
      (if toSigned64 vDst ≥ toSigned64 vSrc then target else pc + 1)
      (CodeReq.singleton pc (.jsge dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) :=
  cuTripleWithin_2reg_cjump dst src vDst vSrc pc target
    (.jsge dst (.reg src) target) (toSigned64 vDst ≥ toSigned64 vSrc)
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-- `jslt dst, src, target`: signed jump-less-than. -/
theorem jslt_reg_spec (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat) :
    cuTripleWithin 1 pc
      (if toSigned64 vDst < toSigned64 vSrc then target else pc + 1)
      (CodeReq.singleton pc (.jslt dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) :=
  cuTripleWithin_2reg_cjump dst src vDst vSrc pc target
    (.jslt dst (.reg src) target) (toSigned64 vDst < toSigned64 vSrc)
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-- `jsle dst, src, target`: signed jump-less-or-equal. -/
theorem jsle_reg_spec (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat) :
    cuTripleWithin 1 pc
      (if toSigned64 vDst ≤ toSigned64 vSrc then target else pc + 1)
      (CodeReq.singleton pc (.jsle dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) :=
  cuTripleWithin_2reg_cjump dst src vDst vSrc pc target
    (.jsle dst (.reg src) target) (toSigned64 vDst ≤ toSigned64 vSrc)
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-- `jset dst, src, target`: jump if any bit-mask bit is set.
    `simp only [..., hdst, hsrc]` instead of `rw`: the `Decidable (_ ≠ 0)`
    instance under `&&&` doesn't synthesize through a `rw` motive. -/
theorem jset_reg_spec (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat) :
    cuTripleWithin 1 pc
      (if vDst &&& vSrc ≠ 0 then target else pc + 1)
      (CodeReq.singleton pc (.jset dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) :=
  cuTripleWithin_2reg_cjump dst src vDst vSrc pc target
    (.jset dst (.reg src) target) (vDst &&& vSrc ≠ 0)
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-! ## Memory-byte reasoning helpers shared across widths

`readU64_eq_of_bytes_match` connects 8 byte-level facts to a single
`readU64` value via the existing `readU64_writeU64_same` axiom — we
show `mem` agrees with `writeU64 mem addr v` at every address, then
apply the axiom. Used by `ldxdw_spec` to discharge step semantics. -/

theorem readU16_eq_of_bytes_match {mem : Memory.Mem} {addr v : Nat}
    (hv : v < 2 ^ 16)
    (h0 : mem addr = v % 256)
    (h1 : mem (addr + 1) = v / 0x100 % 256) :
    Memory.readU16 mem addr = v := by
  unfold Memory.readU16
  rw [h0, h1]
  omega

theorem readU32_eq_of_bytes_match {mem : Memory.Mem} {addr v : Nat}
    (hv : v < 2 ^ 32)
    (h0 : mem addr = v % 256)
    (h1 : mem (addr + 1) = v / 0x100 % 256)
    (h2 : mem (addr + 2) = v / 0x10000 % 256)
    (h3 : mem (addr + 3) = v / 0x1000000 % 256) :
    Memory.readU32 mem addr = v := by
  unfold Memory.readU32
  rw [h0, h1, h2, h3]
  omega

theorem readU64_eq_of_bytes_match {mem : Memory.Mem} {addr v : Nat}
    (hv : v < 2 ^ 64)
    (h0 : mem addr = v % 256)
    (h1 : mem (addr + 1) = v / 0x100 % 256)
    (h2 : mem (addr + 2) = v / 0x10000 % 256)
    (h3 : mem (addr + 3) = v / 0x1000000 % 256)
    (h4 : mem (addr + 4) = v / 0x100000000 % 256)
    (h5 : mem (addr + 5) = v / 0x10000000000 % 256)
    (h6 : mem (addr + 6) = v / 0x1000000000000 % 256)
    (h7 : mem (addr + 7) = v / 0x100000000000000 % 256) :
    Memory.readU64 mem addr = v := by
  unfold Memory.readU64
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  omega

/-! ## Memory loads — byte-width helper + `ldx .byte`

The SL memory-op pattern is "owns a destination register, a base
register, and one memory byte; the instruction reads them and writes
a derived value to the destination." Capturing this once collapses
each per-instruction byte-load spec to a 3-line invocation that
supplies only the `step` reduction.

`cuTripleWithinMem_load_byte_via_reg_addr` is the generic pattern:
- precondition owns `(dst ↦ᵣ vOldDst) ** (src ↦ᵣ baseAddr) ** (addr ↦ₘ byteVal)`,
- postcondition is the same shape with `dst` updated to `vNew`,
- region requirement asserts the 1-byte read range is contained,
- `h_step` is the per-instruction step reduction (caller-supplied).

The proof here pays the 4-level partial-state destructure cost once;
specs built atop it (like `ldxb_spec`) are mechanical. -/

/-- Generic byte-load triple via a register-indexed address. -/
theorem cuTripleWithinMem_load_byte_via_reg_addr
    (dst src : Reg) (off : Int)
    (vOldDst baseAddr byteVal vNew : Nat) (pc : Nat) (insn : Insn)
    (hne : dst ≠ .r10)
    (h_step : ∀ s : State,
        s.regs.get dst = vOldDst →
        s.regs.get src = baseAddr →
        s.mem (effectiveAddr baseAddr off) = byteVal →
        s.regions.containsRange (effectiveAddr baseAddr off) 1 = true →
        step insn s = { s with regs := s.regs.set dst vNew, pc := s.pc + 1 }) :
    cuTripleWithinMem 1 pc (pc + 1)
      (CodeReq.singleton pc insn)
      ((dst ↦ᵣ vOldDst) ** (src ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr off ↦ₘ byteVal))
      ((dst ↦ᵣ vNew) ** (src ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr off ↦ₘ byteVal))
      (fun rt => rt.containsRange (effectiveAddr baseAddr off) 1 = true) := by
  intro R hRfree fetch hcr s hPR hpc hex h_region
  obtain ⟨hp, hcompat, h_P, h_R, hd_PR, hu_PR, h_P_sat, h_R_sat⟩ := hPR
  obtain ⟨h_dst, h_SM, hd_dst_SM, hu_dst_SM, h_dst_pred, h_SM_sat⟩ := h_P_sat
  obtain ⟨h_src, h_mem, hd_src_mem, hu_src_mem, h_src_pred, h_mem_pred⟩ := h_SM_sat
  rw [h_src_pred] at hu_src_mem hd_src_mem
  rw [h_mem_pred] at hu_src_mem hd_src_mem
  rw [h_dst_pred] at hu_dst_SM hd_dst_SM
  clear h_src_pred h_mem_pred h_dst_pred h_src h_mem h_dst
  obtain ⟨hcr_regs, hcm_mem, _⟩ := hcompat
  have hne_dst_src : dst ≠ src := by
    obtain ⟨hd_dst_SM_regs, _, _⟩ := hd_dst_SM
    intro habs
    rcases hd_dst_SM_regs dst with hl | hr
    · rw [PartialState.singletonReg_regs_self] at hl; nomatch hl
    · rw [← hu_src_mem] at hr
      have : ((PartialState.singletonReg src baseAddr).union
              (PartialState.singletonMem (effectiveAddr baseAddr off) byteVal)).regs dst
              = some baseAddr := by
        rw [habs]
        exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
      rw [this] at hr; nomatch hr
  have h_SM_regs_src : h_SM.regs src = some baseAddr := by
    rw [← hu_src_mem]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_SM_mem_addr : h_SM.mem (effectiveAddr baseAddr off) = some byteVal := by
    rw [← hu_src_mem]
    rw [PartialState.union_mem_of_left_none
        (PartialState.singletonReg_mem (effectiveAddr baseAddr off))]
    exact PartialState.singletonMem_mem_self
  have h_P_regs_dst : h_P.regs dst = some vOldDst := by
    rw [← hu_dst_SM]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_regs_src : h_P.regs src = some baseAddr := by
    rw [← hu_dst_SM]
    rw [PartialState.union_regs_of_left_none
        (PartialState.singletonReg_regs_other hne_dst_src.symm)]
    exact h_SM_regs_src
  have h_P_mem_addr : h_P.mem (effectiveAddr baseAddr off) = some byteVal := by
    rw [← hu_dst_SM]
    rw [PartialState.union_mem_of_left_none
        (PartialState.singletonReg_mem (effectiveAddr baseAddr off))]
    exact h_SM_mem_addr
  have hp_regs_dst : hp.regs dst = some vOldDst := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_dst
  have hp_regs_src : hp.regs src = some baseAddr := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_src
  have hp_mem_addr : hp.mem (effectiveAddr baseAddr off) = some byteVal := by
    rw [← hu_PR]; exact PartialState.union_mem_of_left_some h_P_mem_addr
  have hs_regs_dst : s.regs.get dst = vOldDst := hcr_regs dst vOldDst hp_regs_dst
  have hs_regs_src : s.regs.get src = baseAddr := hcr_regs src baseAddr hp_regs_src
  have hs_mem_addr : s.mem (effectiveAddr baseAddr off) = byteVal :=
    hcm_mem _ byteVal hp_mem_addr
  have hfetch : fetch s.pc = some insn := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hexec : executeFn fetch s 1 =
      { s with regs := s.regs.set dst vNew, pc := s.pc + 1 } := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch,
        executeFn_zero,
        h_step s hs_regs_dst hs_regs_src hs_mem_addr h_region]
  obtain ⟨hd_PR_regs, hd_PR_mem, _⟩ := hd_PR
  have h_R_no_dst : h_R.regs dst = none := by
    rcases hd_PR_regs dst with hl | hr
    · rw [h_P_regs_dst] at hl; nomatch hl
    · exact hr
  have h_R_no_src : h_R.regs src = none := by
    rcases hd_PR_regs src with hl | hr
    · rw [h_P_regs_src] at hl; nomatch hl
    · exact hr
  have h_R_no_mem_addr : h_R.mem (effectiveAddr baseAddr off) = none := by
    rcases hd_PR_mem (effectiveAddr baseAddr off) with hl | hr
    · rw [h_P_mem_addr] at hl; nomatch hl
    · exact hr
  have h_R_no_pc : h_R.pc = none := hRfree _ h_R_sat
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_⟩
  · rw [hexec]; show s.pc + 1 = pc + 1; rw [hpc]
  · rw [hexec]; exact hex
  · rw [hexec]
    refine ⟨_, ?_,
            (PartialState.singletonReg dst vNew).union
              ((PartialState.singletonReg src baseAddr).union
                (PartialState.singletonMem (effectiveAddr baseAddr off) byteVal)),
            h_R, ?_, rfl,
            ⟨PartialState.singletonReg dst vNew,
             (PartialState.singletonReg src baseAddr).union
              (PartialState.singletonMem (effectiveAddr baseAddr off) byteVal),
             ?_, rfl, rfl,
             ⟨PartialState.singletonReg src baseAddr,
              PartialState.singletonMem (effectiveAddr baseAddr off) byteVal,
              hd_src_mem, rfl, rfl, rfl⟩⟩,
            h_R_sat⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro r vr hvr
        show (s.regs.set dst vNew).get r = vr
        by_cases hrdst : r = dst
        · rw [hrdst] at hvr
          have h_inner :
              ((PartialState.singletonReg dst vNew).union
                ((PartialState.singletonReg src baseAddr).union
                  (PartialState.singletonMem (effectiveAddr baseAddr off) byteVal))).regs dst
              = some vNew :=
            PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
          rw [PartialState.union_regs_of_left_some h_inner] at hvr
          have : vr = vNew := (Option.some.inj hvr).symm
          rw [hrdst, this]; exact RegFile.get_set_self _ _ _ hne
        · rw [RegFile.get_set_diff _ _ _ _ hrdst]
          by_cases hrsrc : r = src
          · rw [hrsrc] at hvr
            have h_inner :
                ((PartialState.singletonReg dst vNew).union
                  ((PartialState.singletonReg src baseAddr).union
                    (PartialState.singletonMem (effectiveAddr baseAddr off) byteVal))).regs src
                = some baseAddr := by
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hne_dst_src.symm)]
              exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
            rw [PartialState.union_regs_of_left_some h_inner] at hvr
            have : vr = baseAddr := (Option.some.inj hvr).symm
            rw [hrsrc, this]
            exact hcr_regs src baseAddr hp_regs_src
          · have h_outer_h1_none :
                ((PartialState.singletonReg dst vNew).union
                  ((PartialState.singletonReg src baseAddr).union
                    (PartialState.singletonMem (effectiveAddr baseAddr off) byteVal))).regs r
                = none := by
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrdst)]
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrsrc)]
              exact PartialState.singletonMem_regs r
            rw [PartialState.union_regs_of_left_none h_outer_h1_none] at hvr
            apply hcr_regs r vr
            have h_P_none : h_P.regs r = none := by
              rw [← hu_dst_SM]
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrdst)]
              rw [← hu_src_mem]
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrsrc)]
              exact PartialState.singletonMem_regs r
            rw [← hu_PR]
            rw [PartialState.union_regs_of_left_none h_P_none]
            exact hvr
      · intro a vm hvm
        show s.mem a = vm
        by_cases ha : a = effectiveAddr baseAddr off
        · rw [ha] at hvm ⊢
          have h_inner :
              ((PartialState.singletonReg dst vNew).union
                ((PartialState.singletonReg src baseAddr).union
                  (PartialState.singletonMem (effectiveAddr baseAddr off) byteVal))).mem
                  (effectiveAddr baseAddr off)
              = some byteVal := by
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            exact PartialState.singletonMem_mem_self
          rw [PartialState.union_mem_of_left_some h_inner] at hvm
          have : vm = byteVal := (Option.some.inj hvm).symm
          rw [this]; exact hs_mem_addr
        · have h_outer_h1_none :
              ((PartialState.singletonReg dst vNew).union
                ((PartialState.singletonReg src baseAddr).union
                  (PartialState.singletonMem (effectiveAddr baseAddr off) byteVal))).mem a
              = none := by
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            exact PartialState.singletonMem_mem_other ha
          rw [PartialState.union_mem_of_left_none h_outer_h1_none] at hvm
          apply hcm_mem a vm
          have h_P_none : h_P.mem a = none := by
            rw [← hu_dst_SM]
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            rw [← hu_src_mem]
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            exact PartialState.singletonMem_mem_other ha
          rw [← hu_PR]
          rw [PartialState.union_mem_of_left_none h_P_none]
          exact hvm
      · intro vp hvp
        have h_outer_h1_pc :
            ((PartialState.singletonReg dst vNew).union
              ((PartialState.singletonReg src baseAddr).union
                (PartialState.singletonMem (effectiveAddr baseAddr off) byteVal))).pc
            = none := by
          rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
          rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
          exact PartialState.singletonMem_pc
        rw [PartialState.union_pc_of_left_none h_outer_h1_pc] at hvp
        rw [h_R_no_pc] at hvp
        nomatch hvp
    · refine ⟨?_, ?_, ?_⟩
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
            exact PartialState.singletonMem_regs r
      · intro a
        by_cases ha : a = effectiveAddr baseAddr off
        · rw [ha]; right; exact h_R_no_mem_addr
        · left
          rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
          rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
          exact PartialState.singletonMem_mem_other ha
      · left
        rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
        rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
        exact PartialState.singletonMem_pc
    · refine ⟨fun r => ?_, fun a => ?_, ?_⟩
      · by_cases hrdst : r = dst
        · right
          rw [hrdst,
              PartialState.union_regs_of_left_none
                (PartialState.singletonReg_regs_other hne_dst_src)]
          exact PartialState.singletonMem_regs dst
        · left; exact PartialState.singletonReg_regs_other hrdst
      · left; exact PartialState.singletonReg_mem a
      · left; exact PartialState.singletonReg_pc

/-- `ldx .byte dst src off`: load byte at `[src + off]` into `dst`,
    masked to 8 bits. Derived from
    `cuTripleWithinMem_load_byte_via_reg_addr` with `vNew := byteVal % 256`. -/
theorem ldxb_spec
    (dst src : Reg) (off : Int) (vOldDst baseAddr byteVal : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithinMem 1 pc (pc + 1)
      (CodeReq.singleton pc (.ldx .byte dst src off))
      ((dst ↦ᵣ vOldDst) ** (src ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr off ↦ₘ byteVal))
      ((dst ↦ᵣ (byteVal % 256)) ** (src ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr off ↦ₘ byteVal))
      (fun rt => rt.containsRange (effectiveAddr baseAddr off) 1 = true) :=
  cuTripleWithinMem_load_byte_via_reg_addr dst src off vOldDst baseAddr byteVal
    (byteVal % 256) pc (.ldx .byte dst src off) hne
    (fun _ _ hsrc hmem hreg => by
      simp only [step, hsrc, Width.bytes, if_pos hreg,
                 Memory.readByWidth, Memory.readU8, hmem])

/-! ## Memory stores — byte-width helper + `stx .byte`

The byte-store SL pattern: instruction reads two registers (base
address + value), updates one memory byte to a value derived from
those registers. Symmetric to the load helper but with the partial
state's memory cell changing value between pre and post (the byte
masked to 8 bits is what `writeU8` actually stores). -/

/-- Generic byte-store triple via a register-indexed address.
    `newByteVal` is the actual byte stored, so callers pass it
    pre-masked (`< 256`) — `h_lt` discharges `writeU8`'s internal mod. -/
theorem cuTripleWithinMem_store_byte_via_reg_addr
    (baseReg valReg : Reg) (off : Int)
    (baseAddr vSrc oldByteVal newByteVal : Nat)
    (pc : Nat) (insn : Insn)
    (h_lt : newByteVal < 256)
    (h_step : ∀ s : State,
        s.regs.get baseReg = baseAddr →
        s.regs.get valReg = vSrc →
        s.regions.containsWritable (effectiveAddr baseAddr off) 1 = true →
        step insn s =
          { s with mem := Memory.writeU8 s.mem (effectiveAddr baseAddr off) newByteVal,
                   pc := s.pc + 1 }) :
    cuTripleWithinMem 1 pc (pc + 1)
      (CodeReq.singleton pc insn)
      ((baseReg ↦ᵣ baseAddr) ** (valReg ↦ᵣ vSrc) **
        (effectiveAddr baseAddr off ↦ₘ oldByteVal))
      ((baseReg ↦ᵣ baseAddr) ** (valReg ↦ᵣ vSrc) **
        (effectiveAddr baseAddr off ↦ₘ newByteVal))
      (fun rt => rt.containsWritable (effectiveAddr baseAddr off) 1 = true) := by
  intro R hRfree fetch hcr s hPR hpc hex h_region
  obtain ⟨hp, hcompat, h_P, h_R, hd_PR, hu_PR, h_P_sat, h_R_sat⟩ := hPR
  obtain ⟨h_base, h_VM, hd_base_VM, hu_base_VM, h_base_pred, h_VM_sat⟩ := h_P_sat
  obtain ⟨h_val, h_mem, hd_val_mem, hu_val_mem, h_val_pred, h_mem_pred⟩ := h_VM_sat
  rw [h_val_pred] at hu_val_mem hd_val_mem
  rw [h_mem_pred] at hu_val_mem hd_val_mem
  rw [h_base_pred] at hu_base_VM hd_base_VM
  clear h_val_pred h_mem_pred h_base_pred h_val h_mem h_base
  obtain ⟨hcr_regs, hcm_mem, _⟩ := hcompat
  have hne_base_val : baseReg ≠ valReg := by
    obtain ⟨hd_base_VM_regs, _, _⟩ := hd_base_VM
    intro habs
    rcases hd_base_VM_regs baseReg with hl | hr
    · rw [PartialState.singletonReg_regs_self] at hl; nomatch hl
    · rw [← hu_val_mem] at hr
      have : ((PartialState.singletonReg valReg vSrc).union
              (PartialState.singletonMem (effectiveAddr baseAddr off) oldByteVal)).regs baseReg
              = some vSrc := by
        rw [habs]
        exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
      rw [this] at hr; nomatch hr
  have h_VM_regs_val : h_VM.regs valReg = some vSrc := by
    rw [← hu_val_mem]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_VM_mem_addr : h_VM.mem (effectiveAddr baseAddr off) = some oldByteVal := by
    rw [← hu_val_mem]
    rw [PartialState.union_mem_of_left_none
        (PartialState.singletonReg_mem (effectiveAddr baseAddr off))]
    exact PartialState.singletonMem_mem_self
  have h_P_regs_base : h_P.regs baseReg = some baseAddr := by
    rw [← hu_base_VM]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_regs_val : h_P.regs valReg = some vSrc := by
    rw [← hu_base_VM]
    rw [PartialState.union_regs_of_left_none
        (PartialState.singletonReg_regs_other hne_base_val.symm)]
    exact h_VM_regs_val
  have h_P_mem_addr : h_P.mem (effectiveAddr baseAddr off) = some oldByteVal := by
    rw [← hu_base_VM]
    rw [PartialState.union_mem_of_left_none
        (PartialState.singletonReg_mem (effectiveAddr baseAddr off))]
    exact h_VM_mem_addr
  have hp_regs_base : hp.regs baseReg = some baseAddr := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_base
  have hp_regs_val : hp.regs valReg = some vSrc := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_val
  have hp_mem_addr : hp.mem (effectiveAddr baseAddr off) = some oldByteVal := by
    rw [← hu_PR]; exact PartialState.union_mem_of_left_some h_P_mem_addr
  have hs_regs_base : s.regs.get baseReg = baseAddr :=
    hcr_regs baseReg baseAddr hp_regs_base
  have hs_regs_val : s.regs.get valReg = vSrc := hcr_regs valReg vSrc hp_regs_val
  have hfetch : fetch s.pc = some insn := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hexec : executeFn fetch s 1 =
      { s with mem := Memory.writeU8 s.mem (effectiveAddr baseAddr off) newByteVal,
               pc := s.pc + 1 } := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch,
        executeFn_zero,
        h_step s hs_regs_base hs_regs_val h_region]
  obtain ⟨hd_PR_regs, hd_PR_mem, _⟩ := hd_PR
  have h_R_no_base : h_R.regs baseReg = none := by
    rcases hd_PR_regs baseReg with hl | hr
    · rw [h_P_regs_base] at hl; nomatch hl
    · exact hr
  have h_R_no_val : h_R.regs valReg = none := by
    rcases hd_PR_regs valReg with hl | hr
    · rw [h_P_regs_val] at hl; nomatch hl
    · exact hr
  have h_R_no_mem_addr : h_R.mem (effectiveAddr baseAddr off) = none := by
    rcases hd_PR_mem (effectiveAddr baseAddr off) with hl | hr
    · rw [h_P_mem_addr] at hl; nomatch hl
    · exact hr
  have h_R_no_pc : h_R.pc = none := hRfree _ h_R_sat
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_⟩
  · rw [hexec]; show s.pc + 1 = pc + 1; rw [hpc]
  · rw [hexec]; exact hex
  · rw [hexec]
    refine ⟨_, ?_,
            (PartialState.singletonReg baseReg baseAddr).union
              ((PartialState.singletonReg valReg vSrc).union
                (PartialState.singletonMem (effectiveAddr baseAddr off) (newByteVal))),
            h_R, ?_, rfl,
            ⟨PartialState.singletonReg baseReg baseAddr,
             (PartialState.singletonReg valReg vSrc).union
              (PartialState.singletonMem (effectiveAddr baseAddr off) (newByteVal)),
             ?_, rfl, rfl,
             ⟨PartialState.singletonReg valReg vSrc,
              PartialState.singletonMem (effectiveAddr baseAddr off) (newByteVal),
              ?_, rfl, rfl, rfl⟩⟩,
            h_R_sat⟩
    -- (a) Compat of the new witness with the post state (post = { s with mem := ..., pc := s.pc + 1 }).
    · refine ⟨?_, ?_, ?_⟩
      · intro r vr hvr
        -- regs are unchanged in the post state
        show s.regs.get r = vr
        by_cases hrbase : r = baseReg
        · rw [hrbase] at hvr
          have h_inner :
              ((PartialState.singletonReg baseReg baseAddr).union
                ((PartialState.singletonReg valReg vSrc).union
                  (PartialState.singletonMem (effectiveAddr baseAddr off)
                    (newByteVal)))).regs baseReg = some baseAddr :=
            PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
          rw [PartialState.union_regs_of_left_some h_inner] at hvr
          have : vr = baseAddr := (Option.some.inj hvr).symm
          rw [hrbase, this]; exact hs_regs_base
        · by_cases hrval : r = valReg
          · rw [hrval] at hvr
            have h_inner :
                ((PartialState.singletonReg baseReg baseAddr).union
                  ((PartialState.singletonReg valReg vSrc).union
                    (PartialState.singletonMem (effectiveAddr baseAddr off)
                      (newByteVal)))).regs valReg = some vSrc := by
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hne_base_val.symm)]
              exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
            rw [PartialState.union_regs_of_left_some h_inner] at hvr
            have : vr = vSrc := (Option.some.inj hvr).symm
            rw [hrval, this]; exact hs_regs_val
          · have h_outer_h1_none :
                ((PartialState.singletonReg baseReg baseAddr).union
                  ((PartialState.singletonReg valReg vSrc).union
                    (PartialState.singletonMem (effectiveAddr baseAddr off)
                      (newByteVal)))).regs r = none := by
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrbase)]
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrval)]
              exact PartialState.singletonMem_regs r
            rw [PartialState.union_regs_of_left_none h_outer_h1_none] at hvr
            apply hcr_regs r vr
            have h_P_none : h_P.regs r = none := by
              rw [← hu_base_VM]
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrbase)]
              rw [← hu_val_mem]
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrval)]
              exact PartialState.singletonMem_regs r
            rw [← hu_PR]
            rw [PartialState.union_regs_of_left_none h_P_none]
            exact hvr
      · intro a vm hvm
        show (Memory.writeU8 s.mem (effectiveAddr baseAddr off) newByteVal) a = vm
        by_cases ha : a = effectiveAddr baseAddr off
        · rw [ha] at hvm ⊢
          have h_inner :
              ((PartialState.singletonReg baseReg baseAddr).union
                ((PartialState.singletonReg valReg vSrc).union
                  (PartialState.singletonMem (effectiveAddr baseAddr off)
                    (newByteVal)))).mem (effectiveAddr baseAddr off)
              = some (newByteVal) := by
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            exact PartialState.singletonMem_mem_self
          rw [PartialState.union_mem_of_left_some h_inner] at hvm
          have : vm = newByteVal := (Option.some.inj hvm).symm
          rw [this]
          -- writeU8 stores `newByteVal % 256` at addr; with h_lt, equals newByteVal.
          unfold Memory.writeU8; simp
          exact h_lt
        · have h_outer_h1_none :
              ((PartialState.singletonReg baseReg baseAddr).union
                ((PartialState.singletonReg valReg vSrc).union
                  (PartialState.singletonMem (effectiveAddr baseAddr off)
                    (newByteVal)))).mem a = none := by
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            exact PartialState.singletonMem_mem_other ha
          rw [PartialState.union_mem_of_left_none h_outer_h1_none] at hvm
          -- mem at a ≠ addr is unchanged by writeU8
          unfold Memory.writeU8
          simp [ha]
          -- new state mem at a = s.mem a; from pre compat
          apply hcm_mem a vm
          have h_P_none : h_P.mem a = none := by
            rw [← hu_base_VM]
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            rw [← hu_val_mem]
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            exact PartialState.singletonMem_mem_other ha
          rw [← hu_PR]
          rw [PartialState.union_mem_of_left_none h_P_none]
          exact hvm
      · intro vp hvp
        have h_outer_h1_pc :
            ((PartialState.singletonReg baseReg baseAddr).union
              ((PartialState.singletonReg valReg vSrc).union
                (PartialState.singletonMem (effectiveAddr baseAddr off)
                  (newByteVal)))).pc = none := by
          rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
          rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
          exact PartialState.singletonMem_pc
        rw [PartialState.union_pc_of_left_none h_outer_h1_pc] at hvp
        rw [h_R_no_pc] at hvp
        nomatch hvp
    -- (b) Outer disjointness: new witness ⊥ h_R.
    · refine ⟨?_, ?_, ?_⟩
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
            exact PartialState.singletonMem_regs r
      · intro a
        by_cases ha : a = effectiveAddr baseAddr off
        · rw [ha]; right; exact h_R_no_mem_addr
        · left
          rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
          rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
          exact PartialState.singletonMem_mem_other ha
      · left
        rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
        rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
        exact PartialState.singletonMem_pc
    -- (c) Inner disjointness: singletonReg baseReg ⊥ (singletonReg valReg ⊎ singletonMem addr).
    · refine ⟨fun r => ?_, fun a => ?_, ?_⟩
      · by_cases hrbase : r = baseReg
        · right
          rw [hrbase,
              PartialState.union_regs_of_left_none
                (PartialState.singletonReg_regs_other hne_base_val)]
          exact PartialState.singletonMem_regs baseReg
        · left; exact PartialState.singletonReg_regs_other hrbase
      · left; exact PartialState.singletonReg_mem a
      · left; exact PartialState.singletonReg_pc
    -- (d) Innermost disjointness: singletonReg valReg ⊥ singletonMem addr.
    -- singletonMem has no regs, singletonReg has no mem, neither owns pc.
    · refine ⟨fun r => ?_, fun a => ?_, ?_⟩
      · right; exact PartialState.singletonMem_regs r
      · left; exact PartialState.singletonReg_mem a
      · left; exact PartialState.singletonReg_pc

/-- `stx .byte baseReg off valReg`: store byte `(valReg & 0xff)` at
    `[baseReg + off]`. Derived from the store helper with
    `newByteVal := vSrc % 256`. -/
theorem stxb_spec
    (baseReg valReg : Reg) (off : Int)
    (baseAddr vSrc oldByteVal : Nat) (pc : Nat) :
    cuTripleWithinMem 1 pc (pc + 1)
      (CodeReq.singleton pc (.stx .byte baseReg off valReg))
      ((baseReg ↦ᵣ baseAddr) ** (valReg ↦ᵣ vSrc) **
        (effectiveAddr baseAddr off ↦ₘ oldByteVal))
      ((baseReg ↦ᵣ baseAddr) ** (valReg ↦ᵣ vSrc) **
        (effectiveAddr baseAddr off ↦ₘ (vSrc % 256)))
      (fun rt => rt.containsWritable (effectiveAddr baseAddr off) 1 = true) :=
  cuTripleWithinMem_store_byte_via_reg_addr baseReg valReg off
    baseAddr vSrc oldByteVal (vSrc % 256) pc (.stx .byte baseReg off valReg)
    (Nat.mod_lt _ (by decide : (0 : Nat) < 256))
    (fun _ hbase hval hreg => by
      simp only [step, hbase, Width.bytes, if_pos hreg,
                 Memory.writeByWidth, hval])

/-! ## Memory stores from immediates — byte-width helper + `st .byte`

Two-resource pattern: owns one base register and one memory byte.
Simpler than `stxb`'s helper because there's no value register —
the value is the instruction's immediate field. -/

/-- Generic byte-store triple from an immediate value. Mirror of
    `cuTripleWithinMem_store_byte_via_reg_addr` minus the value
    register. -/
theorem cuTripleWithinMem_store_imm_byte_via_reg_addr
    (baseReg : Reg) (off : Int)
    (baseAddr oldByteVal newByteVal : Nat) (pc : Nat) (insn : Insn)
    (h_lt : newByteVal < 256)
    (h_step : ∀ s : State,
        s.regs.get baseReg = baseAddr →
        s.regions.containsWritable (effectiveAddr baseAddr off) 1 = true →
        step insn s =
          { s with mem := Memory.writeU8 s.mem (effectiveAddr baseAddr off) newByteVal,
                   pc := s.pc + 1 }) :
    cuTripleWithinMem 1 pc (pc + 1)
      (CodeReq.singleton pc insn)
      ((baseReg ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr off ↦ₘ oldByteVal))
      ((baseReg ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr off ↦ₘ newByteVal))
      (fun rt => rt.containsWritable (effectiveAddr baseAddr off) 1 = true) := by
  intro R hRfree fetch hcr s hPR hpc hex h_region
  -- 2-level destructure: hp = h_P ⊎ h_R, h_P = h_base ⊎ h_mem.
  obtain ⟨hp, hcompat, h_P, h_R, hd_PR, hu_PR, h_P_sat, h_R_sat⟩ := hPR
  obtain ⟨h_base, h_mem, hd_base_mem, hu_base_mem, h_base_pred, h_mem_pred⟩ := h_P_sat
  rw [h_base_pred] at hu_base_mem hd_base_mem
  rw [h_mem_pred] at hu_base_mem hd_base_mem
  clear h_base_pred h_mem_pred h_base h_mem
  obtain ⟨hcr_regs, hcm_mem, _⟩ := hcompat
  have h_P_regs_base : h_P.regs baseReg = some baseAddr := by
    rw [← hu_base_mem]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_mem_addr : h_P.mem (effectiveAddr baseAddr off) = some oldByteVal := by
    rw [← hu_base_mem]
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact PartialState.singletonMem_mem_self
  have hp_regs_base : hp.regs baseReg = some baseAddr := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_base
  have hp_mem_addr : hp.mem (effectiveAddr baseAddr off) = some oldByteVal := by
    rw [← hu_PR]; exact PartialState.union_mem_of_left_some h_P_mem_addr
  have hs_regs_base : s.regs.get baseReg = baseAddr :=
    hcr_regs baseReg baseAddr hp_regs_base
  have hfetch : fetch s.pc = some insn := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hexec : executeFn fetch s 1 =
      { s with mem := Memory.writeU8 s.mem (effectiveAddr baseAddr off) newByteVal,
               pc := s.pc + 1 } := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch,
        executeFn_zero,
        h_step s hs_regs_base h_region]
  obtain ⟨hd_PR_regs, hd_PR_mem, _⟩ := hd_PR
  have h_R_no_base : h_R.regs baseReg = none := by
    rcases hd_PR_regs baseReg with hl | hr
    · rw [h_P_regs_base] at hl; nomatch hl
    · exact hr
  have h_R_no_mem_addr : h_R.mem (effectiveAddr baseAddr off) = none := by
    rcases hd_PR_mem (effectiveAddr baseAddr off) with hl | hr
    · rw [h_P_mem_addr] at hl; nomatch hl
    · exact hr
  have h_R_no_pc : h_R.pc = none := hRfree _ h_R_sat
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_⟩
  · rw [hexec]; show s.pc + 1 = pc + 1; rw [hpc]
  · rw [hexec]; exact hex
  · rw [hexec]
    refine ⟨_, ?_,
            (PartialState.singletonReg baseReg baseAddr).union
              (PartialState.singletonMem (effectiveAddr baseAddr off) newByteVal),
            h_R, ?_, rfl,
            ⟨PartialState.singletonReg baseReg baseAddr,
             PartialState.singletonMem (effectiveAddr baseAddr off) newByteVal,
             ?_, rfl, rfl, rfl⟩,
            h_R_sat⟩
    -- (a) Compat of the new witness with the post state.
    · refine ⟨?_, ?_, ?_⟩
      · intro r vr hvr
        show s.regs.get r = vr
        by_cases hrbase : r = baseReg
        · rw [hrbase] at hvr
          have h_inner :
              ((PartialState.singletonReg baseReg baseAddr).union
                (PartialState.singletonMem (effectiveAddr baseAddr off) newByteVal)).regs
                  baseReg = some baseAddr :=
            PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
          rw [PartialState.union_regs_of_left_some h_inner] at hvr
          have : vr = baseAddr := (Option.some.inj hvr).symm
          rw [hrbase, this]; exact hs_regs_base
        · -- r ≠ baseReg: outer-h1 doesn't own r → falls through to h_R.
          have h_outer_h1_none :
              ((PartialState.singletonReg baseReg baseAddr).union
                (PartialState.singletonMem (effectiveAddr baseAddr off) newByteVal)).regs r
              = none := by
            rw [PartialState.union_regs_of_left_none
                (PartialState.singletonReg_regs_other hrbase)]
            exact PartialState.singletonMem_regs r
          rw [PartialState.union_regs_of_left_none h_outer_h1_none] at hvr
          apply hcr_regs r vr
          have h_P_none : h_P.regs r = none := by
            rw [← hu_base_mem]
            rw [PartialState.union_regs_of_left_none
                (PartialState.singletonReg_regs_other hrbase)]
            exact PartialState.singletonMem_regs r
          rw [← hu_PR]
          rw [PartialState.union_regs_of_left_none h_P_none]
          exact hvr
      · intro a vm hvm
        show (Memory.writeU8 s.mem (effectiveAddr baseAddr off) newByteVal) a = vm
        by_cases ha : a = effectiveAddr baseAddr off
        · rw [ha] at hvm ⊢
          have h_inner :
              ((PartialState.singletonReg baseReg baseAddr).union
                (PartialState.singletonMem (effectiveAddr baseAddr off) newByteVal)).mem
                  (effectiveAddr baseAddr off) = some newByteVal := by
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            exact PartialState.singletonMem_mem_self
          rw [PartialState.union_mem_of_left_some h_inner] at hvm
          have : vm = newByteVal := (Option.some.inj hvm).symm
          rw [this]
          unfold Memory.writeU8; simp
          exact h_lt
        · have h_outer_h1_none :
              ((PartialState.singletonReg baseReg baseAddr).union
                (PartialState.singletonMem (effectiveAddr baseAddr off) newByteVal)).mem a
              = none := by
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            exact PartialState.singletonMem_mem_other ha
          rw [PartialState.union_mem_of_left_none h_outer_h1_none] at hvm
          unfold Memory.writeU8
          show (if a = effectiveAddr baseAddr off then newByteVal % 256 else s.mem a) = vm
          rw [if_neg ha]
          apply hcm_mem a vm
          have h_P_none : h_P.mem a = none := by
            rw [← hu_base_mem]
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            exact PartialState.singletonMem_mem_other ha
          rw [← hu_PR]
          rw [PartialState.union_mem_of_left_none h_P_none]
          exact hvm
      · intro vp hvp
        have h_outer_h1_pc :
            ((PartialState.singletonReg baseReg baseAddr).union
              (PartialState.singletonMem (effectiveAddr baseAddr off) newByteVal)).pc = none := by
          rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
          exact PartialState.singletonMem_pc
        rw [PartialState.union_pc_of_left_none h_outer_h1_pc] at hvp
        rw [h_R_no_pc] at hvp
        nomatch hvp
    -- (b) Outer disjointness: new witness ⊥ h_R.
    · refine ⟨?_, ?_, ?_⟩
      · intro r
        by_cases hrbase : r = baseReg
        · rw [hrbase]; right; exact h_R_no_base
        · left
          rw [PartialState.union_regs_of_left_none
              (PartialState.singletonReg_regs_other hrbase)]
          exact PartialState.singletonMem_regs r
      · intro a
        by_cases ha : a = effectiveAddr baseAddr off
        · rw [ha]; right; exact h_R_no_mem_addr
        · left
          rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
          exact PartialState.singletonMem_mem_other ha
      · left
        rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
        exact PartialState.singletonMem_pc
    -- (c) Inner disjointness: singletonReg ⊥ singletonMem.
    · refine ⟨fun r => ?_, fun a => ?_, ?_⟩
      · right; exact PartialState.singletonMem_regs r
      · left; exact PartialState.singletonReg_mem a
      · left; exact PartialState.singletonReg_pc

/-- `st .byte baseReg off imm`: store byte `(imm & 0xff)` at
    `[baseReg + off]`. Derived from the immediate-store helper. -/
theorem stb_spec
    (baseReg : Reg) (off : Int) (imm : Int)
    (baseAddr oldByteVal : Nat) (pc : Nat) :
    cuTripleWithinMem 1 pc (pc + 1)
      (CodeReq.singleton pc (.st .byte baseReg off imm))
      ((baseReg ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr off ↦ₘ oldByteVal))
      ((baseReg ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr off ↦ₘ (toU64 imm % 256)))
      (fun rt => rt.containsWritable (effectiveAddr baseAddr off) 1 = true) :=
  cuTripleWithinMem_store_imm_byte_via_reg_addr baseReg off
    baseAddr oldByteVal (toU64 imm % 256) pc (.st .byte baseReg off imm)
    (Nat.mod_lt _ (by decide : (0 : Nat) < 256))
    (fun _ hbase hreg => by
      simp only [step, hbase, Width.bytes, if_pos hreg, Memory.writeByWidth])

/-! ## Memory loads — dword width

`ldxdw` reads 8 consecutive bytes (little-endian) into a register.
The precondition owns the destination register, the source register
(base address), and a `memU64Is` claim over the 8 bytes. The post
writes the assembled u64 to `dst` and leaves memory + src unchanged.

Region requirement: `containsRange addr 8`.

The proof's heavy lifting (4-level destructure for the 3 atoms + R,
plus 8 byte-projection lemmas through the union chain) is structurally
identical to `ldxb_spec`'s helper, just scaled to 8 bytes. The
key new piece is `readU64_eq_of_bytes_match` for step discharge. -/

/-- `ldx .dword dst src off`: load 64-bit value at `[src + off]` into `dst`. -/
theorem ldxdw_spec
    (dst src : Reg) (off : Int) (vOldDst baseAddr v : Nat) (pc : Nat)
    (hne : dst ≠ .r10) (hv : v < 2 ^ 64) :
    cuTripleWithinMem 1 pc (pc + 1)
      (CodeReq.singleton pc (.ldx .dword dst src off))
      ((dst ↦ᵣ vOldDst) ** (src ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr off ↦U64 v))
      ((dst ↦ᵣ v) ** (src ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr off ↦U64 v))
      (fun rt => rt.containsRange (effectiveAddr baseAddr off) 8 = true) := by
  intro R hRfree fetch hcr s hPR hpc hex h_region
  -- Destructure the four-level partial-state split.
  obtain ⟨hp, hcompat, h_P, h_R, hd_PR, hu_PR, h_P_sat, h_R_sat⟩ := hPR
  obtain ⟨h_dst, h_SM, hd_dst_SM, hu_dst_SM, h_dst_pred, h_SM_sat⟩ := h_P_sat
  obtain ⟨h_src, h_mem, hd_src_mem, hu_src_mem, h_src_pred, h_mem_pred⟩ := h_SM_sat
  rw [h_src_pred] at hu_src_mem hd_src_mem
  rw [h_mem_pred] at hu_src_mem hd_src_mem
  rw [h_dst_pred] at hu_dst_SM hd_dst_SM
  clear h_src_pred h_mem_pred h_dst_pred h_src h_mem h_dst
  obtain ⟨hcr_regs, hcm_mem, _⟩ := hcompat
  -- dst ≠ src from inner disjointness (matches ldxb's pattern).
  have hne_dst_src : dst ≠ src := by
    obtain ⟨hd_dst_SM_regs, _, _⟩ := hd_dst_SM
    intro habs
    rcases hd_dst_SM_regs dst with hl | hr
    · rw [PartialState.singletonReg_regs_self] at hl; nomatch hl
    · rw [← hu_src_mem] at hr
      have : ((PartialState.singletonReg src baseAddr).union
              (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v)).regs dst
              = some baseAddr := by
        rw [habs]
        exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
      rw [this] at hr; nomatch hr
  -- ===== Climb-up to extract reg + 8 mem byte values =====
  have h_SM_regs_src : h_SM.regs src = some baseAddr := by
    rw [← hu_src_mem]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  -- 8 byte extractions at h_SM level (similar shape, varying offsets).
  have h_SM_mem_0 :
      h_SM.mem (effectiveAddr baseAddr off) = some (v % 256) := by
    rw [← hu_src_mem,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact PartialState.singletonMemU64_mem_0 _ _
  have h_SM_mem_1 :
      h_SM.mem (effectiveAddr baseAddr off + 1) = some (v / 0x100 % 256) := by
    rw [← hu_src_mem,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact PartialState.singletonMemU64_mem_1 _ _
  have h_SM_mem_2 :
      h_SM.mem (effectiveAddr baseAddr off + 2) = some (v / 0x10000 % 256) := by
    rw [← hu_src_mem,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact PartialState.singletonMemU64_mem_2 _ _
  have h_SM_mem_3 :
      h_SM.mem (effectiveAddr baseAddr off + 3) = some (v / 0x1000000 % 256) := by
    rw [← hu_src_mem,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact PartialState.singletonMemU64_mem_3 _ _
  have h_SM_mem_4 :
      h_SM.mem (effectiveAddr baseAddr off + 4) = some (v / 0x100000000 % 256) := by
    rw [← hu_src_mem,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact PartialState.singletonMemU64_mem_4 _ _
  have h_SM_mem_5 :
      h_SM.mem (effectiveAddr baseAddr off + 5) = some (v / 0x10000000000 % 256) := by
    rw [← hu_src_mem,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact PartialState.singletonMemU64_mem_5 _ _
  have h_SM_mem_6 :
      h_SM.mem (effectiveAddr baseAddr off + 6) = some (v / 0x1000000000000 % 256) := by
    rw [← hu_src_mem,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact PartialState.singletonMemU64_mem_6 _ _
  have h_SM_mem_7 :
      h_SM.mem (effectiveAddr baseAddr off + 7) = some (v / 0x100000000000000 % 256) := by
    rw [← hu_src_mem,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact PartialState.singletonMemU64_mem_7 _ _
  -- Climb to h_P (dst-singleton has no mem and src ≠ dst so regs lookup fall-through is straightforward).
  have h_P_regs_dst : h_P.regs dst = some vOldDst := by
    rw [← hu_dst_SM]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_regs_src : h_P.regs src = some baseAddr := by
    rw [← hu_dst_SM,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other hne_dst_src.symm)]
    exact h_SM_regs_src
  -- 8 byte extractions at h_P level (peel singletonReg dst _ which has no mem).
  have h_P_mem (i : Nat) (hi : i < 8) (val : Nat)
      (h_SM_at : h_SM.mem (effectiveAddr baseAddr off + i) = some val) :
      h_P.mem (effectiveAddr baseAddr off + i) = some val := by
    rw [← hu_dst_SM,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact h_SM_at
  have h_P_mem_0 :
      h_P.mem (effectiveAddr baseAddr off) = some (v % 256) := by
    have := h_P_mem 0 (by omega) _ h_SM_mem_0
    simpa using this
  have h_P_mem_1 :=
    h_P_mem 1 (by omega) _ h_SM_mem_1
  have h_P_mem_2 :=
    h_P_mem 2 (by omega) _ h_SM_mem_2
  have h_P_mem_3 :=
    h_P_mem 3 (by omega) _ h_SM_mem_3
  have h_P_mem_4 :=
    h_P_mem 4 (by omega) _ h_SM_mem_4
  have h_P_mem_5 :=
    h_P_mem 5 (by omega) _ h_SM_mem_5
  have h_P_mem_6 :=
    h_P_mem 6 (by omega) _ h_SM_mem_6
  have h_P_mem_7 :=
    h_P_mem 7 (by omega) _ h_SM_mem_7
  -- Climb to hp.
  have hp_regs_dst : hp.regs dst = some vOldDst := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_dst
  have hp_regs_src : hp.regs src = some baseAddr := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_src
  have hp_mem (i_addr : Nat) (val : Nat)
      (h_P_at : h_P.mem i_addr = some val) :
      hp.mem i_addr = some val := by
    rw [← hu_PR]; exact PartialState.union_mem_of_left_some h_P_at
  have hs_regs_src : s.regs.get src = baseAddr := hcr_regs src baseAddr hp_regs_src
  -- Extract s.mem values.
  have hs_mem_0 : s.mem (effectiveAddr baseAddr off) = v % 256 :=
    hcm_mem _ _ (hp_mem _ _ h_P_mem_0)
  have hs_mem_1 : s.mem (effectiveAddr baseAddr off + 1) = v / 0x100 % 256 :=
    hcm_mem _ _ (hp_mem _ _ h_P_mem_1)
  have hs_mem_2 : s.mem (effectiveAddr baseAddr off + 2) = v / 0x10000 % 256 :=
    hcm_mem _ _ (hp_mem _ _ h_P_mem_2)
  have hs_mem_3 : s.mem (effectiveAddr baseAddr off + 3) = v / 0x1000000 % 256 :=
    hcm_mem _ _ (hp_mem _ _ h_P_mem_3)
  have hs_mem_4 : s.mem (effectiveAddr baseAddr off + 4) = v / 0x100000000 % 256 :=
    hcm_mem _ _ (hp_mem _ _ h_P_mem_4)
  have hs_mem_5 : s.mem (effectiveAddr baseAddr off + 5) = v / 0x10000000000 % 256 :=
    hcm_mem _ _ (hp_mem _ _ h_P_mem_5)
  have hs_mem_6 : s.mem (effectiveAddr baseAddr off + 6) = v / 0x1000000000000 % 256 :=
    hcm_mem _ _ (hp_mem _ _ h_P_mem_6)
  have hs_mem_7 : s.mem (effectiveAddr baseAddr off + 7) = v / 0x100000000000000 % 256 :=
    hcm_mem _ _ (hp_mem _ _ h_P_mem_7)
  -- ===== Step: readU64 yields v via the assembly helper =====
  have h_readU64 : Memory.readU64 s.mem (effectiveAddr baseAddr off) = v :=
    readU64_eq_of_bytes_match hv hs_mem_0 hs_mem_1 hs_mem_2 hs_mem_3
      hs_mem_4 hs_mem_5 hs_mem_6 hs_mem_7
  have hfetch : fetch s.pc = some (.ldx .dword dst src off) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hexec : executeFn fetch s 1 =
      { s with regs := s.regs.set dst v, pc := s.pc + 1 } := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch,
        executeFn_zero]
    simp only [step, hs_regs_src, Width.bytes, if_pos h_region,
               Memory.readByWidth, h_readU64]
  -- ===== h_R cannot own dst, src, or any of the 8 mem bytes =====
  obtain ⟨hd_PR_regs, hd_PR_mem, _⟩ := hd_PR
  have h_R_no_dst : h_R.regs dst = none := by
    rcases hd_PR_regs dst with hl | hr
    · rw [h_P_regs_dst] at hl; nomatch hl
    · exact hr
  have h_R_no_src : h_R.regs src = none := by
    rcases hd_PR_regs src with hl | hr
    · rw [h_P_regs_src] at hl; nomatch hl
    · exact hr
  have h_R_no_mem (a val : Nat) (h_P_at : h_P.mem a = some val) :
      h_R.mem a = none := by
    rcases hd_PR_mem a with hl | hr
    · rw [h_P_at] at hl; nomatch hl
    · exact hr
  have h_R_no_pc : h_R.pc = none := hRfree _ h_R_sat
  -- ===== Build the post =====
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_⟩
  · rw [hexec]; show s.pc + 1 = pc + 1; rw [hpc]
  · rw [hexec]; exact hex
  · rw [hexec]
    refine ⟨_, ?_,
            (PartialState.singletonReg dst v).union
              ((PartialState.singletonReg src baseAddr).union
                (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v)),
            h_R, ?_, rfl,
            ⟨PartialState.singletonReg dst v,
             (PartialState.singletonReg src baseAddr).union
              (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v),
             ?_, rfl, rfl,
             ⟨PartialState.singletonReg src baseAddr,
              PartialState.singletonMemU64 (effectiveAddr baseAddr off) v,
              hd_src_mem, rfl, rfl, rfl⟩⟩,
            h_R_sat⟩
    -- (a) Compat: regs, mem (9-case), pc.
    · refine ⟨?_, ?_, ?_⟩
      -- regs:
      · intro r vr hvr
        show (s.regs.set dst v).get r = vr
        by_cases hrdst : r = dst
        · rw [hrdst] at hvr
          have h_inner :
              ((PartialState.singletonReg dst v).union
                ((PartialState.singletonReg src baseAddr).union
                  (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v))).regs dst
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
                    (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v))).regs src
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
                    (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v))).regs r
                = none := by
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrdst)]
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrsrc)]
              exact PartialState.singletonMemU64_regs r
            rw [PartialState.union_regs_of_left_none h_outer_h1_none] at hvr
            apply hcr_regs r vr
            have h_P_none : h_P.regs r = none := by
              rw [← hu_dst_SM]
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrdst)]
              rw [← hu_src_mem]
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrsrc)]
              exact PartialState.singletonMemU64_regs r
            rw [← hu_PR]
            rw [PartialState.union_regs_of_left_none h_P_none]
            exact hvr
      -- mem: in-range (8 cases) or outside (1 case).
      · intro a vm hvm
        show s.mem a = vm
        -- Helper for in-range case at offset `i`: peel through union to singletonMemU64, equate vm.
        -- Outside case: outer-h1 owns nothing at a, fall through to h_R via hp.
        by_cases ha0 : a = effectiveAddr baseAddr off
        · rw [ha0] at hvm ⊢
          have h_inner :
              ((PartialState.singletonReg dst v).union
                ((PartialState.singletonReg src baseAddr).union
                  (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v))).mem
                  (effectiveAddr baseAddr off) = some (v % 256) := by
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            exact PartialState.singletonMemU64_mem_0 _ _
          rw [PartialState.union_mem_of_left_some h_inner] at hvm
          have : vm = v % 256 := (Option.some.inj hvm).symm
          rw [this]; exact hs_mem_0
        · by_cases ha1 : a = effectiveAddr baseAddr off + 1
          · rw [ha1] at hvm ⊢
            have h_inner :
                ((PartialState.singletonReg dst v).union
                  ((PartialState.singletonReg src baseAddr).union
                    (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v))).mem
                    (effectiveAddr baseAddr off + 1) = some (v / 0x100 % 256) := by
              rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
              rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
              exact PartialState.singletonMemU64_mem_1 _ _
            rw [PartialState.union_mem_of_left_some h_inner] at hvm
            have : vm = v / 0x100 % 256 := (Option.some.inj hvm).symm
            rw [this]; exact hs_mem_1
          · by_cases ha2 : a = effectiveAddr baseAddr off + 2
            · rw [ha2] at hvm ⊢
              have h_inner :
                  ((PartialState.singletonReg dst v).union
                    ((PartialState.singletonReg src baseAddr).union
                      (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v))).mem
                      (effectiveAddr baseAddr off + 2) = some (v / 0x10000 % 256) := by
                rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                exact PartialState.singletonMemU64_mem_2 _ _
              rw [PartialState.union_mem_of_left_some h_inner] at hvm
              have : vm = v / 0x10000 % 256 := (Option.some.inj hvm).symm
              rw [this]; exact hs_mem_2
            · by_cases ha3 : a = effectiveAddr baseAddr off + 3
              · rw [ha3] at hvm ⊢
                have h_inner :
                    ((PartialState.singletonReg dst v).union
                      ((PartialState.singletonReg src baseAddr).union
                        (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v))).mem
                        (effectiveAddr baseAddr off + 3) = some (v / 0x1000000 % 256) := by
                  rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                  rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                  exact PartialState.singletonMemU64_mem_3 _ _
                rw [PartialState.union_mem_of_left_some h_inner] at hvm
                have : vm = v / 0x1000000 % 256 := (Option.some.inj hvm).symm
                rw [this]; exact hs_mem_3
              · by_cases ha4 : a = effectiveAddr baseAddr off + 4
                · rw [ha4] at hvm ⊢
                  have h_inner :
                      ((PartialState.singletonReg dst v).union
                        ((PartialState.singletonReg src baseAddr).union
                          (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v))).mem
                          (effectiveAddr baseAddr off + 4) = some (v / 0x100000000 % 256) := by
                    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                    exact PartialState.singletonMemU64_mem_4 _ _
                  rw [PartialState.union_mem_of_left_some h_inner] at hvm
                  have : vm = v / 0x100000000 % 256 := (Option.some.inj hvm).symm
                  rw [this]; exact hs_mem_4
                · by_cases ha5 : a = effectiveAddr baseAddr off + 5
                  · rw [ha5] at hvm ⊢
                    have h_inner :
                        ((PartialState.singletonReg dst v).union
                          ((PartialState.singletonReg src baseAddr).union
                            (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v))).mem
                            (effectiveAddr baseAddr off + 5) = some (v / 0x10000000000 % 256) := by
                      rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                      rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                      exact PartialState.singletonMemU64_mem_5 _ _
                    rw [PartialState.union_mem_of_left_some h_inner] at hvm
                    have : vm = v / 0x10000000000 % 256 := (Option.some.inj hvm).symm
                    rw [this]; exact hs_mem_5
                  · by_cases ha6 : a = effectiveAddr baseAddr off + 6
                    · rw [ha6] at hvm ⊢
                      have h_inner :
                          ((PartialState.singletonReg dst v).union
                            ((PartialState.singletonReg src baseAddr).union
                              (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v))).mem
                              (effectiveAddr baseAddr off + 6) = some (v / 0x1000000000000 % 256) := by
                        rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                        rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                        exact PartialState.singletonMemU64_mem_6 _ _
                      rw [PartialState.union_mem_of_left_some h_inner] at hvm
                      have : vm = v / 0x1000000000000 % 256 := (Option.some.inj hvm).symm
                      rw [this]; exact hs_mem_6
                    · by_cases ha7 : a = effectiveAddr baseAddr off + 7
                      · rw [ha7] at hvm ⊢
                        have h_inner :
                            ((PartialState.singletonReg dst v).union
                              ((PartialState.singletonReg src baseAddr).union
                                (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v))).mem
                                (effectiveAddr baseAddr off + 7) = some (v / 0x100000000000000 % 256) := by
                          rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                          rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                          exact PartialState.singletonMemU64_mem_7 _ _
                        rw [PartialState.union_mem_of_left_some h_inner] at hvm
                        have : vm = v / 0x100000000000000 % 256 := (Option.some.inj hvm).symm
                        rw [this]; exact hs_mem_7
                      · -- outside [addr, addr+8)
                        have h_outer_none :
                            ((PartialState.singletonReg dst v).union
                              ((PartialState.singletonReg src baseAddr).union
                                (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v))).mem a
                            = none := by
                          rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                          rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                          exact PartialState.singletonMemU64_mem_outside _ _ a (by omega)
                        rw [PartialState.union_mem_of_left_none h_outer_none] at hvm
                        apply hcm_mem a vm
                        have h_P_none : h_P.mem a = none := by
                          rw [← hu_dst_SM]
                          rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                          rw [← hu_src_mem]
                          rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                          exact PartialState.singletonMemU64_mem_outside _ _ a (by omega)
                        rw [← hu_PR]
                        rw [PartialState.union_mem_of_left_none h_P_none]
                        exact hvm
      -- pc:
      · intro vp hvp
        have h_outer_pc :
            ((PartialState.singletonReg dst v).union
              ((PartialState.singletonReg src baseAddr).union
                (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v))).pc = none := by
          rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
          rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
          exact PartialState.singletonMemU64_pc
        rw [PartialState.union_pc_of_left_none h_outer_pc] at hvp
        rw [h_R_no_pc] at hvp
        nomatch hvp
    -- (b) Outer disjointness: new witness ⊥ h_R.
    · refine ⟨?_, ?_, ?_⟩
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
            exact PartialState.singletonMemU64_regs r
      · intro a
        by_cases ha0 : a = effectiveAddr baseAddr off
        · rw [ha0]; right; exact h_R_no_mem _ _ h_P_mem_0
        · by_cases ha1 : a = effectiveAddr baseAddr off + 1
          · rw [ha1]; right; exact h_R_no_mem _ _ h_P_mem_1
          · by_cases ha2 : a = effectiveAddr baseAddr off + 2
            · rw [ha2]; right; exact h_R_no_mem _ _ h_P_mem_2
            · by_cases ha3 : a = effectiveAddr baseAddr off + 3
              · rw [ha3]; right; exact h_R_no_mem _ _ h_P_mem_3
              · by_cases ha4 : a = effectiveAddr baseAddr off + 4
                · rw [ha4]; right; exact h_R_no_mem _ _ h_P_mem_4
                · by_cases ha5 : a = effectiveAddr baseAddr off + 5
                  · rw [ha5]; right; exact h_R_no_mem _ _ h_P_mem_5
                  · by_cases ha6 : a = effectiveAddr baseAddr off + 6
                    · rw [ha6]; right; exact h_R_no_mem _ _ h_P_mem_6
                    · by_cases ha7 : a = effectiveAddr baseAddr off + 7
                      · rw [ha7]; right; exact h_R_no_mem _ _ h_P_mem_7
                      · left
                        rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                        rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                        exact PartialState.singletonMemU64_mem_outside _ _ a (by omega)
      · left
        rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
        rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
        exact PartialState.singletonMemU64_pc
    -- (c) Inner disjointness: singletonReg dst v ⊥ (singletonReg src baseAddr ⊎ singletonMemU64 ...).
    · refine ⟨fun r => ?_, fun a => ?_, ?_⟩
      · by_cases hrdst : r = dst
        · right
          rw [hrdst,
              PartialState.union_regs_of_left_none
                (PartialState.singletonReg_regs_other hne_dst_src)]
          exact PartialState.singletonMemU64_regs dst
        · left; exact PartialState.singletonReg_regs_other hrdst
      · left; exact PartialState.singletonReg_mem a
      · left; exact PartialState.singletonReg_pc

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
  obtain ⟨hcr_regs, hcm_mem, _⟩ := hcompat
  have hne_dst_src : dst ≠ src := by
    obtain ⟨hd_dst_SM_regs, _, _⟩ := hd_dst_SM
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
  obtain ⟨hd_PR_regs, hd_PR_mem, _⟩ := hd_PR
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
    · refine ⟨?_, ?_, ?_⟩
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
    · refine ⟨?_, ?_, ?_⟩
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
    · refine ⟨fun r => ?_, fun a => ?_, ?_⟩
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
  obtain ⟨hcr_regs, hcm_mem, _⟩ := hcompat
  have hne_base_val : baseReg ≠ valReg := by
    obtain ⟨hd_base_VM_regs, _, _⟩ := hd_base_VM
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
  obtain ⟨hd_PR_regs, hd_PR_mem, _⟩ := hd_PR
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
    · refine ⟨?_, ?_, ?_⟩
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
            show (if a = effectiveAddr baseAddr off then _
                  else if a = effectiveAddr baseAddr off + 1 then _
                  else s.mem a) = vm
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
    · refine ⟨?_, ?_, ?_⟩
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
    · refine ⟨fun r => ?_, fun a => ?_, ?_⟩
      · by_cases hrbase : r = baseReg
        · right
          rw [hrbase,
              PartialState.union_regs_of_left_none
                (PartialState.singletonReg_regs_other hne_base_val)]
          exact PartialState.singletonMemU16_regs baseReg
        · left; exact PartialState.singletonReg_regs_other hrbase
      · left; exact PartialState.singletonReg_mem a
      · left; exact PartialState.singletonReg_pc
    · refine ⟨fun r => ?_, fun a => ?_, ?_⟩
      · right; exact PartialState.singletonMemU16_regs r
      · left; exact PartialState.singletonReg_mem a
      · left; exact PartialState.singletonReg_pc

/-! ## Memory loads/stores — word width

4 bytes (`u32`); mem compat case-analysis is 5-way (4 in-range + outside). -/

/-- `ldx .word dst src off`: load 32-bit value at `[src + off]` into `dst`. -/
theorem ldxw_spec
    (dst src : Reg) (off : Int) (vOldDst baseAddr v : Nat) (pc : Nat)
    (hne : dst ≠ .r10) (hv : v < 2 ^ 32) :
    cuTripleWithinMem 1 pc (pc + 1)
      (CodeReq.singleton pc (.ldx .word dst src off))
      ((dst ↦ᵣ vOldDst) ** (src ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr off ↦U32 v))
      ((dst ↦ᵣ v) ** (src ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr off ↦U32 v))
      (fun rt => rt.containsRange (effectiveAddr baseAddr off) 4 = true) := by
  intro R hRfree fetch hcr s hPR hpc hex h_region
  obtain ⟨hp, hcompat, h_P, h_R, hd_PR, hu_PR, h_P_sat, h_R_sat⟩ := hPR
  obtain ⟨h_dst, h_SM, hd_dst_SM, hu_dst_SM, h_dst_pred, h_SM_sat⟩ := h_P_sat
  obtain ⟨h_src, h_mem, hd_src_mem, hu_src_mem, h_src_pred, h_mem_pred⟩ := h_SM_sat
  rw [h_src_pred] at hu_src_mem hd_src_mem
  rw [h_mem_pred] at hu_src_mem hd_src_mem
  rw [h_dst_pred] at hu_dst_SM hd_dst_SM
  clear h_src_pred h_mem_pred h_dst_pred h_src h_mem h_dst
  obtain ⟨hcr_regs, hcm_mem, _⟩ := hcompat
  have hne_dst_src : dst ≠ src := by
    obtain ⟨hd_dst_SM_regs, _, _⟩ := hd_dst_SM
    intro habs
    rcases hd_dst_SM_regs dst with hl | hr
    · rw [PartialState.singletonReg_regs_self] at hl; nomatch hl
    · rw [← hu_src_mem] at hr
      have : ((PartialState.singletonReg src baseAddr).union
              (PartialState.singletonMemU32 (effectiveAddr baseAddr off) v)).regs dst
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
    exact PartialState.singletonMemU32_mem_0 _ _
  have h_SM_mem_1 :
      h_SM.mem (effectiveAddr baseAddr off + 1) = some (v / 0x100 % 256) := by
    rw [← hu_src_mem,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact PartialState.singletonMemU32_mem_1 _ _
  have h_SM_mem_2 :
      h_SM.mem (effectiveAddr baseAddr off + 2) = some (v / 0x10000 % 256) := by
    rw [← hu_src_mem,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact PartialState.singletonMemU32_mem_2 _ _
  have h_SM_mem_3 :
      h_SM.mem (effectiveAddr baseAddr off + 3) = some (v / 0x1000000 % 256) := by
    rw [← hu_src_mem,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact PartialState.singletonMemU32_mem_3 _ _
  have h_P_regs_dst : h_P.regs dst = some vOldDst := by
    rw [← hu_dst_SM]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_regs_src : h_P.regs src = some baseAddr := by
    rw [← hu_dst_SM,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other hne_dst_src.symm)]
    exact h_SM_regs_src
  have h_P_mem (i_addr val : Nat) (h_atom : h_SM.mem i_addr = some val) :
      h_P.mem i_addr = some val := by
    rw [← hu_dst_SM,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact h_atom
  have h_P_mem_0 := h_P_mem _ _ h_SM_mem_0
  have h_P_mem_1 := h_P_mem _ _ h_SM_mem_1
  have h_P_mem_2 := h_P_mem _ _ h_SM_mem_2
  have h_P_mem_3 := h_P_mem _ _ h_SM_mem_3
  have hp_regs_dst : hp.regs dst = some vOldDst := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_dst
  have hp_regs_src : hp.regs src = some baseAddr := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_src
  have hp_mem (i_addr val : Nat) (h_atom : h_P.mem i_addr = some val) :
      hp.mem i_addr = some val := by
    rw [← hu_PR]; exact PartialState.union_mem_of_left_some h_atom
  have hs_regs_src : s.regs.get src = baseAddr := hcr_regs src baseAddr hp_regs_src
  have hs_mem_0 : s.mem (effectiveAddr baseAddr off) = v % 256 :=
    hcm_mem _ _ (hp_mem _ _ h_P_mem_0)
  have hs_mem_1 : s.mem (effectiveAddr baseAddr off + 1) = v / 0x100 % 256 :=
    hcm_mem _ _ (hp_mem _ _ h_P_mem_1)
  have hs_mem_2 : s.mem (effectiveAddr baseAddr off + 2) = v / 0x10000 % 256 :=
    hcm_mem _ _ (hp_mem _ _ h_P_mem_2)
  have hs_mem_3 : s.mem (effectiveAddr baseAddr off + 3) = v / 0x1000000 % 256 :=
    hcm_mem _ _ (hp_mem _ _ h_P_mem_3)
  have h_readU32 : Memory.readU32 s.mem (effectiveAddr baseAddr off) = v :=
    readU32_eq_of_bytes_match hv hs_mem_0 hs_mem_1 hs_mem_2 hs_mem_3
  have hfetch : fetch s.pc = some (.ldx .word dst src off) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hexec : executeFn fetch s 1 =
      { s with regs := s.regs.set dst v, pc := s.pc + 1 } := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch,
        executeFn_zero]
    simp only [step, hs_regs_src, Width.bytes, if_pos h_region,
               Memory.readByWidth, h_readU32]
  obtain ⟨hd_PR_regs, hd_PR_mem, _⟩ := hd_PR
  have h_R_no_dst : h_R.regs dst = none := by
    rcases hd_PR_regs dst with hl | hr
    · rw [h_P_regs_dst] at hl; nomatch hl
    · exact hr
  have h_R_no_src : h_R.regs src = none := by
    rcases hd_PR_regs src with hl | hr
    · rw [h_P_regs_src] at hl; nomatch hl
    · exact hr
  have h_R_no_mem (a val : Nat) (h_P_at : h_P.mem a = some val) :
      h_R.mem a = none := by
    rcases hd_PR_mem a with hl | hr
    · rw [h_P_at] at hl; nomatch hl
    · exact hr
  have h_R_no_pc : h_R.pc = none := hRfree _ h_R_sat
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_⟩
  · rw [hexec]; show s.pc + 1 = pc + 1; rw [hpc]
  · rw [hexec]; exact hex
  · rw [hexec]
    refine ⟨_, ?_,
            (PartialState.singletonReg dst v).union
              ((PartialState.singletonReg src baseAddr).union
                (PartialState.singletonMemU32 (effectiveAddr baseAddr off) v)),
            h_R, ?_, rfl,
            ⟨PartialState.singletonReg dst v,
             (PartialState.singletonReg src baseAddr).union
              (PartialState.singletonMemU32 (effectiveAddr baseAddr off) v),
             ?_, rfl, rfl,
             ⟨PartialState.singletonReg src baseAddr,
              PartialState.singletonMemU32 (effectiveAddr baseAddr off) v,
              hd_src_mem, rfl, rfl, rfl⟩⟩,
            h_R_sat⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro r vr hvr
        show (s.regs.set dst v).get r = vr
        by_cases hrdst : r = dst
        · rw [hrdst] at hvr
          have h_inner :
              ((PartialState.singletonReg dst v).union
                ((PartialState.singletonReg src baseAddr).union
                  (PartialState.singletonMemU32 (effectiveAddr baseAddr off) v))).regs dst
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
                    (PartialState.singletonMemU32 (effectiveAddr baseAddr off) v))).regs src
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
                    (PartialState.singletonMemU32 (effectiveAddr baseAddr off) v))).regs r
                = none := by
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrdst)]
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrsrc)]
              exact PartialState.singletonMemU32_regs r
            rw [PartialState.union_regs_of_left_none h_outer_h1_none] at hvr
            apply hcr_regs r vr
            have h_P_none : h_P.regs r = none := by
              rw [← hu_dst_SM]
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrdst)]
              rw [← hu_src_mem]
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrsrc)]
              exact PartialState.singletonMemU32_regs r
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
                  (PartialState.singletonMemU32 (effectiveAddr baseAddr off) v))).mem
                  (effectiveAddr baseAddr off) = some (v % 256) := by
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            exact PartialState.singletonMemU32_mem_0 _ _
          rw [PartialState.union_mem_of_left_some h_inner] at hvm
          have : vm = v % 256 := (Option.some.inj hvm).symm
          rw [this]; exact hs_mem_0
        · by_cases ha1 : a = effectiveAddr baseAddr off + 1
          · rw [ha1] at hvm ⊢
            have h_inner :
                ((PartialState.singletonReg dst v).union
                  ((PartialState.singletonReg src baseAddr).union
                    (PartialState.singletonMemU32 (effectiveAddr baseAddr off) v))).mem
                    (effectiveAddr baseAddr off + 1) = some (v / 0x100 % 256) := by
              rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
              rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
              exact PartialState.singletonMemU32_mem_1 _ _
            rw [PartialState.union_mem_of_left_some h_inner] at hvm
            have : vm = v / 0x100 % 256 := (Option.some.inj hvm).symm
            rw [this]; exact hs_mem_1
          · by_cases ha2 : a = effectiveAddr baseAddr off + 2
            · rw [ha2] at hvm ⊢
              have h_inner :
                  ((PartialState.singletonReg dst v).union
                    ((PartialState.singletonReg src baseAddr).union
                      (PartialState.singletonMemU32 (effectiveAddr baseAddr off) v))).mem
                      (effectiveAddr baseAddr off + 2) = some (v / 0x10000 % 256) := by
                rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                exact PartialState.singletonMemU32_mem_2 _ _
              rw [PartialState.union_mem_of_left_some h_inner] at hvm
              have : vm = v / 0x10000 % 256 := (Option.some.inj hvm).symm
              rw [this]; exact hs_mem_2
            · by_cases ha3 : a = effectiveAddr baseAddr off + 3
              · rw [ha3] at hvm ⊢
                have h_inner :
                    ((PartialState.singletonReg dst v).union
                      ((PartialState.singletonReg src baseAddr).union
                        (PartialState.singletonMemU32 (effectiveAddr baseAddr off) v))).mem
                        (effectiveAddr baseAddr off + 3) = some (v / 0x1000000 % 256) := by
                  rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                  rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                  exact PartialState.singletonMemU32_mem_3 _ _
                rw [PartialState.union_mem_of_left_some h_inner] at hvm
                have : vm = v / 0x1000000 % 256 := (Option.some.inj hvm).symm
                rw [this]; exact hs_mem_3
              · have h_outer_none :
                    ((PartialState.singletonReg dst v).union
                      ((PartialState.singletonReg src baseAddr).union
                        (PartialState.singletonMemU32 (effectiveAddr baseAddr off) v))).mem a
                    = none := by
                  rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                  rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                  exact PartialState.singletonMemU32_mem_outside _ _ a (by omega)
                rw [PartialState.union_mem_of_left_none h_outer_none] at hvm
                apply hcm_mem a vm
                have h_P_none : h_P.mem a = none := by
                  rw [← hu_dst_SM]
                  rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                  rw [← hu_src_mem]
                  rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                  exact PartialState.singletonMemU32_mem_outside _ _ a (by omega)
                rw [← hu_PR]
                rw [PartialState.union_mem_of_left_none h_P_none]
                exact hvm
      · intro vp hvp
        have h_outer_pc :
            ((PartialState.singletonReg dst v).union
              ((PartialState.singletonReg src baseAddr).union
                (PartialState.singletonMemU32 (effectiveAddr baseAddr off) v))).pc = none := by
          rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
          rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
          exact PartialState.singletonMemU32_pc
        rw [PartialState.union_pc_of_left_none h_outer_pc] at hvp
        rw [h_R_no_pc] at hvp
        nomatch hvp
    · refine ⟨?_, ?_, ?_⟩
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
            exact PartialState.singletonMemU32_regs r
      · intro a
        by_cases ha0 : a = effectiveAddr baseAddr off
        · rw [ha0]; right; exact h_R_no_mem _ _ h_P_mem_0
        · by_cases ha1 : a = effectiveAddr baseAddr off + 1
          · rw [ha1]; right; exact h_R_no_mem _ _ h_P_mem_1
          · by_cases ha2 : a = effectiveAddr baseAddr off + 2
            · rw [ha2]; right; exact h_R_no_mem _ _ h_P_mem_2
            · by_cases ha3 : a = effectiveAddr baseAddr off + 3
              · rw [ha3]; right; exact h_R_no_mem _ _ h_P_mem_3
              · left
                rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                exact PartialState.singletonMemU32_mem_outside _ _ a (by omega)
      · left
        rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
        rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
        exact PartialState.singletonMemU32_pc
    · refine ⟨fun r => ?_, fun a => ?_, ?_⟩
      · by_cases hrdst : r = dst
        · right
          rw [hrdst,
              PartialState.union_regs_of_left_none
                (PartialState.singletonReg_regs_other hne_dst_src)]
          exact PartialState.singletonMemU32_regs dst
        · left; exact PartialState.singletonReg_regs_other hrdst
      · left; exact PartialState.singletonReg_mem a
      · left; exact PartialState.singletonReg_pc

/-- `stx .word baseReg off valReg`: write valReg's low 32 bits at `[baseReg + off]`. -/
theorem stxw_spec
    (baseReg valReg : Reg) (off : Int)
    (baseAddr vSrc oldV : Nat) (pc : Nat) :
    cuTripleWithinMem 1 pc (pc + 1)
      (CodeReq.singleton pc (.stx .word baseReg off valReg))
      ((baseReg ↦ᵣ baseAddr) ** (valReg ↦ᵣ vSrc) **
        (effectiveAddr baseAddr off ↦U32 oldV))
      ((baseReg ↦ᵣ baseAddr) ** (valReg ↦ᵣ vSrc) **
        (effectiveAddr baseAddr off ↦U32 vSrc))
      (fun rt => rt.containsWritable (effectiveAddr baseAddr off) 4 = true) := by
  intro R hRfree fetch hcr s hPR hpc hex h_region
  obtain ⟨hp, hcompat, h_P, h_R, hd_PR, hu_PR, h_P_sat, h_R_sat⟩ := hPR
  obtain ⟨h_base, h_VM, hd_base_VM, hu_base_VM, h_base_pred, h_VM_sat⟩ := h_P_sat
  obtain ⟨h_val, h_mem, hd_val_mem, hu_val_mem, h_val_pred, h_mem_pred⟩ := h_VM_sat
  rw [h_val_pred] at hu_val_mem hd_val_mem
  rw [h_mem_pred] at hu_val_mem hd_val_mem
  rw [h_base_pred] at hu_base_VM hd_base_VM
  clear h_val_pred h_mem_pred h_base_pred h_val h_mem h_base
  obtain ⟨hcr_regs, hcm_mem, _⟩ := hcompat
  have hne_base_val : baseReg ≠ valReg := by
    obtain ⟨hd_base_VM_regs, _, _⟩ := hd_base_VM
    intro habs
    rcases hd_base_VM_regs baseReg with hl | hr
    · rw [PartialState.singletonReg_regs_self] at hl; nomatch hl
    · rw [← hu_val_mem] at hr
      have : ((PartialState.singletonReg valReg vSrc).union
              (PartialState.singletonMemU32 (effectiveAddr baseAddr off) oldV)).regs baseReg
              = some vSrc := by
        rw [habs]
        exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
      rw [this] at hr; nomatch hr
  have h_VM_regs_val : h_VM.regs valReg = some vSrc := by
    rw [← hu_val_mem]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_VM_mem (i_addr val : Nat)
      (h_atom : (PartialState.singletonMemU32 (effectiveAddr baseAddr off) oldV).mem i_addr
                = some val) :
      h_VM.mem i_addr = some val := by
    rw [← hu_val_mem,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact h_atom
  have h_P_mem_i (i_addr val : Nat) (h_atom : h_VM.mem i_addr = some val) :
      h_P.mem i_addr = some val := by
    rw [← hu_base_VM,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact h_atom
  have h_P_regs_base : h_P.regs baseReg = some baseAddr := by
    rw [← hu_base_VM]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_regs_val : h_P.regs valReg = some vSrc := by
    rw [← hu_base_VM]
    rw [PartialState.union_regs_of_left_none
        (PartialState.singletonReg_regs_other hne_base_val.symm)]
    exact h_VM_regs_val
  have hp_regs_base : hp.regs baseReg = some baseAddr := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_base
  have hp_regs_val : hp.regs valReg = some vSrc := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_val
  have hs_regs_base : s.regs.get baseReg = baseAddr :=
    hcr_regs baseReg baseAddr hp_regs_base
  have hs_regs_val : s.regs.get valReg = vSrc := hcr_regs valReg vSrc hp_regs_val
  have hfetch : fetch s.pc = some (.stx .word baseReg off valReg) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hexec : executeFn fetch s 1 =
      { s with mem := Memory.writeU32 s.mem (effectiveAddr baseAddr off) (vSrc % 2 ^ 32),
               pc := s.pc + 1 } := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch,
        executeFn_zero]
    simp only [step, hs_regs_base, Width.bytes, if_pos h_region,
               Memory.writeByWidth, hs_regs_val]
  obtain ⟨hd_PR_regs, hd_PR_mem, _⟩ := hd_PR
  have h_R_no_base : h_R.regs baseReg = none := by
    rcases hd_PR_regs baseReg with hl | hr
    · rw [h_P_regs_base] at hl; nomatch hl
    · exact hr
  have h_R_no_val : h_R.regs valReg = none := by
    rcases hd_PR_regs valReg with hl | hr
    · rw [h_P_regs_val] at hl; nomatch hl
    · exact hr
  have h_R_no_mem_at (a val : Nat) (h_P_at : h_P.mem a = some val) :
      h_R.mem a = none := by
    rcases hd_PR_mem a with hl | hr
    · rw [h_P_at] at hl; nomatch hl
    · exact hr
  have h_R_no_pc : h_R.pc = none := hRfree _ h_R_sat
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_⟩
  · rw [hexec]; show s.pc + 1 = pc + 1; rw [hpc]
  · rw [hexec]; exact hex
  · rw [hexec]
    refine ⟨_, ?_,
            (PartialState.singletonReg baseReg baseAddr).union
              ((PartialState.singletonReg valReg vSrc).union
                (PartialState.singletonMemU32 (effectiveAddr baseAddr off) vSrc)),
            h_R, ?_, rfl,
            ⟨PartialState.singletonReg baseReg baseAddr,
             (PartialState.singletonReg valReg vSrc).union
              (PartialState.singletonMemU32 (effectiveAddr baseAddr off) vSrc),
             ?_, rfl, rfl,
             ⟨PartialState.singletonReg valReg vSrc,
              PartialState.singletonMemU32 (effectiveAddr baseAddr off) vSrc,
              ?_, rfl, rfl, rfl⟩⟩,
            h_R_sat⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro r vr hvr
        show s.regs.get r = vr
        by_cases hrbase : r = baseReg
        · rw [hrbase] at hvr
          have h_inner :
              ((PartialState.singletonReg baseReg baseAddr).union
                ((PartialState.singletonReg valReg vSrc).union
                  (PartialState.singletonMemU32 (effectiveAddr baseAddr off) vSrc))).regs baseReg
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
                    (PartialState.singletonMemU32 (effectiveAddr baseAddr off) vSrc))).regs valReg
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
                    (PartialState.singletonMemU32 (effectiveAddr baseAddr off) vSrc))).regs r
                = none := by
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrbase)]
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrval)]
              exact PartialState.singletonMemU32_regs r
            rw [PartialState.union_regs_of_left_none h_outer_h1_none] at hvr
            apply hcr_regs r vr
            have h_P_none : h_P.regs r = none := by
              rw [← hu_base_VM]
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrbase)]
              rw [← hu_val_mem]
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrval)]
              exact PartialState.singletonMemU32_regs r
            rw [← hu_PR]
            rw [PartialState.union_regs_of_left_none h_P_none]
            exact hvr
      · intro a vm hvm
        show (Memory.writeU32 s.mem (effectiveAddr baseAddr off) (vSrc % 2 ^ 32)) a = vm
        by_cases ha0 : a = effectiveAddr baseAddr off
        · rw [ha0] at hvm ⊢
          have h_inner :
              ((PartialState.singletonReg baseReg baseAddr).union
                ((PartialState.singletonReg valReg vSrc).union
                  (PartialState.singletonMemU32 (effectiveAddr baseAddr off) vSrc))).mem
                  (effectiveAddr baseAddr off) = some (vSrc % 256) := by
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            exact PartialState.singletonMemU32_mem_0 _ _
          rw [PartialState.union_mem_of_left_some h_inner] at hvm
          have : vm = vSrc % 256 := (Option.some.inj hvm).symm
          rw [this]
          unfold Memory.writeU32
          simp
        · by_cases ha1 : a = effectiveAddr baseAddr off + 1
          · rw [ha1] at hvm ⊢
            have h_inner :
                ((PartialState.singletonReg baseReg baseAddr).union
                  ((PartialState.singletonReg valReg vSrc).union
                    (PartialState.singletonMemU32 (effectiveAddr baseAddr off) vSrc))).mem
                    (effectiveAddr baseAddr off + 1) = some (vSrc / 0x100 % 256) := by
              rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
              rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
              exact PartialState.singletonMemU32_mem_1 _ _
            rw [PartialState.union_mem_of_left_some h_inner] at hvm
            have : vm = vSrc / 0x100 % 256 := (Option.some.inj hvm).symm
            rw [this]
            unfold Memory.writeU32
            simp [show effectiveAddr baseAddr off + 1 ≠ effectiveAddr baseAddr off from by omega]
            omega
          · by_cases ha2 : a = effectiveAddr baseAddr off + 2
            · rw [ha2] at hvm ⊢
              have h_inner :
                  ((PartialState.singletonReg baseReg baseAddr).union
                    ((PartialState.singletonReg valReg vSrc).union
                      (PartialState.singletonMemU32 (effectiveAddr baseAddr off) vSrc))).mem
                      (effectiveAddr baseAddr off + 2) = some (vSrc / 0x10000 % 256) := by
                rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                exact PartialState.singletonMemU32_mem_2 _ _
              rw [PartialState.union_mem_of_left_some h_inner] at hvm
              have : vm = vSrc / 0x10000 % 256 := (Option.some.inj hvm).symm
              rw [this]
              unfold Memory.writeU32
              simp [show effectiveAddr baseAddr off + 2 ≠ effectiveAddr baseAddr off from by omega,
                    show effectiveAddr baseAddr off + 2 ≠ effectiveAddr baseAddr off + 1 from by omega]
              omega
            · by_cases ha3 : a = effectiveAddr baseAddr off + 3
              · rw [ha3] at hvm ⊢
                have h_inner :
                    ((PartialState.singletonReg baseReg baseAddr).union
                      ((PartialState.singletonReg valReg vSrc).union
                        (PartialState.singletonMemU32 (effectiveAddr baseAddr off) vSrc))).mem
                        (effectiveAddr baseAddr off + 3) = some (vSrc / 0x1000000 % 256) := by
                  rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                  rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                  exact PartialState.singletonMemU32_mem_3 _ _
                rw [PartialState.union_mem_of_left_some h_inner] at hvm
                have : vm = vSrc / 0x1000000 % 256 := (Option.some.inj hvm).symm
                rw [this]
                unfold Memory.writeU32
                simp [show effectiveAddr baseAddr off + 3 ≠ effectiveAddr baseAddr off from by omega,
                      show effectiveAddr baseAddr off + 3 ≠ effectiveAddr baseAddr off + 1 from by omega,
                      show effectiveAddr baseAddr off + 3 ≠ effectiveAddr baseAddr off + 2 from by omega]
                omega
              · have h_outer_none :
                    ((PartialState.singletonReg baseReg baseAddr).union
                      ((PartialState.singletonReg valReg vSrc).union
                        (PartialState.singletonMemU32 (effectiveAddr baseAddr off) vSrc))).mem a
                    = none := by
                  rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                  rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                  exact PartialState.singletonMemU32_mem_outside _ _ a (by omega)
                rw [PartialState.union_mem_of_left_none h_outer_none] at hvm
                unfold Memory.writeU32
                show (if a = effectiveAddr baseAddr off then _
                      else if a = effectiveAddr baseAddr off + 1 then _
                      else if a = effectiveAddr baseAddr off + 2 then _
                      else if a = effectiveAddr baseAddr off + 3 then _
                      else s.mem a) = vm
                rw [if_neg ha0, if_neg ha1, if_neg ha2, if_neg ha3]
                apply hcm_mem a vm
                have h_P_none : h_P.mem a = none := by
                  rw [← hu_base_VM]
                  rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                  rw [← hu_val_mem]
                  rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                  exact PartialState.singletonMemU32_mem_outside _ _ a (by omega)
                rw [← hu_PR]
                rw [PartialState.union_mem_of_left_none h_P_none]
                exact hvm
      · intro vp hvp
        have h_outer_pc :
            ((PartialState.singletonReg baseReg baseAddr).union
              ((PartialState.singletonReg valReg vSrc).union
                (PartialState.singletonMemU32 (effectiveAddr baseAddr off) vSrc))).pc = none := by
          rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
          rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
          exact PartialState.singletonMemU32_pc
        rw [PartialState.union_pc_of_left_none h_outer_pc] at hvp
        rw [h_R_no_pc] at hvp
        nomatch hvp
    · refine ⟨?_, ?_, ?_⟩
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
            exact PartialState.singletonMemU32_regs r
      · intro a
        by_cases ha0 : a = effectiveAddr baseAddr off
        · rw [ha0]; right
          exact h_R_no_mem_at _ _ (h_P_mem_i _ _ (h_VM_mem _ _ (PartialState.singletonMemU32_mem_0 _ _)))
        · by_cases ha1 : a = effectiveAddr baseAddr off + 1
          · rw [ha1]; right
            exact h_R_no_mem_at _ _ (h_P_mem_i _ _ (h_VM_mem _ _ (PartialState.singletonMemU32_mem_1 _ _)))
          · by_cases ha2 : a = effectiveAddr baseAddr off + 2
            · rw [ha2]; right
              exact h_R_no_mem_at _ _ (h_P_mem_i _ _ (h_VM_mem _ _ (PartialState.singletonMemU32_mem_2 _ _)))
            · by_cases ha3 : a = effectiveAddr baseAddr off + 3
              · rw [ha3]; right
                exact h_R_no_mem_at _ _ (h_P_mem_i _ _ (h_VM_mem _ _ (PartialState.singletonMemU32_mem_3 _ _)))
              · left
                rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                exact PartialState.singletonMemU32_mem_outside _ _ a (by omega)
      · left
        rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
        rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
        exact PartialState.singletonMemU32_pc
    · refine ⟨fun r => ?_, fun a => ?_, ?_⟩
      · by_cases hrbase : r = baseReg
        · right
          rw [hrbase,
              PartialState.union_regs_of_left_none
                (PartialState.singletonReg_regs_other hne_base_val)]
          exact PartialState.singletonMemU32_regs baseReg
        · left; exact PartialState.singletonReg_regs_other hrbase
      · left; exact PartialState.singletonReg_mem a
      · left; exact PartialState.singletonReg_pc
    · refine ⟨fun r => ?_, fun a => ?_, ?_⟩
      · right; exact PartialState.singletonMemU32_regs r
      · left; exact PartialState.singletonReg_mem a
      · left; exact PartialState.singletonReg_pc

/-! ## Memory stores — dword width

`stxdw` writes 8 consecutive bytes (little-endian decomposition of
the value register `valReg`) to memory at `[baseReg + off]`. The
precondition owns the two registers and an existing `memU64Is` claim
with some `oldV`; the post replaces that with `memU64Is addr vSrc`.

Region requirement: `containsWritable addr 8`.

Note: no `vSrc < 2^64` hypothesis is needed because `writeU64` masks
to `% 256` at each byte slot, and `256 | 2^64`, so `(vSrc % 2^64) / 256^i % 256
= vSrc / 256^i % 256` for `i ∈ 0..7` (omega discharges). -/

/-- `stx .dword baseReg off valReg`: write valReg's 64 bits little-endian
    at `[baseReg + off]`. -/
theorem stxdw_spec
    (baseReg valReg : Reg) (off : Int)
    (baseAddr vSrc oldV : Nat) (pc : Nat) :
    cuTripleWithinMem 1 pc (pc + 1)
      (CodeReq.singleton pc (.stx .dword baseReg off valReg))
      ((baseReg ↦ᵣ baseAddr) ** (valReg ↦ᵣ vSrc) **
        (effectiveAddr baseAddr off ↦U64 oldV))
      ((baseReg ↦ᵣ baseAddr) ** (valReg ↦ᵣ vSrc) **
        (effectiveAddr baseAddr off ↦U64 vSrc))
      (fun rt => rt.containsWritable (effectiveAddr baseAddr off) 8 = true) := by
  intro R hRfree fetch hcr s hPR hpc hex h_region
  obtain ⟨hp, hcompat, h_P, h_R, hd_PR, hu_PR, h_P_sat, h_R_sat⟩ := hPR
  obtain ⟨h_base, h_VM, hd_base_VM, hu_base_VM, h_base_pred, h_VM_sat⟩ := h_P_sat
  obtain ⟨h_val, h_mem, hd_val_mem, hu_val_mem, h_val_pred, h_mem_pred⟩ := h_VM_sat
  rw [h_val_pred] at hu_val_mem hd_val_mem
  rw [h_mem_pred] at hu_val_mem hd_val_mem
  rw [h_base_pred] at hu_base_VM hd_base_VM
  clear h_val_pred h_mem_pred h_base_pred h_val h_mem h_base
  obtain ⟨hcr_regs, hcm_mem, _⟩ := hcompat
  have hne_base_val : baseReg ≠ valReg := by
    obtain ⟨hd_base_VM_regs, _, _⟩ := hd_base_VM
    intro habs
    rcases hd_base_VM_regs baseReg with hl | hr
    · rw [PartialState.singletonReg_regs_self] at hl; nomatch hl
    · rw [← hu_val_mem] at hr
      have : ((PartialState.singletonReg valReg vSrc).union
              (PartialState.singletonMemU64 (effectiveAddr baseAddr off) oldV)).regs baseReg
              = some vSrc := by
        rw [habs]
        exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
      rw [this] at hr; nomatch hr
  have h_VM_regs_val : h_VM.regs valReg = some vSrc := by
    rw [← hu_val_mem]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  -- 8 byte projection facts at h_VM, h_P, hp levels (mirror of ldxdw).
  have h_VM_mem_i (i_addr : Nat) (val : Nat)
      (h_atom : (PartialState.singletonMemU64 (effectiveAddr baseAddr off) oldV).mem i_addr
                = some val) :
      h_VM.mem i_addr = some val := by
    rw [← hu_val_mem,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact h_atom
  have h_P_mem_i (i_addr : Nat) (val : Nat)
      (h_atom : h_VM.mem i_addr = some val) :
      h_P.mem i_addr = some val := by
    rw [← hu_base_VM,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact h_atom
  have hp_mem_i (i_addr : Nat) (val : Nat) (h_atom : h_P.mem i_addr = some val) :
      hp.mem i_addr = some val := by
    rw [← hu_PR]; exact PartialState.union_mem_of_left_some h_atom
  -- Climb to extract baseAddr and vSrc through hp.
  have h_P_regs_base : h_P.regs baseReg = some baseAddr := by
    rw [← hu_base_VM]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_regs_val : h_P.regs valReg = some vSrc := by
    rw [← hu_base_VM]
    rw [PartialState.union_regs_of_left_none
        (PartialState.singletonReg_regs_other hne_base_val.symm)]
    exact h_VM_regs_val
  have hp_regs_base : hp.regs baseReg = some baseAddr := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_base
  have hp_regs_val : hp.regs valReg = some vSrc := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_val
  have hs_regs_base : s.regs.get baseReg = baseAddr :=
    hcr_regs baseReg baseAddr hp_regs_base
  have hs_regs_val : s.regs.get valReg = vSrc := hcr_regs valReg vSrc hp_regs_val
  have hfetch : fetch s.pc = some (.stx .dword baseReg off valReg) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  -- The step writes (vSrc % 2^64) via writeU64.
  have hexec : executeFn fetch s 1 =
      { s with mem := Memory.writeU64 s.mem (effectiveAddr baseAddr off) (vSrc % 2 ^ 64),
               pc := s.pc + 1 } := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch,
        executeFn_zero]
    simp only [step, hs_regs_base, Width.bytes, if_pos h_region,
               Memory.writeByWidth, hs_regs_val]
  obtain ⟨hd_PR_regs, hd_PR_mem, _⟩ := hd_PR
  have h_R_no_base : h_R.regs baseReg = none := by
    rcases hd_PR_regs baseReg with hl | hr
    · rw [h_P_regs_base] at hl; nomatch hl
    · exact hr
  have h_R_no_val : h_R.regs valReg = none := by
    rcases hd_PR_regs valReg with hl | hr
    · rw [h_P_regs_val] at hl; nomatch hl
    · exact hr
  have h_R_no_mem_at (a val : Nat) (h_P_at : h_P.mem a = some val) :
      h_R.mem a = none := by
    rcases hd_PR_mem a with hl | hr
    · rw [h_P_at] at hl; nomatch hl
    · exact hr
  have h_R_no_pc : h_R.pc = none := hRfree _ h_R_sat
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_⟩
  · rw [hexec]; show s.pc + 1 = pc + 1; rw [hpc]
  · rw [hexec]; exact hex
  · rw [hexec]
    refine ⟨_, ?_,
            (PartialState.singletonReg baseReg baseAddr).union
              ((PartialState.singletonReg valReg vSrc).union
                (PartialState.singletonMemU64 (effectiveAddr baseAddr off) vSrc)),
            h_R, ?_, rfl,
            ⟨PartialState.singletonReg baseReg baseAddr,
             (PartialState.singletonReg valReg vSrc).union
              (PartialState.singletonMemU64 (effectiveAddr baseAddr off) vSrc),
             ?_, rfl, rfl,
             ⟨PartialState.singletonReg valReg vSrc,
              PartialState.singletonMemU64 (effectiveAddr baseAddr off) vSrc,
              ?_, rfl, rfl, rfl⟩⟩,
            h_R_sat⟩
    -- (a) Compat.
    · refine ⟨?_, ?_, ?_⟩
      -- regs: unchanged by stxdw (only mem changes).
      · intro r vr hvr
        show s.regs.get r = vr
        by_cases hrbase : r = baseReg
        · rw [hrbase] at hvr
          have h_inner :
              ((PartialState.singletonReg baseReg baseAddr).union
                ((PartialState.singletonReg valReg vSrc).union
                  (PartialState.singletonMemU64 (effectiveAddr baseAddr off) vSrc))).regs baseReg
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
                    (PartialState.singletonMemU64 (effectiveAddr baseAddr off) vSrc))).regs valReg
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
                    (PartialState.singletonMemU64 (effectiveAddr baseAddr off) vSrc))).regs r
                = none := by
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrbase)]
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrval)]
              exact PartialState.singletonMemU64_regs r
            rw [PartialState.union_regs_of_left_none h_outer_h1_none] at hvr
            apply hcr_regs r vr
            have h_P_none : h_P.regs r = none := by
              rw [← hu_base_VM]
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrbase)]
              rw [← hu_val_mem]
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrval)]
              exact PartialState.singletonMemU64_regs r
            rw [← hu_PR]
            rw [PartialState.union_regs_of_left_none h_P_none]
            exact hvr
      -- mem: new state mem = writeU64 ... (vSrc % 2^64).
      -- At addr+i (i ∈ 0..7): writeU64 writes byte_i of (vSrc % 2^64) = byte_i of vSrc.
      -- Outside [addr, addr+8): unchanged.
      · intro a vm hvm
        show (Memory.writeU64 s.mem (effectiveAddr baseAddr off) (vSrc % 2 ^ 64)) a = vm
        -- Helper for each in-range case at offset i:
        by_cases ha0 : a = effectiveAddr baseAddr off
        · rw [ha0] at hvm ⊢
          have h_inner :
              ((PartialState.singletonReg baseReg baseAddr).union
                ((PartialState.singletonReg valReg vSrc).union
                  (PartialState.singletonMemU64 (effectiveAddr baseAddr off) vSrc))).mem
                  (effectiveAddr baseAddr off) = some (vSrc % 256) := by
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            exact PartialState.singletonMemU64_mem_0 _ _
          rw [PartialState.union_mem_of_left_some h_inner] at hvm
          have : vm = vSrc % 256 := (Option.some.inj hvm).symm
          rw [this]
          unfold Memory.writeU64
          simp
        · by_cases ha1 : a = effectiveAddr baseAddr off + 1
          · rw [ha1] at hvm ⊢
            have h_inner :
                ((PartialState.singletonReg baseReg baseAddr).union
                  ((PartialState.singletonReg valReg vSrc).union
                    (PartialState.singletonMemU64 (effectiveAddr baseAddr off) vSrc))).mem
                    (effectiveAddr baseAddr off + 1) = some (vSrc / 0x100 % 256) := by
              rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
              rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
              exact PartialState.singletonMemU64_mem_1 _ _
            rw [PartialState.union_mem_of_left_some h_inner] at hvm
            have : vm = vSrc / 0x100 % 256 := (Option.some.inj hvm).symm
            rw [this]
            unfold Memory.writeU64
            simp [show effectiveAddr baseAddr off + 1 ≠ effectiveAddr baseAddr off from by omega]
            omega
          · by_cases ha2 : a = effectiveAddr baseAddr off + 2
            · rw [ha2] at hvm ⊢
              have h_inner :
                  ((PartialState.singletonReg baseReg baseAddr).union
                    ((PartialState.singletonReg valReg vSrc).union
                      (PartialState.singletonMemU64 (effectiveAddr baseAddr off) vSrc))).mem
                      (effectiveAddr baseAddr off + 2) = some (vSrc / 0x10000 % 256) := by
                rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                exact PartialState.singletonMemU64_mem_2 _ _
              rw [PartialState.union_mem_of_left_some h_inner] at hvm
              have : vm = vSrc / 0x10000 % 256 := (Option.some.inj hvm).symm
              rw [this]
              unfold Memory.writeU64
              simp [show effectiveAddr baseAddr off + 2 ≠ effectiveAddr baseAddr off from by omega,
                    show effectiveAddr baseAddr off + 2 ≠ effectiveAddr baseAddr off + 1 from by omega]
              omega
            · by_cases ha3 : a = effectiveAddr baseAddr off + 3
              · rw [ha3] at hvm ⊢
                have h_inner :
                    ((PartialState.singletonReg baseReg baseAddr).union
                      ((PartialState.singletonReg valReg vSrc).union
                        (PartialState.singletonMemU64 (effectiveAddr baseAddr off) vSrc))).mem
                        (effectiveAddr baseAddr off + 3) = some (vSrc / 0x1000000 % 256) := by
                  rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                  rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                  exact PartialState.singletonMemU64_mem_3 _ _
                rw [PartialState.union_mem_of_left_some h_inner] at hvm
                have : vm = vSrc / 0x1000000 % 256 := (Option.some.inj hvm).symm
                rw [this]
                unfold Memory.writeU64
                simp [show effectiveAddr baseAddr off + 3 ≠ effectiveAddr baseAddr off from by omega,
                      show effectiveAddr baseAddr off + 3 ≠ effectiveAddr baseAddr off + 1 from by omega,
                      show effectiveAddr baseAddr off + 3 ≠ effectiveAddr baseAddr off + 2 from by omega]
                omega
              · by_cases ha4 : a = effectiveAddr baseAddr off + 4
                · rw [ha4] at hvm ⊢
                  have h_inner :
                      ((PartialState.singletonReg baseReg baseAddr).union
                        ((PartialState.singletonReg valReg vSrc).union
                          (PartialState.singletonMemU64 (effectiveAddr baseAddr off) vSrc))).mem
                          (effectiveAddr baseAddr off + 4) = some (vSrc / 0x100000000 % 256) := by
                    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                    exact PartialState.singletonMemU64_mem_4 _ _
                  rw [PartialState.union_mem_of_left_some h_inner] at hvm
                  have : vm = vSrc / 0x100000000 % 256 := (Option.some.inj hvm).symm
                  rw [this]
                  unfold Memory.writeU64
                  simp [show effectiveAddr baseAddr off + 4 ≠ effectiveAddr baseAddr off from by omega,
                        show effectiveAddr baseAddr off + 4 ≠ effectiveAddr baseAddr off + 1 from by omega,
                        show effectiveAddr baseAddr off + 4 ≠ effectiveAddr baseAddr off + 2 from by omega,
                        show effectiveAddr baseAddr off + 4 ≠ effectiveAddr baseAddr off + 3 from by omega]
                  omega
                · by_cases ha5 : a = effectiveAddr baseAddr off + 5
                  · rw [ha5] at hvm ⊢
                    have h_inner :
                        ((PartialState.singletonReg baseReg baseAddr).union
                          ((PartialState.singletonReg valReg vSrc).union
                            (PartialState.singletonMemU64 (effectiveAddr baseAddr off) vSrc))).mem
                            (effectiveAddr baseAddr off + 5) = some (vSrc / 0x10000000000 % 256) := by
                      rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                      rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                      exact PartialState.singletonMemU64_mem_5 _ _
                    rw [PartialState.union_mem_of_left_some h_inner] at hvm
                    have : vm = vSrc / 0x10000000000 % 256 := (Option.some.inj hvm).symm
                    rw [this]
                    unfold Memory.writeU64
                    simp [show effectiveAddr baseAddr off + 5 ≠ effectiveAddr baseAddr off from by omega,
                          show effectiveAddr baseAddr off + 5 ≠ effectiveAddr baseAddr off + 1 from by omega,
                          show effectiveAddr baseAddr off + 5 ≠ effectiveAddr baseAddr off + 2 from by omega,
                          show effectiveAddr baseAddr off + 5 ≠ effectiveAddr baseAddr off + 3 from by omega,
                          show effectiveAddr baseAddr off + 5 ≠ effectiveAddr baseAddr off + 4 from by omega]
                    omega
                  · by_cases ha6 : a = effectiveAddr baseAddr off + 6
                    · rw [ha6] at hvm ⊢
                      have h_inner :
                          ((PartialState.singletonReg baseReg baseAddr).union
                            ((PartialState.singletonReg valReg vSrc).union
                              (PartialState.singletonMemU64 (effectiveAddr baseAddr off) vSrc))).mem
                              (effectiveAddr baseAddr off + 6) = some (vSrc / 0x1000000000000 % 256) := by
                        rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                        rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                        exact PartialState.singletonMemU64_mem_6 _ _
                      rw [PartialState.union_mem_of_left_some h_inner] at hvm
                      have : vm = vSrc / 0x1000000000000 % 256 := (Option.some.inj hvm).symm
                      rw [this]
                      unfold Memory.writeU64
                      simp [show effectiveAddr baseAddr off + 6 ≠ effectiveAddr baseAddr off from by omega,
                            show effectiveAddr baseAddr off + 6 ≠ effectiveAddr baseAddr off + 1 from by omega,
                            show effectiveAddr baseAddr off + 6 ≠ effectiveAddr baseAddr off + 2 from by omega,
                            show effectiveAddr baseAddr off + 6 ≠ effectiveAddr baseAddr off + 3 from by omega,
                            show effectiveAddr baseAddr off + 6 ≠ effectiveAddr baseAddr off + 4 from by omega,
                            show effectiveAddr baseAddr off + 6 ≠ effectiveAddr baseAddr off + 5 from by omega]
                      omega
                    · by_cases ha7 : a = effectiveAddr baseAddr off + 7
                      · rw [ha7] at hvm ⊢
                        have h_inner :
                            ((PartialState.singletonReg baseReg baseAddr).union
                              ((PartialState.singletonReg valReg vSrc).union
                                (PartialState.singletonMemU64 (effectiveAddr baseAddr off) vSrc))).mem
                                (effectiveAddr baseAddr off + 7) = some (vSrc / 0x100000000000000 % 256) := by
                          rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                          rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                          exact PartialState.singletonMemU64_mem_7 _ _
                        rw [PartialState.union_mem_of_left_some h_inner] at hvm
                        have : vm = vSrc / 0x100000000000000 % 256 := (Option.some.inj hvm).symm
                        rw [this]
                        unfold Memory.writeU64
                        simp [show effectiveAddr baseAddr off + 7 ≠ effectiveAddr baseAddr off from by omega,
                              show effectiveAddr baseAddr off + 7 ≠ effectiveAddr baseAddr off + 1 from by omega,
                              show effectiveAddr baseAddr off + 7 ≠ effectiveAddr baseAddr off + 2 from by omega,
                              show effectiveAddr baseAddr off + 7 ≠ effectiveAddr baseAddr off + 3 from by omega,
                              show effectiveAddr baseAddr off + 7 ≠ effectiveAddr baseAddr off + 4 from by omega,
                              show effectiveAddr baseAddr off + 7 ≠ effectiveAddr baseAddr off + 5 from by omega,
                              show effectiveAddr baseAddr off + 7 ≠ effectiveAddr baseAddr off + 6 from by omega]
                        omega
                      · -- a is outside [addr, addr+8).
                        have h_outer_none :
                            ((PartialState.singletonReg baseReg baseAddr).union
                              ((PartialState.singletonReg valReg vSrc).union
                                (PartialState.singletonMemU64 (effectiveAddr baseAddr off) vSrc))).mem a
                            = none := by
                          rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                          rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                          exact PartialState.singletonMemU64_mem_outside _ _ a (by omega)
                        rw [PartialState.union_mem_of_left_none h_outer_none] at hvm
                        unfold Memory.writeU64
                        show (if a = effectiveAddr baseAddr off then _
                              else if a = effectiveAddr baseAddr off + 1 then _
                              else if a = effectiveAddr baseAddr off + 2 then _
                              else if a = effectiveAddr baseAddr off + 3 then _
                              else if a = effectiveAddr baseAddr off + 4 then _
                              else if a = effectiveAddr baseAddr off + 5 then _
                              else if a = effectiveAddr baseAddr off + 6 then _
                              else if a = effectiveAddr baseAddr off + 7 then _
                              else s.mem a) = vm
                        rw [if_neg ha0, if_neg ha1, if_neg ha2, if_neg ha3,
                            if_neg ha4, if_neg ha5, if_neg ha6, if_neg ha7]
                        apply hcm_mem a vm
                        have h_P_none : h_P.mem a = none := by
                          rw [← hu_base_VM]
                          rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                          rw [← hu_val_mem]
                          rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                          exact PartialState.singletonMemU64_mem_outside _ _ a (by omega)
                        rw [← hu_PR]
                        rw [PartialState.union_mem_of_left_none h_P_none]
                        exact hvm
      -- pc:
      · intro vp hvp
        have h_outer_pc :
            ((PartialState.singletonReg baseReg baseAddr).union
              ((PartialState.singletonReg valReg vSrc).union
                (PartialState.singletonMemU64 (effectiveAddr baseAddr off) vSrc))).pc = none := by
          rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
          rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
          exact PartialState.singletonMemU64_pc
        rw [PartialState.union_pc_of_left_none h_outer_pc] at hvp
        rw [h_R_no_pc] at hvp
        nomatch hvp
    -- (b) Outer disjointness.
    · refine ⟨?_, ?_, ?_⟩
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
            exact PartialState.singletonMemU64_regs r
      · intro a
        by_cases ha0 : a = effectiveAddr baseAddr off
        · rw [ha0]; right
          exact h_R_no_mem_at _ _ (h_P_mem_i _ _ (h_VM_mem_i _ _ (PartialState.singletonMemU64_mem_0 _ _)))
        · by_cases ha1 : a = effectiveAddr baseAddr off + 1
          · rw [ha1]; right
            exact h_R_no_mem_at _ _ (h_P_mem_i _ _ (h_VM_mem_i _ _ (PartialState.singletonMemU64_mem_1 _ _)))
          · by_cases ha2 : a = effectiveAddr baseAddr off + 2
            · rw [ha2]; right
              exact h_R_no_mem_at _ _ (h_P_mem_i _ _ (h_VM_mem_i _ _ (PartialState.singletonMemU64_mem_2 _ _)))
            · by_cases ha3 : a = effectiveAddr baseAddr off + 3
              · rw [ha3]; right
                exact h_R_no_mem_at _ _ (h_P_mem_i _ _ (h_VM_mem_i _ _ (PartialState.singletonMemU64_mem_3 _ _)))
              · by_cases ha4 : a = effectiveAddr baseAddr off + 4
                · rw [ha4]; right
                  exact h_R_no_mem_at _ _ (h_P_mem_i _ _ (h_VM_mem_i _ _ (PartialState.singletonMemU64_mem_4 _ _)))
                · by_cases ha5 : a = effectiveAddr baseAddr off + 5
                  · rw [ha5]; right
                    exact h_R_no_mem_at _ _ (h_P_mem_i _ _ (h_VM_mem_i _ _ (PartialState.singletonMemU64_mem_5 _ _)))
                  · by_cases ha6 : a = effectiveAddr baseAddr off + 6
                    · rw [ha6]; right
                      exact h_R_no_mem_at _ _ (h_P_mem_i _ _ (h_VM_mem_i _ _ (PartialState.singletonMemU64_mem_6 _ _)))
                    · by_cases ha7 : a = effectiveAddr baseAddr off + 7
                      · rw [ha7]; right
                        exact h_R_no_mem_at _ _ (h_P_mem_i _ _ (h_VM_mem_i _ _ (PartialState.singletonMemU64_mem_7 _ _)))
                      · left
                        rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                        rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                        exact PartialState.singletonMemU64_mem_outside _ _ a (by omega)
      · left
        rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
        rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
        exact PartialState.singletonMemU64_pc
    -- (c) Inner disjointness: singletonReg baseReg ⊥ (singletonReg valReg ⊎ singletonMemU64).
    · refine ⟨fun r => ?_, fun a => ?_, ?_⟩
      · by_cases hrbase : r = baseReg
        · right
          rw [hrbase,
              PartialState.union_regs_of_left_none
                (PartialState.singletonReg_regs_other hne_base_val)]
          exact PartialState.singletonMemU64_regs baseReg
        · left; exact PartialState.singletonReg_regs_other hrbase
      · left; exact PartialState.singletonReg_mem a
      · left; exact PartialState.singletonReg_pc
    -- (d) Innermost disjointness: singletonReg valReg ⊥ singletonMemU64.
    · refine ⟨fun r => ?_, fun a => ?_, ?_⟩
      · right; exact PartialState.singletonMemU64_regs r
      · left; exact PartialState.singletonReg_mem a
      · left; exact PartialState.singletonReg_pc

/-! ## Control flow: unconditional jump

`ja target` reads no resources, writes only the PC. The triple uses
`emp` as both pre- and postcondition: the spec owns nothing, the
universally-quantified `R` frame carries every actual resource through
unchanged. Entry is `pc`; exit is `target`. -/

/-- `ja target`: unconditional jump. PC moves from `pc` to `target`
    in one step, charging 1 CU. -/
theorem ja_spec (target pc : Nat) :
    cuTripleWithin 1 pc target (CodeReq.singleton pc (.ja target))
      emp emp := by
  intro R hRfree fetch hcr s hPR hpc hex
  obtain ⟨hp, hcompat, h1, hR, hd, hu, hP1, hRsat⟩ := hPR
  -- hP1 : h1 = empty (from emp)
  rw [hP1, PartialState.union_empty_left] at hu
  -- so hp = hR; rewrite for compat reasoning below
  rw [hP1] at hd
  clear hP1 h1
  obtain ⟨hcr_regs, hcm_mem, hcp_pc⟩ := hcompat
  have hfetch : fetch s.pc = some (.ja target) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hexec : executeFn fetch s 1 = { s with pc := target } := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch,
        executeFn_zero]
    simp only [step]
  have hR_no_pc : hR.pc = none := hRfree _ hRsat
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_⟩
  · rw [hexec]
  · rw [hexec]; exact hex
  · rw [hexec]
    refine ⟨PartialState.empty.union hR, ?_,
            PartialState.empty, hR,
            PartialState.Disjoint_empty_left, rfl, rfl, hRsat⟩
    refine ⟨?_, ?_, ?_⟩
    · intro r vr hvr
      rw [PartialState.union_regs_of_left_none (by rfl : PartialState.empty.regs r = none)] at hvr
      show s.regs.get r = vr
      exact hcr_regs r vr (hu ▸ hvr)
    · intro a vm hvm
      rw [PartialState.union_mem_of_left_none (by rfl : PartialState.empty.mem a = none)] at hvm
      show s.mem a = vm
      exact hcm_mem a vm (hu ▸ hvm)
    · intro vp hvp
      rw [PartialState.union_pc_of_left_none (by rfl : PartialState.empty.pc = none)] at hvp
      rw [hR_no_pc] at hvp
      nomatch hvp

end Svm.SBPF
