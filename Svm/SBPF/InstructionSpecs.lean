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

/-! ## Conditional-jump branch-shape specs

The base `jXX_imm_spec` / `jXX_reg_spec` theorems above use the form
`cuTripleWithin 1 pc (if cond then target else pc + 1) ...`. The
`_branch` flavours below lift that into `cuTripleWithinBranch`, which
exposes the two exit PCs separately (suitable for plugging into
`cuTripleWithinBranch_join`). Each is a one-line wrapper applying
`cuTripleWithin.toBranch`. -/

/-- Branch shape of `jeq dst, imm`: exitT = target (taken when
    `vDst = toU64 imm`), exitF = pc + 1 (otherwise). -/
theorem jeq_imm_branch_spec (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat) :
    cuTripleWithinBranch 1 pc target (pc + 1)
      (vDst = toU64 imm)
      (CodeReq.singleton pc (.jeq dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) :=
  (jeq_imm_spec dst imm vDst pc target).toBranch

/-- Branch shape of `jne dst, imm`: exitT = target (taken when
    `vDst ≠ toU64 imm`), exitF = pc + 1 (otherwise). -/
theorem jne_imm_branch_spec (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat) :
    cuTripleWithinBranch 1 pc target (pc + 1)
      (vDst ≠ toU64 imm)
      (CodeReq.singleton pc (.jne dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) :=
  (jne_imm_spec dst imm vDst pc target).toBranch

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
          simp only [Memory.Mem.read_put]
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
                simp only [Memory.Mem.read_put]
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
                        simp only [Memory.Mem.read_put]
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

/-! ## Indirect call: `callx`

`.callx reg` is sBPF's indirect call. Semantically (per `Execute.lean`)
it is a tail-call / panic-path-style jump: PC moves to `regs[reg]`, no
`callStack` push, no register writes. The Hoare triple is the closest
analogue to `ja_spec` but the exit PC is value-dependent (`vReg` rather
than a literal `target`). The caller must already know the value held
in `reg` at entry to compose this spec into a chain — that's typical
for verifying a decompiled program where you've reasoned about `reg`
upstream.

Built by specializing `cuTripleWithin_1reg_cjump` with `cond := True`
and `target := vReg` — the `if True then vReg else pc + 1` reduces to
`vReg`, giving the unconditional value-dependent jump shape we want. -/

/-- `callx reg`: indirect call. PC moves from `pc` to `regs[reg]` in
    one step. The pre/post both retain `reg ↦ᵣ vReg` since `reg` is
    only read. -/
theorem callx_spec (reg : Reg) (vReg pc : Nat) :
    cuTripleWithin 1 pc vReg
      (CodeReq.singleton pc (.callx reg))
      (reg ↦ᵣ vReg) (reg ↦ᵣ vReg) := by
  have h := cuTripleWithin_1reg_cjump reg vReg pc vReg (.callx reg) True
    (fun s hreg => by simp only [step, if_true]; rw [hreg])
  simpa using h

/-! ## Generic syscall helper: writes only `r0`, leaves everything else alone

Many syscalls (logging, return-data set, get-stack-height, etc.) follow a
common shape at the SL level: write some value to `r0`, leave registers /
memory / pc otherwise unchanged. The actual `step` result mutates
`State.log`, `State.returnData`, `State.cuConsumed`, or other observable
side-channel fields — but those are all silent in `PartialState` by design.

This helper captures the pattern. Each concrete syscall spec just supplies
four projection lemmas (`regs`, `mem`, `pc`, `exitCode`) on the step
result, plus the new `r0` value. -/

theorem cuTripleWithin_syscall_writes_r0_only
    (sc : Syscall) (vNew : Nat) (pc : Nat)
    (h_step_regs : ∀ s : State, (step (.call sc) s).regs = s.regs.set .r0 vNew)
    (h_step_mem  : ∀ s : State, (step (.call sc) s).mem = s.mem)
    (h_step_pc   : ∀ s : State, (step (.call sc) s).pc = s.pc + 1)
    (h_step_exit : ∀ s : State, s.exitCode = none →
        (step (.call sc) s).exitCode = none) :
    ∀ r0Old, cuTripleWithin 1 pc (pc + 1)
      (CodeReq.singleton pc (.call sc))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ vNew) := by
  intro r0Old R hRfree fetch hcr s hPR hpc hex
  obtain ⟨hp, hcompat, h1, hR, hd, hu, hreg, hRsat⟩ := hPR
  rw [hreg] at hu hd
  clear hreg h1
  obtain ⟨hcr_regs, hcm_mem, _⟩ := hcompat
  obtain ⟨hd_regs, _, _⟩ := hd
  have hfetch : fetch s.pc = some (.call sc) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hstep_eq : executeFn fetch s 1 = step (.call sc) s := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch,
        executeFn_zero]
  have hexec_regs : (executeFn fetch s 1).regs = s.regs.set .r0 vNew := by
    rw [hstep_eq]; exact h_step_regs s
  have hexec_mem : (executeFn fetch s 1).mem = s.mem := by
    rw [hstep_eq]; exact h_step_mem s
  have hexec_pc : (executeFn fetch s 1).pc = s.pc + 1 := by
    rw [hstep_eq]; exact h_step_pc s
  have hexec_exit : (executeFn fetch s 1).exitCode = none := by
    rw [hstep_eq]; exact h_step_exit s hex
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
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_⟩
  · rw [hexec_pc, hpc]
  · exact hexec_exit
  · refine ⟨(PartialState.singletonReg .r0 vNew).union hR, ?_,
            PartialState.singletonReg .r0 vNew, hR, ?_, rfl, rfl, hRsat⟩
    · refine ⟨?_, ?_, ?_⟩
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
    · refine ⟨?_, ?_, ?_⟩
      · intro r
        by_cases hr : r = .r0
        · rw [hr]; right; exact hR_no_r0
        · left; exact PartialState.singletonReg_regs_other hr
      · intro a; left; exact PartialState.singletonReg_mem a
      · left; exact PartialState.singletonReg_pc

/-! ## Syscall: `sol_log_`

`sol_log_(ptr, len)`: log a byte slice from `[r1..r1+r2)`, set `r0 := 0`.
Memory is read but not written; r1 and r2 are unchanged. `State.log` is
silent in `PartialState` by design. -/

theorem call_sol_log_spec (r0Old : Nat) (pc : Nat) :
    cuTripleWithin 1 pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_log_))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ 0) :=
  cuTripleWithin_syscall_writes_r0_only .sol_log_ 0 pc
    (fun s => by simp [step, execSyscall, Logging.execLog])
    (fun s => by simp [step, execSyscall, Logging.execLog])
    (fun s => by simp [step, execSyscall, Logging.execLog])
    (fun s hex => by simp [step, execSyscall, Logging.execLog]; exact hex)
    r0Old

/-! ## Syscall: `sol_log_pubkey`

`sol_log_pubkey(ptr)`: log 32 bytes from `[r1..r1+32)`, set `r0 := 0`.
Same single-atom shape as `sol_log_`. -/

theorem call_sol_log_pubkey_spec (r0Old : Nat) (pc : Nat) :
    cuTripleWithin 1 pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_log_pubkey))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ 0) :=
  cuTripleWithin_syscall_writes_r0_only .sol_log_pubkey 0 pc
    (fun s => by simp [step, execSyscall, Logging.execLogPubkey])
    (fun s => by simp [step, execSyscall, Logging.execLogPubkey])
    (fun s => by simp [step, execSyscall, Logging.execLogPubkey])
    (fun s hex => by simp [step, execSyscall, Logging.execLogPubkey]; exact hex)
    r0Old

/-! ## Syscall: `sol_get_stack_height`

Returns the current CPI depth in `r0`. Our model fixes this to `1`
(top-level) regardless of `State.callStack` — see `Misc.execGetStackHeight`. -/

theorem call_sol_get_stack_height_spec (r0Old : Nat) (pc : Nat) :
    cuTripleWithin 1 pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_get_stack_height))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ 1) :=
  cuTripleWithin_syscall_writes_r0_only .sol_get_stack_height 1 pc
    (fun s => by simp [step, execSyscall, Misc.execGetStackHeight])
    (fun s => by simp [step, execSyscall, Misc.execGetStackHeight])
    (fun s => by simp [step, execSyscall, Misc.execGetStackHeight])
    (fun s hex => by simp [step, execSyscall, Misc.execGetStackHeight]; exact hex)
    r0Old

/-! ## Syscall: `sol_log_64_`

`sol_log_64_(r1..r5)`: emit hex-formatted register dump. r0 := 0.
Memory unchanged. -/

theorem call_sol_log_64_spec (r0Old : Nat) (pc : Nat) :
    cuTripleWithin 1 pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_log_64_))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ 0) :=
  cuTripleWithin_syscall_writes_r0_only .sol_log_64_ 0 pc
    (fun s => by simp [step, execSyscall, Logging.execLog64])
    (fun s => by simp [step, execSyscall, Logging.execLog64])
    (fun s => by simp [step, execSyscall, Logging.execLog64])
    (fun s hex => by simp [step, execSyscall, Logging.execLog64]; exact hex)
    r0Old

/-! ## Syscall: `sol_log_compute_units_`

Emit "Program consumption: <remaining> units remaining". r0 := 0. -/

theorem call_sol_log_compute_units_spec (r0Old : Nat) (pc : Nat) :
    cuTripleWithin 1 pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_log_compute_units_))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ 0) :=
  cuTripleWithin_syscall_writes_r0_only .sol_log_compute_units_ 0 pc
    (fun s => by simp [step, execSyscall, Logging.execLogComputeUnits])
    (fun s => by simp [step, execSyscall, Logging.execLogComputeUnits])
    (fun s => by simp [step, execSyscall, Logging.execLogComputeUnits])
    (fun s hex => by simp [step, execSyscall, Logging.execLogComputeUnits]; exact hex)
    r0Old

/-! ## Syscall: `sol_log_data`

`sol_log_data(fields_ptr, count)`: read `count` SliceDesc descriptors
from r1, base64-encode each slice they point to, emit joined message.
Memory is read (descriptors + each slice) but not written. r0 := 0. -/

theorem call_sol_log_data_spec (r0Old : Nat) (pc : Nat) :
    cuTripleWithin 1 pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_log_data))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ 0) :=
  cuTripleWithin_syscall_writes_r0_only .sol_log_data 0 pc
    (fun s => by simp [step, execSyscall, Logging.execLogData])
    (fun s => by simp [step, execSyscall, Logging.execLogData])
    (fun s => by simp [step, execSyscall, Logging.execLogData])
    (fun s hex => by simp [step, execSyscall, Logging.execLogData]; exact hex)
    r0Old

/-! ## Syscall: `sol_get_epoch_stake`

Returns 0 in `r0` (stake not modeled). Memory unchanged. -/

theorem call_sol_get_epoch_stake_spec (r0Old : Nat) (pc : Nat) :
    cuTripleWithin 1 pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_get_epoch_stake))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ 0) :=
  cuTripleWithin_syscall_writes_r0_only .sol_get_epoch_stake 0 pc
    (fun s => by simp [step, execSyscall, Sysvar.execEpochStake])
    (fun s => by simp [step, execSyscall, Sysvar.execEpochStake])
    (fun s => by simp [step, execSyscall, Sysvar.execEpochStake])
    (fun s hex => by simp [step, execSyscall, Sysvar.execEpochStake]; exact hex)
    r0Old

/-! ## Syscall: `sol_get_processed_sibling_instruction`

Sibling-instruction tracking is not modeled; the syscall returns 0
in `r0` and otherwise leaves state unchanged. -/

theorem call_sol_get_processed_sibling_instruction_spec
    (r0Old : Nat) (pc : Nat) :
    cuTripleWithin 1 pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_get_processed_sibling_instruction))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ 0) :=
  cuTripleWithin_syscall_writes_r0_only
    .sol_get_processed_sibling_instruction 0 pc
    (fun s => by simp [step, execSyscall, Misc.execProcessedSibling])
    (fun s => by simp [step, execSyscall, Misc.execProcessedSibling])
    (fun s => by simp [step, execSyscall, Misc.execProcessedSibling])
    (fun s hex => by simp [step, execSyscall, Misc.execProcessedSibling]; exact hex)
    r0Old

/-! ## Syscall: `sol_get_sysvar` (generic accessor)

Returns 0 in `r0`; per-sysvar getters (`sol_get_{clock,rent,...}_sysvar`)
are the modeled path that actually populates the output buffer. -/

theorem call_sol_get_sysvar_spec (r0Old : Nat) (pc : Nat) :
    cuTripleWithin 1 pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_get_sysvar))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ 0) :=
  cuTripleWithin_syscall_writes_r0_only .sol_get_sysvar 0 pc
    (fun s => by simp [step, execSyscall, Misc.execGetSysvar])
    (fun s => by simp [step, execSyscall, Misc.execGetSysvar])
    (fun s => by simp [step, execSyscall, Misc.execGetSysvar])
    (fun s hex => by simp [step, execSyscall, Misc.execGetSysvar]; exact hex)
    r0Old

/-! ## Syscall: `.unknown` (unrecognized hash)

For any unrecognized syscall hash, agave aborts; we return 0 in `r0`
so programs that test against opaque hashes don't spuriously fail. -/

theorem call_sol_unknown_spec (hash r0Old : Nat) (pc : Nat) :
    cuTripleWithin 1 pc (pc + 1)
      (CodeReq.singleton pc (.call (.unknown hash)))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ 0) :=
  cuTripleWithin_syscall_writes_r0_only (.unknown hash) 0 pc
    (fun s => by simp [step, execSyscall, Misc.execUnknown])
    (fun s => by simp [step, execSyscall, Misc.execUnknown])
    (fun s => by simp [step, execSyscall, Misc.execUnknown])
    (fun s hex => by simp [step, execSyscall, Misc.execUnknown]; exact hex)
    r0Old

/-! ## Syscall: `sol_set_return_data`

`sol_set_return_data(ptr, len)`: replace `State.returnData` with the
slice `[r1..r1+r2)`, set `r0 := 0`. Memory is read but not written;
`returnData` is silent in `PartialState`. -/

theorem call_sol_set_return_data_spec (r0Old : Nat) (pc : Nat) :
    cuTripleWithin 1 pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_set_return_data))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ 0) :=
  cuTripleWithin_syscall_writes_r0_only .sol_set_return_data 0 pc
    (fun s => by simp [step, execSyscall, ReturnData.execSet])
    (fun s => by simp [step, execSyscall, ReturnData.execSet])
    (fun s => by simp [step, execSyscall, ReturnData.execSet])
    (fun s hex => by simp [step, execSyscall, ReturnData.execSet]; exact hex)
    r0Old

/-! ## Silent-syscall helper: `cuTripleWithin_syscall_silent`

For syscalls whose `step` is a no-op on `PartialState` (regs, mem, pc
all match modulo `pc + 1`). The spec is `emp ↓ emp` — the syscall
advances pc by 1 and consumes fuel/CU but doesn't observably touch
any SL-tracked resource. Composed with the frame rule, it transports
any pc-free assertion through the call. -/

theorem cuTripleWithin_syscall_silent
    (sc : Syscall) (pc : Nat)
    (h_step_regs : ∀ s : State, (step (.call sc) s).regs = s.regs)
    (h_step_mem  : ∀ s : State, (step (.call sc) s).mem = s.mem)
    (h_step_pc   : ∀ s : State, (step (.call sc) s).pc = s.pc + 1)
    (h_step_exit : ∀ s : State, s.exitCode = none →
        (step (.call sc) s).exitCode = none) :
    cuTripleWithin 1 pc (pc + 1)
      (CodeReq.singleton pc (.call sc))
      emp
      emp := by
  intro R hRfree fetch hcr s hPR hpc hex
  obtain ⟨hp, hcompat, hP, hR, _, hu, hPemp, hRsat⟩ := hPR
  obtain ⟨hcr_regs, hcm_mem, hcm_pc⟩ := hcompat
  have hfetch : fetch s.pc = some (.call sc) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hstep_eq : executeFn fetch s 1 = step (.call sc) s := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch,
        executeFn_zero]
  have hexec_regs : (executeFn fetch s 1).regs = s.regs := by
    rw [hstep_eq]; exact h_step_regs s
  have hexec_mem : (executeFn fetch s 1).mem = s.mem := by
    rw [hstep_eq]; exact h_step_mem s
  have hexec_pc : (executeFn fetch s 1).pc = s.pc + 1 := by
    rw [hstep_eq]; exact h_step_pc s
  have hexec_exit : (executeFn fetch s 1).exitCode = none := by
    rw [hstep_eq]; exact h_step_exit s hex
  -- hp = empty.union h_R = h_R; transport hcompat to (executeFn fetch s 1).
  have hP_empty : hP = PartialState.empty := hPemp
  have hp_eq : hp = hR := by
    rw [← hu, hP_empty, PartialState.union_empty_left]
  refine ⟨1, Nat.le_refl 1, ?_, hexec_exit, ?_⟩
  · rw [hexec_pc, hpc]
  · refine ⟨PartialState.empty.union hR, ?_, PartialState.empty, hR,
            ?_, rfl, rfl, hRsat⟩
    · refine ⟨?_, ?_, ?_⟩
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
    · refine ⟨fun r => ?_, fun a => ?_, ?_⟩
      · left; exact PartialState.empty_regs r
      · left; exact PartialState.empty_mem a
      · left; exact PartialState.empty_pc

/-! ## Syscall: `sol_remaining_compute_units`

Opaque in our model: `execRemainingComputeUnits s := s` (no register,
memory, or returnData change). At the SL level, the syscall is silent
— just advances pc by 1 and consumes its base CU charge. -/

theorem call_sol_remaining_compute_units_spec (pc : Nat) :
    cuTripleWithin 1 pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_remaining_compute_units))
      emp
      emp :=
  cuTripleWithin_syscall_silent .sol_remaining_compute_units pc
    (fun s => by simp [step, execSyscall, Misc.execRemainingComputeUnits])
    (fun s => by simp [step, execSyscall, Misc.execRemainingComputeUnits])
    (fun s => by simp [step, execSyscall, Misc.execRemainingComputeUnits])
    (fun s hex => by simp [step, execSyscall, Misc.execRemainingComputeUnits]; exact hex)

/-! ## Syscall: `sol_create_program_address` (n=0 seed case)

The degenerate (zero-seed) form of the PDA syscall: the caller passes
`r2 = 0`, a program-id pointer in `r3`, and an output buffer in `r4`.
The syscall hashes the program-id with the PDA marker, validates the
result is off-curve, and either writes the 32-byte PDA at `*r4`
(setting `r0 := 0`) or signals failure (`r0 := 1`).

This is the first syscall-level Hoare triple in the SL track. The
proof exercises:

- The 6-atom `(P ** R)` destructure (vs. the 3-atom ldx/stx pattern).
- The bytes-level memory atom `↦Bytes32` with `singletonMem32Bytes`
  (vs. the integer-decoded `↦U64` / `↦U32` / `↦U16`).
- `readBytes_eq_of_match` to recover `pidBytes` from the SL ownership.
- A two-arm post conditioned on `Pda.createProgramAddress` returning
  `some` or `none` — case-split via `Option.rec` in the partial-state
  construction. -/

theorem call_create_program_address_n0_spec
    (r0Old r3V r4V : Nat) (pidBytes outOldBytes : ByteArray) (pc : Nat)
    (hpid : pidBytes.size = 32) :
    cuTripleWithin 1 pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_create_program_address))
      ((.r0 ↦ᵣ r0Old) ** (.r2 ↦ᵣ 0) ** (.r3 ↦ᵣ r3V) ** (.r4 ↦ᵣ r4V) **
        (r3V ↦Bytes32 pidBytes) ** (r4V ↦Bytes32 outOldBytes))
      ((.r0 ↦ᵣ (match Pda.createProgramAddress [] pidBytes with
                | some _ => 0 | none => 1)) **
        (.r2 ↦ᵣ 0) ** (.r3 ↦ᵣ r3V) ** (.r4 ↦ᵣ r4V) **
        (r3V ↦Bytes32 pidBytes) **
        (r4V ↦Bytes32 (match Pda.createProgramAddress [] pidBytes with
                       | some bs => bs | none => outOldBytes))) := by
  intro R hRfree fetch hcr s hPR hpc hex
  -- ==== Phase 1: destructure the 6-atom (P ** R) layered split. ====
  obtain ⟨hp, hcompat, h_P, h_R, hd_PR, hu_PR, h_P_sat, h_R_sat⟩ := hPR
  obtain ⟨h_r0, h_T1, hd_r0_T1, hu_r0_T1, h_r0_pred, h_T1_sat⟩ := h_P_sat
  obtain ⟨h_r2, h_T2, hd_r2_T2, hu_r2_T2, h_r2_pred, h_T2_sat⟩ := h_T1_sat
  obtain ⟨h_r3, h_T3, hd_r3_T3, hu_r3_T3, h_r3_pred, h_T3_sat⟩ := h_T2_sat
  obtain ⟨h_r4, h_T4, hd_r4_T4, hu_r4_T4, h_r4_pred, h_T4_sat⟩ := h_T3_sat
  obtain ⟨h_b3, h_b4, hd_b3_b4, hu_b3_b4, h_b3_pred, h_b4_pred⟩ := h_T4_sat
  -- Inline the atom predicates so the disjointness / union facts
  -- become statements about concrete singletons.
  rw [h_r0_pred] at hu_r0_T1 hd_r0_T1
  rw [h_r2_pred] at hu_r2_T2 hd_r2_T2
  rw [h_r3_pred] at hu_r3_T3 hd_r3_T3
  rw [h_r4_pred] at hu_r4_T4 hd_r4_T4
  rw [h_b3_pred] at hu_b3_b4 hd_b3_b4
  rw [h_b4_pred] at hu_b3_b4 hd_b3_b4
  clear h_r0_pred h_r2_pred h_r3_pred h_r4_pred h_b3_pred h_b4_pred
  clear h_r0 h_r2 h_r3 h_r4 h_b3 h_b4
  obtain ⟨hcr_regs, hcm_mem, _⟩ := hcompat
  -- ==== Phase 2: range disjointness between [r3V..r3V+32) and [r4V..r4V+32). ====
  -- Derive the strong "ranges fully disjoint" statement from hd_b3_b4 by
  -- specializing on a concrete in-range address.
  have h_ranges_disjoint : r3V + 32 ≤ r4V ∨ r4V + 32 ≤ r3V := by
    obtain ⟨_, hd_mem, _⟩ := hd_b3_b4
    rcases hd_mem r4V with hl | hr
    · -- r3-atom doesn't own r4V. Either r4V is below r3V or past r3V+32.
      rcases Nat.lt_or_ge r4V r3V with h | h
      · right
        -- r4V < r3V. If r4V + 32 > r3V, then r3V ∈ [r4V..r4V+32), so
        -- the r4-atom owns r3V. Then disjointness at r3V forces the
        -- r3-atom NOT to own r3V — but it does (by mem_at offset 0).
        rcases Nat.lt_or_ge r3V (r4V + 32) with hh | hh
        · -- r3V ∈ [r4V..r4V+32). r4-atom owns r3V; r3-atom also owns r3V (offset 0).
          -- Two owners → disjointness violation at r3V.
          have hr3lt : r3V - r4V < 32 := by omega
          have hat_r4 :
              (PartialState.singletonMem32Bytes r4V outOldBytes).mem r3V
                = some (outOldBytes.get! (r3V - r4V)).toNat := by
            have hkey :=
              PartialState.singletonMem32Bytes_mem_at r4V outOldBytes _ hr3lt
            rwa [show r4V + (r3V - r4V) = r3V from by omega] at hkey
          have hat_r3 :
              (PartialState.singletonMem32Bytes r3V pidBytes).mem r3V
                = some (pidBytes.get! 0).toNat := by
            have := PartialState.singletonMem32Bytes_mem_at r3V pidBytes 0 (by decide)
            simpa using this
          rcases hd_mem r3V with hl' | hr'
          · rw [hat_r3] at hl'; nomatch hl'
          · rw [hat_r4] at hr'; nomatch hr'
        · exact hh
      · -- r4V ≥ r3V. r3-atom doesn't own r4V (by hl), so r4V ≥ r3V + 32.
        rcases Nat.lt_or_ge r4V (r3V + 32) with hh | hh
        · -- r4V ∈ [r3V..r3V+32), so the r3-atom owns r4V — contradicting hl.
          have h_eq : r4V = r3V + (r4V - r3V) := by omega
          have h_lt : r4V - r3V < 32 := by omega
          rw [h_eq,
              PartialState.singletonMem32Bytes_mem_at r3V pidBytes _ h_lt] at hl
          nomatch hl
        · left; exact hh
    · -- r4-atom doesn't own r4V — but it does (mem_at offset 0).
      have := PartialState.singletonMem32Bytes_mem_at r4V outOldBytes 0 (by decide)
      have h0 : (PartialState.singletonMem32Bytes r4V outOldBytes).mem r4V
              = some (outOldBytes.get! 0).toNat := by simpa using this
      rw [h0] at hr; nomatch hr
  -- Two helpful corollaries.
  have h_disj_r3_r4 : ∀ i, i < 32 → r4V + i < r3V ∨ r4V + i ≥ r3V + 32 := by
    intro i _; omega
  have h_disj_r4_r3 : ∀ i, i < 32 → r3V + i < r4V ∨ r3V + i ≥ r4V + 32 := by
    intro i _; omega
  have h_r4_not_in_r3 : ∀ a, r4V ≤ a → a < r4V + 32 → a < r3V ∨ a ≥ r3V + 32 := by
    intro a _ _; omega
  have h_r3_not_in_r4 : ∀ a, r3V ≤ a → a < r3V + 32 → a < r4V ∨ a ≥ r4V + 32 := by
    intro a _ _; omega
  -- ==== Phase 3: climb-up of regs / mem to hp, then to s. ====
  -- Reg climb chains. Each reg sits at a known position in the layered
  -- union; non-matching levels are passed through via `union_regs_of_left_none`
  -- + `singletonReg_regs_other` (different register).
  have h_T4_regs_none (r : Reg) : h_T4.regs r = none := by
    rw [← hu_b3_b4]
    rw [PartialState.union_regs_of_left_none
        (PartialState.singletonMem32Bytes_regs r)]
    exact PartialState.singletonMem32Bytes_regs r
  have h_T3_regs_r4 : h_T3.regs .r4 = some r4V := by
    rw [← hu_r4_T4]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_T3_regs_other (r : Reg) (h : r ≠ .r4) : h_T3.regs r = h_T4.regs r := by
    rw [← hu_r4_T4]
    exact PartialState.union_regs_of_left_none
      (PartialState.singletonReg_regs_other h)
  have h_T2_regs_r3 : h_T2.regs .r3 = some r3V := by
    rw [← hu_r3_T3]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_T2_regs_r4 : h_T2.regs .r4 = some r4V := by
    rw [← hu_r3_T3,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r4 ≠ Reg.r3))]
    exact h_T3_regs_r4
  have h_T1_regs_r2 : h_T1.regs .r2 = some 0 := by
    rw [← hu_r2_T2]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_T1_regs_r3 : h_T1.regs .r3 = some r3V := by
    rw [← hu_r2_T2,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r3 ≠ Reg.r2))]
    exact h_T2_regs_r3
  have h_T1_regs_r4 : h_T1.regs .r4 = some r4V := by
    rw [← hu_r2_T2,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r4 ≠ Reg.r2))]
    exact h_T2_regs_r4
  have h_P_regs_r0 : h_P.regs .r0 = some r0Old := by
    rw [← hu_r0_T1]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_regs_r2 : h_P.regs .r2 = some 0 := by
    rw [← hu_r0_T1,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r2 ≠ Reg.r0))]
    exact h_T1_regs_r2
  have h_P_regs_r3 : h_P.regs .r3 = some r3V := by
    rw [← hu_r0_T1,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r3 ≠ Reg.r0))]
    exact h_T1_regs_r3
  have h_P_regs_r4 : h_P.regs .r4 = some r4V := by
    rw [← hu_r0_T1,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r4 ≠ Reg.r0))]
    exact h_T1_regs_r4
  -- All reg atoms have no mem; the bytes atoms own all 32-byte ranges.
  have h_P_mem_eq_T4 (a : Nat) : h_P.mem a = h_T4.mem a := by
    rw [← hu_r0_T1,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _),
        ← hu_r2_T2,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _),
        ← hu_r3_T3,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _),
        ← hu_r4_T4,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
  have h_T4_mem_r3 (i : Nat) (hi : i < 32) :
      h_T4.mem (r3V + i) = some (pidBytes.get! i).toNat := by
    rw [← hu_b3_b4]
    exact PartialState.union_mem_of_left_some
      (PartialState.singletonMem32Bytes_mem_at r3V pidBytes i hi)
  have h_T4_mem_r4 (i : Nat) (hi : i < 32) :
      h_T4.mem (r4V + i) = some (outOldBytes.get! i).toNat := by
    rw [← hu_b3_b4,
        PartialState.union_mem_of_left_none
          (PartialState.singletonMem32Bytes_mem_outside r3V pidBytes _
            (h_disj_r3_r4 i hi))]
    exact PartialState.singletonMem32Bytes_mem_at r4V outOldBytes i hi
  have h_T4_mem_outside (a : Nat)
      (h3 : a < r3V ∨ a ≥ r3V + 32) (h4 : a < r4V ∨ a ≥ r4V + 32) :
      h_T4.mem a = none := by
    rw [← hu_b3_b4,
        PartialState.union_mem_of_left_none
          (PartialState.singletonMem32Bytes_mem_outside r3V pidBytes _ h3)]
    exact PartialState.singletonMem32Bytes_mem_outside r4V outOldBytes _ h4
  -- hp = h_P ⊎ h_R. Climb one more level.
  have hp_regs_r0 : hp.regs .r0 = some r0Old := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r0
  have hp_regs_r2 : hp.regs .r2 = some 0 := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r2
  have hp_regs_r3 : hp.regs .r3 = some r3V := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r3
  have hp_regs_r4 : hp.regs .r4 = some r4V := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r4
  have hp_mem_r3 (i : Nat) (hi : i < 32) :
      hp.mem (r3V + i) = some (pidBytes.get! i).toNat := by
    rw [← hu_PR]
    exact PartialState.union_mem_of_left_some (h_P_mem_eq_T4 _ ▸ h_T4_mem_r3 i hi)
  -- Translate to s.regs / s.mem via compatibility.
  have hs_regs_r0 : s.regs.get .r0 = r0Old := hcr_regs .r0 r0Old hp_regs_r0
  have hs_regs_r2 : s.regs.get .r2 = 0 := hcr_regs .r2 0 hp_regs_r2
  have hs_regs_r3 : s.regs.get .r3 = r3V := hcr_regs .r3 r3V hp_regs_r3
  have hs_regs_r4 : s.regs.get .r4 = r4V := hcr_regs .r4 r4V hp_regs_r4
  have hs_mem_r3 (i : Nat) (hi : i < 32) :
      s.mem (r3V + i) = (pidBytes.get! i).toNat :=
    hcm_mem _ _ (hp_mem_r3 i hi)
  have hp_mem_r4 (i : Nat) (hi : i < 32) :
      hp.mem (r4V + i) = some (outOldBytes.get! i).toNat := by
    rw [← hu_PR]
    exact PartialState.union_mem_of_left_some (h_P_mem_eq_T4 _ ▸ h_T4_mem_r4 i hi)
  have hs_mem_r4 (i : Nat) (hi : i < 32) :
      s.mem (r4V + i) = (outOldBytes.get! i).toNat :=
    hcm_mem _ _ (hp_mem_r4 i hi)
  -- ==== Phase 4: compute the syscall input + the executeFn equation. ====
  -- Each byte of pidBytes is a UInt8.toNat, hence < 256, hence equal to itself mod 256.
  have h_readBytes : readBytes s.mem r3V 32 = pidBytes := by
    apply readBytes_eq_of_match _ _ _ _ hpid
    intro i hi
    rw [hs_mem_r3 i hi]
    exact Nat.mod_eq_of_lt (by have := (pidBytes.get! i).toNat_lt; omega)
  have hfetch : fetch s.pc = some (.call .sol_create_program_address) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  -- Reduce `Pda.execCreate s` to the target `commitOptional` form. With
  -- `r2 = 0`, `readSeeds` returns []; the 32 mem bytes at r3 decode to
  -- `pidBytes` (h_readBytes); the output address resolves to `r4V`.
  have h_create_eq :
      Pda.execCreate s
        = commitOptional s r4V 32 (Pda.createProgramAddress [] pidBytes) := by
    show commitOptional s (s.regs.get .r4) 32
            (Pda.createProgramAddress
              (Pda.readSeeds s.mem (s.regs.get .r1) (s.regs.get .r2))
              (readBytes s.mem (s.regs.get .r3) 32))
          = commitOptional s r4V 32 (Pda.createProgramAddress [] pidBytes)
    rw [hs_regs_r2, hs_regs_r3, hs_regs_r4, h_readBytes]
    rfl
  -- Reduce one execution step. `step (.call sc) s` unfolds to
  -- `{ execSyscall sc s with pc := pc+1, cuConsumed := … }`; for
  -- `.sol_create_program_address`, `execSyscall` is `Pda.execCreate`.
  -- The step's full output as a single State value, used both for the
  -- `executeFn` equation and downstream compat reasoning.
  let s' : State := commitOptional s r4V 32 (Pda.createProgramAddress [] pidBytes)
  have hs'_def : s' = commitOptional s r4V 32 (Pda.createProgramAddress [] pidBytes) := rfl
  have hexec : executeFn fetch s 1 =
      { s' with pc := s.pc + 1
                cuConsumed := s'.cuConsumed + syscallCu .sol_create_program_address s } := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch, executeFn_zero]
    show ({ Pda.execCreate s with
            pc := s.pc + 1
            cuConsumed := (Pda.execCreate s).cuConsumed
                          + syscallCu .sol_create_program_address s }) = _
    rw [h_create_eq]
  -- ==== Phase 5: facts about the post-state from `commitOptional`. ====
  -- Convenience properties of `commitOptional s r4V 32 cpa` extracted by
  -- a case split on `cpa`.
  -- (a) regs.r0 equals the post value (0 on success, 1 on failure).
  have h_post_r0 :
      (commitOptional s r4V 32 (Pda.createProgramAddress [] pidBytes)).regs.get .r0
        = (match Pda.createProgramAddress [] pidBytes with | some _ => 0 | none => 1) := by
    cases Pda.createProgramAddress [] pidBytes <;> rfl
  -- (b) regs.get on any other reg is unchanged.
  have h_post_regs_other (r : Reg) (hr : r ≠ .r0) :
      (commitOptional s r4V 32 (Pda.createProgramAddress [] pidBytes)).regs.get r
        = s.regs.get r := by
    cases Pda.createProgramAddress [] pidBytes with
    | some _ =>
      show (s.regs.set .r0 0).get r = _
      exact RegFile.get_set_diff _ _ _ _ hr
    | none =>
      show (s.regs.set .r0 1).get r = _
      exact RegFile.get_set_diff _ _ _ _ hr
  -- (c) mem at an address inside [r4..r4+32) equals the appropriate byte
  --     of the post-bytes (newPda on success, outOldBytes on failure).
  have h_post_mem_r4 (i : Nat) (hi : i < 32) :
      (commitOptional s r4V 32 (Pda.createProgramAddress [] pidBytes)).mem (r4V + i)
        = ((match Pda.createProgramAddress [] pidBytes with
            | some bs => bs | none => outOldBytes).get! i).toNat := by
    cases h_cpa : Pda.createProgramAddress [] pidBytes with
    | some bs =>
      show (writeBytes s.mem r4V 32 bs).read (r4V + i) = _
      exact writeBytes_read_inside _ _ _ _ _ hi
    | none =>
      show s.mem (r4V + i) = _
      exact hs_mem_r4 i hi
  -- (d) mem at an address outside [r4..r4+32) is unchanged.
  have h_post_mem_outside (a : Nat) (h : a < r4V ∨ a ≥ r4V + 32) :
      (commitOptional s r4V 32 (Pda.createProgramAddress [] pidBytes)).mem a = s.mem a := by
    cases Pda.createProgramAddress [] pidBytes with
    | some bs =>
      show (writeBytes s.mem r4V 32 bs).read a = _
      exact writeBytes_read_outside _ _ _ _ _ h
    | none => rfl
  -- ==== Phase 6: assemble the witness for (Q ** R).holdsFor (executeFn fetch s 1). ====
  -- New partial state: same 6-atom structure as P, with two atoms updated.
  let h_r0_new : PartialState := PartialState.singletonReg .r0
    (match Pda.createProgramAddress [] pidBytes with | some _ => 0 | none => 1)
  let h_b4_new : PartialState := PartialState.singletonMem32Bytes r4V
    (match Pda.createProgramAddress [] pidBytes with | some bs => bs | none => outOldBytes)
  -- Re-introduce the singleton atoms for the unchanged registers / bytes.
  let h_r2_new : PartialState := PartialState.singletonReg .r2 0
  let h_r3_new : PartialState := PartialState.singletonReg .r3 r3V
  let h_r4_new : PartialState := PartialState.singletonReg .r4 r4V
  let h_b3_new : PartialState := PartialState.singletonMem32Bytes r3V pidBytes
  let h_T4_new : PartialState := h_b3_new.union h_b4_new
  let h_T3_new : PartialState := h_r4_new.union h_T4_new
  let h_T2_new : PartialState := h_r3_new.union h_T3_new
  let h_T1_new : PartialState := h_r2_new.union h_T2_new
  let h_P_new : PartialState := h_r0_new.union h_T1_new
  -- commitOptional preserves exitCode.
  have h_post_exitCode :
      (commitOptional s r4V 32 (Pda.createProgramAddress [] pidBytes)).exitCode = s.exitCode := by
    cases Pda.createProgramAddress [] pidBytes <;> rfl
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_⟩
  · rw [hexec]; show s.pc + 1 = pc + 1; rw [hpc]
  · rw [hexec]; show _ = none; rw [h_post_exitCode]; exact hex
  · rw [hexec]
    -- ===== h_R cannot own any of P's affected slots. =====
    obtain ⟨hd_PR_regs, hd_PR_mem, hd_PR_pc⟩ := hd_PR
    have h_R_no_r0 : h_R.regs .r0 = none := by
      rcases hd_PR_regs .r0 with hl | hr
      · rw [h_P_regs_r0] at hl; nomatch hl
      · exact hr
    have h_R_no_r2 : h_R.regs .r2 = none := by
      rcases hd_PR_regs .r2 with hl | hr
      · rw [h_P_regs_r2] at hl; nomatch hl
      · exact hr
    have h_R_no_r3 : h_R.regs .r3 = none := by
      rcases hd_PR_regs .r3 with hl | hr
      · rw [h_P_regs_r3] at hl; nomatch hl
      · exact hr
    have h_R_no_r4 : h_R.regs .r4 = none := by
      rcases hd_PR_regs .r4 with hl | hr
      · rw [h_P_regs_r4] at hl; nomatch hl
      · exact hr
    have h_R_no_pc : h_R.pc = none := hRfree _ h_R_sat
    -- For mem in either bytes region: h_P owns; h_R doesn't.
    have h_R_no_mem_r3 (i : Nat) (hi : i < 32) : h_R.mem (r3V + i) = none := by
      rcases hd_PR_mem (r3V + i) with hl | hr
      · rw [show h_P.mem (r3V + i) = some (pidBytes.get! i).toNat from
            h_P_mem_eq_T4 _ ▸ h_T4_mem_r3 i hi] at hl
        nomatch hl
      · exact hr
    have h_R_no_mem_r4 (i : Nat) (hi : i < 32) : h_R.mem (r4V + i) = none := by
      rcases hd_PR_mem (r4V + i) with hl | hr
      · rw [show h_P.mem (r4V + i) = some (outOldBytes.get! i).toNat from
            h_P_mem_eq_T4 _ ▸ h_T4_mem_r4 i hi] at hl
        nomatch hl
      · exact hr
    -- ===== Inner disjointness of h_P_new (bottom-up by atom layer). =====
    -- (i) bytes atom at r3V is disjoint from bytes atom at r4V — uses h_ranges_disjoint.
    have hd_b3b4_new : h_b3_new.Disjoint h_b4_new := by
      refine ⟨fun r => ?_, fun a => ?_, ?_⟩
      · left; exact PartialState.singletonMem32Bytes_regs r
      · rcases Nat.lt_or_ge a r3V with h1 | h1
        · left
          exact PartialState.singletonMem32Bytes_mem_outside r3V pidBytes a (Or.inl h1)
        · rcases Nat.lt_or_ge a (r3V + 32) with h2 | h2
          · right
            apply PartialState.singletonMem32Bytes_mem_outside r4V _ a
            rcases h_ranges_disjoint with hl | hr
            · left; omega
            · right; omega
          · left
            exact PartialState.singletonMem32Bytes_mem_outside r3V pidBytes a (Or.inr h2)
      · left; exact PartialState.singletonMem32Bytes_pc
    -- (ii) singletonReg .r4 ⊥ T4 (h_b3_new ⊎ h_b4_new): regs differ; bytes have no regs;
    --      singletonReg has no mem; no pc.
    have hd_r4_T4_new : h_r4_new.Disjoint h_T4_new := by
      refine ⟨fun r => ?_, fun a => ?_, ?_⟩
      · right
        show h_T4_new.regs r = none
        show ((PartialState.singletonMem32Bytes r3V pidBytes).union _).regs r = none
        rw [PartialState.union_regs_of_left_none (PartialState.singletonMem32Bytes_regs r)]
        exact PartialState.singletonMem32Bytes_regs r
      · left; exact PartialState.singletonReg_mem a
      · left; exact PartialState.singletonReg_pc
    have hd_r3_T3_new : h_r3_new.Disjoint h_T3_new := by
      refine ⟨fun r => ?_, fun a => ?_, ?_⟩
      · by_cases hreq : r = .r3
        · right
          show h_T3_new.regs r = none
          show ((PartialState.singletonReg .r4 r4V).union h_T4_new).regs r = none
          rw [PartialState.union_regs_of_left_none
              (PartialState.singletonReg_regs_other (hreq ▸ (by decide : Reg.r3 ≠ Reg.r4)))]
          show h_T4_new.regs r = none
          show ((PartialState.singletonMem32Bytes r3V pidBytes).union _).regs r = none
          rw [PartialState.union_regs_of_left_none (PartialState.singletonMem32Bytes_regs r)]
          exact PartialState.singletonMem32Bytes_regs r
        · left; exact PartialState.singletonReg_regs_other hreq
      · left; exact PartialState.singletonReg_mem a
      · left; exact PartialState.singletonReg_pc
    have hd_r2_T2_new : h_r2_new.Disjoint h_T2_new := by
      refine ⟨fun r => ?_, fun a => ?_, ?_⟩
      · by_cases hreq : r = .r2
        · right
          show h_T2_new.regs r = none
          show ((PartialState.singletonReg .r3 r3V).union h_T3_new).regs r = none
          rw [PartialState.union_regs_of_left_none
              (PartialState.singletonReg_regs_other (hreq ▸ (by decide : Reg.r2 ≠ Reg.r3)))]
          show h_T3_new.regs r = none
          show ((PartialState.singletonReg .r4 r4V).union h_T4_new).regs r = none
          rw [PartialState.union_regs_of_left_none
              (PartialState.singletonReg_regs_other (hreq ▸ (by decide : Reg.r2 ≠ Reg.r4)))]
          show h_T4_new.regs r = none
          show ((PartialState.singletonMem32Bytes r3V pidBytes).union _).regs r = none
          rw [PartialState.union_regs_of_left_none (PartialState.singletonMem32Bytes_regs r)]
          exact PartialState.singletonMem32Bytes_regs r
        · left; exact PartialState.singletonReg_regs_other hreq
      · left; exact PartialState.singletonReg_mem a
      · left; exact PartialState.singletonReg_pc
    have hd_r0_T1_new : h_r0_new.Disjoint h_T1_new := by
      refine ⟨fun r => ?_, fun a => ?_, ?_⟩
      · by_cases hreq : r = .r0
        · right
          show h_T1_new.regs r = none
          show ((PartialState.singletonReg .r2 0).union h_T2_new).regs r = none
          rw [PartialState.union_regs_of_left_none
              (PartialState.singletonReg_regs_other (hreq ▸ (by decide : Reg.r0 ≠ Reg.r2)))]
          show h_T2_new.regs r = none
          show ((PartialState.singletonReg .r3 r3V).union h_T3_new).regs r = none
          rw [PartialState.union_regs_of_left_none
              (PartialState.singletonReg_regs_other (hreq ▸ (by decide : Reg.r0 ≠ Reg.r3)))]
          show h_T3_new.regs r = none
          show ((PartialState.singletonReg .r4 r4V).union h_T4_new).regs r = none
          rw [PartialState.union_regs_of_left_none
              (PartialState.singletonReg_regs_other (hreq ▸ (by decide : Reg.r0 ≠ Reg.r4)))]
          show h_T4_new.regs r = none
          show ((PartialState.singletonMem32Bytes r3V pidBytes).union _).regs r = none
          rw [PartialState.union_regs_of_left_none (PartialState.singletonMem32Bytes_regs r)]
          exact PartialState.singletonMem32Bytes_regs r
        · left; exact PartialState.singletonReg_regs_other hreq
      · left; exact PartialState.singletonReg_mem a
      · left; exact PartialState.singletonReg_pc
    -- ===== Mem-level "outside both regions" predicate for h_P_new. =====
    -- A handy lemma: h_P_new.mem a = none whenever a is outside both
    -- 32-byte regions.
    have h_P_new_mem_outside (a : Nat)
        (h3 : a < r3V ∨ a ≥ r3V + 32) (h4 : a < r4V ∨ a ≥ r4V + 32) :
        h_P_new.mem a = none := by
      show ((PartialState.singletonReg .r0 _).union h_T1_new).mem a = none
      rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
      show ((PartialState.singletonReg .r2 0).union h_T2_new).mem a = none
      rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
      show ((PartialState.singletonReg .r3 r3V).union h_T3_new).mem a = none
      rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
      show ((PartialState.singletonReg .r4 r4V).union h_T4_new).mem a = none
      rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
      show ((PartialState.singletonMem32Bytes r3V pidBytes).union h_b4_new).mem a = none
      rw [PartialState.union_mem_of_left_none
          (PartialState.singletonMem32Bytes_mem_outside r3V pidBytes a h3)]
      exact PartialState.singletonMem32Bytes_mem_outside r4V _ a h4
    -- h_P_new owns each reg only at its assigned slot.
    have h_P_new_regs_other (r : Reg)
        (h0 : r ≠ .r0) (h2 : r ≠ .r2) (h3 : r ≠ .r3) (h4 : r ≠ .r4) :
        h_P_new.regs r = none := by
      show ((PartialState.singletonReg .r0 _).union h_T1_new).regs r = none
      rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other h0)]
      show ((PartialState.singletonReg .r2 0).union h_T2_new).regs r = none
      rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other h2)]
      show ((PartialState.singletonReg .r3 r3V).union h_T3_new).regs r = none
      rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other h3)]
      show ((PartialState.singletonReg .r4 r4V).union h_T4_new).regs r = none
      rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other h4)]
      show ((PartialState.singletonMem32Bytes r3V pidBytes).union h_b4_new).regs r = none
      rw [PartialState.union_regs_of_left_none (PartialState.singletonMem32Bytes_regs r)]
      exact PartialState.singletonMem32Bytes_regs r
    -- h_P_new.regs at each owned reg.
    have h_P_new_regs_r0 :
        h_P_new.regs .r0 = some
          (match Pda.createProgramAddress [] pidBytes with | some _ => 0 | none => 1) :=
      PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
    have h_P_new_regs_r2 : h_P_new.regs .r2 = some 0 := by
      show ((PartialState.singletonReg .r0 _).union h_T1_new).regs .r2 = some 0
      rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r2 ≠ Reg.r0))]
      exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
    have h_P_new_regs_r3 : h_P_new.regs .r3 = some r3V := by
      show ((PartialState.singletonReg .r0 _).union h_T1_new).regs .r3 = some r3V
      rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r3 ≠ Reg.r0))]
      show ((PartialState.singletonReg .r2 0).union h_T2_new).regs .r3 = some r3V
      rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r3 ≠ Reg.r2))]
      exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
    have h_P_new_regs_r4 : h_P_new.regs .r4 = some r4V := by
      show ((PartialState.singletonReg .r0 _).union h_T1_new).regs .r4 = some r4V
      rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r4 ≠ Reg.r0))]
      show ((PartialState.singletonReg .r2 0).union h_T2_new).regs .r4 = some r4V
      rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r4 ≠ Reg.r2))]
      show ((PartialState.singletonReg .r3 r3V).union h_T3_new).regs .r4 = some r4V
      rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r4 ≠ Reg.r3))]
      exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
    -- h_P_new owns mem in [r3..r3+32) and [r4..r4+32).
    have h_P_new_mem_r3 (i : Nat) (hi : i < 32) :
        h_P_new.mem (r3V + i) = some (pidBytes.get! i).toNat := by
      show ((PartialState.singletonReg .r0 _).union h_T1_new).mem (r3V + i) = _
      rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
      show ((PartialState.singletonReg .r2 0).union h_T2_new).mem (r3V + i) = _
      rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
      show ((PartialState.singletonReg .r3 r3V).union h_T3_new).mem (r3V + i) = _
      rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
      show ((PartialState.singletonReg .r4 r4V).union h_T4_new).mem (r3V + i) = _
      rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
      show ((PartialState.singletonMem32Bytes r3V pidBytes).union h_b4_new).mem (r3V + i) = _
      exact PartialState.union_mem_of_left_some
        (PartialState.singletonMem32Bytes_mem_at r3V pidBytes i hi)
    have h_P_new_mem_r4 (i : Nat) (hi : i < 32) :
        h_P_new.mem (r4V + i) = some
          ((match Pda.createProgramAddress [] pidBytes with
            | some bs => bs | none => outOldBytes).get! i).toNat := by
      show ((PartialState.singletonReg .r0 _).union h_T1_new).mem (r4V + i) = _
      rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
      show ((PartialState.singletonReg .r2 0).union h_T2_new).mem (r4V + i) = _
      rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
      show ((PartialState.singletonReg .r3 r3V).union h_T3_new).mem (r4V + i) = _
      rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
      show ((PartialState.singletonReg .r4 r4V).union h_T4_new).mem (r4V + i) = _
      rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
      show ((PartialState.singletonMem32Bytes r3V pidBytes).union h_b4_new).mem (r4V + i) = _
      rw [PartialState.union_mem_of_left_none
          (PartialState.singletonMem32Bytes_mem_outside r3V pidBytes _
            (h_disj_r3_r4 i hi))]
      exact PartialState.singletonMem32Bytes_mem_at r4V _ i hi
    -- h_P_new owns no pc.
    have h_P_new_pc : h_P_new.pc = none := by
      show ((PartialState.singletonReg .r0 _).union h_T1_new).pc = none
      rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
      show ((PartialState.singletonReg .r2 0).union h_T2_new).pc = none
      rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
      show ((PartialState.singletonReg .r3 r3V).union h_T3_new).pc = none
      rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
      show ((PartialState.singletonReg .r4 r4V).union h_T4_new).pc = none
      rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
      show ((PartialState.singletonMem32Bytes r3V pidBytes).union h_b4_new).pc = none
      rw [PartialState.union_pc_of_left_none PartialState.singletonMem32Bytes_pc]
      exact PartialState.singletonMem32Bytes_pc
    -- ===== Outer disjointness: h_P_new ⊥ h_R. =====
    have hd_PnewR : h_P_new.Disjoint h_R := by
      refine ⟨fun r => ?_, fun a => ?_, ?_⟩
      · by_cases h0 : r = .r0
        · right; rw [h0]; exact h_R_no_r0
        by_cases h2 : r = .r2
        · right; rw [h2]; exact h_R_no_r2
        by_cases h3 : r = .r3
        · right; rw [h3]; exact h_R_no_r3
        by_cases h4 : r = .r4
        · right; rw [h4]; exact h_R_no_r4
        · left; exact h_P_new_regs_other r h0 h2 h3 h4
      · by_cases ha3 : r3V ≤ a ∧ a < r3V + 32
        · right
          obtain ⟨h1, h2⟩ := ha3
          have h_eq : a = r3V + (a - r3V) := by omega
          have h_lt : a - r3V < 32 := by omega
          rw [h_eq]
          exact h_R_no_mem_r3 _ h_lt
        · by_cases ha4 : r4V ≤ a ∧ a < r4V + 32
          · right
            obtain ⟨h1, h2⟩ := ha4
            have h_eq : a = r4V + (a - r4V) := by omega
            have h_lt : a - r4V < 32 := by omega
            rw [h_eq]
            exact h_R_no_mem_r4 _ h_lt
          · left
            apply h_P_new_mem_outside
            · rcases Nat.lt_or_ge a r3V with h | h
              · left; exact h
              · rcases Nat.lt_or_ge a (r3V + 32) with h' | h'
                · exact absurd ⟨h, h'⟩ ha3
                · right; exact h'
            · rcases Nat.lt_or_ge a r4V with h | h
              · left; exact h
              · rcases Nat.lt_or_ge a (r4V + 32) with h' | h'
                · exact absurd ⟨h, h'⟩ ha4
                · right; exact h'
      · left; exact h_P_new_pc
    -- ===== Provide the (Q ** R).holdsFor witness. =====
    refine ⟨h_P_new.union h_R, ?_, h_P_new, h_R, hd_PnewR, rfl,
            ?_, h_R_sat⟩
    -- (a) Compatibility of `h_P_new ⊎ h_R` with the post state.
    · refine ⟨?_, ?_, ?_⟩
      -- regs
      · intro r vr hvr
        show (commitOptional s r4V 32 (Pda.createProgramAddress [] pidBytes)).regs.get r = vr
        by_cases h0 : r = .r0
        · rw [h0] at hvr
          rw [PartialState.union_regs_of_left_some h_P_new_regs_r0] at hvr
          rw [h0, h_post_r0]
          exact Option.some.inj hvr
        by_cases h2 : r = .r2
        · rw [h2] at hvr
          rw [PartialState.union_regs_of_left_some h_P_new_regs_r2] at hvr
          rw [h2, h_post_regs_other .r2 (by decide), hs_regs_r2]
          exact Option.some.inj hvr
        by_cases h3 : r = .r3
        · rw [h3] at hvr
          rw [PartialState.union_regs_of_left_some h_P_new_regs_r3] at hvr
          rw [h3, h_post_regs_other .r3 (by decide), hs_regs_r3]
          exact Option.some.inj hvr
        by_cases h4 : r = .r4
        · rw [h4] at hvr
          rw [PartialState.union_regs_of_left_some h_P_new_regs_r4] at hvr
          rw [h4, h_post_regs_other .r4 (by decide), hs_regs_r4]
          exact Option.some.inj hvr
        · rw [PartialState.union_regs_of_left_none
              (h_P_new_regs_other r h0 h2 h3 h4)] at hvr
          rw [h_post_regs_other r h0]
          have h_P_none : h_P.regs r = none := by
            rcases hd_PR_regs r with hl | hr
            · exact hl
            · rw [hr] at hvr; nomatch hvr
          have : hp.regs r = some vr := by
            rw [← hu_PR]
            rw [PartialState.union_regs_of_left_none h_P_none]
            exact hvr
          exact hcr_regs r vr this
      -- mem
      · intro a vm hvm
        show (commitOptional s r4V 32 (Pda.createProgramAddress [] pidBytes)).mem a = vm
        by_cases ha3 : r3V ≤ a ∧ a < r3V + 32
        · obtain ⟨h1, h2⟩ := ha3
          have h_eq : a = r3V + (a - r3V) := by omega
          have h_lt : a - r3V < 32 := by omega
          rw [h_eq] at hvm ⊢
          rw [PartialState.union_mem_of_left_some (h_P_new_mem_r3 _ h_lt)] at hvm
          -- commit doesn't change mem outside [r4..r4+32); r3V + (a-r3V) ∉ [r4..r4+32).
          rw [h_post_mem_outside _ (h_r3_not_in_r4 _ (Nat.le_add_right _ _) (by omega))]
          rw [hs_mem_r3 _ h_lt]
          exact Option.some.inj hvm
        · by_cases ha4 : r4V ≤ a ∧ a < r4V + 32
          · obtain ⟨h1, h2⟩ := ha4
            have h_eq : a = r4V + (a - r4V) := by omega
            have h_lt : a - r4V < 32 := by omega
            rw [h_eq] at hvm ⊢
            rw [PartialState.union_mem_of_left_some (h_P_new_mem_r4 _ h_lt)] at hvm
            rw [h_post_mem_r4 _ h_lt]
            exact Option.some.inj hvm
          · -- Outside both regions.
            have h3_out : a < r3V ∨ a ≥ r3V + 32 := by
              rcases Nat.lt_or_ge a r3V with h | h
              · left; exact h
              · rcases Nat.lt_or_ge a (r3V + 32) with h' | h'
                · exact absurd ⟨h, h'⟩ ha3
                · right; exact h'
            have h4_out : a < r4V ∨ a ≥ r4V + 32 := by
              rcases Nat.lt_or_ge a r4V with h | h
              · left; exact h
              · rcases Nat.lt_or_ge a (r4V + 32) with h' | h'
                · exact absurd ⟨h, h'⟩ ha4
                · right; exact h'
            rw [PartialState.union_mem_of_left_none
                (h_P_new_mem_outside a h3_out h4_out)] at hvm
            rw [h_post_mem_outside a h4_out]
            -- Need s.mem a = vm. From hvm : h_R.mem a = some vm, and h_P.mem a = none too.
            have h_P_none : h_P.mem a = none := by
              rcases hd_PR_mem a with hl | hr
              · exact hl
              · rw [hr] at hvm; nomatch hvm
            have : hp.mem a = some vm := by
              rw [← hu_PR]
              rw [PartialState.union_mem_of_left_none h_P_none]
              exact hvm
            exact hcm_mem a vm this
      -- pc
      · intro vp hvp
        rw [PartialState.union_pc_of_left_none h_P_new_pc] at hvp
        rw [h_R_no_pc] at hvp
        nomatch hvp
    -- (b) Q h_P_new — provide the nested witnesses.
    · refine ⟨h_r0_new, h_T1_new, hd_r0_T1_new, rfl, rfl,
              h_r2_new, h_T2_new, hd_r2_T2_new, rfl, rfl,
              h_r3_new, h_T3_new, hd_r3_T3_new, rfl, rfl,
              h_r4_new, h_T4_new, hd_r4_T4_new, rfl, rfl,
              h_b3_new, h_b4_new, hd_b3b4_new, rfl, rfl, rfl⟩

/-! ## Syscall: `sol_create_program_address` (n=1 seed case)

One-seed form of the PDA syscall. The caller passes:
- `r1` = pointer to a length-1 `VmSlice` descriptor array
- `r2 = 1`
- `r3` = pointer to the 32-byte program-id
- `r4` = pointer to the 32-byte output buffer

The descriptor at `*r1` is two `u64`s: `descriptor.ptr` (pointer to
seed bytes) and `descriptor.len` (seed length).

Pre-state ownership (10 atoms):
- 5 register atoms: `r0`, `r1`, `r2 (= 1)`, `r3`, `r4`
- 2 ↦U64 atoms for the descriptor (at `r1V` and `r1V + 8`)
- 1 ↦Bytes atom for the seed bytes (at `seedPtr`, length `seedBytes.size`)
- 2 ↦Bytes32 atoms for `pidBytes` (at `r3V`) and `outOldBytes` (at `r4V`)

Post: `r0` and `r4V`'s bytes follow `Pda.createProgramAddress
[seedBytes] pidBytes` (success: r0 := 0 + pda written; failure:
r0 := 1 + output unchanged). -/

theorem call_create_program_address_n1_spec
    (r0Old r1V r3V r4V seedPtr : Nat)
    (seedBytes pidBytes outOldBytes : ByteArray) (pc : Nat)
    (hpid : pidBytes.size = 32)
    (hseed_lt : seedPtr < 2 ^ 64)
    (hslen_lt : seedBytes.size < 2 ^ 64) :
    cuTripleWithin 1 pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_create_program_address))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ 1) **
        (.r3 ↦ᵣ r3V) ** (.r4 ↦ᵣ r4V) **
        (r1V ↦U64 seedPtr) ** (r1V + 8 ↦U64 seedBytes.size) **
        (seedPtr ↦Bytes seedBytes) **
        (r3V ↦Bytes32 pidBytes) ** (r4V ↦Bytes32 outOldBytes))
      ((.r0 ↦ᵣ (match Pda.createProgramAddress [seedBytes] pidBytes with
                | some _ => 0 | none => 1)) **
        (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ 1) **
        (.r3 ↦ᵣ r3V) ** (.r4 ↦ᵣ r4V) **
        (r1V ↦U64 seedPtr) ** (r1V + 8 ↦U64 seedBytes.size) **
        (seedPtr ↦Bytes seedBytes) **
        (r3V ↦Bytes32 pidBytes) **
        (r4V ↦Bytes32 (match Pda.createProgramAddress [seedBytes] pidBytes with
                       | some bs => bs | none => outOldBytes))) := by
  intro R hRfree fetch hcr s hPR hpc hex
  -- ==== Phase 1: destructure the 10-atom (P ** R) layered split. ====
  obtain ⟨hp, hcompat, h_P, h_R, hd_PR, hu_PR, h_P_sat, h_R_sat⟩ := hPR
  obtain ⟨h_a0, h_T1, hd_a0_T1, hu_a0_T1, h_a0_pred, h_T1_sat⟩ := h_P_sat
  obtain ⟨h_a1, h_T2, hd_a1_T2, hu_a1_T2, h_a1_pred, h_T2_sat⟩ := h_T1_sat
  obtain ⟨h_a2, h_T3, hd_a2_T3, hu_a2_T3, h_a2_pred, h_T3_sat⟩ := h_T2_sat
  obtain ⟨h_a3, h_T4, hd_a3_T4, hu_a3_T4, h_a3_pred, h_T4_sat⟩ := h_T3_sat
  obtain ⟨h_a4, h_T5, hd_a4_T5, hu_a4_T5, h_a4_pred, h_T5_sat⟩ := h_T4_sat
  obtain ⟨h_d0, h_T6, hd_d0_T6, hu_d0_T6, h_d0_pred, h_T6_sat⟩ := h_T5_sat
  obtain ⟨h_d1, h_T7, hd_d1_T7, hu_d1_T7, h_d1_pred, h_T7_sat⟩ := h_T6_sat
  obtain ⟨h_s,  h_T8, hd_s_T8,  hu_s_T8,  h_s_pred,  h_T8_sat⟩ := h_T7_sat
  obtain ⟨h_b3, h_b4, hd_b3_b4, hu_b3_b4, h_b3_pred, h_b4_pred⟩ := h_T8_sat
  rw [h_a0_pred] at hu_a0_T1 hd_a0_T1
  rw [h_a1_pred] at hu_a1_T2 hd_a1_T2
  rw [h_a2_pred] at hu_a2_T3 hd_a2_T3
  rw [h_a3_pred] at hu_a3_T4 hd_a3_T4
  rw [h_a4_pred] at hu_a4_T5 hd_a4_T5
  rw [h_d0_pred] at hu_d0_T6 hd_d0_T6
  rw [h_d1_pred] at hu_d1_T7 hd_d1_T7
  rw [h_s_pred]  at hu_s_T8  hd_s_T8
  rw [h_b3_pred] at hu_b3_b4 hd_b3_b4
  rw [h_b4_pred] at hu_b3_b4 hd_b3_b4
  clear h_a0_pred h_a1_pred h_a2_pred h_a3_pred h_a4_pred
  clear h_d0_pred h_d1_pred h_s_pred h_b3_pred h_b4_pred
  clear h_a0 h_a1 h_a2 h_a3 h_a4 h_d0 h_d1 h_s h_b3 h_b4
  obtain ⟨hcr_regs, hcm_mem, _⟩ := hcompat
  -- ==== Phase 2: pairwise range disjointness for the 4 memory regions. ====
  -- Memory regions:
  --   D0: [r1V .. r1V+8)             (descriptor.ptr, ↦U64)
  --   D1: [r1V+8 .. r1V+16)          (descriptor.len, ↦U64)
  --   S:  [seedPtr .. seedPtr+slen)  (seed bytes, ↦Bytes)
  --   B3: [r3V .. r3V+32)            (pid bytes, ↦Bytes32)
  --   B4: [r4V .. r4V+32)            (output bytes, ↦Bytes32)
  -- (D0 vs D1 is automatic from `r1V + 8`.)
  --
  -- For each pair, we derive `addr1 + len1 ≤ addr2 ∨ addr2 + len2 ≤ addr1`
  -- by picking a sentinel address owned by one atom + showing the other
  -- atom doesn't own it (so it's outside that other range).
  --
  -- The 9 pairs derived: (D0,S), (D0,B3), (D0,B4),
  --                      (D1,S), (D1,B3), (D1,B4),
  --                      (S,B3), (S,B4), (B3,B4).

  -- Substitute the union equalities so disjointness hypotheses on
  -- abstract `h_Tk` become structural unions of singletons.
  rw [← hu_d1_T7] at hd_d0_T6
  rw [← hu_s_T8] at hd_d1_T7 hd_d0_T6
  rw [← hu_b3_b4] at hd_s_T8 hd_d1_T7 hd_d0_T6

  -- Extract pairwise SL disjointness for memory atoms.
  have hd_D0_D1 : (PartialState.singletonMemU64 r1V seedPtr).Disjoint
                     (PartialState.singletonMemU64 (r1V + 8) seedBytes.size) :=
    PartialState.Disjoint_symm_of_union_left hd_d0_T6
  have hd_D0_S : (PartialState.singletonMemU64 r1V seedPtr).Disjoint
                    (PartialState.singletonMemBytes seedPtr seedBytes) :=
    PartialState.Disjoint_symm_of_union_left
      (PartialState.Disjoint_symm_of_union_right hd_d0_T6)
  have hd_D0_B3 : (PartialState.singletonMemU64 r1V seedPtr).Disjoint
                    (PartialState.singletonMem32Bytes r3V pidBytes) :=
    PartialState.Disjoint_symm_of_union_left
      (PartialState.Disjoint_symm_of_union_right
        (PartialState.Disjoint_symm_of_union_right hd_d0_T6))
  have hd_D0_B4 : (PartialState.singletonMemU64 r1V seedPtr).Disjoint
                    (PartialState.singletonMem32Bytes r4V outOldBytes) :=
    PartialState.Disjoint_symm_of_union_right
      (PartialState.Disjoint_symm_of_union_right
        (PartialState.Disjoint_symm_of_union_right hd_d0_T6))
  have hd_D1_S : (PartialState.singletonMemU64 (r1V + 8) seedBytes.size).Disjoint
                    (PartialState.singletonMemBytes seedPtr seedBytes) :=
    PartialState.Disjoint_symm_of_union_left hd_d1_T7
  have hd_D1_B3 : (PartialState.singletonMemU64 (r1V + 8) seedBytes.size).Disjoint
                    (PartialState.singletonMem32Bytes r3V pidBytes) :=
    PartialState.Disjoint_symm_of_union_left
      (PartialState.Disjoint_symm_of_union_right hd_d1_T7)
  have hd_D1_B4 : (PartialState.singletonMemU64 (r1V + 8) seedBytes.size).Disjoint
                    (PartialState.singletonMem32Bytes r4V outOldBytes) :=
    PartialState.Disjoint_symm_of_union_right
      (PartialState.Disjoint_symm_of_union_right hd_d1_T7)
  have hd_S_B3 : (PartialState.singletonMemBytes seedPtr seedBytes).Disjoint
                    (PartialState.singletonMem32Bytes r3V pidBytes) :=
    PartialState.Disjoint_symm_of_union_left hd_s_T8
  have hd_S_B4 : (PartialState.singletonMemBytes seedPtr seedBytes).Disjoint
                    (PartialState.singletonMem32Bytes r4V outOldBytes) :=
    PartialState.Disjoint_symm_of_union_right hd_s_T8
  -- hd_b3_b4 already has the right shape.

  -- Derive per-address range disjointness. The form
  --   "if `addr1 + i ∈ range1`, then `addr1 + i ∉ range2`"
  -- is the workhorse for both climb-up and compat. It's vacuously
  -- true when `range1` is empty (e.g. `seedBytes.size = 0`).
  --
  -- Strategy for each pair: pick a sentinel address from one range,
  -- use SL disjointness + the OTHER atom's `_mem_isSome` to derive
  -- the sentinel is outside the OTHER range.

  -- (D0, S) : r1V-range disjoint from seedPtr-range.
  have h_D0_not_in_S : ∀ a, r1V ≤ a → a < r1V + 8 →
      a < seedPtr ∨ a ≥ seedPtr + seedBytes.size := by
    intro a h1 h2
    obtain ⟨v_D0, hv_D0⟩ := PartialState.singletonMemU64_mem_isSome r1V seedPtr a ⟨h1, h2⟩
    obtain ⟨_, hd_mem, _⟩ := hd_D0_S
    rcases Nat.lt_or_ge a seedPtr with hl | hge
    · left; exact hl
    rcases Nat.lt_or_ge a (seedPtr + seedBytes.size) with hlt | hge2
    · obtain ⟨v_S, hv_S⟩ :=
        PartialState.singletonMemBytes_mem_isSome seedPtr seedBytes a ⟨hge, hlt⟩
      rcases hd_mem a with hl | hr
      · rw [hv_D0] at hl; nomatch hl
      · rw [hv_S] at hr; nomatch hr
    · right; exact hge2
  -- Symmetric: if a in S range, a not in D0 range.
  have h_S_not_in_D0 : ∀ a, seedPtr ≤ a → a < seedPtr + seedBytes.size →
      a < r1V ∨ a ≥ r1V + 8 := by
    intro a h1 h2
    obtain ⟨v_S, hv_S⟩ :=
      PartialState.singletonMemBytes_mem_isSome seedPtr seedBytes a ⟨h1, h2⟩
    obtain ⟨_, hd_mem, _⟩ := hd_D0_S
    rcases Nat.lt_or_ge a r1V with hl | hge
    · left; exact hl
    rcases Nat.lt_or_ge a (r1V + 8) with hlt | hge2
    · obtain ⟨v_D0, hv_D0⟩ := PartialState.singletonMemU64_mem_isSome r1V seedPtr a ⟨hge, hlt⟩
      rcases hd_mem a with hl | hr
      · rw [hv_D0] at hl; nomatch hl
      · rw [hv_S] at hr; nomatch hr
    · right; exact hge2

  -- (D0, B3)
  have h_D0_not_in_B3 : ∀ a, r1V ≤ a → a < r1V + 8 →
      a < r3V ∨ a ≥ r3V + 32 := by
    intro a h1 h2
    obtain ⟨v_D0, hv_D0⟩ := PartialState.singletonMemU64_mem_isSome r1V seedPtr a ⟨h1, h2⟩
    obtain ⟨_, hd_mem, _⟩ := hd_D0_B3
    rcases Nat.lt_or_ge a r3V with hl | hge
    · left; exact hl
    rcases Nat.lt_or_ge a (r3V + 32) with hlt | hge2
    · obtain ⟨v_B3, hv_B3⟩ :=
        PartialState.singletonMem32Bytes_mem_isSome r3V pidBytes a ⟨hge, hlt⟩
      rcases hd_mem a with hl | hr
      · rw [hv_D0] at hl; nomatch hl
      · rw [hv_B3] at hr; nomatch hr
    · right; exact hge2
  have h_B3_not_in_D0 : ∀ a, r3V ≤ a → a < r3V + 32 →
      a < r1V ∨ a ≥ r1V + 8 := by
    intro a h1 h2
    obtain ⟨v_B3, hv_B3⟩ :=
      PartialState.singletonMem32Bytes_mem_isSome r3V pidBytes a ⟨h1, h2⟩
    obtain ⟨_, hd_mem, _⟩ := hd_D0_B3
    rcases Nat.lt_or_ge a r1V with hl | hge
    · left; exact hl
    rcases Nat.lt_or_ge a (r1V + 8) with hlt | hge2
    · obtain ⟨v_D0, hv_D0⟩ := PartialState.singletonMemU64_mem_isSome r1V seedPtr a ⟨hge, hlt⟩
      rcases hd_mem a with hl | hr
      · rw [hv_D0] at hl; nomatch hl
      · rw [hv_B3] at hr; nomatch hr
    · right; exact hge2

  -- (D0, B4)
  have h_D0_not_in_B4 : ∀ a, r1V ≤ a → a < r1V + 8 →
      a < r4V ∨ a ≥ r4V + 32 := by
    intro a h1 h2
    obtain ⟨v_D0, hv_D0⟩ := PartialState.singletonMemU64_mem_isSome r1V seedPtr a ⟨h1, h2⟩
    obtain ⟨_, hd_mem, _⟩ := hd_D0_B4
    rcases Nat.lt_or_ge a r4V with hl | hge
    · left; exact hl
    rcases Nat.lt_or_ge a (r4V + 32) with hlt | hge2
    · obtain ⟨v_B4, hv_B4⟩ :=
        PartialState.singletonMem32Bytes_mem_isSome r4V outOldBytes a ⟨hge, hlt⟩
      rcases hd_mem a with hl | hr
      · rw [hv_D0] at hl; nomatch hl
      · rw [hv_B4] at hr; nomatch hr
    · right; exact hge2
  have h_B4_not_in_D0 : ∀ a, r4V ≤ a → a < r4V + 32 →
      a < r1V ∨ a ≥ r1V + 8 := by
    intro a h1 h2
    obtain ⟨v_B4, hv_B4⟩ :=
      PartialState.singletonMem32Bytes_mem_isSome r4V outOldBytes a ⟨h1, h2⟩
    obtain ⟨_, hd_mem, _⟩ := hd_D0_B4
    rcases Nat.lt_or_ge a r1V with hl | hge
    · left; exact hl
    rcases Nat.lt_or_ge a (r1V + 8) with hlt | hge2
    · obtain ⟨v_D0, hv_D0⟩ := PartialState.singletonMemU64_mem_isSome r1V seedPtr a ⟨hge, hlt⟩
      rcases hd_mem a with hl | hr
      · rw [hv_D0] at hl; nomatch hl
      · rw [hv_B4] at hr; nomatch hr
    · right; exact hge2

  -- (D1, S)
  have h_D1_not_in_S : ∀ a, r1V + 8 ≤ a → a < r1V + 16 →
      a < seedPtr ∨ a ≥ seedPtr + seedBytes.size := by
    intro a h1 h2
    obtain ⟨v_D1, hv_D1⟩ :=
      PartialState.singletonMemU64_mem_isSome (r1V + 8) seedBytes.size a ⟨h1, by omega⟩
    obtain ⟨_, hd_mem, _⟩ := hd_D1_S
    rcases Nat.lt_or_ge a seedPtr with hl | hge
    · left; exact hl
    rcases Nat.lt_or_ge a (seedPtr + seedBytes.size) with hlt | hge2
    · obtain ⟨v_S, hv_S⟩ :=
        PartialState.singletonMemBytes_mem_isSome seedPtr seedBytes a ⟨hge, hlt⟩
      rcases hd_mem a with hl | hr
      · rw [hv_D1] at hl; nomatch hl
      · rw [hv_S] at hr; nomatch hr
    · right; exact hge2
  have h_S_not_in_D1 : ∀ a, seedPtr ≤ a → a < seedPtr + seedBytes.size →
      a < r1V + 8 ∨ a ≥ r1V + 16 := by
    intro a h1 h2
    obtain ⟨v_S, hv_S⟩ :=
      PartialState.singletonMemBytes_mem_isSome seedPtr seedBytes a ⟨h1, h2⟩
    obtain ⟨_, hd_mem, _⟩ := hd_D1_S
    rcases Nat.lt_or_ge a (r1V + 8) with hl | hge
    · left; exact hl
    rcases Nat.lt_or_ge a (r1V + 16) with hlt | hge2
    · obtain ⟨v_D1, hv_D1⟩ :=
        PartialState.singletonMemU64_mem_isSome (r1V + 8) seedBytes.size a ⟨hge, by omega⟩
      rcases hd_mem a with hl | hr
      · rw [hv_D1] at hl; nomatch hl
      · rw [hv_S] at hr; nomatch hr
    · right; exact hge2

  -- (D1, B3)
  have h_D1_not_in_B3 : ∀ a, r1V + 8 ≤ a → a < r1V + 16 →
      a < r3V ∨ a ≥ r3V + 32 := by
    intro a h1 h2
    obtain ⟨v_D1, hv_D1⟩ :=
      PartialState.singletonMemU64_mem_isSome (r1V + 8) seedBytes.size a ⟨h1, by omega⟩
    obtain ⟨_, hd_mem, _⟩ := hd_D1_B3
    rcases Nat.lt_or_ge a r3V with hl | hge
    · left; exact hl
    rcases Nat.lt_or_ge a (r3V + 32) with hlt | hge2
    · obtain ⟨v_B3, hv_B3⟩ :=
        PartialState.singletonMem32Bytes_mem_isSome r3V pidBytes a ⟨hge, hlt⟩
      rcases hd_mem a with hl | hr
      · rw [hv_D1] at hl; nomatch hl
      · rw [hv_B3] at hr; nomatch hr
    · right; exact hge2
  have h_B3_not_in_D1 : ∀ a, r3V ≤ a → a < r3V + 32 →
      a < r1V + 8 ∨ a ≥ r1V + 16 := by
    intro a h1 h2
    obtain ⟨v_B3, hv_B3⟩ :=
      PartialState.singletonMem32Bytes_mem_isSome r3V pidBytes a ⟨h1, h2⟩
    obtain ⟨_, hd_mem, _⟩ := hd_D1_B3
    rcases Nat.lt_or_ge a (r1V + 8) with hl | hge
    · left; exact hl
    rcases Nat.lt_or_ge a (r1V + 16) with hlt | hge2
    · obtain ⟨v_D1, hv_D1⟩ :=
        PartialState.singletonMemU64_mem_isSome (r1V + 8) seedBytes.size a ⟨hge, by omega⟩
      rcases hd_mem a with hl | hr
      · rw [hv_D1] at hl; nomatch hl
      · rw [hv_B3] at hr; nomatch hr
    · right; exact hge2

  -- (D1, B4)
  have h_D1_not_in_B4 : ∀ a, r1V + 8 ≤ a → a < r1V + 16 →
      a < r4V ∨ a ≥ r4V + 32 := by
    intro a h1 h2
    obtain ⟨v_D1, hv_D1⟩ :=
      PartialState.singletonMemU64_mem_isSome (r1V + 8) seedBytes.size a ⟨h1, by omega⟩
    obtain ⟨_, hd_mem, _⟩ := hd_D1_B4
    rcases Nat.lt_or_ge a r4V with hl | hge
    · left; exact hl
    rcases Nat.lt_or_ge a (r4V + 32) with hlt | hge2
    · obtain ⟨v_B4, hv_B4⟩ :=
        PartialState.singletonMem32Bytes_mem_isSome r4V outOldBytes a ⟨hge, hlt⟩
      rcases hd_mem a with hl | hr
      · rw [hv_D1] at hl; nomatch hl
      · rw [hv_B4] at hr; nomatch hr
    · right; exact hge2
  have h_B4_not_in_D1 : ∀ a, r4V ≤ a → a < r4V + 32 →
      a < r1V + 8 ∨ a ≥ r1V + 16 := by
    intro a h1 h2
    obtain ⟨v_B4, hv_B4⟩ :=
      PartialState.singletonMem32Bytes_mem_isSome r4V outOldBytes a ⟨h1, h2⟩
    obtain ⟨_, hd_mem, _⟩ := hd_D1_B4
    rcases Nat.lt_or_ge a (r1V + 8) with hl | hge
    · left; exact hl
    rcases Nat.lt_or_ge a (r1V + 16) with hlt | hge2
    · obtain ⟨v_D1, hv_D1⟩ :=
        PartialState.singletonMemU64_mem_isSome (r1V + 8) seedBytes.size a ⟨hge, by omega⟩
      rcases hd_mem a with hl | hr
      · rw [hv_D1] at hl; nomatch hl
      · rw [hv_B4] at hr; nomatch hr
    · right; exact hge2

  -- (S, B3)
  have h_S_not_in_B3 : ∀ a, seedPtr ≤ a → a < seedPtr + seedBytes.size →
      a < r3V ∨ a ≥ r3V + 32 := by
    intro a h1 h2
    obtain ⟨v_S, hv_S⟩ :=
      PartialState.singletonMemBytes_mem_isSome seedPtr seedBytes a ⟨h1, h2⟩
    obtain ⟨_, hd_mem, _⟩ := hd_S_B3
    rcases Nat.lt_or_ge a r3V with hl | hge
    · left; exact hl
    rcases Nat.lt_or_ge a (r3V + 32) with hlt | hge2
    · obtain ⟨v_B3, hv_B3⟩ :=
        PartialState.singletonMem32Bytes_mem_isSome r3V pidBytes a ⟨hge, hlt⟩
      rcases hd_mem a with hl | hr
      · rw [hv_S] at hl; nomatch hl
      · rw [hv_B3] at hr; nomatch hr
    · right; exact hge2
  have h_B3_not_in_S : ∀ a, r3V ≤ a → a < r3V + 32 →
      a < seedPtr ∨ a ≥ seedPtr + seedBytes.size := by
    intro a h1 h2
    obtain ⟨v_B3, hv_B3⟩ :=
      PartialState.singletonMem32Bytes_mem_isSome r3V pidBytes a ⟨h1, h2⟩
    obtain ⟨_, hd_mem, _⟩ := hd_S_B3
    rcases Nat.lt_or_ge a seedPtr with hl | hge
    · left; exact hl
    rcases Nat.lt_or_ge a (seedPtr + seedBytes.size) with hlt | hge2
    · obtain ⟨v_S, hv_S⟩ :=
        PartialState.singletonMemBytes_mem_isSome seedPtr seedBytes a ⟨hge, hlt⟩
      rcases hd_mem a with hl | hr
      · rw [hv_S] at hl; nomatch hl
      · rw [hv_B3] at hr; nomatch hr
    · right; exact hge2

  -- (S, B4)
  have h_S_not_in_B4 : ∀ a, seedPtr ≤ a → a < seedPtr + seedBytes.size →
      a < r4V ∨ a ≥ r4V + 32 := by
    intro a h1 h2
    obtain ⟨v_S, hv_S⟩ :=
      PartialState.singletonMemBytes_mem_isSome seedPtr seedBytes a ⟨h1, h2⟩
    obtain ⟨_, hd_mem, _⟩ := hd_S_B4
    rcases Nat.lt_or_ge a r4V with hl | hge
    · left; exact hl
    rcases Nat.lt_or_ge a (r4V + 32) with hlt | hge2
    · obtain ⟨v_B4, hv_B4⟩ :=
        PartialState.singletonMem32Bytes_mem_isSome r4V outOldBytes a ⟨hge, hlt⟩
      rcases hd_mem a with hl | hr
      · rw [hv_S] at hl; nomatch hl
      · rw [hv_B4] at hr; nomatch hr
    · right; exact hge2
  have h_B4_not_in_S : ∀ a, r4V ≤ a → a < r4V + 32 →
      a < seedPtr ∨ a ≥ seedPtr + seedBytes.size := by
    intro a h1 h2
    obtain ⟨v_B4, hv_B4⟩ :=
      PartialState.singletonMem32Bytes_mem_isSome r4V outOldBytes a ⟨h1, h2⟩
    obtain ⟨_, hd_mem, _⟩ := hd_S_B4
    rcases Nat.lt_or_ge a seedPtr with hl | hge
    · left; exact hl
    rcases Nat.lt_or_ge a (seedPtr + seedBytes.size) with hlt | hge2
    · obtain ⟨v_S, hv_S⟩ :=
        PartialState.singletonMemBytes_mem_isSome seedPtr seedBytes a ⟨hge, hlt⟩
      rcases hd_mem a with hl | hr
      · rw [hv_S] at hl; nomatch hl
      · rw [hv_B4] at hr; nomatch hr
    · right; exact hge2

  -- (B3, B4): same as n=0.
  have h_B3_not_in_B4 : ∀ a, r3V ≤ a → a < r3V + 32 →
      a < r4V ∨ a ≥ r4V + 32 := by
    intro a h1 h2
    obtain ⟨v_B3, hv_B3⟩ :=
      PartialState.singletonMem32Bytes_mem_isSome r3V pidBytes a ⟨h1, h2⟩
    obtain ⟨_, hd_mem, _⟩ := hd_b3_b4
    rcases Nat.lt_or_ge a r4V with hl | hge
    · left; exact hl
    rcases Nat.lt_or_ge a (r4V + 32) with hlt | hge2
    · obtain ⟨v_B4, hv_B4⟩ :=
        PartialState.singletonMem32Bytes_mem_isSome r4V outOldBytes a ⟨hge, hlt⟩
      rcases hd_mem a with hl | hr
      · rw [hv_B3] at hl; nomatch hl
      · rw [hv_B4] at hr; nomatch hr
    · right; exact hge2
  have h_B4_not_in_B3 : ∀ a, r4V ≤ a → a < r4V + 32 →
      a < r3V ∨ a ≥ r3V + 32 := by
    intro a h1 h2
    obtain ⟨v_B4, hv_B4⟩ :=
      PartialState.singletonMem32Bytes_mem_isSome r4V outOldBytes a ⟨h1, h2⟩
    obtain ⟨_, hd_mem, _⟩ := hd_b3_b4
    rcases Nat.lt_or_ge a r3V with hl | hge
    · left; exact hl
    rcases Nat.lt_or_ge a (r3V + 32) with hlt | hge2
    · obtain ⟨v_B3, hv_B3⟩ :=
        PartialState.singletonMem32Bytes_mem_isSome r3V pidBytes a ⟨hge, hlt⟩
      rcases hd_mem a with hl | hr
      · rw [hv_B3] at hl; nomatch hl
      · rw [hv_B4] at hr; nomatch hr
    · right; exact hge2
  -- ==== Phase 3: climb-up reg / mem to hp, then s. ====
  -- All reg layers have no mem; collapse h_P.mem to h_T5.mem.
  have h_P_mem_eq_T5 (a : Nat) : h_P.mem a = h_T5.mem a := by
    rw [← hu_a0_T1,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _),
        ← hu_a1_T2,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _),
        ← hu_a2_T3,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _),
        ← hu_a3_T4,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _),
        ← hu_a4_T5,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
  -- Reg ownership: each level-k reg atom owns its reg; higher levels'
  -- regs are skipped via `union_regs_of_left_none + singletonReg_regs_other`.
  have h_P_regs_r0 : h_P.regs .r0 = some r0Old := by
    rw [← hu_a0_T1]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_T1_regs_r1 : h_T1.regs .r1 = some r1V := by
    rw [← hu_a1_T2]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_regs_r1 : h_P.regs .r1 = some r1V := by
    rw [← hu_a0_T1,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r1 ≠ Reg.r0))]
    exact h_T1_regs_r1
  have h_T2_regs_r2 : h_T2.regs .r2 = some 1 := by
    rw [← hu_a2_T3]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_T1_regs_r2 : h_T1.regs .r2 = some 1 := by
    rw [← hu_a1_T2,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r2 ≠ Reg.r1))]
    exact h_T2_regs_r2
  have h_P_regs_r2 : h_P.regs .r2 = some 1 := by
    rw [← hu_a0_T1,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r2 ≠ Reg.r0))]
    exact h_T1_regs_r2
  have h_T3_regs_r3 : h_T3.regs .r3 = some r3V := by
    rw [← hu_a3_T4]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_T2_regs_r3 : h_T2.regs .r3 = some r3V := by
    rw [← hu_a2_T3,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r3 ≠ Reg.r2))]
    exact h_T3_regs_r3
  have h_T1_regs_r3 : h_T1.regs .r3 = some r3V := by
    rw [← hu_a1_T2,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r3 ≠ Reg.r1))]
    exact h_T2_regs_r3
  have h_P_regs_r3 : h_P.regs .r3 = some r3V := by
    rw [← hu_a0_T1,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r3 ≠ Reg.r0))]
    exact h_T1_regs_r3
  have h_T4_regs_r4 : h_T4.regs .r4 = some r4V := by
    rw [← hu_a4_T5]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_T3_regs_r4 : h_T3.regs .r4 = some r4V := by
    rw [← hu_a3_T4,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r4 ≠ Reg.r3))]
    exact h_T4_regs_r4
  have h_T2_regs_r4 : h_T2.regs .r4 = some r4V := by
    rw [← hu_a2_T3,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r4 ≠ Reg.r2))]
    exact h_T3_regs_r4
  have h_T1_regs_r4 : h_T1.regs .r4 = some r4V := by
    rw [← hu_a1_T2,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r4 ≠ Reg.r1))]
    exact h_T2_regs_r4
  have h_P_regs_r4 : h_P.regs .r4 = some r4V := by
    rw [← hu_a0_T1,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r4 ≠ Reg.r0))]
    exact h_T1_regs_r4
  -- ==== Mem climb-up at each region ====
  -- h_T8.mem in [r3V..r3V+32) and [r4V..r4V+32).
  have h_T8_mem_pid (i : Nat) (hi : i < 32) :
      h_T8.mem (r3V + i) = some (pidBytes.get! i).toNat := by
    rw [← hu_b3_b4]
    exact PartialState.union_mem_of_left_some
      (PartialState.singletonMem32Bytes_mem_at r3V pidBytes i hi)
  have h_T8_mem_out (i : Nat) (hi : i < 32) :
      h_T8.mem (r4V + i) = some (outOldBytes.get! i).toNat := by
    rw [← hu_b3_b4,
        PartialState.union_mem_of_left_none
          (PartialState.singletonMem32Bytes_mem_outside r3V pidBytes _
            (h_B4_not_in_B3 _ (Nat.le_add_right _ _) (by omega)))]
    exact PartialState.singletonMem32Bytes_mem_at r4V outOldBytes i hi
  -- Climb h_T7 (= h_s ⊎ h_T8) through the seed atom.
  have h_T7_mem_seed (i : Nat) (hi : i < seedBytes.size) :
      h_T7.mem (seedPtr + i) = some (seedBytes.get! i).toNat := by
    rw [← hu_s_T8]
    exact PartialState.union_mem_of_left_some
      (PartialState.singletonMemBytes_mem_at seedPtr seedBytes i hi)
  have h_T7_mem_pid (i : Nat) (hi : i < 32) :
      h_T7.mem (r3V + i) = some (pidBytes.get! i).toNat := by
    rw [← hu_s_T8,
        PartialState.union_mem_of_left_none
          (PartialState.singletonMemBytes_mem_outside seedPtr seedBytes _
            (h_B3_not_in_S _ (Nat.le_add_right _ _) (by omega)))]
    exact h_T8_mem_pid i hi
  have h_T7_mem_out (i : Nat) (hi : i < 32) :
      h_T7.mem (r4V + i) = some (outOldBytes.get! i).toNat := by
    rw [← hu_s_T8,
        PartialState.union_mem_of_left_none
          (PartialState.singletonMemBytes_mem_outside seedPtr seedBytes _
            (h_B4_not_in_S _ (Nat.le_add_right _ _) (by omega)))]
    exact h_T8_mem_out i hi
  -- Climb h_T6 (= h_d1 ⊎ h_T7) through descriptor.len.
  have h_T6_mem_d1_byte (j : Nat) (hj : j < 8)
      (hv : (PartialState.singletonMemU64 (r1V + 8) seedBytes.size).mem (r1V + 8 + j) = some
              ((seedBytes.size / 256^j) % 256)) :
      h_T6.mem (r1V + 8 + j) = some ((seedBytes.size / 256^j) % 256) := by
    rw [← hu_d1_T7]
    exact PartialState.union_mem_of_left_some hv
  have h_T6_mem_seed (i : Nat) (hi : i < seedBytes.size) :
      h_T6.mem (seedPtr + i) = some (seedBytes.get! i).toNat := by
    have h_outside : seedPtr + i < r1V + 8 ∨ seedPtr + i ≥ r1V + 8 + 8 := by
      have := h_S_not_in_D1 (seedPtr + i) (Nat.le_add_right _ _) (by omega)
      rcases this with h | h
      · left; exact h
      · right; omega
    rw [← hu_d1_T7,
        PartialState.union_mem_of_left_none
          (PartialState.singletonMemU64_mem_outside (r1V + 8) seedBytes.size _ h_outside)]
    exact h_T7_mem_seed i hi
  have h_T6_mem_pid (i : Nat) (hi : i < 32) :
      h_T6.mem (r3V + i) = some (pidBytes.get! i).toNat := by
    have h_outside : r3V + i < r1V + 8 ∨ r3V + i ≥ r1V + 8 + 8 := by
      have := h_B3_not_in_D1 (r3V + i) (Nat.le_add_right _ _) (by omega)
      rcases this with h | h
      · left; exact h
      · right; omega
    rw [← hu_d1_T7,
        PartialState.union_mem_of_left_none
          (PartialState.singletonMemU64_mem_outside (r1V + 8) seedBytes.size _ h_outside)]
    exact h_T7_mem_pid i hi
  have h_T6_mem_out (i : Nat) (hi : i < 32) :
      h_T6.mem (r4V + i) = some (outOldBytes.get! i).toNat := by
    have h_outside : r4V + i < r1V + 8 ∨ r4V + i ≥ r1V + 8 + 8 := by
      have := h_B4_not_in_D1 (r4V + i) (Nat.le_add_right _ _) (by omega)
      rcases this with h | h
      · left; exact h
      · right; omega
    rw [← hu_d1_T7,
        PartialState.union_mem_of_left_none
          (PartialState.singletonMemU64_mem_outside (r1V + 8) seedBytes.size _ h_outside)]
    exact h_T7_mem_out i hi
  -- Climb h_T5 (= h_d0 ⊎ h_T6) through descriptor.ptr.
  have h_T5_mem_d1 (j : Nat) (hj : j < 8) (val : Nat)
      (hv : h_T6.mem (r1V + 8 + j) = some val) :
      h_T5.mem (r1V + 8 + j) = some val := by
    rw [← hu_d0_T6,
        PartialState.union_mem_of_left_none
          (PartialState.singletonMemU64_mem_outside r1V seedPtr _ (Or.inr (by omega)))]
    exact hv
  have h_T5_mem_seed (i : Nat) (hi : i < seedBytes.size) :
      h_T5.mem (seedPtr + i) = some (seedBytes.get! i).toNat := by
    rw [← hu_d0_T6,
        PartialState.union_mem_of_left_none
          (PartialState.singletonMemU64_mem_outside r1V seedPtr _
            (h_S_not_in_D0 _ (Nat.le_add_right _ _) (by omega)))]
    exact h_T6_mem_seed i hi
  have h_T5_mem_pid (i : Nat) (hi : i < 32) :
      h_T5.mem (r3V + i) = some (pidBytes.get! i).toNat := by
    rw [← hu_d0_T6,
        PartialState.union_mem_of_left_none
          (PartialState.singletonMemU64_mem_outside r1V seedPtr _
            (h_B3_not_in_D0 _ (Nat.le_add_right _ _) (by omega)))]
    exact h_T6_mem_pid i hi
  have h_T5_mem_out (i : Nat) (hi : i < 32) :
      h_T5.mem (r4V + i) = some (outOldBytes.get! i).toNat := by
    rw [← hu_d0_T6,
        PartialState.union_mem_of_left_none
          (PartialState.singletonMemU64_mem_outside r1V seedPtr _
            (h_B4_not_in_D0 _ (Nat.le_add_right _ _) (by omega)))]
    exact h_T6_mem_out i hi
  -- ==== Descriptor.ptr byte extractions (D0 at [r1V..r1V+8)) ====
  have h_T5_d0_0 : h_T5.mem r1V = some (seedPtr % 256) := by
    rw [← hu_d0_T6]
    exact PartialState.union_mem_of_left_some (PartialState.singletonMemU64_mem_0 _ _)
  have h_T5_d0_1 : h_T5.mem (r1V + 1) = some (seedPtr / 0x100 % 256) := by
    rw [← hu_d0_T6]
    exact PartialState.union_mem_of_left_some (PartialState.singletonMemU64_mem_1 _ _)
  have h_T5_d0_2 : h_T5.mem (r1V + 2) = some (seedPtr / 0x10000 % 256) := by
    rw [← hu_d0_T6]
    exact PartialState.union_mem_of_left_some (PartialState.singletonMemU64_mem_2 _ _)
  have h_T5_d0_3 : h_T5.mem (r1V + 3) = some (seedPtr / 0x1000000 % 256) := by
    rw [← hu_d0_T6]
    exact PartialState.union_mem_of_left_some (PartialState.singletonMemU64_mem_3 _ _)
  have h_T5_d0_4 : h_T5.mem (r1V + 4) = some (seedPtr / 0x100000000 % 256) := by
    rw [← hu_d0_T6]
    exact PartialState.union_mem_of_left_some (PartialState.singletonMemU64_mem_4 _ _)
  have h_T5_d0_5 : h_T5.mem (r1V + 5) = some (seedPtr / 0x10000000000 % 256) := by
    rw [← hu_d0_T6]
    exact PartialState.union_mem_of_left_some (PartialState.singletonMemU64_mem_5 _ _)
  have h_T5_d0_6 : h_T5.mem (r1V + 6) = some (seedPtr / 0x1000000000000 % 256) := by
    rw [← hu_d0_T6]
    exact PartialState.union_mem_of_left_some (PartialState.singletonMemU64_mem_6 _ _)
  have h_T5_d0_7 : h_T5.mem (r1V + 7) = some (seedPtr / 0x100000000000000 % 256) := by
    rw [← hu_d0_T6]
    exact PartialState.union_mem_of_left_some (PartialState.singletonMemU64_mem_7 _ _)
  -- ==== Descriptor.len byte extractions (D1 at [r1V+8..r1V+16)) ====
  -- D1 = singletonMemU64 (r1V+8) seedBytes.size. Each byte is at r1V + 8 + j.
  -- We need h_T5.mem (r1V + 8 + j); D0 doesn't own this range, so climb through.
  have h_T6_d1_byte (j : Nat) (val : Nat)
      (hv : (PartialState.singletonMemU64 (r1V + 8) seedBytes.size).mem (r1V + 8 + j) = some val) :
      h_T6.mem (r1V + 8 + j) = some val := by
    rw [← hu_d1_T7]
    exact PartialState.union_mem_of_left_some hv
  have h_T5_d1_byte (j : Nat) (val : Nat)
      (hv : (PartialState.singletonMemU64 (r1V + 8) seedBytes.size).mem (r1V + 8 + j) = some val) :
      h_T5.mem (r1V + 8 + j) = some val := by
    rw [← hu_d0_T6,
        PartialState.union_mem_of_left_none
          (PartialState.singletonMemU64_mem_outside r1V seedPtr _ (Or.inr (by omega)))]
    exact h_T6_d1_byte j val hv
  have h_T5_d1_0 : h_T5.mem (r1V + 8) = some (seedBytes.size % 256) := by
    have := PartialState.singletonMemU64_mem_0 (r1V + 8) seedBytes.size
    have hkey : h_T5.mem (r1V + 8 + 0) = some (seedBytes.size % 256) :=
      h_T5_d1_byte 0 _ (by simpa using this)
    simpa using hkey
  have h_T5_d1_1 : h_T5.mem (r1V + 9) = some (seedBytes.size / 0x100 % 256) := by
    have hkey := h_T5_d1_byte 1 _ (PartialState.singletonMemU64_mem_1 (r1V + 8) seedBytes.size)
    simpa using hkey
  have h_T5_d1_2 : h_T5.mem (r1V + 10) = some (seedBytes.size / 0x10000 % 256) := by
    have hkey := h_T5_d1_byte 2 _ (PartialState.singletonMemU64_mem_2 (r1V + 8) seedBytes.size)
    simpa using hkey
  have h_T5_d1_3 : h_T5.mem (r1V + 11) = some (seedBytes.size / 0x1000000 % 256) := by
    have hkey := h_T5_d1_byte 3 _ (PartialState.singletonMemU64_mem_3 (r1V + 8) seedBytes.size)
    simpa using hkey
  have h_T5_d1_4 : h_T5.mem (r1V + 12) = some (seedBytes.size / 0x100000000 % 256) := by
    have hkey := h_T5_d1_byte 4 _ (PartialState.singletonMemU64_mem_4 (r1V + 8) seedBytes.size)
    simpa using hkey
  have h_T5_d1_5 : h_T5.mem (r1V + 13) = some (seedBytes.size / 0x10000000000 % 256) := by
    have hkey := h_T5_d1_byte 5 _ (PartialState.singletonMemU64_mem_5 (r1V + 8) seedBytes.size)
    simpa using hkey
  have h_T5_d1_6 : h_T5.mem (r1V + 14) = some (seedBytes.size / 0x1000000000000 % 256) := by
    have hkey := h_T5_d1_byte 6 _ (PartialState.singletonMemU64_mem_6 (r1V + 8) seedBytes.size)
    simpa using hkey
  have h_T5_d1_7 : h_T5.mem (r1V + 15) = some (seedBytes.size / 0x100000000000000 % 256) := by
    have hkey := h_T5_d1_byte 7 _ (PartialState.singletonMemU64_mem_7 (r1V + 8) seedBytes.size)
    simpa using hkey
  -- ==== Climb to hp.mem and s.mem ====
  -- All needed mem values pulled to the level of hp.
  have hp_mem_of_h_P (a : Nat) (val : Nat) (h : h_P.mem a = some val) :
      hp.mem a = some val := by
    rw [← hu_PR]; exact PartialState.union_mem_of_left_some h
  have hs_mem_of_hp (a : Nat) (val : Nat) (h : hp.mem a = some val) :
      s.mem a = val := hcm_mem _ _ h
  -- Descriptor.ptr (8 bytes at r1V): values match LE decode of seedPtr.
  have hs_d0_0 : s.mem r1V = seedPtr % 256 :=
    hs_mem_of_hp _ _ (hp_mem_of_h_P _ _ (h_P_mem_eq_T5 _ ▸ h_T5_d0_0))
  have hs_d0_1 : s.mem (r1V + 1) = seedPtr / 0x100 % 256 :=
    hs_mem_of_hp _ _ (hp_mem_of_h_P _ _ (h_P_mem_eq_T5 _ ▸ h_T5_d0_1))
  have hs_d0_2 : s.mem (r1V + 2) = seedPtr / 0x10000 % 256 :=
    hs_mem_of_hp _ _ (hp_mem_of_h_P _ _ (h_P_mem_eq_T5 _ ▸ h_T5_d0_2))
  have hs_d0_3 : s.mem (r1V + 3) = seedPtr / 0x1000000 % 256 :=
    hs_mem_of_hp _ _ (hp_mem_of_h_P _ _ (h_P_mem_eq_T5 _ ▸ h_T5_d0_3))
  have hs_d0_4 : s.mem (r1V + 4) = seedPtr / 0x100000000 % 256 :=
    hs_mem_of_hp _ _ (hp_mem_of_h_P _ _ (h_P_mem_eq_T5 _ ▸ h_T5_d0_4))
  have hs_d0_5 : s.mem (r1V + 5) = seedPtr / 0x10000000000 % 256 :=
    hs_mem_of_hp _ _ (hp_mem_of_h_P _ _ (h_P_mem_eq_T5 _ ▸ h_T5_d0_5))
  have hs_d0_6 : s.mem (r1V + 6) = seedPtr / 0x1000000000000 % 256 :=
    hs_mem_of_hp _ _ (hp_mem_of_h_P _ _ (h_P_mem_eq_T5 _ ▸ h_T5_d0_6))
  have hs_d0_7 : s.mem (r1V + 7) = seedPtr / 0x100000000000000 % 256 :=
    hs_mem_of_hp _ _ (hp_mem_of_h_P _ _ (h_P_mem_eq_T5 _ ▸ h_T5_d0_7))
  -- Descriptor.len (8 bytes at r1V+8).
  have hs_d1_0 : s.mem (r1V + 8) = seedBytes.size % 256 :=
    hs_mem_of_hp _ _ (hp_mem_of_h_P _ _ (h_P_mem_eq_T5 _ ▸ h_T5_d1_0))
  have hs_d1_1 : s.mem (r1V + 9) = seedBytes.size / 0x100 % 256 :=
    hs_mem_of_hp _ _ (hp_mem_of_h_P _ _ (h_P_mem_eq_T5 _ ▸ h_T5_d1_1))
  have hs_d1_2 : s.mem (r1V + 10) = seedBytes.size / 0x10000 % 256 :=
    hs_mem_of_hp _ _ (hp_mem_of_h_P _ _ (h_P_mem_eq_T5 _ ▸ h_T5_d1_2))
  have hs_d1_3 : s.mem (r1V + 11) = seedBytes.size / 0x1000000 % 256 :=
    hs_mem_of_hp _ _ (hp_mem_of_h_P _ _ (h_P_mem_eq_T5 _ ▸ h_T5_d1_3))
  have hs_d1_4 : s.mem (r1V + 12) = seedBytes.size / 0x100000000 % 256 :=
    hs_mem_of_hp _ _ (hp_mem_of_h_P _ _ (h_P_mem_eq_T5 _ ▸ h_T5_d1_4))
  have hs_d1_5 : s.mem (r1V + 13) = seedBytes.size / 0x10000000000 % 256 :=
    hs_mem_of_hp _ _ (hp_mem_of_h_P _ _ (h_P_mem_eq_T5 _ ▸ h_T5_d1_5))
  have hs_d1_6 : s.mem (r1V + 14) = seedBytes.size / 0x1000000000000 % 256 :=
    hs_mem_of_hp _ _ (hp_mem_of_h_P _ _ (h_P_mem_eq_T5 _ ▸ h_T5_d1_6))
  have hs_d1_7 : s.mem (r1V + 15) = seedBytes.size / 0x100000000000000 % 256 :=
    hs_mem_of_hp _ _ (hp_mem_of_h_P _ _ (h_P_mem_eq_T5 _ ▸ h_T5_d1_7))
  -- Seed bytes at seedPtr..seedPtr+slen.
  have hs_seed (i : Nat) (hi : i < seedBytes.size) :
      s.mem (seedPtr + i) = (seedBytes.get! i).toNat :=
    hs_mem_of_hp _ _ (hp_mem_of_h_P _ _ (h_P_mem_eq_T5 _ ▸ h_T5_mem_seed i hi))
  -- Pid bytes at r3V..r3V+32.
  have hs_pid (i : Nat) (hi : i < 32) :
      s.mem (r3V + i) = (pidBytes.get! i).toNat :=
    hs_mem_of_hp _ _ (hp_mem_of_h_P _ _ (h_P_mem_eq_T5 _ ▸ h_T5_mem_pid i hi))
  -- Output bytes at r4V..r4V+32 (used later for the new partial state).
  have hs_out (i : Nat) (hi : i < 32) :
      s.mem (r4V + i) = (outOldBytes.get! i).toNat :=
    hs_mem_of_hp _ _ (hp_mem_of_h_P _ _ (h_P_mem_eq_T5 _ ▸ h_T5_mem_out i hi))
  -- ==== s.regs values via hp + compat. ====
  have hs_regs_r0 : s.regs.get .r0 = r0Old :=
    hcr_regs .r0 r0Old (by rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r0)
  have hs_regs_r1 : s.regs.get .r1 = r1V :=
    hcr_regs .r1 r1V (by rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r1)
  have hs_regs_r2 : s.regs.get .r2 = 1 :=
    hcr_regs .r2 1 (by rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r2)
  have hs_regs_r3 : s.regs.get .r3 = r3V :=
    hcr_regs .r3 r3V (by rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r3)
  have hs_regs_r4 : s.regs.get .r4 = r4V :=
    hcr_regs .r4 r4V (by rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r4)
  -- ==== Phase 5: compute readU64, readBytes, readSeeds, executeFn. ====
  have h_readU64_ptr : Memory.readU64 s.mem r1V = seedPtr :=
    readU64_eq_of_bytes_match hseed_lt hs_d0_0 hs_d0_1 hs_d0_2 hs_d0_3 hs_d0_4 hs_d0_5 hs_d0_6 hs_d0_7
  have h_readU64_len : Memory.readU64 s.mem (r1V + 8) = seedBytes.size :=
    readU64_eq_of_bytes_match hslen_lt hs_d1_0 hs_d1_1 hs_d1_2 hs_d1_3 hs_d1_4 hs_d1_5 hs_d1_6 hs_d1_7
  have h_readBytes_seed : readBytes s.mem seedPtr seedBytes.size = seedBytes := by
    apply readBytes_eq_of_match _ _ _ _ rfl
    intro i hi
    rw [hs_seed i hi]
    exact Nat.mod_eq_of_lt (by have := (seedBytes.get! i).toNat_lt; omega)
  have h_readBytes_pid : readBytes s.mem r3V 32 = pidBytes := by
    apply readBytes_eq_of_match _ _ _ _ hpid
    intro i hi
    rw [hs_pid i hi]
    exact Nat.mod_eq_of_lt (by have := (pidBytes.get! i).toNat_lt; omega)
  -- readSeeds with n = 1 produces a one-element list.
  have h_readSeeds : Pda.readSeeds s.mem r1V 1 = [seedBytes] := by
    show (List.range 1).map _ = [seedBytes]
    simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons,
               List.map_nil, List.nil_append]
    show [readBytes s.mem (Memory.readU64 s.mem (r1V + 0 * 16))
                          (Memory.readU64 s.mem (r1V + 0 * 16 + 8))] = [seedBytes]
    rw [Nat.zero_mul, Nat.add_zero, h_readU64_ptr, h_readU64_len, h_readBytes_seed]
  have hfetch : fetch s.pc = some (.call .sol_create_program_address) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have h_create_eq :
      Pda.execCreate s
        = commitOptional s r4V 32 (Pda.createProgramAddress [seedBytes] pidBytes) := by
    show commitOptional s (s.regs.get .r4) 32
            (Pda.createProgramAddress
              (Pda.readSeeds s.mem (s.regs.get .r1) (s.regs.get .r2))
              (readBytes s.mem (s.regs.get .r3) 32))
          = commitOptional s r4V 32 (Pda.createProgramAddress [seedBytes] pidBytes)
    rw [hs_regs_r1, hs_regs_r2, hs_regs_r3, hs_regs_r4, h_readSeeds, h_readBytes_pid]
  let s' : State := commitOptional s r4V 32 (Pda.createProgramAddress [seedBytes] pidBytes)
  have hs'_def : s' = commitOptional s r4V 32 (Pda.createProgramAddress [seedBytes] pidBytes) := rfl
  have hexec : executeFn fetch s 1 =
      { s' with pc := s.pc + 1
                cuConsumed := s'.cuConsumed + syscallCu .sol_create_program_address s } := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch, executeFn_zero]
    show ({ Pda.execCreate s with
            pc := s.pc + 1
            cuConsumed := (Pda.execCreate s).cuConsumed
                          + syscallCu .sol_create_program_address s }) = _
    rw [h_create_eq]
  -- ==== Phase 6: commitOptional helpers (parallel to n=0). ====
  have h_post_r0 :
      (commitOptional s r4V 32 (Pda.createProgramAddress [seedBytes] pidBytes)).regs.get .r0
        = (match Pda.createProgramAddress [seedBytes] pidBytes with
           | some _ => 0 | none => 1) := by
    cases Pda.createProgramAddress [seedBytes] pidBytes <;> rfl
  have h_post_regs_other (r : Reg) (hr : r ≠ .r0) :
      (commitOptional s r4V 32 (Pda.createProgramAddress [seedBytes] pidBytes)).regs.get r
        = s.regs.get r := by
    cases Pda.createProgramAddress [seedBytes] pidBytes with
    | some _ =>
      show (s.regs.set .r0 0).get r = _
      exact RegFile.get_set_diff _ _ _ _ hr
    | none =>
      show (s.regs.set .r0 1).get r = _
      exact RegFile.get_set_diff _ _ _ _ hr
  have h_post_mem_r4 (i : Nat) (hi : i < 32) :
      (commitOptional s r4V 32 (Pda.createProgramAddress [seedBytes] pidBytes)).mem (r4V + i)
        = ((match Pda.createProgramAddress [seedBytes] pidBytes with
            | some bs => bs | none => outOldBytes).get! i).toNat := by
    cases h_cpa : Pda.createProgramAddress [seedBytes] pidBytes with
    | some bs =>
      show (writeBytes s.mem r4V 32 bs).read (r4V + i) = _
      exact writeBytes_read_inside _ _ _ _ _ hi
    | none =>
      show s.mem (r4V + i) = _
      exact hs_out i hi
  have h_post_mem_outside (a : Nat) (h : a < r4V ∨ a ≥ r4V + 32) :
      (commitOptional s r4V 32 (Pda.createProgramAddress [seedBytes] pidBytes)).mem a = s.mem a := by
    cases Pda.createProgramAddress [seedBytes] pidBytes with
    | some bs =>
      show (writeBytes s.mem r4V 32 bs).read a = _
      exact writeBytes_read_outside _ _ _ _ _ h
    | none => rfl
  have h_post_exitCode :
      (commitOptional s r4V 32 (Pda.createProgramAddress [seedBytes] pidBytes)).exitCode
        = s.exitCode := by
    cases Pda.createProgramAddress [seedBytes] pidBytes <;> rfl
  -- ==== Phase 7: assemble Q's partial state. ====
  let h_a0_new : PartialState := PartialState.singletonReg .r0
    (match Pda.createProgramAddress [seedBytes] pidBytes with | some _ => 0 | none => 1)
  let h_a1_new : PartialState := PartialState.singletonReg .r1 r1V
  let h_a2_new : PartialState := PartialState.singletonReg .r2 1
  let h_a3_new : PartialState := PartialState.singletonReg .r3 r3V
  let h_a4_new : PartialState := PartialState.singletonReg .r4 r4V
  let h_d0_new : PartialState := PartialState.singletonMemU64 r1V seedPtr
  let h_d1_new : PartialState := PartialState.singletonMemU64 (r1V + 8) seedBytes.size
  let h_s_new  : PartialState := PartialState.singletonMemBytes seedPtr seedBytes
  let h_b3_new : PartialState := PartialState.singletonMem32Bytes r3V pidBytes
  let h_b4_new : PartialState := PartialState.singletonMem32Bytes r4V
    (match Pda.createProgramAddress [seedBytes] pidBytes with | some bs => bs | none => outOldBytes)
  let h_T8_new : PartialState := h_b3_new.union h_b4_new
  let h_T7_new : PartialState := h_s_new.union h_T8_new
  let h_T6_new : PartialState := h_d1_new.union h_T7_new
  let h_T5_new : PartialState := h_d0_new.union h_T6_new
  let h_T4_new : PartialState := h_a4_new.union h_T5_new
  let h_T3_new : PartialState := h_a3_new.union h_T4_new
  let h_T2_new : PartialState := h_a2_new.union h_T3_new
  let h_T1_new : PartialState := h_a1_new.union h_T2_new
  let h_P_new : PartialState := h_a0_new.union h_T1_new
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_⟩
  · rw [hexec]; show s.pc + 1 = pc + 1; rw [hpc]
  · rw [hexec]; show _ = none; rw [h_post_exitCode]; exact hex
  · rw [hexec]
    -- ===== h_R non-ownership facts. =====
    have h_R_no_r0 : h_R.regs .r0 = none := by
      rcases hd_PR.1 .r0 with hl | hr
      · rw [h_P_regs_r0] at hl; nomatch hl
      · exact hr
    have h_R_no_r1 : h_R.regs .r1 = none := by
      rcases hd_PR.1 .r1 with hl | hr
      · rw [h_P_regs_r1] at hl; nomatch hl
      · exact hr
    have h_R_no_r2 : h_R.regs .r2 = none := by
      rcases hd_PR.1 .r2 with hl | hr
      · rw [h_P_regs_r2] at hl; nomatch hl
      · exact hr
    have h_R_no_r3 : h_R.regs .r3 = none := by
      rcases hd_PR.1 .r3 with hl | hr
      · rw [h_P_regs_r3] at hl; nomatch hl
      · exact hr
    have h_R_no_r4 : h_R.regs .r4 = none := by
      rcases hd_PR.1 .r4 with hl | hr
      · rw [h_P_regs_r4] at hl; nomatch hl
      · exact hr
    have h_R_no_pc : h_R.pc = none := hRfree _ h_R_sat
    -- h_R doesn't own mem in any of the 5 regions. Pattern: pick a sentinel
    -- in the atom's range; the SL-disjointness via hd_PR rules out h_R.
    have h_R_no_mem_d0 (a : Nat) (h : r1V ≤ a ∧ a < r1V + 8) : h_R.mem a = none := by
      rcases hd_PR.2.1 a with hl | hr
      · obtain ⟨v, hv⟩ := PartialState.singletonMemU64_mem_isSome r1V seedPtr a h
        have hT5 : h_T5.mem a = some v := by
          rw [← hu_d0_T6]; exact PartialState.union_mem_of_left_some hv
        rw [h_P_mem_eq_T5 a, hT5] at hl; nomatch hl
      · exact hr
    have h_R_no_mem_d1 (a : Nat) (h : r1V + 8 ≤ a ∧ a < r1V + 16) : h_R.mem a = none := by
      rcases hd_PR.2.1 a with hl | hr
      · obtain ⟨v, hv⟩ :=
          PartialState.singletonMemU64_mem_isSome (r1V + 8) seedBytes.size a ⟨h.1, by omega⟩
        have hT6 : h_T6.mem a = some v := by
          rw [← hu_d1_T7]; exact PartialState.union_mem_of_left_some hv
        have hT5 : h_T5.mem a = some v := by
          rw [← hu_d0_T6,
              PartialState.union_mem_of_left_none
                (PartialState.singletonMemU64_mem_outside r1V seedPtr _ (Or.inr (by omega)))]
          exact hT6
        rw [h_P_mem_eq_T5 a, hT5] at hl; nomatch hl
      · exact hr
    have h_R_no_mem_s (a : Nat) (h : seedPtr ≤ a ∧ a < seedPtr + seedBytes.size) :
        h_R.mem a = none := by
      rcases hd_PR.2.1 a with hl | hr
      · obtain ⟨v, hv⟩ := PartialState.singletonMemBytes_mem_isSome seedPtr seedBytes a h
        have hT7 : h_T7.mem a = some v := by
          rw [← hu_s_T8]; exact PartialState.union_mem_of_left_some hv
        have hT6 : h_T6.mem a = some v := by
          rw [← hu_d1_T7,
              PartialState.union_mem_of_left_none
                (PartialState.singletonMemU64_mem_outside (r1V + 8) seedBytes.size _
                  (by have := h_S_not_in_D1 a h.1 h.2; rcases this with h | h
                      · left; exact h
                      · right; omega))]
          exact hT7
        have hT5 : h_T5.mem a = some v := by
          rw [← hu_d0_T6,
              PartialState.union_mem_of_left_none
                (PartialState.singletonMemU64_mem_outside r1V seedPtr _
                  (h_S_not_in_D0 a h.1 h.2))]
          exact hT6
        rw [h_P_mem_eq_T5 a, hT5] at hl; nomatch hl
      · exact hr
    have h_R_no_mem_b3 (a : Nat) (h : r3V ≤ a ∧ a < r3V + 32) : h_R.mem a = none := by
      rcases hd_PR.2.1 a with hl | hr
      · obtain ⟨v, hv⟩ := PartialState.singletonMem32Bytes_mem_isSome r3V pidBytes a h
        have hT8 : h_T8.mem a = some v := by
          rw [← hu_b3_b4]; exact PartialState.union_mem_of_left_some hv
        have hT7 : h_T7.mem a = some v := by
          rw [← hu_s_T8,
              PartialState.union_mem_of_left_none
                (PartialState.singletonMemBytes_mem_outside seedPtr seedBytes _
                  (h_B3_not_in_S a h.1 h.2))]
          exact hT8
        have hT6 : h_T6.mem a = some v := by
          rw [← hu_d1_T7,
              PartialState.union_mem_of_left_none
                (PartialState.singletonMemU64_mem_outside (r1V + 8) seedBytes.size _
                  (by have := h_B3_not_in_D1 a h.1 h.2; rcases this with h | h
                      · left; exact h
                      · right; omega))]
          exact hT7
        have hT5 : h_T5.mem a = some v := by
          rw [← hu_d0_T6,
              PartialState.union_mem_of_left_none
                (PartialState.singletonMemU64_mem_outside r1V seedPtr _
                  (h_B3_not_in_D0 a h.1 h.2))]
          exact hT6
        rw [h_P_mem_eq_T5 a, hT5] at hl; nomatch hl
      · exact hr
    have h_R_no_mem_b4 (a : Nat) (h : r4V ≤ a ∧ a < r4V + 32) : h_R.mem a = none := by
      rcases hd_PR.2.1 a with hl | hr
      · obtain ⟨v, hv⟩ := PartialState.singletonMem32Bytes_mem_isSome r4V outOldBytes a h
        have hT8 : h_T8.mem a = some v := by
          rw [← hu_b3_b4,
              PartialState.union_mem_of_left_none
                (PartialState.singletonMem32Bytes_mem_outside r3V pidBytes _
                  (h_B4_not_in_B3 a h.1 h.2))]
          exact hv
        have hT7 : h_T7.mem a = some v := by
          rw [← hu_s_T8,
              PartialState.union_mem_of_left_none
                (PartialState.singletonMemBytes_mem_outside seedPtr seedBytes _
                  (h_B4_not_in_S a h.1 h.2))]
          exact hT8
        have hT6 : h_T6.mem a = some v := by
          rw [← hu_d1_T7,
              PartialState.union_mem_of_left_none
                (PartialState.singletonMemU64_mem_outside (r1V + 8) seedBytes.size _
                  (by have := h_B4_not_in_D1 a h.1 h.2; rcases this with h | h
                      · left; exact h
                      · right; omega))]
          exact hT7
        have hT5 : h_T5.mem a = some v := by
          rw [← hu_d0_T6,
              PartialState.union_mem_of_left_none
                (PartialState.singletonMemU64_mem_outside r1V seedPtr _
                  (h_B4_not_in_D0 a h.1 h.2))]
          exact hT6
        rw [h_P_mem_eq_T5 a, hT5] at hl; nomatch hl
      · exact hr
    -- ===== "T_k_new has no regs" for the memory-only tail layers. =====
    have h_T8_new_no_regs (r : Reg) : h_T8_new.regs r = none := by
      show ((PartialState.singletonMem32Bytes r3V pidBytes).union h_b4_new).regs r = none
      rw [PartialState.union_regs_of_left_none (PartialState.singletonMem32Bytes_regs r)]
      exact PartialState.singletonMem32Bytes_regs r
    have h_T7_new_no_regs (r : Reg) : h_T7_new.regs r = none := by
      show ((PartialState.singletonMemBytes seedPtr seedBytes).union h_T8_new).regs r = none
      rw [PartialState.union_regs_of_left_none (PartialState.singletonMemBytes_regs r)]
      exact h_T8_new_no_regs r
    have h_T6_new_no_regs (r : Reg) : h_T6_new.regs r = none := by
      show ((PartialState.singletonMemU64 (r1V + 8) seedBytes.size).union h_T7_new).regs r = none
      rw [PartialState.union_regs_of_left_none (PartialState.singletonMemU64_regs r)]
      exact h_T7_new_no_regs r
    have h_T5_new_no_regs (r : Reg) : h_T5_new.regs r = none := by
      show ((PartialState.singletonMemU64 r1V seedPtr).union h_T6_new).regs r = none
      rw [PartialState.union_regs_of_left_none (PartialState.singletonMemU64_regs r)]
      exact h_T6_new_no_regs r
    -- "T_k_new has no pc" (only for the memory-only tails; same shape).
    have h_T8_new_no_pc : h_T8_new.pc = none := by
      show ((PartialState.singletonMem32Bytes r3V pidBytes).union h_b4_new).pc = none
      rw [PartialState.union_pc_of_left_none PartialState.singletonMem32Bytes_pc]
      exact PartialState.singletonMem32Bytes_pc
    have h_T7_new_no_pc : h_T7_new.pc = none := by
      show ((PartialState.singletonMemBytes seedPtr seedBytes).union h_T8_new).pc = none
      rw [PartialState.union_pc_of_left_none PartialState.singletonMemBytes_pc]
      exact h_T8_new_no_pc
    have h_T6_new_no_pc : h_T6_new.pc = none := by
      show ((PartialState.singletonMemU64 (r1V + 8) seedBytes.size).union h_T7_new).pc = none
      rw [PartialState.union_pc_of_left_none PartialState.singletonMemU64_pc]
      exact h_T7_new_no_pc
    have h_T5_new_no_pc : h_T5_new.pc = none := by
      show ((PartialState.singletonMemU64 r1V seedPtr).union h_T6_new).pc = none
      rw [PartialState.union_pc_of_left_none PartialState.singletonMemU64_pc]
      exact h_T6_new_no_pc
    -- ===== Inner disjointness of h_P_new — 9 pairs, bottom-up. =====
    have hd_b3b4_new : h_b3_new.Disjoint h_b4_new := by
      refine ⟨fun r => Or.inl (PartialState.singletonMem32Bytes_regs r),
              fun a => ?_,
              Or.inl PartialState.singletonMem32Bytes_pc⟩
      by_cases ha3 : r3V ≤ a ∧ a < r3V + 32
      · right
        exact PartialState.singletonMem32Bytes_mem_outside r4V _ a
          (h_B3_not_in_B4 a ha3.1 ha3.2)
      · left
        apply PartialState.singletonMem32Bytes_mem_outside
        rcases Nat.lt_or_ge a r3V with hlo | hhi
        · left; exact hlo
        rcases Nat.lt_or_ge a (r3V + 32) with hin | hout
        · exact absurd ⟨hhi, hin⟩ ha3
        · right; exact hout
    have hd_s_T8_new : h_s_new.Disjoint h_T8_new := by
      refine ⟨fun r => Or.inl (PartialState.singletonMemBytes_regs r),
              fun a => ?_,
              Or.inl PartialState.singletonMemBytes_pc⟩
      by_cases hs : seedPtr ≤ a ∧ a < seedPtr + seedBytes.size
      · right
        show h_T8_new.mem a = none
        show ((PartialState.singletonMem32Bytes r3V pidBytes).union h_b4_new).mem a = none
        rw [PartialState.union_mem_of_left_none
            (PartialState.singletonMem32Bytes_mem_outside r3V pidBytes a
              (h_S_not_in_B3 a hs.1 hs.2))]
        exact PartialState.singletonMem32Bytes_mem_outside r4V _ a
          (h_S_not_in_B4 a hs.1 hs.2)
      · left
        apply PartialState.singletonMemBytes_mem_outside
        rcases Nat.lt_or_ge a seedPtr with hlo | hhi
        · left; exact hlo
        rcases Nat.lt_or_ge a (seedPtr + seedBytes.size) with hin | hout
        · exact absurd ⟨hhi, hin⟩ hs
        · right; exact hout
    have hd_d1_T7_new : h_d1_new.Disjoint h_T7_new := by
      refine ⟨fun r => Or.inl (PartialState.singletonMemU64_regs r),
              fun a => ?_,
              Or.inl PartialState.singletonMemU64_pc⟩
      by_cases hd1 : r1V + 8 ≤ a ∧ a < r1V + 16
      · right
        show h_T7_new.mem a = none
        show ((PartialState.singletonMemBytes seedPtr seedBytes).union h_T8_new).mem a = none
        rw [PartialState.union_mem_of_left_none
            (PartialState.singletonMemBytes_mem_outside seedPtr seedBytes a
              (by have := h_D1_not_in_S a hd1.1 hd1.2; rcases this with h | h
                  · left; exact h
                  · right; omega))]
        show h_T8_new.mem a = none
        show ((PartialState.singletonMem32Bytes r3V pidBytes).union h_b4_new).mem a = none
        rw [PartialState.union_mem_of_left_none
            (PartialState.singletonMem32Bytes_mem_outside r3V pidBytes a
              (h_D1_not_in_B3 a hd1.1 hd1.2))]
        exact PartialState.singletonMem32Bytes_mem_outside r4V _ a
          (h_D1_not_in_B4 a hd1.1 hd1.2)
      · left
        apply PartialState.singletonMemU64_mem_outside
        rcases Nat.lt_or_ge a (r1V + 8) with hlo | hhi
        · left; exact hlo
        rcases Nat.lt_or_ge a (r1V + 16) with hin | hout
        · exact absurd ⟨hhi, hin⟩ hd1
        · right; omega
    have hd_d0_T6_new : h_d0_new.Disjoint h_T6_new := by
      refine ⟨fun r => Or.inl (PartialState.singletonMemU64_regs r),
              fun a => ?_,
              Or.inl PartialState.singletonMemU64_pc⟩
      by_cases hd0 : r1V ≤ a ∧ a < r1V + 8
      · right
        show h_T6_new.mem a = none
        show ((PartialState.singletonMemU64 (r1V + 8) seedBytes.size).union h_T7_new).mem a = none
        rw [PartialState.union_mem_of_left_none
            (PartialState.singletonMemU64_mem_outside (r1V + 8) seedBytes.size a
              (Or.inl (by omega)))]
        show h_T7_new.mem a = none
        show ((PartialState.singletonMemBytes seedPtr seedBytes).union h_T8_new).mem a = none
        rw [PartialState.union_mem_of_left_none
            (PartialState.singletonMemBytes_mem_outside seedPtr seedBytes a
              (h_D0_not_in_S a hd0.1 hd0.2))]
        show h_T8_new.mem a = none
        show ((PartialState.singletonMem32Bytes r3V pidBytes).union h_b4_new).mem a = none
        rw [PartialState.union_mem_of_left_none
            (PartialState.singletonMem32Bytes_mem_outside r3V pidBytes a
              (h_D0_not_in_B3 a hd0.1 hd0.2))]
        exact PartialState.singletonMem32Bytes_mem_outside r4V _ a
          (h_D0_not_in_B4 a hd0.1 hd0.2)
      · left
        apply PartialState.singletonMemU64_mem_outside
        rcases Nat.lt_or_ge a r1V with hlo | hhi
        · left; exact hlo
        rcases Nat.lt_or_ge a (r1V + 8) with hin | hout
        · exact absurd ⟨hhi, hin⟩ hd0
        · right; exact hout
    have hd_a4_T5_new : h_a4_new.Disjoint h_T5_new := by
      refine ⟨fun r => Or.inr (h_T5_new_no_regs r),
              fun a => Or.inl (PartialState.singletonReg_mem a),
              Or.inl PartialState.singletonReg_pc⟩
    have hd_a3_T4_new : h_a3_new.Disjoint h_T4_new := by
      refine ⟨fun r => ?_,
              fun a => Or.inl (PartialState.singletonReg_mem a),
              Or.inl PartialState.singletonReg_pc⟩
      by_cases hr : r = .r3
      · right; rw [hr]
        show ((PartialState.singletonReg .r4 r4V).union h_T5_new).regs .r3 = none
        rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r3 ≠ Reg.r4))]
        exact h_T5_new_no_regs _
      · left; exact PartialState.singletonReg_regs_other hr
    have hd_a2_T3_new : h_a2_new.Disjoint h_T3_new := by
      refine ⟨fun r => ?_,
              fun a => Or.inl (PartialState.singletonReg_mem a),
              Or.inl PartialState.singletonReg_pc⟩
      by_cases hr : r = .r2
      · right; rw [hr]
        show ((PartialState.singletonReg .r3 r3V).union h_T4_new).regs .r2 = none
        rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r2 ≠ Reg.r3))]
        show ((PartialState.singletonReg .r4 r4V).union h_T5_new).regs .r2 = none
        rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r2 ≠ Reg.r4))]
        exact h_T5_new_no_regs _
      · left; exact PartialState.singletonReg_regs_other hr
    have hd_a1_T2_new : h_a1_new.Disjoint h_T2_new := by
      refine ⟨fun r => ?_,
              fun a => Or.inl (PartialState.singletonReg_mem a),
              Or.inl PartialState.singletonReg_pc⟩
      by_cases hr : r = .r1
      · right; rw [hr]
        show ((PartialState.singletonReg .r2 1).union h_T3_new).regs .r1 = none
        rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r1 ≠ Reg.r2))]
        show ((PartialState.singletonReg .r3 r3V).union h_T4_new).regs .r1 = none
        rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r1 ≠ Reg.r3))]
        show ((PartialState.singletonReg .r4 r4V).union h_T5_new).regs .r1 = none
        rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r1 ≠ Reg.r4))]
        exact h_T5_new_no_regs _
      · left; exact PartialState.singletonReg_regs_other hr
    have hd_a0_T1_new : h_a0_new.Disjoint h_T1_new := by
      refine ⟨fun r => ?_,
              fun a => Or.inl (PartialState.singletonReg_mem a),
              Or.inl PartialState.singletonReg_pc⟩
      by_cases hr : r = .r0
      · right; rw [hr]
        show ((PartialState.singletonReg .r1 r1V).union h_T2_new).regs .r0 = none
        rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r0 ≠ Reg.r1))]
        show ((PartialState.singletonReg .r2 1).union h_T3_new).regs .r0 = none
        rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r0 ≠ Reg.r2))]
        show ((PartialState.singletonReg .r3 r3V).union h_T4_new).regs .r0 = none
        rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r0 ≠ Reg.r3))]
        show ((PartialState.singletonReg .r4 r4V).union h_T5_new).regs .r0 = none
        rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r0 ≠ Reg.r4))]
        exact h_T5_new_no_regs _
      · left; exact PartialState.singletonReg_regs_other hr
    -- ===== h_P_new structural helpers. =====
    -- pc: no atom owns pc.
    have h_P_new_pc : h_P_new.pc = none := by
      show ((PartialState.singletonReg .r0 _).union h_T1_new).pc = none
      rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
      show ((PartialState.singletonReg .r1 r1V).union h_T2_new).pc = none
      rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
      show ((PartialState.singletonReg .r2 1).union h_T3_new).pc = none
      rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
      show ((PartialState.singletonReg .r3 r3V).union h_T4_new).pc = none
      rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
      show ((PartialState.singletonReg .r4 r4V).union h_T5_new).pc = none
      rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
      exact h_T5_new_no_pc
    -- regs: own exactly r0, r1, r2, r3, r4.
    have h_P_new_regs_r0 :
        h_P_new.regs .r0 = some
          (match Pda.createProgramAddress [seedBytes] pidBytes with | some _ => 0 | none => 1) :=
      PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
    have h_P_new_regs_r1 : h_P_new.regs .r1 = some r1V := by
      show ((PartialState.singletonReg .r0 _).union h_T1_new).regs .r1 = some r1V
      rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r1 ≠ Reg.r0))]
      exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
    have h_P_new_regs_r2 : h_P_new.regs .r2 = some 1 := by
      show ((PartialState.singletonReg .r0 _).union h_T1_new).regs .r2 = some 1
      rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r2 ≠ Reg.r0))]
      show ((PartialState.singletonReg .r1 r1V).union h_T2_new).regs .r2 = some 1
      rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r2 ≠ Reg.r1))]
      exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
    have h_P_new_regs_r3 : h_P_new.regs .r3 = some r3V := by
      show ((PartialState.singletonReg .r0 _).union h_T1_new).regs .r3 = some r3V
      rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r3 ≠ Reg.r0))]
      show ((PartialState.singletonReg .r1 r1V).union h_T2_new).regs .r3 = some r3V
      rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r3 ≠ Reg.r1))]
      show ((PartialState.singletonReg .r2 1).union h_T3_new).regs .r3 = some r3V
      rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r3 ≠ Reg.r2))]
      exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
    have h_P_new_regs_r4 : h_P_new.regs .r4 = some r4V := by
      show ((PartialState.singletonReg .r0 _).union h_T1_new).regs .r4 = some r4V
      rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r4 ≠ Reg.r0))]
      show ((PartialState.singletonReg .r1 r1V).union h_T2_new).regs .r4 = some r4V
      rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r4 ≠ Reg.r1))]
      show ((PartialState.singletonReg .r2 1).union h_T3_new).regs .r4 = some r4V
      rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r4 ≠ Reg.r2))]
      show ((PartialState.singletonReg .r3 r3V).union h_T4_new).regs .r4 = some r4V
      rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r4 ≠ Reg.r3))]
      exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
    have h_P_new_regs_other (r : Reg)
        (h0 : r ≠ .r0) (h1 : r ≠ .r1) (h2 : r ≠ .r2) (h3 : r ≠ .r3) (h4 : r ≠ .r4) :
        h_P_new.regs r = none := by
      show ((PartialState.singletonReg .r0 _).union h_T1_new).regs r = none
      rw [PartialState.union_regs_of_left_none (PartialState.singletonReg_regs_other h0)]
      show ((PartialState.singletonReg .r1 r1V).union h_T2_new).regs r = none
      rw [PartialState.union_regs_of_left_none (PartialState.singletonReg_regs_other h1)]
      show ((PartialState.singletonReg .r2 1).union h_T3_new).regs r = none
      rw [PartialState.union_regs_of_left_none (PartialState.singletonReg_regs_other h2)]
      show ((PartialState.singletonReg .r3 r3V).union h_T4_new).regs r = none
      rw [PartialState.union_regs_of_left_none (PartialState.singletonReg_regs_other h3)]
      show ((PartialState.singletonReg .r4 r4V).union h_T5_new).regs r = none
      rw [PartialState.union_regs_of_left_none (PartialState.singletonReg_regs_other h4)]
      exact h_T5_new_no_regs r
    -- h_P_new.mem unfolded through reg layers to h_T5_new.
    have h_P_new_mem_eq_T5_new (a : Nat) : h_P_new.mem a = h_T5_new.mem a := by
      show ((PartialState.singletonReg .r0 _).union h_T1_new).mem a = h_T5_new.mem a
      rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
      show ((PartialState.singletonReg .r1 r1V).union h_T2_new).mem a = h_T5_new.mem a
      rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
      show ((PartialState.singletonReg .r2 1).union h_T3_new).mem a = h_T5_new.mem a
      rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
      show ((PartialState.singletonReg .r3 r3V).union h_T4_new).mem a = h_T5_new.mem a
      rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
      show ((PartialState.singletonReg .r4 r4V).union h_T5_new).mem a = h_T5_new.mem a
      rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
    -- h_T5_new mem at descriptor.ptr range
    have h_T5_new_mem_d0_some (a : Nat) (h : r1V ≤ a ∧ a < r1V + 8) :
        ∃ v, h_T5_new.mem a = some v := by
      obtain ⟨v, hv⟩ := PartialState.singletonMemU64_mem_isSome r1V seedPtr a h
      exact ⟨v, PartialState.union_mem_of_left_some hv⟩
    -- h_T5_new mem at descriptor.len range
    have h_T5_new_mem_d1_some (a : Nat) (h : r1V + 8 ≤ a ∧ a < r1V + 16) :
        ∃ v, h_T5_new.mem a = some v := by
      obtain ⟨v, hv⟩ :=
        PartialState.singletonMemU64_mem_isSome (r1V + 8) seedBytes.size a ⟨h.1, by omega⟩
      have hT6 : h_T6_new.mem a = some v :=
        PartialState.union_mem_of_left_some hv
      refine ⟨v, ?_⟩
      show ((PartialState.singletonMemU64 r1V seedPtr).union h_T6_new).mem a = some v
      rw [PartialState.union_mem_of_left_none
          (PartialState.singletonMemU64_mem_outside r1V seedPtr a (Or.inr (by omega)))]
      exact hT6
    -- h_T5_new mem at seed range
    have h_T5_new_mem_seed (i : Nat) (hi : i < seedBytes.size) :
        h_T5_new.mem (seedPtr + i) = some (seedBytes.get! i).toNat := by
      have h_in : seedPtr ≤ seedPtr + i ∧ seedPtr + i < seedPtr + seedBytes.size := ⟨Nat.le_add_right _ _, by omega⟩
      have hT7 : h_T7_new.mem (seedPtr + i) = some (seedBytes.get! i).toNat :=
        PartialState.union_mem_of_left_some
          (PartialState.singletonMemBytes_mem_at seedPtr seedBytes i hi)
      have hT6 : h_T6_new.mem (seedPtr + i) = some (seedBytes.get! i).toNat := by
        show ((PartialState.singletonMemU64 (r1V + 8) seedBytes.size).union h_T7_new).mem _ = _
        rw [PartialState.union_mem_of_left_none
            (PartialState.singletonMemU64_mem_outside (r1V + 8) seedBytes.size _
              (by have := h_S_not_in_D1 (seedPtr + i) h_in.1 h_in.2
                  rcases this with h | h
                  · left; exact h
                  · right; omega))]
        exact hT7
      show ((PartialState.singletonMemU64 r1V seedPtr).union h_T6_new).mem _ = _
      rw [PartialState.union_mem_of_left_none
          (PartialState.singletonMemU64_mem_outside r1V seedPtr _
            (h_S_not_in_D0 (seedPtr + i) h_in.1 h_in.2))]
      exact hT6
    -- h_T5_new mem at pid range
    have h_T5_new_mem_pid (i : Nat) (hi : i < 32) :
        h_T5_new.mem (r3V + i) = some (pidBytes.get! i).toNat := by
      have h_in : r3V ≤ r3V + i ∧ r3V + i < r3V + 32 := ⟨Nat.le_add_right _ _, by omega⟩
      have hT8 : h_T8_new.mem (r3V + i) = some (pidBytes.get! i).toNat :=
        PartialState.union_mem_of_left_some
          (PartialState.singletonMem32Bytes_mem_at r3V pidBytes i hi)
      have hT7 : h_T7_new.mem (r3V + i) = some (pidBytes.get! i).toNat := by
        show ((PartialState.singletonMemBytes seedPtr seedBytes).union h_T8_new).mem _ = _
        rw [PartialState.union_mem_of_left_none
            (PartialState.singletonMemBytes_mem_outside seedPtr seedBytes _
              (h_B3_not_in_S (r3V + i) h_in.1 h_in.2))]
        exact hT8
      have hT6 : h_T6_new.mem (r3V + i) = some (pidBytes.get! i).toNat := by
        show ((PartialState.singletonMemU64 (r1V + 8) seedBytes.size).union h_T7_new).mem _ = _
        rw [PartialState.union_mem_of_left_none
            (PartialState.singletonMemU64_mem_outside (r1V + 8) seedBytes.size _
              (by have := h_B3_not_in_D1 (r3V + i) h_in.1 h_in.2
                  rcases this with h | h
                  · left; exact h
                  · right; omega))]
        exact hT7
      show ((PartialState.singletonMemU64 r1V seedPtr).union h_T6_new).mem _ = _
      rw [PartialState.union_mem_of_left_none
          (PartialState.singletonMemU64_mem_outside r1V seedPtr _
            (h_B3_not_in_D0 (r3V + i) h_in.1 h_in.2))]
      exact hT6
    -- h_T5_new mem at output range — uses the NEW bytes (= match cpa with | some bs => bs | none => outOldBytes).
    have h_T5_new_mem_out (i : Nat) (hi : i < 32) :
        h_T5_new.mem (r4V + i) = some
          ((match Pda.createProgramAddress [seedBytes] pidBytes with
            | some bs => bs | none => outOldBytes).get! i).toNat := by
      have h_in : r4V ≤ r4V + i ∧ r4V + i < r4V + 32 := ⟨Nat.le_add_right _ _, by omega⟩
      have hT8 : h_T8_new.mem (r4V + i) = some
          ((match Pda.createProgramAddress [seedBytes] pidBytes with
            | some bs => bs | none => outOldBytes).get! i).toNat := by
        show ((PartialState.singletonMem32Bytes r3V pidBytes).union h_b4_new).mem _ = _
        rw [PartialState.union_mem_of_left_none
            (PartialState.singletonMem32Bytes_mem_outside r3V pidBytes _
              (h_B4_not_in_B3 (r4V + i) h_in.1 h_in.2))]
        exact PartialState.singletonMem32Bytes_mem_at r4V _ i hi
      have hT7 : h_T7_new.mem (r4V + i) = some
          ((match Pda.createProgramAddress [seedBytes] pidBytes with
            | some bs => bs | none => outOldBytes).get! i).toNat := by
        show ((PartialState.singletonMemBytes seedPtr seedBytes).union h_T8_new).mem _ = _
        rw [PartialState.union_mem_of_left_none
            (PartialState.singletonMemBytes_mem_outside seedPtr seedBytes _
              (h_B4_not_in_S (r4V + i) h_in.1 h_in.2))]
        exact hT8
      have hT6 : h_T6_new.mem (r4V + i) = some
          ((match Pda.createProgramAddress [seedBytes] pidBytes with
            | some bs => bs | none => outOldBytes).get! i).toNat := by
        show ((PartialState.singletonMemU64 (r1V + 8) seedBytes.size).union h_T7_new).mem _ = _
        rw [PartialState.union_mem_of_left_none
            (PartialState.singletonMemU64_mem_outside (r1V + 8) seedBytes.size _
              (by have := h_B4_not_in_D1 (r4V + i) h_in.1 h_in.2
                  rcases this with h | h
                  · left; exact h
                  · right; omega))]
        exact hT7
      show ((PartialState.singletonMemU64 r1V seedPtr).union h_T6_new).mem _ = _
      rw [PartialState.union_mem_of_left_none
          (PartialState.singletonMemU64_mem_outside r1V seedPtr _
            (h_B4_not_in_D0 (r4V + i) h_in.1 h_in.2))]
      exact hT6
    -- h_T5_new mem outside all 5 ranges = none.
    have h_T5_new_mem_outside (a : Nat)
        (h_d0 : a < r1V ∨ a ≥ r1V + 8)
        (h_d1 : a < r1V + 8 ∨ a ≥ r1V + 16)
        (h_s : a < seedPtr ∨ a ≥ seedPtr + seedBytes.size)
        (h_b3 : a < r3V ∨ a ≥ r3V + 32)
        (h_b4 : a < r4V ∨ a ≥ r4V + 32) :
        h_T5_new.mem a = none := by
      show ((PartialState.singletonMemU64 r1V seedPtr).union h_T6_new).mem a = none
      rw [PartialState.union_mem_of_left_none
          (PartialState.singletonMemU64_mem_outside r1V seedPtr a h_d0)]
      show ((PartialState.singletonMemU64 (r1V + 8) seedBytes.size).union h_T7_new).mem a = none
      rw [PartialState.union_mem_of_left_none
          (PartialState.singletonMemU64_mem_outside (r1V + 8) seedBytes.size a h_d1)]
      show ((PartialState.singletonMemBytes seedPtr seedBytes).union h_T8_new).mem a = none
      rw [PartialState.union_mem_of_left_none
          (PartialState.singletonMemBytes_mem_outside seedPtr seedBytes a h_s)]
      show ((PartialState.singletonMem32Bytes r3V pidBytes).union h_b4_new).mem a = none
      rw [PartialState.union_mem_of_left_none
          (PartialState.singletonMem32Bytes_mem_outside r3V pidBytes a h_b3)]
      exact PartialState.singletonMem32Bytes_mem_outside r4V _ a h_b4
    -- ===== Outer disjointness: h_P_new ⊥ h_R. =====
    have hd_PnewR : h_P_new.Disjoint h_R := by
      refine ⟨fun r => ?_, fun a => ?_, ?_⟩
      · by_cases h0 : r = .r0
        · right; rw [h0]; exact h_R_no_r0
        by_cases h1 : r = .r1
        · right; rw [h1]; exact h_R_no_r1
        by_cases h2 : r = .r2
        · right; rw [h2]; exact h_R_no_r2
        by_cases h3 : r = .r3
        · right; rw [h3]; exact h_R_no_r3
        by_cases h4 : r = .r4
        · right; rw [h4]; exact h_R_no_r4
        · left; exact h_P_new_regs_other r h0 h1 h2 h3 h4
      · -- mem: case split on which of the 5 ranges (or outside).
        by_cases ha_d0 : r1V ≤ a ∧ a < r1V + 8
        · right; exact h_R_no_mem_d0 a ha_d0
        by_cases ha_d1 : r1V + 8 ≤ a ∧ a < r1V + 16
        · right; exact h_R_no_mem_d1 a ha_d1
        by_cases ha_s : seedPtr ≤ a ∧ a < seedPtr + seedBytes.size
        · right; exact h_R_no_mem_s a ha_s
        by_cases ha_b3 : r3V ≤ a ∧ a < r3V + 32
        · right; exact h_R_no_mem_b3 a ha_b3
        by_cases ha_b4 : r4V ≤ a ∧ a < r4V + 32
        · right; exact h_R_no_mem_b4 a ha_b4
        · -- outside all 5 ranges
          left
          rw [h_P_new_mem_eq_T5_new]
          apply h_T5_new_mem_outside
          · rcases Nat.lt_or_ge a r1V with h | h
            · left; exact h
            rcases Nat.lt_or_ge a (r1V + 8) with h' | h'
            · exact absurd ⟨h, h'⟩ ha_d0
            · right; exact h'
          · rcases Nat.lt_or_ge a (r1V + 8) with h | h
            · left; exact h
            rcases Nat.lt_or_ge a (r1V + 16) with h' | h'
            · exact absurd ⟨h, h'⟩ ha_d1
            · right; exact h'
          · rcases Nat.lt_or_ge a seedPtr with h | h
            · left; exact h
            rcases Nat.lt_or_ge a (seedPtr + seedBytes.size) with h' | h'
            · exact absurd ⟨h, h'⟩ ha_s
            · right; exact h'
          · rcases Nat.lt_or_ge a r3V with h | h
            · left; exact h
            rcases Nat.lt_or_ge a (r3V + 32) with h' | h'
            · exact absurd ⟨h, h'⟩ ha_b3
            · right; exact h'
          · rcases Nat.lt_or_ge a r4V with h | h
            · left; exact h
            rcases Nat.lt_or_ge a (r4V + 32) with h' | h'
            · exact absurd ⟨h, h'⟩ ha_b4
            · right; exact h'
      · left; exact h_P_new_pc
    -- ===== Provide the (Q ** R).holdsFor witness. =====
    refine ⟨h_P_new.union h_R, ?_, h_P_new, h_R, hd_PnewR, rfl, ?_, h_R_sat⟩
    -- (a) Compat: regs, mem, pc.
    · refine ⟨?_, ?_, ?_⟩
      -- regs
      · intro r vr hvr
        show (commitOptional s r4V 32 (Pda.createProgramAddress [seedBytes] pidBytes)).regs.get r = vr
        by_cases h0 : r = .r0
        · rw [h0] at hvr
          rw [PartialState.union_regs_of_left_some h_P_new_regs_r0] at hvr
          rw [h0, h_post_r0]; exact Option.some.inj hvr
        by_cases h1 : r = .r1
        · rw [h1] at hvr
          rw [PartialState.union_regs_of_left_some h_P_new_regs_r1] at hvr
          rw [h1, h_post_regs_other .r1 (by decide), hs_regs_r1]
          exact Option.some.inj hvr
        by_cases h2 : r = .r2
        · rw [h2] at hvr
          rw [PartialState.union_regs_of_left_some h_P_new_regs_r2] at hvr
          rw [h2, h_post_regs_other .r2 (by decide), hs_regs_r2]
          exact Option.some.inj hvr
        by_cases h3 : r = .r3
        · rw [h3] at hvr
          rw [PartialState.union_regs_of_left_some h_P_new_regs_r3] at hvr
          rw [h3, h_post_regs_other .r3 (by decide), hs_regs_r3]
          exact Option.some.inj hvr
        by_cases h4 : r = .r4
        · rw [h4] at hvr
          rw [PartialState.union_regs_of_left_some h_P_new_regs_r4] at hvr
          rw [h4, h_post_regs_other .r4 (by decide), hs_regs_r4]
          exact Option.some.inj hvr
        · -- r ∉ {r0..r4}: h_P_new doesn't own; h_R owns.
          rw [PartialState.union_regs_of_left_none
              (h_P_new_regs_other r h0 h1 h2 h3 h4)] at hvr
          rw [h_post_regs_other r h0]
          have h_P_none : h_P.regs r = none := by
            rcases hd_PR.1 r with hl | hr
            · exact hl
            · rw [hr] at hvr; nomatch hvr
          exact hcr_regs r vr (by rw [← hu_PR,
              PartialState.union_regs_of_left_none h_P_none]; exact hvr)
      -- mem
      · intro a vm hvm
        show (commitOptional s r4V 32 (Pda.createProgramAddress [seedBytes] pidBytes)).mem a = vm
        by_cases ha_d0 : r1V ≤ a ∧ a < r1V + 8
        · obtain ⟨v_atom, hv_atom⟩ :=
            PartialState.singletonMemU64_mem_isSome r1V seedPtr a ha_d0
          have h_P_new_a : h_P_new.mem a = some v_atom := by
            rw [h_P_new_mem_eq_T5_new]
            show ((PartialState.singletonMemU64 r1V seedPtr).union h_T6_new).mem a = _
            exact PartialState.union_mem_of_left_some hv_atom
          have hp_a : hp.mem a = some v_atom := by
            rw [← hu_PR]
            apply PartialState.union_mem_of_left_some
            rw [h_P_mem_eq_T5 a, ← hu_d0_T6]
            exact PartialState.union_mem_of_left_some hv_atom
          rw [PartialState.union_mem_of_left_some h_P_new_a] at hvm
          rw [h_post_mem_outside a (h_D0_not_in_B4 a ha_d0.1 ha_d0.2)]
          exact (hcm_mem a v_atom hp_a).trans (Option.some.inj hvm)
        by_cases ha_d1 : r1V + 8 ≤ a ∧ a < r1V + 16
        · obtain ⟨v_atom, hv_atom⟩ :=
            PartialState.singletonMemU64_mem_isSome (r1V + 8) seedBytes.size a ⟨ha_d1.1, by omega⟩
          have h_P_new_a : h_P_new.mem a = some v_atom := by
            rw [h_P_new_mem_eq_T5_new]
            show ((PartialState.singletonMemU64 r1V seedPtr).union h_T6_new).mem a = _
            rw [PartialState.union_mem_of_left_none
                (PartialState.singletonMemU64_mem_outside r1V seedPtr a (Or.inr (by omega)))]
            show ((PartialState.singletonMemU64 (r1V + 8) seedBytes.size).union h_T7_new).mem a = _
            exact PartialState.union_mem_of_left_some hv_atom
          have hp_a : hp.mem a = some v_atom := by
            rw [← hu_PR]
            apply PartialState.union_mem_of_left_some
            rw [h_P_mem_eq_T5 a, ← hu_d0_T6,
                PartialState.union_mem_of_left_none
                  (PartialState.singletonMemU64_mem_outside r1V seedPtr a (Or.inr (by omega))),
                ← hu_d1_T7]
            exact PartialState.union_mem_of_left_some hv_atom
          rw [PartialState.union_mem_of_left_some h_P_new_a] at hvm
          rw [h_post_mem_outside a (h_D1_not_in_B4 a ha_d1.1 ha_d1.2)]
          exact (hcm_mem a v_atom hp_a).trans (Option.some.inj hvm)
        by_cases ha_s : seedPtr ≤ a ∧ a < seedPtr + seedBytes.size
        · -- Same S atom in P and Q (seed bytes unchanged). commitOptional doesn't touch S range.
          obtain ⟨v_atom, hv_atom⟩ :=
            PartialState.singletonMemBytes_mem_isSome seedPtr seedBytes a ha_s
          have h_D1_outside : a < r1V + 8 ∨ a ≥ r1V + 8 + 8 := by
            have := h_S_not_in_D1 a ha_s.1 ha_s.2; rcases this with h | h
            · left; exact h
            · right; omega
          have h_P_new_a : h_P_new.mem a = some v_atom := by
            rw [h_P_new_mem_eq_T5_new]
            show ((PartialState.singletonMemU64 r1V seedPtr).union h_T6_new).mem a = _
            rw [PartialState.union_mem_of_left_none
                (PartialState.singletonMemU64_mem_outside r1V seedPtr a
                  (h_S_not_in_D0 a ha_s.1 ha_s.2))]
            show ((PartialState.singletonMemU64 (r1V + 8) seedBytes.size).union h_T7_new).mem a = _
            rw [PartialState.union_mem_of_left_none
                (PartialState.singletonMemU64_mem_outside (r1V + 8) seedBytes.size a h_D1_outside)]
            show ((PartialState.singletonMemBytes seedPtr seedBytes).union h_T8_new).mem a = _
            exact PartialState.union_mem_of_left_some hv_atom
          have hp_a : hp.mem a = some v_atom := by
            rw [← hu_PR]
            apply PartialState.union_mem_of_left_some
            rw [h_P_mem_eq_T5 a, ← hu_d0_T6,
                PartialState.union_mem_of_left_none
                  (PartialState.singletonMemU64_mem_outside r1V seedPtr a
                    (h_S_not_in_D0 a ha_s.1 ha_s.2)),
                ← hu_d1_T7,
                PartialState.union_mem_of_left_none
                  (PartialState.singletonMemU64_mem_outside (r1V + 8) seedBytes.size a h_D1_outside),
                ← hu_s_T8]
            exact PartialState.union_mem_of_left_some hv_atom
          rw [PartialState.union_mem_of_left_some h_P_new_a] at hvm
          rw [h_post_mem_outside a (h_S_not_in_B4 a ha_s.1 ha_s.2)]
          exact (hcm_mem a v_atom hp_a).trans (Option.some.inj hvm)
        by_cases ha_b3 : r3V ≤ a ∧ a < r3V + 32
        · -- Same B3 atom (pid bytes unchanged); commitOptional doesn't touch B3 range.
          obtain ⟨v_atom, hv_atom⟩ :=
            PartialState.singletonMem32Bytes_mem_isSome r3V pidBytes a ha_b3
          have h_D1_outside : a < r1V + 8 ∨ a ≥ r1V + 8 + 8 := by
            have := h_B3_not_in_D1 a ha_b3.1 ha_b3.2; rcases this with h | h
            · left; exact h
            · right; omega
          have h_P_new_a : h_P_new.mem a = some v_atom := by
            rw [h_P_new_mem_eq_T5_new]
            show ((PartialState.singletonMemU64 r1V seedPtr).union h_T6_new).mem a = _
            rw [PartialState.union_mem_of_left_none
                (PartialState.singletonMemU64_mem_outside r1V seedPtr a
                  (h_B3_not_in_D0 a ha_b3.1 ha_b3.2))]
            show ((PartialState.singletonMemU64 (r1V + 8) seedBytes.size).union h_T7_new).mem a = _
            rw [PartialState.union_mem_of_left_none
                (PartialState.singletonMemU64_mem_outside (r1V + 8) seedBytes.size a h_D1_outside)]
            show ((PartialState.singletonMemBytes seedPtr seedBytes).union h_T8_new).mem a = _
            rw [PartialState.union_mem_of_left_none
                (PartialState.singletonMemBytes_mem_outside seedPtr seedBytes a
                  (h_B3_not_in_S a ha_b3.1 ha_b3.2))]
            show ((PartialState.singletonMem32Bytes r3V pidBytes).union h_b4_new).mem a = _
            exact PartialState.union_mem_of_left_some hv_atom
          have hp_a : hp.mem a = some v_atom := by
            rw [← hu_PR]
            apply PartialState.union_mem_of_left_some
            rw [h_P_mem_eq_T5 a, ← hu_d0_T6,
                PartialState.union_mem_of_left_none
                  (PartialState.singletonMemU64_mem_outside r1V seedPtr a
                    (h_B3_not_in_D0 a ha_b3.1 ha_b3.2)),
                ← hu_d1_T7,
                PartialState.union_mem_of_left_none
                  (PartialState.singletonMemU64_mem_outside (r1V + 8) seedBytes.size a h_D1_outside),
                ← hu_s_T8,
                PartialState.union_mem_of_left_none
                  (PartialState.singletonMemBytes_mem_outside seedPtr seedBytes a
                    (h_B3_not_in_S a ha_b3.1 ha_b3.2)),
                ← hu_b3_b4]
            exact PartialState.union_mem_of_left_some hv_atom
          rw [PartialState.union_mem_of_left_some h_P_new_a] at hvm
          rw [h_post_mem_outside a (h_B3_not_in_B4 a ha_b3.1 ha_b3.2)]
          exact (hcm_mem a v_atom hp_a).trans (Option.some.inj hvm)
        by_cases ha_b4 : r4V ≤ a ∧ a < r4V + 32
        · -- Output range: B4 atom CHANGES (newOutBytes vs outOldBytes). commitOptional writes.
          have h_i_lt : a - r4V < 32 := by omega
          have h_a_eq : r4V + (a - r4V) = a := by omega
          -- Use h_T5_new_mem_out which gives the NEW bytes at r4V + i.
          have h_T5_mem : h_T5_new.mem a = some
              ((match Pda.createProgramAddress [seedBytes] pidBytes with
                | some bs => bs | none => outOldBytes).get! (a - r4V)).toNat := by
            have := h_T5_new_mem_out (a - r4V) h_i_lt
            rw [h_a_eq] at this; exact this
          have h_P_new_a : h_P_new.mem a = some
              ((match Pda.createProgramAddress [seedBytes] pidBytes with
                | some bs => bs | none => outOldBytes).get! (a - r4V)).toNat :=
            (h_P_new_mem_eq_T5_new a).trans h_T5_mem
          rw [PartialState.union_mem_of_left_some h_P_new_a] at hvm
          rw [show a = r4V + (a - r4V) from by omega, h_post_mem_r4 _ h_i_lt]
          exact Option.some.inj hvm
        · -- Outside all 5 ranges: h_P_new doesn't own; h_R owns. commitOptional unchanged.
          have h3_out : a < r3V ∨ a ≥ r3V + 32 := by
            rcases Nat.lt_or_ge a r3V with h | h
            · left; exact h
            rcases Nat.lt_or_ge a (r3V + 32) with h' | h'
            · exact absurd ⟨h, h'⟩ ha_b3
            · right; exact h'
          have h4_out : a < r4V ∨ a ≥ r4V + 32 := by
            rcases Nat.lt_or_ge a r4V with h | h
            · left; exact h
            rcases Nat.lt_or_ge a (r4V + 32) with h' | h'
            · exact absurd ⟨h, h'⟩ ha_b4
            · right; exact h'
          have h_d0_out : a < r1V ∨ a ≥ r1V + 8 := by
            rcases Nat.lt_or_ge a r1V with h | h
            · left; exact h
            rcases Nat.lt_or_ge a (r1V + 8) with h' | h'
            · exact absurd ⟨h, h'⟩ ha_d0
            · right; exact h'
          have h_d1_out : a < r1V + 8 ∨ a ≥ r1V + 16 := by
            rcases Nat.lt_or_ge a (r1V + 8) with h | h
            · left; exact h
            rcases Nat.lt_or_ge a (r1V + 16) with h' | h'
            · exact absurd ⟨h, h'⟩ ha_d1
            · right; exact h'
          have h_s_out : a < seedPtr ∨ a ≥ seedPtr + seedBytes.size := by
            rcases Nat.lt_or_ge a seedPtr with h | h
            · left; exact h
            rcases Nat.lt_or_ge a (seedPtr + seedBytes.size) with h' | h'
            · exact absurd ⟨h, h'⟩ ha_s
            · right; exact h'
          have h_P_new_none : h_P_new.mem a = none := by
            rw [h_P_new_mem_eq_T5_new]
            exact h_T5_new_mem_outside a h_d0_out h_d1_out h_s_out h3_out h4_out
          rw [PartialState.union_mem_of_left_none h_P_new_none] at hvm
          rw [h_post_mem_outside a h4_out]
          have h_P_none : h_P.mem a = none := by
            rcases hd_PR.2.1 a with hl | hr
            · exact hl
            · rw [hr] at hvm; nomatch hvm
          exact hcm_mem a vm (by rw [← hu_PR,
              PartialState.union_mem_of_left_none h_P_none]; exact hvm)
      -- pc
      · intro vp hvp
        rw [PartialState.union_pc_of_left_none h_P_new_pc] at hvp
        rw [h_R_no_pc] at hvp
        nomatch hvp
    -- (b) Q h_P_new — provide the 10-deep nested witnesses.
    · refine ⟨h_a0_new, h_T1_new, hd_a0_T1_new, rfl, rfl,
              h_a1_new, h_T2_new, hd_a1_T2_new, rfl, rfl,
              h_a2_new, h_T3_new, hd_a2_T3_new, rfl, rfl,
              h_a3_new, h_T4_new, hd_a3_T4_new, rfl, rfl,
              h_a4_new, h_T5_new, hd_a4_T5_new, rfl, rfl,
              h_d0_new, h_T6_new, hd_d0_T6_new, rfl, rfl,
              h_d1_new, h_T7_new, hd_d1_T7_new, rfl, rfl,
              h_s_new,  h_T8_new, hd_s_T8_new,  rfl, rfl,
              h_b3_new, h_b4_new, hd_b3b4_new, rfl, rfl, rfl⟩

/-! ## Generic fixed-payload-write helper: `cuTripleWithin_syscall_writesR1Bytes`

The 6 fixed-payload sysvars (4 zero-fill: `sol_get_last_restart_slot`,
`sol_get_fees_sysvar`, `sol_get_clock_sysvar`, `sol_get_epoch_rewards_sysvar`
+ 2 non-zero-fill: `sol_get_rent_sysvar`, `sol_get_epoch_schedule_sysvar`)
all share the same Hoare-triple shape: write a fixed `ByteArray` payload
of size `N` at `*r1`, set `r0 := 0`. This helper captures that pattern
parametrically in `(sc, bsNew)`, using the generic `↦Bytes` atom so the
proof scales to 17B / 40B / 81B without per-byte case ladders.

The zero-fill case is the special instantiation `bsNew := zerosByteArray N`. -/

/-- `ByteArray` of `N` zero bytes. Used as the post-state byte payload
    in zero-fill sysvar Hoare triples. -/
def zerosByteArray (N : Nat) : ByteArray :=
  ⟨Array.replicate N (0 : UInt8)⟩

@[simp] theorem zerosByteArray_size (N : Nat) :
    (zerosByteArray N).size = N := by
  show (Array.replicate N (0 : UInt8)).size = N
  exact Array.size_replicate

theorem zerosByteArray_get! (N i : Nat) (hi : i < N) :
    (zerosByteArray N).get! i = (0 : UInt8) := by
  show (Array.replicate N (0 : UInt8))[i]! = 0
  rw [getElem!_pos _ _ (by rw [Array.size_replicate]; exact hi)]
  exact Array.getElem_replicate _

/-- `ByteArray` of `n` copies of byte `b`. Generalizes `zerosByteArray`
    to an arbitrary fill byte. Used as the post-state payload for
    `sol_memset_` Hoare triples. -/
def replicateByte (b : UInt8) (n : Nat) : ByteArray :=
  ⟨Array.replicate n b⟩

@[simp] theorem replicateByte_size (b : UInt8) (n : Nat) :
    (replicateByte b n).size = n := by
  show (Array.replicate n b).size = n
  exact Array.size_replicate

theorem replicateByte_get! (b : UInt8) (n i : Nat) (hi : i < n) :
    (replicateByte b n).get! i = b := by
  show (Array.replicate n b)[i]! = b
  rw [getElem!_pos _ _ (by rw [Array.size_replicate]; exact hi)]
  exact Array.getElem_replicate _

/-- Bridge lemma: `Mem.read` on a coerced bare `Nat → Nat` function
    equals the function applied. The closure-style memory writes in
    `Sysvar.zeroFillR1` produce a `Mem` of the form `↑(fun a => ...)`,
    so reads fall through `default` (the HashMap overlay is empty).

    Used by every fixed-payload sysvar spec to discharge the post-mem
    evaluation. -/
private theorem Mem_read_default (f : Nat → Nat) (a : Nat) :
    ({ default := f } : Memory.Mem).read a = f a := by
  unfold Memory.Mem.read
  simp

/-- For any syscall `sc` whose `step` semantics:
    • writes 0 to register r0,
    • writes the bytes of `bsNew` at `[s.regs.r1, s.regs.r1 + bsNew.size)`,
    • leaves all other memory untouched,
    • advances pc by 1,
    • preserves the (none) exit code,
    the Hoare triple

      `(r0 ↦ᵣ r0Old) ** (r1 ↦ᵣ r1V) ** (r1V ↦Bytes bsOld)`
      ↓
      `(r0 ↦ᵣ 0)     ** (r1 ↦ᵣ r1V) ** (r1V ↦Bytes bsNew)`

    holds for any precondition byte payload `bsOld` of the same size as `bsNew`.

    Concrete sysvar specs supply the step-projection lemmas via
    `simp [step, execSyscall, Sysvar.execX]`. The zero-fill case
    is just `bsNew := zerosByteArray N`. -/
theorem cuTripleWithin_syscall_writesR1Bytes
    (sc : Syscall) (bsNew : ByteArray) (pc : Nat)
    (h_step_regs : ∀ s : State, (step (.call sc) s).regs = s.regs.set .r0 0)
    (h_step_mem_in  : ∀ s : State, ∀ i, i < bsNew.size →
        (step (.call sc) s).mem (s.regs.r1 + i) = (bsNew.get! i).toNat)
    (h_step_mem_out : ∀ s : State, ∀ a,
        (a < s.regs.r1 ∨ a ≥ s.regs.r1 + bsNew.size) →
        (step (.call sc) s).mem a = s.mem a)
    (h_step_pc   : ∀ s : State, (step (.call sc) s).pc = s.pc + 1)
    (h_step_exit : ∀ s : State, s.exitCode = none →
        (step (.call sc) s).exitCode = none) :
    ∀ r0Old r1V (bsOld : ByteArray), bsOld.size = bsNew.size →
      cuTripleWithin 1 pc (pc + 1)
        (CodeReq.singleton pc (.call sc))
        ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1V) ** (r1V ↦Bytes bsOld))
        ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ r1V) ** (r1V ↦Bytes bsNew)) := by
  intro r0Old r1V bsOld hbsSize R hRfree fetch hcr s hPR hpc hex
  let N : Nat := bsNew.size
  -- ==== Phase 1: destructure the 3-atom (P ** R) split. ====
  obtain ⟨hp, hcompat, h_P, h_R, hd_PR, hu_PR, h_P_sat, h_R_sat⟩ := hPR
  obtain ⟨h_r0, h_T1, hd_r0_T1, hu_r0_T1, h_r0_pred, h_T1_sat⟩ := h_P_sat
  obtain ⟨h_r1, h_b, hd_r1_b, hu_r1_b, h_r1_pred, h_b_pred⟩ := h_T1_sat
  rw [h_r0_pred] at hu_r0_T1 hd_r0_T1
  rw [h_r1_pred] at hu_r1_b hd_r1_b
  rw [h_b_pred] at hu_r1_b hd_r1_b
  clear h_r0_pred h_r1_pred h_b_pred h_r0 h_r1 h_b
  obtain ⟨hcr_regs, hcm_mem, _⟩ := hcompat
  -- ==== Phase 2: climb regs / mem from atoms through hp to s. ====
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
  -- ==== Phase 3: fetch + per-field facts about (executeFn fetch s 1). ====
  have hfetch : fetch s.pc = some (.call sc) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hstep_eq : executeFn fetch s 1 = step (.call sc) s := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch, executeFn_zero]
  have hexec_pc : (executeFn fetch s 1).pc = s.pc + 1 := by
    rw [hstep_eq]; exact h_step_pc s
  have hexec_exit : (executeFn fetch s 1).exitCode = none := by
    rw [hstep_eq]; exact h_step_exit s hex
  have hexec_regs : (executeFn fetch s 1).regs = s.regs.set .r0 0 := by
    rw [hstep_eq]; exact h_step_regs s
  have hexec_mem_in (i : Nat) (hi : i < N) :
      (executeFn fetch s 1).mem (r1V + i) = (bsNew.get! i).toNat := by
    rw [hstep_eq, ← hs_r1_field]; exact h_step_mem_in s i hi
  have hexec_mem_out (a : Nat) (h : a < r1V ∨ a ≥ r1V + N) :
      (executeFn fetch s 1).mem a = s.mem a := by
    rw [hstep_eq]; apply h_step_mem_out s a
    rw [hs_r1_field]; exact h
  -- ==== Phase 4: facts about h_R from outer disjointness with h_P. ====
  obtain ⟨hd_PR_regs, hd_PR_mem, hd_PR_pc⟩ := hd_PR
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
  -- ==== Phase 5: build the new post partial state. ====
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
    refine ⟨fun r => ?_, fun a => ?_, ?_⟩
    · right; exact PartialState.singletonMemBytes_regs r
    · left; exact PartialState.singletonReg_mem a
    · left; exact PartialState.singletonReg_pc
  have hd_r0_T1_new : h_r0_new.Disjoint h_T1_new := by
    refine ⟨fun r => ?_, fun a => ?_, ?_⟩
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
  -- ==== Phase 6: outer disjointness h_P_new ⊥ h_R. ====
  have hd_PnewR : h_P_new.Disjoint h_R := by
    refine ⟨fun r => ?_, fun a => ?_, ?_⟩
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
  -- ==== Phase 7: assemble the witness for (Q ** R).holdsFor. ====
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_⟩
  · rw [hexec_pc, hpc]
  · exact hexec_exit
  · refine ⟨h_P_new.union h_R, ?_, h_P_new, h_R, hd_PnewR, rfl,
            ⟨h_r0_new, h_T1_new, hd_r0_T1_new, rfl, rfl,
             h_r1_new, h_b_new, hd_r1_b_new, rfl, rfl, rfl⟩,
            h_R_sat⟩
    refine ⟨?_, ?_, ?_⟩
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

/-! ## 5-atom mem-write helper: `cuTripleWithin_syscall_writesR1Bytes_r2r3`

Generalization of `cuTripleWithin_syscall_writesR1Bytes` for syscalls
whose mem-write payload depends on register values `r2V` and `r3V`
(memset, memcpy, memmove, memcmp). The precondition adds `r2 ↦ᵣ r2V`
and `r3 ↦ᵣ r3V` atoms so the proof body can extract those values and
feed them to the step-projection hypotheses (which are conditional
on `s.regs.r2 = r2V` and `s.regs.r3 = r3V`).

`bsNew` is the fixed post-state payload (computed from `r2V`, `r3V`
at theorem-instantiation time, e.g. `replicateByte (r2V % 256) r3V`
for memset). -/

theorem cuTripleWithin_syscall_writesR1Bytes_r2r3
    (sc : Syscall) (bsNew : ByteArray) (pc : Nat) (r2V r3V : Nat)
    (h_step_regs : ∀ s : State, (step (.call sc) s).regs = s.regs.set .r0 0)
    (h_step_mem_in  : ∀ s : State, s.regs.r2 = r2V → s.regs.r3 = r3V →
        ∀ i, i < bsNew.size →
        (step (.call sc) s).mem (s.regs.r1 + i) = (bsNew.get! i).toNat)
    (h_step_mem_out : ∀ s : State, s.regs.r3 = r3V →
        ∀ a, (a < s.regs.r1 ∨ a ≥ s.regs.r1 + bsNew.size) →
        (step (.call sc) s).mem a = s.mem a)
    (h_step_pc   : ∀ s : State, (step (.call sc) s).pc = s.pc + 1)
    (h_step_exit : ∀ s : State, s.exitCode = none →
        (step (.call sc) s).exitCode = none) :
    ∀ r0Old r1V (bsOld : ByteArray), bsOld.size = bsNew.size →
      cuTripleWithin 1 pc (pc + 1)
        (CodeReq.singleton pc (.call sc))
        ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V)
         ** (r1V ↦Bytes bsOld))
        ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V)
         ** (r1V ↦Bytes bsNew)) := by
  intro r0Old r1V bsOld hbsSize R hRfree fetch hcr s hPR hpc hex
  let N : Nat := bsNew.size
  -- ==== Phase 1: destructure the 5-atom (P ** R) split. ====
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
  obtain ⟨hcr_regs, hcm_mem, _⟩ := hcompat
  -- ==== Phase 2: climb regs / mem from atoms through hp to s. ====
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
      h_P.mem a = (PartialState.singletonMemBytes r1V bsOld).mem a := by
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
  -- ==== Phase 3: fetch + per-field facts about (executeFn fetch s 1). ====
  have hfetch : fetch s.pc = some (.call sc) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hstep_eq : executeFn fetch s 1 = step (.call sc) s := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch, executeFn_zero]
  have hexec_pc : (executeFn fetch s 1).pc = s.pc + 1 := by
    rw [hstep_eq]; exact h_step_pc s
  have hexec_exit : (executeFn fetch s 1).exitCode = none := by
    rw [hstep_eq]; exact h_step_exit s hex
  have hexec_regs : (executeFn fetch s 1).regs = s.regs.set .r0 0 := by
    rw [hstep_eq]; exact h_step_regs s
  have hexec_mem_in (i : Nat) (hi : i < N) :
      (executeFn fetch s 1).mem (r1V + i) = (bsNew.get! i).toNat := by
    rw [hstep_eq, ← hs_r1_field]
    exact h_step_mem_in s hs_r2_field hs_r3_field i hi
  have hexec_mem_out (a : Nat) (h : a < r1V ∨ a ≥ r1V + N) :
      (executeFn fetch s 1).mem a = s.mem a := by
    rw [hstep_eq]
    apply h_step_mem_out s hs_r3_field a
    rw [hs_r1_field]; exact h
  -- ==== Phase 4: facts about h_R from outer disjointness with h_P. ====
  obtain ⟨hd_PR_regs, hd_PR_mem, hd_PR_pc⟩ := hd_PR
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
  have h_R_no_mem_in (i : Nat) (hi : i < N) : h_R.mem (r1V + i) = none := by
    obtain ⟨v, hatom⟩ := PartialState.singletonMemBytes_mem_isSome r1V bsOld
      (r1V + i) ⟨Nat.le_add_right _ _, by rw [hbsSize]; show r1V + i < r1V + N; omega⟩
    have h_P_some : h_P.mem (r1V + i) = some v := by
      rw [h_P_mem_eq_b]; exact hatom
    rcases hd_PR_mem (r1V + i) with hl | hr
    · rw [h_P_some] at hl; nomatch hl
    · exact hr
  -- ==== Phase 5: build the new post partial state. ====
  let h_r0_new : PartialState := PartialState.singletonReg .r0 0
  let h_r1_new : PartialState := PartialState.singletonReg .r1 r1V
  let h_r2_new : PartialState := PartialState.singletonReg .r2 r2V
  let h_r3_new : PartialState := PartialState.singletonReg .r3 r3V
  let h_b_new  : PartialState := PartialState.singletonMemBytes r1V bsNew
  let h_T3_new : PartialState := h_r3_new.union h_b_new
  let h_T2_new : PartialState := h_r2_new.union h_T3_new
  let h_T1_new : PartialState := h_r1_new.union h_T2_new
  let h_P_new  : PartialState := h_r0_new.union h_T1_new
  have h_bsNew_mem_in (j : Nat) (hj : j < N) :
      (PartialState.singletonMemBytes r1V bsNew).mem (r1V + j) =
        some (bsNew.get! j).toNat :=
    PartialState.singletonMemBytes_mem_at r1V bsNew j hj
  have h_bsNew_mem_outside (a : Nat) (h : a < r1V ∨ a ≥ r1V + N) :
      (PartialState.singletonMemBytes r1V bsNew).mem a = none :=
    PartialState.singletonMemBytes_mem_outside r1V bsNew a h
  -- Inner disjointness: r3 ⊥ b.
  have hd_r3_b_new : h_r3_new.Disjoint h_b_new := by
    refine ⟨fun r => ?_, fun a => ?_, ?_⟩
    · right; exact PartialState.singletonMemBytes_regs r
    · left; exact PartialState.singletonReg_mem a
    · left; exact PartialState.singletonReg_pc
  -- r2 ⊥ (r3 ∪ b)
  have hd_r2_T3_new : h_r2_new.Disjoint h_T3_new := by
    refine ⟨fun r => ?_, fun a => ?_, ?_⟩
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
    refine ⟨fun r => ?_, fun a => ?_, ?_⟩
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
    refine ⟨fun r => ?_, fun a => ?_, ?_⟩
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
    show ((PartialState.singletonReg .r1 r1V).union h_T2_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    show ((PartialState.singletonReg .r2 r2V).union h_T3_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    show ((PartialState.singletonReg .r3 r3V).union h_b_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    exact PartialState.singletonMemBytes_pc
  -- ==== Phase 6: outer disjointness h_P_new ⊥ h_R. ====
  have hd_PnewR : h_P_new.Disjoint h_R := by
    refine ⟨fun r => ?_, fun a => ?_, ?_⟩
    · by_cases h0 : r = .r0
      · right; rw [h0]; exact h_R_no_r0
      by_cases h1 : r = .r1
      · right; rw [h1]; exact h_R_no_r1
      by_cases h2 : r = .r2
      · right; rw [h2]; exact h_R_no_r2
      by_cases h3 : r = .r3
      · right; rw [h3]; exact h_R_no_r3
      · left; exact h_P_new_regs_other r h0 h1 h2 h3
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
  -- ==== Phase 7: assemble the witness for (Q ** R).holdsFor. ====
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_⟩
  · rw [hexec_pc, hpc]
  · exact hexec_exit
  · refine ⟨h_P_new.union h_R, ?_, h_P_new, h_R, hd_PnewR, rfl,
            ⟨h_r0_new, h_T1_new, hd_r0_T1_new, rfl, rfl,
             h_r1_new, h_T2_new, hd_r1_T2_new, rfl, rfl,
             h_r2_new, h_T3_new, hd_r2_T3_new, rfl, rfl,
             h_r3_new, h_b_new,  hd_r3_b_new,  rfl, rfl, rfl⟩,
            h_R_sat⟩
    refine ⟨?_, ?_, ?_⟩
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

/-! ## Syscall: `sol_memset_`

`sol_memset_(dst, val, n)`: write the low byte of `r2` (`r2 % 256`)
into `n = r3` bytes starting at `dst = r1`. Sets `r0 := 0`. First
state-dependent payload syscall in the SL track — uses the 5-atom
helper `cuTripleWithin_syscall_writesR1Bytes_r2r3` because the
bytes written depend on the register values `r2V` and `r3V`. -/

theorem call_sol_memset_spec
    (r0Old r1V r2V r3V pc : Nat) (bsOld : ByteArray) (hbs : bsOld.size = r3V) :
    cuTripleWithin 1 pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_memset))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V)
       ** (r1V ↦Bytes bsOld))
      ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V)
       ** (r1V ↦Bytes (replicateByte (r2V % 256).toUInt8 r3V))) := by
  refine cuTripleWithin_syscall_writesR1Bytes_r2r3
    .sol_memset (replicateByte (r2V % 256).toUInt8 r3V) pc r2V r3V
    ?_ ?_ ?_ ?_ ?_ r0Old r1V bsOld ?_
  · intro s
    simp only [step, execSyscall, MemOps.execSet]
  · intro s hr2 hr3 i hi
    rw [replicateByte_size] at hi
    simp only [step, execSyscall, MemOps.execSet]
    rw [Mem_read_default]
    rw [if_pos ⟨Nat.le_add_right _ _, by rw [hr3]; omega⟩]
    rw [replicateByte_get! _ _ _ hi]
    rw [hr2]
    -- Goal: r2V % 256 = ((r2V % 256).toUInt8).toNat
    show r2V % 256 = (UInt8.ofNat (r2V % 256)).toNat
    unfold UInt8.ofNat UInt8.toNat
    simp
  · intro s hr3 a ha
    rw [replicateByte_size] at ha
    simp only [step, execSyscall, MemOps.execSet]
    rw [Mem_read_default]
    have hneg : ¬(a ≥ s.regs.r1 ∧ a - s.regs.r1 < s.regs.r3) := by
      rintro ⟨h1, h2⟩
      rw [hr3] at h2
      rcases ha with hl | hr
      · omega
      · omega
    rw [if_neg hneg]
  · intro s
    simp only [step, execSyscall, MemOps.execSet]
  · intro s hex
    simp only [step, execSyscall, MemOps.execSet]
    exact hex
  · rw [replicateByte_size]; exact hbs

/-! ## Syscall: `sol_get_clock_sysvar`

Writes 40 bytes of zeros at `*r1`, sets `r0 := 0`. First multi-region
sysvar spec driven by the generic
`cuTripleWithin_syscall_writesR1Bytes` helper — proves the same
shape as `sol_get_last_restart_slot` but at 40 bytes without a
per-byte case ladder. -/

theorem call_sol_get_clock_sysvar_spec
    (r0Old r1V pc : Nat) (bsOld : ByteArray) (hbs : bsOld.size = 40) :
    cuTripleWithin 1 pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_get_clock_sysvar))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1V) ** (r1V ↦Bytes bsOld))
      ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ r1V) ** (r1V ↦Bytes (zerosByteArray 40))) := by
  refine cuTripleWithin_syscall_writesR1Bytes
    .sol_get_clock_sysvar (zerosByteArray 40) pc
    ?_ ?_ ?_ ?_ ?_ r0Old r1V bsOld ?_
  · intro s
    simp only [step, execSyscall, Sysvar.execClock, Sysvar.zeroFillR1]
  · intro s i hi
    rw [zerosByteArray_size] at hi
    simp only [step, execSyscall, Sysvar.execClock, Sysvar.zeroFillR1]
    rw [Mem_read_default,
        if_pos ⟨Nat.le_add_right _ _, by omega⟩,
        zerosByteArray_get! 40 i hi]
    rfl
  · intro s a ha
    rw [zerosByteArray_size] at ha
    simp only [step, execSyscall, Sysvar.execClock, Sysvar.zeroFillR1]
    rw [Mem_read_default]
    have hneg : ¬(a ≥ s.regs.r1 ∧ a - s.regs.r1 < 40) := by
      rintro ⟨h1, h2⟩
      rcases ha with hl | hr
      · omega
      · omega
    rw [if_neg hneg]
  · intro s
    simp only [step, execSyscall, Sysvar.execClock, Sysvar.zeroFillR1]
  · intro s hex
    simp only [step, execSyscall, Sysvar.execClock, Sysvar.zeroFillR1]
    exact hex
  · rw [zerosByteArray_size]; exact hbs

/-! ## Syscall: `sol_get_epoch_rewards_sysvar`

Writes 81 bytes of zeros at `*r1`, sets `r0 := 0`. Mainnet default
EpochRewards struct under `active = false`. -/

theorem call_sol_get_epoch_rewards_sysvar_spec
    (r0Old r1V pc : Nat) (bsOld : ByteArray) (hbs : bsOld.size = 81) :
    cuTripleWithin 1 pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_get_epoch_rewards_sysvar))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1V) ** (r1V ↦Bytes bsOld))
      ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ r1V) ** (r1V ↦Bytes (zerosByteArray 81))) := by
  refine cuTripleWithin_syscall_writesR1Bytes
    .sol_get_epoch_rewards_sysvar (zerosByteArray 81) pc
    ?_ ?_ ?_ ?_ ?_ r0Old r1V bsOld ?_
  · intro s
    simp only [step, execSyscall, Sysvar.execEpochRewards, Sysvar.zeroFillR1]
  · intro s i hi
    rw [zerosByteArray_size] at hi
    simp only [step, execSyscall, Sysvar.execEpochRewards, Sysvar.zeroFillR1]
    rw [Mem_read_default,
        if_pos ⟨Nat.le_add_right _ _, by omega⟩,
        zerosByteArray_get! 81 i hi]
    rfl
  · intro s a ha
    rw [zerosByteArray_size] at ha
    simp only [step, execSyscall, Sysvar.execEpochRewards, Sysvar.zeroFillR1]
    rw [Mem_read_default]
    have hneg : ¬(a ≥ s.regs.r1 ∧ a - s.regs.r1 < 81) := by
      rintro ⟨h1, h2⟩
      rcases ha with hl | hr
      · omega
      · omega
    rw [if_neg hneg]
  · intro s
    simp only [step, execSyscall, Sysvar.execEpochRewards, Sysvar.zeroFillR1]
  · intro s hex
    simp only [step, execSyscall, Sysvar.execEpochRewards, Sysvar.zeroFillR1]
    exact hex
  · rw [zerosByteArray_size]; exact hbs

/-! ## Syscall: `sol_get_rent_sysvar`

Writes the 17-byte mainnet-default Rent struct at `*r1`, sets `r0 := 0`.
Unlike the zero-fill sysvars, the payload has non-zero bytes:

    [0..8)   lamports_per_byte_year = 3480 (0x0D98)  → bytes 0x98, 0x0D
    [8..16)  exemption_threshold    = 2.0  (f64 raw 0x4000_0000_0000_0000)
                                         → byte 15 = 0x40
    [16]     burn_percent           = 50              → byte 16 = 0x32

First non-zero-fill instantiation of `cuTripleWithin_syscall_writesR1Bytes`. -/

/-- The 17-byte mainnet-default Rent struct as a `ByteArray`. -/
def rentBytes : ByteArray :=
  ⟨#[0x98, 0x0D, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0x40, 50]⟩

@[simp] theorem rentBytes_size : rentBytes.size = 17 := by decide

theorem call_sol_get_rent_sysvar_spec
    (r0Old r1V pc : Nat) (bsOld : ByteArray) (hbs : bsOld.size = 17) :
    cuTripleWithin 1 pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_get_rent_sysvar))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1V) ** (r1V ↦Bytes bsOld))
      ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ r1V) ** (r1V ↦Bytes rentBytes)) := by
  refine cuTripleWithin_syscall_writesR1Bytes
    .sol_get_rent_sysvar rentBytes pc
    ?_ ?_ ?_ ?_ ?_ r0Old r1V bsOld ?_
  · intro s
    simp only [step, execSyscall, Sysvar.execRent]
  · intro s i hi
    rw [rentBytes_size] at hi
    simp only [step, execSyscall, Sysvar.execRent]
    rw [Mem_read_default]
    match i, hi with
    | 0, _ => simp; decide
    | 1, _ => simp; decide
    | 2, _ => simp; decide
    | 3, _ => simp; decide
    | 4, _ => simp; decide
    | 5, _ => simp; decide
    | 6, _ => simp; decide
    | 7, _ => simp; decide
    | 8, _ => simp; decide
    | 9, _ => simp; decide
    | 10, _ => simp; decide
    | 11, _ => simp; decide
    | 12, _ => simp; decide
    | 13, _ => simp; decide
    | 14, _ => simp; decide
    | 15, _ => simp; decide
    | 16, _ => simp; decide
    | k + 17, hk => exact absurd hk (by omega)
  · intro s a ha
    rw [rentBytes_size] at ha
    simp only [step, execSyscall, Sysvar.execRent]
    rw [Mem_read_default]
    rcases ha with hl | hr <;>
    · iterate 17 rw [if_neg (by omega)]
  · intro s
    simp only [step, execSyscall, Sysvar.execRent]
  · intro s hex
    simp only [step, execSyscall, Sysvar.execRent]
    exact hex
  · rw [rentBytes_size]; exact hbs

/-! ## Syscall: `sol_get_epoch_schedule_sysvar`

Writes the 40-byte mainnet-default `EpochSchedule::without_warmup()`
struct at `*r1`, sets `r0 := 0`. Layout:

    [0..8)   slots_per_epoch              = 432_000 (0x69780, LE [0x80,0x97,0x06,0,…])
    [8..16)  leader_schedule_slot_offset  = 432_000 (same bytes)
    [16]     warmup                       = 0
    [17..24) padding                      = 7 zero bytes
    [24..32) first_normal_epoch           = 0
    [32..40) first_normal_slot            = 0

Bytes 16..39 are all zero — `Sysvar.execEpochSchedule` writes them via
a single range conditional, while bytes 0..15 use per-byte equality
checks. The proof handles both via the same `simp; decide` per case. -/

/-- The 40-byte mainnet-default EpochSchedule struct as a `ByteArray`. -/
def epochScheduleBytes : ByteArray :=
  ⟨#[0x80, 0x97, 0x06, 0, 0, 0, 0, 0,
     0x80, 0x97, 0x06, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0]⟩

@[simp] theorem epochScheduleBytes_size : epochScheduleBytes.size = 40 := by decide

theorem call_sol_get_epoch_schedule_sysvar_spec
    (r0Old r1V pc : Nat) (bsOld : ByteArray) (hbs : bsOld.size = 40) :
    cuTripleWithin 1 pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_get_epoch_schedule_sysvar))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1V) ** (r1V ↦Bytes bsOld))
      ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ r1V) ** (r1V ↦Bytes epochScheduleBytes)) := by
  refine cuTripleWithin_syscall_writesR1Bytes
    .sol_get_epoch_schedule_sysvar epochScheduleBytes pc
    ?_ ?_ ?_ ?_ ?_ r0Old r1V bsOld ?_
  · intro s
    simp only [step, execSyscall, Sysvar.execEpochSchedule]
  · intro s i hi
    rw [epochScheduleBytes_size] at hi
    simp only [step, execSyscall, Sysvar.execEpochSchedule]
    rw [Mem_read_default]
    match i, hi with
    | 0, _ => simp; decide
    | 1, _ => simp; decide
    | 2, _ => simp; decide
    | 3, _ => simp; decide
    | 4, _ => simp; decide
    | 5, _ => simp; decide
    | 6, _ => simp; decide
    | 7, _ => simp; decide
    | 8, _ => simp; decide
    | 9, _ => simp; decide
    | 10, _ => simp; decide
    | 11, _ => simp; decide
    | 12, _ => simp; decide
    | 13, _ => simp; decide
    | 14, _ => simp; decide
    | 15, _ => simp; decide
    | 16, _ => simp; decide
    | 17, _ => simp; decide
    | 18, _ => simp; decide
    | 19, _ => simp; decide
    | 20, _ => simp; decide
    | 21, _ => simp; decide
    | 22, _ => simp; decide
    | 23, _ => simp; decide
    | 24, _ => simp; decide
    | 25, _ => simp; decide
    | 26, _ => simp; decide
    | 27, _ => simp; decide
    | 28, _ => simp; decide
    | 29, _ => simp; decide
    | 30, _ => simp; decide
    | 31, _ => simp; decide
    | 32, _ => simp; decide
    | 33, _ => simp; decide
    | 34, _ => simp; decide
    | 35, _ => simp; decide
    | 36, _ => simp; decide
    | 37, _ => simp; decide
    | 38, _ => simp; decide
    | 39, _ => simp; decide
    | k + 40, hk => exact absurd hk (by omega)
  · intro s a ha
    rw [epochScheduleBytes_size] at ha
    simp only [step, execSyscall, Sysvar.execEpochSchedule]
    rw [Mem_read_default]
    rcases ha with hl | hr <;>
    · iterate 16 rw [if_neg (by omega)]
      rw [if_neg (by rintro ⟨_, _⟩; omega)]
  · intro s
    simp only [step, execSyscall, Sysvar.execEpochSchedule]
  · intro s hex
    simp only [step, execSyscall, Sysvar.execEpochSchedule]
    exact hex
  · rw [epochScheduleBytes_size]; exact hbs

/-! ## Syscall: `sol_get_last_restart_slot`

Writes 8 bytes of zeros at `*r1`, sets `r0 := 0`. First memory-writing
syscall triple in the SL track — exercises the basic "r0-and-8-byte-mem"
shape that the U64-sized sysvar zero-fills (this and `sol_get_fees_sysvar`)
share. Memory is owned only at `[r1V, r1V+8)` by the precondition. -/

theorem call_sol_get_last_restart_slot_spec
    (r0Old r1V vOld pc : Nat) :
    cuTripleWithin 1 pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_get_last_restart_slot))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1V) ** (r1V ↦U64 vOld))
      ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ r1V) ** (r1V ↦U64 0)) := by
  intro R hRfree fetch hcr s hPR hpc hex
  -- ==== Phase 1: destructure the 3-atom (P ** R) split. ====
  obtain ⟨hp, hcompat, h_P, h_R, hd_PR, hu_PR, h_P_sat, h_R_sat⟩ := hPR
  obtain ⟨h_r0, h_T1, hd_r0_T1, hu_r0_T1, h_r0_pred, h_T1_sat⟩ := h_P_sat
  obtain ⟨h_r1, h_b, hd_r1_b, hu_r1_b, h_r1_pred, h_b_pred⟩ := h_T1_sat
  rw [h_r0_pred] at hu_r0_T1 hd_r0_T1
  rw [h_r1_pred] at hu_r1_b hd_r1_b
  rw [h_b_pred] at hu_r1_b hd_r1_b
  clear h_r0_pred h_r1_pred h_b_pred h_r0 h_r1 h_b
  obtain ⟨hcr_regs, hcm_mem, _⟩ := hcompat
  -- ==== Phase 2: climb regs / mem from atoms through hp to s. ====
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
  -- Only the bytes atom owns mem; reg atoms are mem-free.
  have h_P_mem_eq_b (a : Nat) :
      h_P.mem a = (PartialState.singletonMemU64 r1V vOld).mem a := by
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
  -- ==== Phase 3: fetch + per-field facts about (executeFn fetch s 1). ====
  have hfetch : fetch s.pc = some (.call .sol_get_last_restart_slot) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hexec_pc : (executeFn fetch s 1).pc = s.pc + 1 := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch, executeFn_zero]
    rfl
  have hexec_exit : (executeFn fetch s 1).exitCode = none := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch, executeFn_zero]
    exact hex
  have hexec_regs : (executeFn fetch s 1).regs = s.regs.set .r0 0 := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch, executeFn_zero]
    rfl
  -- Memory writes: 8 zero bytes at r1V; unchanged outside. `step` unfolds
  -- through `execSyscall .sol_get_last_restart_slot s = Sysvar.execLastRestartSlot s`
  -- = `Sysvar.zeroFillR1 s 8`, which sets `mem := ↑(fun a => if … then 0
  -- else s.mem a)`. The bare-function coercion lifts via `Mem_read_default`.
  have hexec_mem_in (i : Nat) (hi : i < 8) :
      (executeFn fetch s 1).mem (r1V + i) = 0 := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch, executeFn_zero]
    simp only [step, execSyscall, Sysvar.execLastRestartSlot, Sysvar.zeroFillR1]
    rw [Mem_read_default, hs_r1_field,
        if_pos ⟨Nat.le_add_right _ _, by omega⟩]
  have hexec_mem_out (a : Nat) (h : a < r1V ∨ a ≥ r1V + 8) :
      (executeFn fetch s 1).mem a = s.mem a := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch, executeFn_zero]
    simp only [step, execSyscall, Sysvar.execLastRestartSlot, Sysvar.zeroFillR1]
    rw [Mem_read_default, hs_r1_field]
    have hneg : ¬(a ≥ r1V ∧ a - r1V < 8) := by
      rintro ⟨h1, h2⟩
      rcases h with hl | hr
      · omega
      · omega
    rw [if_neg hneg]
  -- ==== Phase 4: facts about h_R from outer disjointness with h_P. ====
  obtain ⟨hd_PR_regs, hd_PR_mem, hd_PR_pc⟩ := hd_PR
  have h_R_no_r0 : h_R.regs .r0 = none := by
    rcases hd_PR_regs .r0 with hl | hr
    · rw [h_P_regs_r0] at hl; nomatch hl
    · exact hr
  have h_R_no_r1 : h_R.regs .r1 = none := by
    rcases hd_PR_regs .r1 with hl | hr
    · rw [h_P_regs_r1] at hl; nomatch hl
    · exact hr
  have h_R_no_pc : h_R.pc = none := hRfree _ h_R_sat
  have h_R_no_mem_in (i : Nat) (hi : i < 8) : h_R.mem (r1V + i) = none := by
    obtain ⟨v, hatom⟩ := PartialState.singletonMemU64_mem_isSome r1V vOld
      (r1V + i) ⟨Nat.le_add_right _ _, by omega⟩
    have h_P_some : h_P.mem (r1V + i) = some v := by
      rw [h_P_mem_eq_b]; exact hatom
    rcases hd_PR_mem (r1V + i) with hl | hr
    · rw [h_P_some] at hl; nomatch hl
    · exact hr
  -- ==== Phase 5: build the new post partial state. ====
  let h_r0_new : PartialState := PartialState.singletonReg .r0 0
  let h_r1_new : PartialState := PartialState.singletonReg .r1 r1V
  let h_b_new  : PartialState := PartialState.singletonMemU64 r1V 0
  let h_T1_new : PartialState := h_r1_new.union h_b_new
  let h_P_new  : PartialState := h_r0_new.union h_T1_new
  -- (singletonMemU64 r1V 0).mem at any in-range byte is `some 0`. Used both
  -- in disjointness reasoning (matching h_R against the post atom) and
  -- in the post-state compat check (recovering vm = 0).
  have h_singleton_zero (j : Nat) (hj : j < 8) :
      (PartialState.singletonMemU64 r1V 0).mem (r1V + j) = some 0 := by
    match j, hj with
    | 0, _ => simpa using PartialState.singletonMemU64_mem_0 r1V 0
    | 1, _ => simpa using PartialState.singletonMemU64_mem_1 r1V 0
    | 2, _ => simpa using PartialState.singletonMemU64_mem_2 r1V 0
    | 3, _ => simpa using PartialState.singletonMemU64_mem_3 r1V 0
    | 4, _ => simpa using PartialState.singletonMemU64_mem_4 r1V 0
    | 5, _ => simpa using PartialState.singletonMemU64_mem_5 r1V 0
    | 6, _ => simpa using PartialState.singletonMemU64_mem_6 r1V 0
    | 7, _ => simpa using PartialState.singletonMemU64_mem_7 r1V 0
  -- Inner disjointness: r1_new ⊥ b_new.
  have hd_r1_b_new : h_r1_new.Disjoint h_b_new := by
    refine ⟨fun r => ?_, fun a => ?_, ?_⟩
    · right; exact PartialState.singletonMemU64_regs r
    · left; exact PartialState.singletonReg_mem a
    · left; exact PartialState.singletonReg_pc
  -- Inner disjointness: r0_new ⊥ (r1_new ⊎ b_new).
  have hd_r0_T1_new : h_r0_new.Disjoint h_T1_new := by
    refine ⟨fun r => ?_, fun a => ?_, ?_⟩
    · by_cases hr0 : r = .r0
      · right
        show h_T1_new.regs r = none
        show ((PartialState.singletonReg .r1 r1V).union h_b_new).regs r = none
        rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other
              (hr0 ▸ (by decide : Reg.r0 ≠ Reg.r1)))]
        exact PartialState.singletonMemU64_regs r
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
    exact PartialState.singletonMemU64_regs r
  have h_P_new_mem_eq_b (a : Nat) : h_P_new.mem a = h_b_new.mem a := by
    show ((PartialState.singletonReg .r0 0).union h_T1_new).mem a = h_b_new.mem a
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    show ((PartialState.singletonReg .r1 r1V).union h_b_new).mem a = h_b_new.mem a
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
  have h_P_new_mem_outside (a : Nat) (h : a < r1V ∨ a ≥ r1V + 8) :
      h_P_new.mem a = none := by
    rw [h_P_new_mem_eq_b]
    exact PartialState.singletonMemU64_mem_outside r1V 0 a h
  have h_P_new_mem_in (j : Nat) (hj : j < 8) :
      h_P_new.mem (r1V + j) = some 0 := by
    rw [h_P_new_mem_eq_b]
    exact h_singleton_zero j hj
  have h_P_new_pc : h_P_new.pc = none := by
    show ((PartialState.singletonReg .r0 0).union h_T1_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    show ((PartialState.singletonReg .r1 r1V).union h_b_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    exact PartialState.singletonMemU64_pc
  -- ==== Phase 6: outer disjointness h_P_new ⊥ h_R. ====
  have hd_PnewR : h_P_new.Disjoint h_R := by
    refine ⟨fun r => ?_, fun a => ?_, ?_⟩
    · by_cases h0 : r = .r0
      · right; rw [h0]; exact h_R_no_r0
      by_cases h1 : r = .r1
      · right; rw [h1]; exact h_R_no_r1
      · left; exact h_P_new_regs_other r h0 h1
    · by_cases ha : r1V ≤ a ∧ a < r1V + 8
      · right
        obtain ⟨h1, h2⟩ := ha
        have h_eq : a = r1V + (a - r1V) := by omega
        have h_lt : a - r1V < 8 := by omega
        rw [h_eq]; exact h_R_no_mem_in _ h_lt
      · left
        apply h_P_new_mem_outside
        rcases Nat.lt_or_ge a r1V with h | h
        · left; exact h
        · rcases Nat.lt_or_ge a (r1V + 8) with h' | h'
          · exact absurd ⟨h, h'⟩ ha
          · right; exact h'
    · left; exact h_P_new_pc
  -- ==== Phase 7: assemble the witness for (Q ** R).holdsFor. ====
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_⟩
  · rw [hexec_pc, hpc]
  · exact hexec_exit
  · refine ⟨h_P_new.union h_R, ?_, h_P_new, h_R, hd_PnewR, rfl,
            ⟨h_r0_new, h_T1_new, hd_r0_T1_new, rfl, rfl,
             h_r1_new, h_b_new, hd_r1_b_new, rfl, rfl, rfl⟩,
            h_R_sat⟩
    refine ⟨?_, ?_, ?_⟩
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
      by_cases ha : r1V ≤ a ∧ a < r1V + 8
      · obtain ⟨h1, h2⟩ := ha
        have h_eq : a = r1V + (a - r1V) := by omega
        have h_lt : a - r1V < 8 := by omega
        rw [h_eq] at hvm ⊢
        rw [PartialState.union_mem_of_left_some
            (h_P_new_mem_in _ h_lt)] at hvm
        have hvm0 : vm = 0 := (Option.some.inj hvm).symm
        rw [hexec_mem_in _ h_lt, hvm0]
      · have h_out : a < r1V ∨ a ≥ r1V + 8 := by
          rcases Nat.lt_or_ge a r1V with h | h
          · left; exact h
          · rcases Nat.lt_or_ge a (r1V + 8) with h' | h'
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

/-! ## Syscall: `sol_get_fees_sysvar`

Deprecated sysvar; identical 8-byte zero-fill body to `sol_get_last_restart_slot`
via `Sysvar.execFees s = Sysvar.zeroFillR1 s 8`. Same precondition,
same postcondition, same proof up to the syscall-variant name and the
unfold target. -/

theorem call_sol_get_fees_sysvar_spec
    (r0Old r1V vOld pc : Nat) :
    cuTripleWithin 1 pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_get_fees_sysvar))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1V) ** (r1V ↦U64 vOld))
      ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ r1V) ** (r1V ↦U64 0)) := by
  intro R hRfree fetch hcr s hPR hpc hex
  -- ==== Phase 1: destructure the 3-atom (P ** R) split. ====
  obtain ⟨hp, hcompat, h_P, h_R, hd_PR, hu_PR, h_P_sat, h_R_sat⟩ := hPR
  obtain ⟨h_r0, h_T1, hd_r0_T1, hu_r0_T1, h_r0_pred, h_T1_sat⟩ := h_P_sat
  obtain ⟨h_r1, h_b, hd_r1_b, hu_r1_b, h_r1_pred, h_b_pred⟩ := h_T1_sat
  rw [h_r0_pred] at hu_r0_T1 hd_r0_T1
  rw [h_r1_pred] at hu_r1_b hd_r1_b
  rw [h_b_pred] at hu_r1_b hd_r1_b
  clear h_r0_pred h_r1_pred h_b_pred h_r0 h_r1 h_b
  obtain ⟨hcr_regs, hcm_mem, _⟩ := hcompat
  -- ==== Phase 2: climb regs / mem from atoms through hp to s. ====
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
      h_P.mem a = (PartialState.singletonMemU64 r1V vOld).mem a := by
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
  -- ==== Phase 3: fetch + per-field facts about (executeFn fetch s 1). ====
  have hfetch : fetch s.pc = some (.call .sol_get_fees_sysvar) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hexec_pc : (executeFn fetch s 1).pc = s.pc + 1 := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch, executeFn_zero]
    rfl
  have hexec_exit : (executeFn fetch s 1).exitCode = none := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch, executeFn_zero]
    exact hex
  have hexec_regs : (executeFn fetch s 1).regs = s.regs.set .r0 0 := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch, executeFn_zero]
    rfl
  have hexec_mem_in (i : Nat) (hi : i < 8) :
      (executeFn fetch s 1).mem (r1V + i) = 0 := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch, executeFn_zero]
    simp only [step, execSyscall, Sysvar.execFees, Sysvar.zeroFillR1]
    rw [Mem_read_default, hs_r1_field,
        if_pos ⟨Nat.le_add_right _ _, by omega⟩]
  have hexec_mem_out (a : Nat) (h : a < r1V ∨ a ≥ r1V + 8) :
      (executeFn fetch s 1).mem a = s.mem a := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch, executeFn_zero]
    simp only [step, execSyscall, Sysvar.execFees, Sysvar.zeroFillR1]
    rw [Mem_read_default, hs_r1_field]
    have hneg : ¬(a ≥ r1V ∧ a - r1V < 8) := by
      rintro ⟨h1, h2⟩
      rcases h with hl | hr
      · omega
      · omega
    rw [if_neg hneg]
  -- ==== Phase 4: facts about h_R from outer disjointness with h_P. ====
  obtain ⟨hd_PR_regs, hd_PR_mem, hd_PR_pc⟩ := hd_PR
  have h_R_no_r0 : h_R.regs .r0 = none := by
    rcases hd_PR_regs .r0 with hl | hr
    · rw [h_P_regs_r0] at hl; nomatch hl
    · exact hr
  have h_R_no_r1 : h_R.regs .r1 = none := by
    rcases hd_PR_regs .r1 with hl | hr
    · rw [h_P_regs_r1] at hl; nomatch hl
    · exact hr
  have h_R_no_pc : h_R.pc = none := hRfree _ h_R_sat
  have h_R_no_mem_in (i : Nat) (hi : i < 8) : h_R.mem (r1V + i) = none := by
    obtain ⟨v, hatom⟩ := PartialState.singletonMemU64_mem_isSome r1V vOld
      (r1V + i) ⟨Nat.le_add_right _ _, by omega⟩
    have h_P_some : h_P.mem (r1V + i) = some v := by
      rw [h_P_mem_eq_b]; exact hatom
    rcases hd_PR_mem (r1V + i) with hl | hr
    · rw [h_P_some] at hl; nomatch hl
    · exact hr
  -- ==== Phase 5: build the new post partial state. ====
  let h_r0_new : PartialState := PartialState.singletonReg .r0 0
  let h_r1_new : PartialState := PartialState.singletonReg .r1 r1V
  let h_b_new  : PartialState := PartialState.singletonMemU64 r1V 0
  let h_T1_new : PartialState := h_r1_new.union h_b_new
  let h_P_new  : PartialState := h_r0_new.union h_T1_new
  have h_singleton_zero (j : Nat) (hj : j < 8) :
      (PartialState.singletonMemU64 r1V 0).mem (r1V + j) = some 0 := by
    match j, hj with
    | 0, _ => simpa using PartialState.singletonMemU64_mem_0 r1V 0
    | 1, _ => simpa using PartialState.singletonMemU64_mem_1 r1V 0
    | 2, _ => simpa using PartialState.singletonMemU64_mem_2 r1V 0
    | 3, _ => simpa using PartialState.singletonMemU64_mem_3 r1V 0
    | 4, _ => simpa using PartialState.singletonMemU64_mem_4 r1V 0
    | 5, _ => simpa using PartialState.singletonMemU64_mem_5 r1V 0
    | 6, _ => simpa using PartialState.singletonMemU64_mem_6 r1V 0
    | 7, _ => simpa using PartialState.singletonMemU64_mem_7 r1V 0
  have hd_r1_b_new : h_r1_new.Disjoint h_b_new := by
    refine ⟨fun r => ?_, fun a => ?_, ?_⟩
    · right; exact PartialState.singletonMemU64_regs r
    · left; exact PartialState.singletonReg_mem a
    · left; exact PartialState.singletonReg_pc
  have hd_r0_T1_new : h_r0_new.Disjoint h_T1_new := by
    refine ⟨fun r => ?_, fun a => ?_, ?_⟩
    · by_cases hr0 : r = .r0
      · right
        show h_T1_new.regs r = none
        show ((PartialState.singletonReg .r1 r1V).union h_b_new).regs r = none
        rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other
              (hr0 ▸ (by decide : Reg.r0 ≠ Reg.r1)))]
        exact PartialState.singletonMemU64_regs r
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
    exact PartialState.singletonMemU64_regs r
  have h_P_new_mem_eq_b (a : Nat) : h_P_new.mem a = h_b_new.mem a := by
    show ((PartialState.singletonReg .r0 0).union h_T1_new).mem a = h_b_new.mem a
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    show ((PartialState.singletonReg .r1 r1V).union h_b_new).mem a = h_b_new.mem a
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
  have h_P_new_mem_outside (a : Nat) (h : a < r1V ∨ a ≥ r1V + 8) :
      h_P_new.mem a = none := by
    rw [h_P_new_mem_eq_b]
    exact PartialState.singletonMemU64_mem_outside r1V 0 a h
  have h_P_new_mem_in (j : Nat) (hj : j < 8) :
      h_P_new.mem (r1V + j) = some 0 := by
    rw [h_P_new_mem_eq_b]
    exact h_singleton_zero j hj
  have h_P_new_pc : h_P_new.pc = none := by
    show ((PartialState.singletonReg .r0 0).union h_T1_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    show ((PartialState.singletonReg .r1 r1V).union h_b_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    exact PartialState.singletonMemU64_pc
  -- ==== Phase 6: outer disjointness h_P_new ⊥ h_R. ====
  have hd_PnewR : h_P_new.Disjoint h_R := by
    refine ⟨fun r => ?_, fun a => ?_, ?_⟩
    · by_cases h0 : r = .r0
      · right; rw [h0]; exact h_R_no_r0
      by_cases h1 : r = .r1
      · right; rw [h1]; exact h_R_no_r1
      · left; exact h_P_new_regs_other r h0 h1
    · by_cases ha : r1V ≤ a ∧ a < r1V + 8
      · right
        obtain ⟨h1, h2⟩ := ha
        have h_eq : a = r1V + (a - r1V) := by omega
        have h_lt : a - r1V < 8 := by omega
        rw [h_eq]; exact h_R_no_mem_in _ h_lt
      · left
        apply h_P_new_mem_outside
        rcases Nat.lt_or_ge a r1V with h | h
        · left; exact h
        · rcases Nat.lt_or_ge a (r1V + 8) with h' | h'
          · exact absurd ⟨h, h'⟩ ha
          · right; exact h'
    · left; exact h_P_new_pc
  -- ==== Phase 7: assemble the witness for (Q ** R).holdsFor. ====
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_⟩
  · rw [hexec_pc, hpc]
  · exact hexec_exit
  · refine ⟨h_P_new.union h_R, ?_, h_P_new, h_R, hd_PnewR, rfl,
            ⟨h_r0_new, h_T1_new, hd_r0_T1_new, rfl, rfl,
             h_r1_new, h_b_new, hd_r1_b_new, rfl, rfl, rfl⟩,
            h_R_sat⟩
    refine ⟨?_, ?_, ?_⟩
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
      by_cases ha : r1V ≤ a ∧ a < r1V + 8
      · obtain ⟨h1, h2⟩ := ha
        have h_eq : a = r1V + (a - r1V) := by omega
        have h_lt : a - r1V < 8 := by omega
        rw [h_eq] at hvm ⊢
        rw [PartialState.union_mem_of_left_some
            (h_P_new_mem_in _ h_lt)] at hvm
        have hvm0 : vm = 0 := (Option.some.inj hvm).symm
        rw [hexec_mem_in _ h_lt, hvm0]
      · have h_out : a < r1V ∨ a ≥ r1V + 8 := by
          rcases Nat.lt_or_ge a r1V with h | h
          · left; exact h
          · rcases Nat.lt_or_ge a (r1V + 8) with h' | h'
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

end Svm.SBPF
