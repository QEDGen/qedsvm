import SVM.SBPF.InstructionSpecs.Alu

namespace SVM.SBPF

open Memory

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
    cuTripleWithin 1 0 pc (if cond then target else pc + 1)
      (CodeReq.singleton pc insn) (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) := by
  intro R hRfree fetch hcr s hPR hpc hex
  obtain ⟨hp, hcompat, h1, hR, hd, hu, hreg, hRsat⟩ := hPR
  rw [hreg] at hu hd
  clear hreg h1
  have hcr_regs := hcompat.regs
  have hcm_mem := hcompat.mem
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
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_, ?_⟩
  · rw [hexec]
    show (if cond then target else s.pc + 1) = if cond then target else pc + 1
    rw [hpc]
  · rw [hexec]; exact hex
  · rw [hexec]; show s.cuConsumed ≤ s.cuConsumed + 0; omega
  · rw [hexec]
    refine ⟨(PartialState.singletonReg dst vDst).union hR, ?_,
            PartialState.singletonReg dst vDst, hR, hd, rfl, rfl, hRsat⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
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

/-- Generic 2-register-read conditional jump: instruction reads `dst`
    (value `vDst`) and `src` (value `vSrc`), tests `cond`, jumps. Same
    "regs/mem unchanged" shape. `dst ≠ src` falls out of disjointness. -/
theorem cuTripleWithin_2reg_cjump
    (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat) (insn : Insn)
    (cond : Prop) [Decidable cond]
    (h_step : ∀ s : State, s.regs.get dst = vDst → s.regs.get src = vSrc →
        step insn s = { s with pc := if cond then target else s.pc + 1 }) :
    cuTripleWithin 1 0 pc (if cond then target else pc + 1)
      (CodeReq.singleton pc insn)
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) := by
  intro R hRfree fetch hcr s hPR hpc hex
  obtain ⟨hp, hcompat, hPQ, hR, hd_PQR, hu_PQR, hPQ_pred, hR_sat⟩ := hPR
  obtain ⟨h_dst, h_src, hd_dst_src, hu_PQ, h_dst_eq, h_src_eq⟩ := hPQ_pred
  rw [h_dst_eq] at hu_PQ hd_dst_src
  rw [h_src_eq] at hu_PQ hd_dst_src
  clear h_dst_eq h_src_eq h_dst h_src
  have hcr_regs := hcompat.regs
  have hcm_mem := hcompat.mem
  have hne_dst_src : dst ≠ src := by
    have hd_inner_regs := hd_dst_src.regs
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
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_, ?_⟩
  · rw [hexec]
    show (if cond then target else s.pc + 1) = if cond then target else pc + 1
    rw [hpc]
  · rw [hexec]; exact hex
  · rw [hexec]; show s.cuConsumed ≤ s.cuConsumed + 0; omega
  · rw [hexec]
    refine ⟨hp, ?_,
            (PartialState.singletonReg dst vDst).union
              (PartialState.singletonReg src vSrc),
            hR, ?_, hp_eq,
            ⟨PartialState.singletonReg dst vDst,
             PartialState.singletonReg src vSrc,
             ?_, rfl, rfl, rfl⟩,
            hR_sat⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
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
    cuTripleWithin 1 0 pc (if vDst = toU64 imm then target else pc + 1)
      (CodeReq.singleton pc (.jeq dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) :=
  cuTripleWithin_1reg_cjump dst vDst pc target (.jeq dst (.imm imm) target)
    (vDst = toU64 imm)
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-- `jne dst, imm, target`: jump if `dst ≠ toU64 imm`. -/
theorem jne_imm_spec (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat) :
    cuTripleWithin 1 0 pc (if vDst ≠ toU64 imm then target else pc + 1)
      (CodeReq.singleton pc (.jne dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) :=
  cuTripleWithin_1reg_cjump dst vDst pc target (.jne dst (.imm imm) target)
    (vDst ≠ toU64 imm)
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-! ## Linear (fall-through / taken) variants of conditional jumps

These are the shapes `sl_block_auto` needs to chain conditional jumps
into a straight-line block. Each takes the path hypothesis as a
precondition and collapses the conditional in the corresponding
`*_imm_spec`. The path hypothesis becomes a side goal in `mkSpec`'s
dispatch, discharged by the user via `<;> assumption`. -/

/-- `jeq dst, imm`: NOT taken case. Given `vDst ≠ toU64 imm` the
    conditional collapses to the fall-through (`pc + 1`). -/
theorem jeq_imm_not_taken_spec
    (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat)
    (h : vDst ≠ toU64 imm) :
    cuTripleWithin 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.jeq dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) := by
  have base := jeq_imm_spec dst imm vDst pc target
  rwa [if_neg h] at base

/-- `jeq dst, imm`: TAKEN case. Given `vDst = toU64 imm` the
    conditional collapses to the jump target. -/
theorem jeq_imm_taken_spec
    (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat)
    (h : vDst = toU64 imm) :
    cuTripleWithin 1 0 pc target
      (CodeReq.singleton pc (.jeq dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) := by
  have base := jeq_imm_spec dst imm vDst pc target
  rwa [if_pos h] at base

/-- `jne dst, imm`: NOT taken case. Given `vDst = toU64 imm` the
    conditional collapses to the fall-through (`pc + 1`). -/
theorem jne_imm_not_taken_spec
    (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat)
    (h : vDst = toU64 imm) :
    cuTripleWithin 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.jne dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) := by
  have base := jne_imm_spec dst imm vDst pc target
  rwa [if_neg (by simp [h] : ¬ (vDst ≠ toU64 imm))] at base

/-- `jne dst, imm`: TAKEN case. Given `vDst ≠ toU64 imm` the
    conditional collapses to the jump target. -/
theorem jne_imm_taken_spec
    (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat)
    (h : vDst ≠ toU64 imm) :
    cuTripleWithin 1 0 pc target
      (CodeReq.singleton pc (.jne dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) := by
  have base := jne_imm_spec dst imm vDst pc target
  rwa [if_pos h] at base

/-- `jgt dst, imm, target`: unsigned jump-greater-than. -/
theorem jgt_imm_spec (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat) :
    cuTripleWithin 1 0 pc (if vDst > toU64 imm then target else pc + 1)
      (CodeReq.singleton pc (.jgt dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) :=
  cuTripleWithin_1reg_cjump dst vDst pc target (.jgt dst (.imm imm) target)
    (vDst > toU64 imm)
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-- `jgt dst, imm`: NOT taken case (fall-through). The exit PC
    collapses to `pc + 1` under `¬ (vDst > toU64 imm)`. -/
theorem jgt_imm_not_taken_spec
    (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat)
    (h : ¬ vDst > toU64 imm) :
    cuTripleWithin 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.jgt dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) := by
  have base := jgt_imm_spec dst imm vDst pc target
  rwa [if_neg h] at base

/-- `jgt dst, imm`: TAKEN case. The exit PC collapses to `target`
    under `vDst > toU64 imm`. -/
theorem jgt_imm_taken_spec
    (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat)
    (h : vDst > toU64 imm) :
    cuTripleWithin 1 0 pc target
      (CodeReq.singleton pc (.jgt dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) := by
  have base := jgt_imm_spec dst imm vDst pc target
  rwa [if_pos h] at base

/-- `jge dst, imm, target`: unsigned jump-greater-or-equal. -/
theorem jge_imm_spec (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat) :
    cuTripleWithin 1 0 pc (if vDst ≥ toU64 imm then target else pc + 1)
      (CodeReq.singleton pc (.jge dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) :=
  cuTripleWithin_1reg_cjump dst vDst pc target (.jge dst (.imm imm) target)
    (vDst ≥ toU64 imm)
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-- `jlt dst, imm, target`: unsigned jump-less-than. -/
theorem jlt_imm_spec (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat) :
    cuTripleWithin 1 0 pc (if vDst < toU64 imm then target else pc + 1)
      (CodeReq.singleton pc (.jlt dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) :=
  cuTripleWithin_1reg_cjump dst vDst pc target (.jlt dst (.imm imm) target)
    (vDst < toU64 imm)
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-- `jlt dst, imm`: NOT taken (fall-through). -/
theorem jlt_imm_not_taken_spec
    (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat)
    (h : ¬ vDst < toU64 imm) :
    cuTripleWithin 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.jlt dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) := by
  have base := jlt_imm_spec dst imm vDst pc target
  rwa [if_neg h] at base

/-- `jlt dst, imm`: TAKEN. -/
theorem jlt_imm_taken_spec
    (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat)
    (h : vDst < toU64 imm) :
    cuTripleWithin 1 0 pc target
      (CodeReq.singleton pc (.jlt dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) := by
  have base := jlt_imm_spec dst imm vDst pc target
  rwa [if_pos h] at base

/-- `jle dst, imm, target`: unsigned jump-less-or-equal. -/
theorem jle_imm_spec (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat) :
    cuTripleWithin 1 0 pc (if vDst ≤ toU64 imm then target else pc + 1)
      (CodeReq.singleton pc (.jle dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) :=
  cuTripleWithin_1reg_cjump dst vDst pc target (.jle dst (.imm imm) target)
    (vDst ≤ toU64 imm)
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-- `jle dst, imm`: NOT taken (fall-through). -/
theorem jle_imm_not_taken_spec
    (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat)
    (h : ¬ vDst ≤ toU64 imm) :
    cuTripleWithin 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.jle dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) := by
  have base := jle_imm_spec dst imm vDst pc target
  rwa [if_neg h] at base

/-- `jle dst, imm`: TAKEN. -/
theorem jle_imm_taken_spec
    (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat)
    (h : vDst ≤ toU64 imm) :
    cuTripleWithin 1 0 pc target
      (CodeReq.singleton pc (.jle dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) := by
  have base := jle_imm_spec dst imm vDst pc target
  rwa [if_pos h] at base

/-- `jsgt dst, imm, target`: signed jump-greater-than. -/
theorem jsgt_imm_spec (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat) :
    cuTripleWithin 1 0 pc
      (if toSigned64 vDst > toSigned64 (toU64 imm) then target else pc + 1)
      (CodeReq.singleton pc (.jsgt dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) :=
  cuTripleWithin_1reg_cjump dst vDst pc target (.jsgt dst (.imm imm) target)
    (toSigned64 vDst > toSigned64 (toU64 imm))
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-- `jsgt dst, imm`: NOT taken (signed). -/
theorem jsgt_imm_not_taken_spec
    (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat)
    (h : ¬ toSigned64 vDst > toSigned64 (toU64 imm)) :
    cuTripleWithin 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.jsgt dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) := by
  have base := jsgt_imm_spec dst imm vDst pc target
  rwa [if_neg h] at base

/-- `jsgt dst, imm`: TAKEN (signed). -/
theorem jsgt_imm_taken_spec
    (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat)
    (h : toSigned64 vDst > toSigned64 (toU64 imm)) :
    cuTripleWithin 1 0 pc target
      (CodeReq.singleton pc (.jsgt dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) := by
  have base := jsgt_imm_spec dst imm vDst pc target
  rwa [if_pos h] at base

/-- `jsge dst, imm, target`: signed jump-greater-or-equal. -/
theorem jsge_imm_spec (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat) :
    cuTripleWithin 1 0 pc
      (if toSigned64 vDst ≥ toSigned64 (toU64 imm) then target else pc + 1)
      (CodeReq.singleton pc (.jsge dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) :=
  cuTripleWithin_1reg_cjump dst vDst pc target (.jsge dst (.imm imm) target)
    (toSigned64 vDst ≥ toSigned64 (toU64 imm))
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-- `jslt dst, imm, target`: signed jump-less-than. -/
theorem jslt_imm_spec (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat) :
    cuTripleWithin 1 0 pc
      (if toSigned64 vDst < toSigned64 (toU64 imm) then target else pc + 1)
      (CodeReq.singleton pc (.jslt dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) :=
  cuTripleWithin_1reg_cjump dst vDst pc target (.jslt dst (.imm imm) target)
    (toSigned64 vDst < toSigned64 (toU64 imm))
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-- `jsle dst, imm, target`: signed jump-less-or-equal. -/
theorem jsle_imm_spec (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat) :
    cuTripleWithin 1 0 pc
      (if toSigned64 vDst ≤ toSigned64 (toU64 imm) then target else pc + 1)
      (CodeReq.singleton pc (.jsle dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) :=
  cuTripleWithin_1reg_cjump dst vDst pc target (.jsle dst (.imm imm) target)
    (toSigned64 vDst ≤ toSigned64 (toU64 imm))
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-- `jsle dst, imm`: NOT taken (signed imm form). -/
theorem jsle_imm_not_taken_spec
    (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat)
    (h : ¬ toSigned64 vDst ≤ toSigned64 (toU64 imm)) :
    cuTripleWithin 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.jsle dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) := by
  have base := jsle_imm_spec dst imm vDst pc target
  rwa [if_neg h] at base

/-- `jsle dst, imm`: TAKEN (signed imm form). -/
theorem jsle_imm_taken_spec
    (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat)
    (h : toSigned64 vDst ≤ toSigned64 (toU64 imm)) :
    cuTripleWithin 1 0 pc target
      (CodeReq.singleton pc (.jsle dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) := by
  have base := jsle_imm_spec dst imm vDst pc target
  rwa [if_pos h] at base

/-- `jset dst, imm, target`: jump if any bit-mask bit is set. -/
theorem jset_imm_spec (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat) :
    cuTripleWithin 1 0 pc
      (if vDst &&& toU64 imm ≠ 0 then target else pc + 1)
      (CodeReq.singleton pc (.jset dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) :=
  cuTripleWithin_1reg_cjump dst vDst pc target (.jset dst (.imm imm) target)
    (vDst &&& toU64 imm ≠ 0)
    (fun _ hdst => by simp only [step, resolveSrc, hdst])

/-! ## Conditional-jump branch-shape specs

The base `jXX_imm_spec` / `jXX_reg_spec` theorems above use the form
`cuTripleWithin 1 0 pc (if cond then target else pc + 1) ...`. The
`_branch` flavours below lift that into `cuTripleWithinBranch`, which
exposes the two exit PCs separately (suitable for plugging into
`cuTripleWithinBranch_join`). Each is a one-line wrapper applying
`cuTripleWithin.toBranch`. -/

/-- Branch shape of `jeq dst, imm`: exitT = target (taken when
    `vDst = toU64 imm`), exitF = pc + 1 (otherwise). -/
theorem jeq_imm_branch_spec (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat) :
    cuTripleWithinBranch 1 0 pc target (pc + 1)
      (vDst = toU64 imm)
      (CodeReq.singleton pc (.jeq dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) :=
  (jeq_imm_spec dst imm vDst pc target).toBranch

/-- Branch shape of `jne dst, imm`: exitT = target (taken when
    `vDst ≠ toU64 imm`), exitF = pc + 1 (otherwise). -/
theorem jne_imm_branch_spec (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat) :
    cuTripleWithinBranch 1 0 pc target (pc + 1)
      (vDst ≠ toU64 imm)
      (CodeReq.singleton pc (.jne dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) :=
  (jne_imm_spec dst imm vDst pc target).toBranch

-- reg-source --

/-- `jeq dst, src, target`: jump if `dst = src`. -/
theorem jeq_reg_spec (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat) :
    cuTripleWithin 1 0 pc (if vDst = vSrc then target else pc + 1)
      (CodeReq.singleton pc (.jeq dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) :=
  cuTripleWithin_2reg_cjump dst src vDst vSrc pc target
    (.jeq dst (.reg src) target) (vDst = vSrc)
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-- `jeq dst, src`: NOT taken (reg form). -/
theorem jeq_reg_not_taken_spec
    (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat)
    (h : vDst ≠ vSrc) :
    cuTripleWithin 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.jeq dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) := by
  have base := jeq_reg_spec dst src vDst vSrc pc target
  rwa [if_neg h] at base

/-- `jeq dst, src`: TAKEN (reg form). -/
theorem jeq_reg_taken_spec
    (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat)
    (h : vDst = vSrc) :
    cuTripleWithin 1 0 pc target
      (CodeReq.singleton pc (.jeq dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) := by
  have base := jeq_reg_spec dst src vDst vSrc pc target
  rwa [if_pos h] at base

/-- `jne dst, src, target`: jump if `dst ≠ src`. -/
theorem jne_reg_spec (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat) :
    cuTripleWithin 1 0 pc (if vDst ≠ vSrc then target else pc + 1)
      (CodeReq.singleton pc (.jne dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) :=
  cuTripleWithin_2reg_cjump dst src vDst vSrc pc target
    (.jne dst (.reg src) target) (vDst ≠ vSrc)
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-- `jne dst, src`: NOT taken (reg form). -/
theorem jne_reg_not_taken_spec
    (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat)
    (h : vDst = vSrc) :
    cuTripleWithin 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.jne dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) := by
  have base := jne_reg_spec dst src vDst vSrc pc target
  rwa [if_neg (by simp [h] : ¬ (vDst ≠ vSrc))] at base

/-- `jne dst, src`: TAKEN (reg form). -/
theorem jne_reg_taken_spec
    (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat)
    (h : vDst ≠ vSrc) :
    cuTripleWithin 1 0 pc target
      (CodeReq.singleton pc (.jne dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) := by
  have base := jne_reg_spec dst src vDst vSrc pc target
  rwa [if_pos h] at base

/-- `jgt dst, src, target`: unsigned jump-greater-than. -/
theorem jgt_reg_spec (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat) :
    cuTripleWithin 1 0 pc (if vDst > vSrc then target else pc + 1)
      (CodeReq.singleton pc (.jgt dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) :=
  cuTripleWithin_2reg_cjump dst src vDst vSrc pc target
    (.jgt dst (.reg src) target) (vDst > vSrc)
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-- `jge dst, src, target`: unsigned jump-greater-or-equal. -/
theorem jge_reg_spec (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat) :
    cuTripleWithin 1 0 pc (if vDst ≥ vSrc then target else pc + 1)
      (CodeReq.singleton pc (.jge dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) :=
  cuTripleWithin_2reg_cjump dst src vDst vSrc pc target
    (.jge dst (.reg src) target) (vDst ≥ vSrc)
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-- `jlt dst, src, target`: unsigned jump-less-than. -/
theorem jlt_reg_spec (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat) :
    cuTripleWithin 1 0 pc (if vDst < vSrc then target else pc + 1)
      (CodeReq.singleton pc (.jlt dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) :=
  cuTripleWithin_2reg_cjump dst src vDst vSrc pc target
    (.jlt dst (.reg src) target) (vDst < vSrc)
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-- `jlt dst, src`: NOT taken (reg form). -/
theorem jlt_reg_not_taken_spec
    (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat)
    (h : ¬ vDst < vSrc) :
    cuTripleWithin 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.jlt dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) := by
  have base := jlt_reg_spec dst src vDst vSrc pc target
  rwa [if_neg h] at base

/-- `jlt dst, src`: TAKEN (reg form). -/
theorem jlt_reg_taken_spec
    (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat)
    (h : vDst < vSrc) :
    cuTripleWithin 1 0 pc target
      (CodeReq.singleton pc (.jlt dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) := by
  have base := jlt_reg_spec dst src vDst vSrc pc target
  rwa [if_pos h] at base

/-- `jle dst, src, target`: unsigned jump-less-or-equal. -/
theorem jle_reg_spec (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat) :
    cuTripleWithin 1 0 pc (if vDst ≤ vSrc then target else pc + 1)
      (CodeReq.singleton pc (.jle dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) :=
  cuTripleWithin_2reg_cjump dst src vDst vSrc pc target
    (.jle dst (.reg src) target) (vDst ≤ vSrc)
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-- `jsgt dst, src, target`: signed jump-greater-than. -/
theorem jsgt_reg_spec (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat) :
    cuTripleWithin 1 0 pc
      (if toSigned64 vDst > toSigned64 vSrc then target else pc + 1)
      (CodeReq.singleton pc (.jsgt dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) :=
  cuTripleWithin_2reg_cjump dst src vDst vSrc pc target
    (.jsgt dst (.reg src) target) (toSigned64 vDst > toSigned64 vSrc)
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-- `jsge dst, src, target`: signed jump-greater-or-equal. -/
theorem jsge_reg_spec (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat) :
    cuTripleWithin 1 0 pc
      (if toSigned64 vDst ≥ toSigned64 vSrc then target else pc + 1)
      (CodeReq.singleton pc (.jsge dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) :=
  cuTripleWithin_2reg_cjump dst src vDst vSrc pc target
    (.jsge dst (.reg src) target) (toSigned64 vDst ≥ toSigned64 vSrc)
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-- `jslt dst, src, target`: signed jump-less-than. -/
theorem jslt_reg_spec (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat) :
    cuTripleWithin 1 0 pc
      (if toSigned64 vDst < toSigned64 vSrc then target else pc + 1)
      (CodeReq.singleton pc (.jslt dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) :=
  cuTripleWithin_2reg_cjump dst src vDst vSrc pc target
    (.jslt dst (.reg src) target) (toSigned64 vDst < toSigned64 vSrc)
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-- `jsle dst, src, target`: signed jump-less-or-equal. -/
theorem jsle_reg_spec (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat) :
    cuTripleWithin 1 0 pc
      (if toSigned64 vDst ≤ toSigned64 vSrc then target else pc + 1)
      (CodeReq.singleton pc (.jsle dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) :=
  cuTripleWithin_2reg_cjump dst src vDst vSrc pc target
    (.jsle dst (.reg src) target) (toSigned64 vDst ≤ toSigned64 vSrc)
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-- `jsle dst, src`: NOT taken (signed, reg form). -/
theorem jsle_reg_not_taken_spec
    (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat)
    (h : ¬ toSigned64 vDst ≤ toSigned64 vSrc) :
    cuTripleWithin 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.jsle dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) := by
  have base := jsle_reg_spec dst src vDst vSrc pc target
  rwa [if_neg h] at base

/-- `jsle dst, src`: TAKEN (signed, reg form). -/
theorem jsle_reg_taken_spec
    (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat)
    (h : toSigned64 vDst ≤ toSigned64 vSrc) :
    cuTripleWithin 1 0 pc target
      (CodeReq.singleton pc (.jsle dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) := by
  have base := jsle_reg_spec dst src vDst vSrc pc target
  rwa [if_pos h] at base

/-- `jset dst, src, target`: jump if any bit-mask bit is set.
    `simp only [..., hdst, hsrc]` instead of `rw`: the `Decidable (_ ≠ 0)`
    instance under `&&&` doesn't synthesize through a `rw` motive. -/
theorem jset_reg_spec (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat) :
    cuTripleWithin 1 0 pc
      (if vDst &&& vSrc ≠ 0 then target else pc + 1)
      (CodeReq.singleton pc (.jset dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) :=
  cuTripleWithin_2reg_cjump dst src vDst vSrc pc target
    (.jset dst (.reg src) target) (vDst &&& vSrc ≠ 0)
    (fun _ hdst hsrc => by simp only [step, resolveSrc, hdst, hsrc])

/-! ## Direction-specialised variants for the trace-guided lifter

`sl_block_iter` needs each conditional jump's post-PC to be a concrete
value (`target` or `pc + 1`), not the `if cond then … else …` the
combined specs carry. These split the combined spec by branch direction
via `if_pos` / `if_neg`, mirroring the `jeq`/`jlt`/`jsle` variants above.
Added for the opcodes the p-token init arms walk (`jgt`/`jle`/`jsge`
reg-form, `jslt` imm-form). -/

theorem jgt_reg_not_taken_spec (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat)
    (h : ¬ vDst > vSrc) :
    cuTripleWithin 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.jgt dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) := by
  have base := jgt_reg_spec dst src vDst vSrc pc target; rwa [if_neg h] at base

theorem jgt_reg_taken_spec (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat)
    (h : vDst > vSrc) :
    cuTripleWithin 1 0 pc target
      (CodeReq.singleton pc (.jgt dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) := by
  have base := jgt_reg_spec dst src vDst vSrc pc target; rwa [if_pos h] at base

theorem jle_reg_not_taken_spec (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat)
    (h : ¬ vDst ≤ vSrc) :
    cuTripleWithin 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.jle dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) := by
  have base := jle_reg_spec dst src vDst vSrc pc target; rwa [if_neg h] at base

theorem jle_reg_taken_spec (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat)
    (h : vDst ≤ vSrc) :
    cuTripleWithin 1 0 pc target
      (CodeReq.singleton pc (.jle dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) := by
  have base := jle_reg_spec dst src vDst vSrc pc target; rwa [if_pos h] at base

theorem jsge_reg_not_taken_spec (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat)
    (h : ¬ toSigned64 vDst ≥ toSigned64 vSrc) :
    cuTripleWithin 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.jsge dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) := by
  have base := jsge_reg_spec dst src vDst vSrc pc target; rwa [if_neg h] at base

theorem jsge_reg_taken_spec (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat)
    (h : toSigned64 vDst ≥ toSigned64 vSrc) :
    cuTripleWithin 1 0 pc target
      (CodeReq.singleton pc (.jsge dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) := by
  have base := jsge_reg_spec dst src vDst vSrc pc target; rwa [if_pos h] at base

theorem jslt_imm_not_taken_spec (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat)
    (h : ¬ toSigned64 vDst < toSigned64 (toU64 imm)) :
    cuTripleWithin 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.jslt dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) := by
  have base := jslt_imm_spec dst imm vDst pc target; rwa [if_neg h] at base

theorem jslt_imm_taken_spec (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat)
    (h : toSigned64 vDst < toSigned64 (toU64 imm)) :
    cuTripleWithin 1 0 pc target
      (CodeReq.singleton pc (.jslt dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) := by
  have base := jslt_imm_spec dst imm vDst pc target; rwa [if_pos h] at base

/-! ### Second buildout batch: jge / jsgt-reg / jslt-reg / jsge-imm / jset -/

theorem jge_imm_not_taken_spec (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat)
    (h : ¬ vDst ≥ toU64 imm) :
    cuTripleWithin 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.jge dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) := by
  have base := jge_imm_spec dst imm vDst pc target; rwa [if_neg h] at base

theorem jge_imm_taken_spec (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat)
    (h : vDst ≥ toU64 imm) :
    cuTripleWithin 1 0 pc target
      (CodeReq.singleton pc (.jge dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) := by
  have base := jge_imm_spec dst imm vDst pc target; rwa [if_pos h] at base

theorem jge_reg_not_taken_spec (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat)
    (h : ¬ vDst ≥ vSrc) :
    cuTripleWithin 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.jge dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) := by
  have base := jge_reg_spec dst src vDst vSrc pc target; rwa [if_neg h] at base

theorem jge_reg_taken_spec (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat)
    (h : vDst ≥ vSrc) :
    cuTripleWithin 1 0 pc target
      (CodeReq.singleton pc (.jge dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) := by
  have base := jge_reg_spec dst src vDst vSrc pc target; rwa [if_pos h] at base

theorem jsgt_reg_not_taken_spec (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat)
    (h : ¬ toSigned64 vDst > toSigned64 vSrc) :
    cuTripleWithin 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.jsgt dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) := by
  have base := jsgt_reg_spec dst src vDst vSrc pc target; rwa [if_neg h] at base

theorem jsgt_reg_taken_spec (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat)
    (h : toSigned64 vDst > toSigned64 vSrc) :
    cuTripleWithin 1 0 pc target
      (CodeReq.singleton pc (.jsgt dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) := by
  have base := jsgt_reg_spec dst src vDst vSrc pc target; rwa [if_pos h] at base

theorem jslt_reg_not_taken_spec (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat)
    (h : ¬ toSigned64 vDst < toSigned64 vSrc) :
    cuTripleWithin 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.jslt dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) := by
  have base := jslt_reg_spec dst src vDst vSrc pc target; rwa [if_neg h] at base

theorem jslt_reg_taken_spec (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat)
    (h : toSigned64 vDst < toSigned64 vSrc) :
    cuTripleWithin 1 0 pc target
      (CodeReq.singleton pc (.jslt dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) := by
  have base := jslt_reg_spec dst src vDst vSrc pc target; rwa [if_pos h] at base

theorem jsge_imm_not_taken_spec (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat)
    (h : ¬ toSigned64 vDst ≥ toSigned64 (toU64 imm)) :
    cuTripleWithin 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.jsge dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) := by
  have base := jsge_imm_spec dst imm vDst pc target; rwa [if_neg h] at base

theorem jsge_imm_taken_spec (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat)
    (h : toSigned64 vDst ≥ toSigned64 (toU64 imm)) :
    cuTripleWithin 1 0 pc target
      (CodeReq.singleton pc (.jsge dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) := by
  have base := jsge_imm_spec dst imm vDst pc target; rwa [if_pos h] at base

theorem jset_imm_not_taken_spec (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat)
    (h : ¬ vDst &&& toU64 imm ≠ 0) :
    cuTripleWithin 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.jset dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) := by
  have base := jset_imm_spec dst imm vDst pc target; rwa [if_neg h] at base

theorem jset_imm_taken_spec (dst : Reg) (imm : Int) (vDst : Nat) (pc target : Nat)
    (h : vDst &&& toU64 imm ≠ 0) :
    cuTripleWithin 1 0 pc target
      (CodeReq.singleton pc (.jset dst (.imm imm) target))
      (dst ↦ᵣ vDst) (dst ↦ᵣ vDst) := by
  have base := jset_imm_spec dst imm vDst pc target; rwa [if_pos h] at base

theorem jset_reg_not_taken_spec (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat)
    (h : ¬ vDst &&& vSrc ≠ 0) :
    cuTripleWithin 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.jset dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) := by
  have base := jset_reg_spec dst src vDst vSrc pc target; rwa [if_neg h] at base

theorem jset_reg_taken_spec (dst src : Reg) (vDst vSrc : Nat) (pc target : Nat)
    (h : vDst &&& vSrc ≠ 0) :
    cuTripleWithin 1 0 pc target
      (CodeReq.singleton pc (.jset dst (.reg src) target))
      ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) ((dst ↦ᵣ vDst) ** (src ↦ᵣ vSrc)) := by
  have base := jset_reg_spec dst src vDst vSrc pc target; rwa [if_pos h] at base

end SVM.SBPF
