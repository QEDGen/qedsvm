import SVM.SBPF.InstructionSpecs.MemDwordStore

namespace SVM.SBPF

open Memory

/-! ## Control flow: unconditional jump

`ja target` writes only the PC, so both pre- and post are `emp`: the
universally-quantified `R` frame carries every actual resource unchanged. -/

/-- `ja target`: unconditional jump. PC moves from `pc` to `target`
    in one step, charging 1 CU. -/
theorem ja_spec (target pc : Nat) :
    cuTripleWithin 1 0 pc target (CodeReq.singleton pc (.ja target))
      emp emp := by
  intro R hRfree fetch hcr s hPR hpc hex hbud
  obtain ⟨hp, hcompat, h1, hR, hd, hu, hP1, hRsat⟩ := hPR
  rw [hP1, PartialState.union_empty_left] at hu
  rw [hP1] at hd
  clear hP1 h1
  have hcr_regs := hcompat.regs
  have hcm_mem := hcompat.mem
  have hcp_pc := hcompat.pc
  have hfetch : fetch s.pc = some (.ja target) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hexec : executeFn fetch s 1 = chargeCu { s with pc := target } := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch,
        executeFn_zero]
    simp only [step]
  have hR_no_pc : hR.pc = none := hRfree _ hRsat
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_, ?_⟩
  · rw [hexec]; rfl
  · rw [hexec]; exact hex
  · rw [hexec]; show s.cuConsumed + 1 ≤ s.cuConsumed + 1 + 0; omega
  · rw [hexec]
    refine ⟨PartialState.empty.union hR, ?_,
            PartialState.empty, hR,
            PartialState.Disjoint_empty_left, rfl, rfl, hRsat⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
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

/-! ## Indirect call: `callx`

Per `Execute.lean`, `.callx reg` is a tail-call/panic-style jump: PC moves
to `regs[reg]`, no callStack push, no register writes. The exit PC is
value-dependent (`vReg`), so the caller must know `reg`'s entry value to
compose this into a chain.

Built by specializing `cuTripleWithin_1reg_cjump` with `cond := True`,
`target := vReg` (so `if True then vReg else pc + 1` reduces to `vReg`). -/

/-- `callx reg`: indirect call. The model fails closed (real sBPF V0
    frame-push + vaddr→PC translation + depth check are not modeled), so
    a step on `.callx` aborts with `ERR_UNSUPPORTED_INSTRUCTION`. A lift
    that reaches a `callx` therefore proves an ABORT at that point. See
    docs/SOUNDNESS_AUDIT_* (C2). -/
theorem callx_aborts_spec (reg : Reg) (pc : Nat) :
    cuTripleAbortsWithin 1 0 pc
      (CodeReq.singleton pc (.callx reg))
      emp ERR_UNSUPPORTED_INSTRUCTION := by
  intro R hRfree fetch hcr s hPR hpc hex hbud
  obtain ⟨hp, hcompat, h1, hR, hd, hu, hP1, hRsat⟩ := hPR
  rw [hP1, PartialState.union_empty_left] at hu
  rw [hP1] at hd
  clear hP1 h1
  have hfetch : fetch s.pc = some (.callx reg) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hexec : executeFn fetch s 1 = chargeCu (step (.callx reg) s) := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch, executeFn_zero]
  refine ⟨1, Nat.le_refl 1, ?_, ?_⟩
  · rw [hexec]
    show (step (.callx reg) s).exitCode = some ERR_UNSUPPORTED_INSTRUCTION
    rfl
  · rw [hexec]; simp [step]


end SVM.SBPF
