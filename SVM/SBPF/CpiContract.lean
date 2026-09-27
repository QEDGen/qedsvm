/-
  CPI contracts in separation-logic form, for composing a caller's path
  across an invoke (the suffix after `Cpi.cuTripleWithinMem_cpi_bridge`).

  `cpiTriple callee Pc Qc`: from any state owning `Pc` framed by `R`, every
  result the callee contract admits lands in `Qc r ** R` after
  `Cpi.applyResult`. `applyResult` rewrites r0 and the return-data buffer, so
  `Pc` must own both; on success it installs the callee's proposed memory, so
  preserving `R`'s memory is the contract's obligation.

  `cpiTriple_of_mem_preserving` discharges the triple for callees that never
  change caller memory (zero-account or read-only CPIs): the result's code
  lands in r0 and its return data in the owned buffer, everything else framed.
-/

import SVM.SBPF.CpiBridge

namespace SVM.SBPF

namespace PartialState

/-- The right half of a compatible disjoint union is itself compatible. -/
theorem CompatibleWith.of_union_right {h1 h2 hp : PartialState} {s : State}
    (hc : hp.CompatibleWith s) (hu : h1.union h2 = hp) (hd : h1.Disjoint h2) :
    h2.CompatibleWith s where
  regs r v h := by
    rcases hd.regs r with hn | hn
    · exact hc.regs r v (by rw [← hu, union_regs_of_left_none hn]; exact h)
    · rw [hn] at h; cases h
  mem a v h := by
    rcases hd.mem a with hn | hn
    · exact hc.mem a v (by rw [← hu, union_mem_of_left_none hn]; exact h)
    · rw [hn] at h; cases h
  pc v h := by
    rcases hd.pc with hn | hn
    · exact hc.pc v (by rw [← hu, union_pc_of_left_none hn]; exact h)
    · rw [hn] at h; cases h
  returnData rd h := by
    rcases hd.returnData with hn | hn
    · exact hc.returnData rd (by rw [← hu, union_returnData_of_left_none hn]; exact h)
    · rw [hn] at h; cases h
  callStack cs h := by
    rcases hd.callStack with hn | hn
    · exact hc.callStack cs (by rw [← hu, union_callStack_of_left_none hn]; exact h)
    · rw [hn] at h; cases h

end PartialState

namespace Cpi

open PartialState

/-- Separation-logic CPI contract: `Pc ** R` before the invoke, `Qc r ** R`
    after `applyResult` for every result `r` the callee admits. -/
def cpiTriple (callee : CalleeSemantics) (Pc : Assertion)
    (Qc : CalleeResult → Assertion) : Prop :=
  ∀ (R : Assertion), R.pcFree →
  ∀ (s : State) (r : CalleeResult),
    (Pc ** R).holdsFor s → callee s r → (Qc r ** R).holdsFor (applyResult s r)

/-- The owned r0 + return-data footprint as a partial state. -/
private def r0RdState (v : Nat) (rd : ByteArray) : PartialState :=
  (singletonReg .r0 v).union (singletonReturnData rd)

private theorem r0Rd_disjoint (v : Nat) (rd : ByteArray) :
    (singletonReg .r0 v).Disjoint (singletonReturnData rd) where
  regs _ := Or.inr (singletonReturnData_regs _)
  mem _ := Or.inl (singletonReg_mem _)
  pc := Or.inl singletonReg_pc
  returnData := Or.inl singletonReg_returnData
  callStack := Or.inl singletonReg_callStack

private theorem r0Rd_sat (v : Nat) (rd : ByteArray) :
    ((.r0 ↦ᵣ v) ** returnDataIs rd) (r0RdState v rd) :=
  ⟨_, _, r0Rd_disjoint v rd, rfl, rfl, rfl⟩

private theorem r0Rd_regs_r0 (v : Nat) (rd : ByteArray) :
    (r0RdState v rd).regs .r0 = some v :=
  union_regs_of_left_some singletonReg_regs_self

private theorem r0Rd_regs_other (v : Nat) (rd : ByteArray) {reg : Reg} (h : reg ≠ .r0) :
    (r0RdState v rd).regs reg = none := by
  unfold r0RdState
  rw [union_regs_of_left_none (singletonReg_regs_other h)]
  exact singletonReturnData_regs _

private theorem r0Rd_returnData (v : Nat) (rd : ByteArray) :
    (r0RdState v rd).returnData = some rd := by
  unfold r0RdState
  rw [union_returnData_of_left_none singletonReg_returnData]
  exact singletonReturnData_returnData_self

/-- A callee that never changes caller memory satisfies the r0/return-data
    CPI triple: the result code lands in r0 and its return data in the owned
    buffer; every framed register, memory cell and the call stack survive. -/
theorem cpiTriple_of_mem_preserving (callee : CalleeSemantics) (v : Nat) (rd : ByteArray)
    (hMem : ∀ s r, callee s r → r.mem = s.mem) :
    cpiTriple callee ((.r0 ↦ᵣ v) ** returnDataIs rd)
      (fun r => (.r0 ↦ᵣ r.code) ** returnDataIs r.returnData) := by
  intro R hR s r hPre hCallee
  obtain ⟨hp, hcompat, h1, h2, hd12, hu12, hPc, hRh2⟩ := hPre
  obtain ⟨a, b, _, huab, ha, hb⟩ := hPc
  subst ha hb
  have h1Eq : h1 = r0RdState v rd := huab.symm
  subst h1Eq
  have h2r0 : h2.regs .r0 = none :=
    (hd12.regs .r0).resolve_left (by rw [r0Rd_regs_r0]; simp)
  have h2rd : h2.returnData = none :=
    hd12.returnData.resolve_left (by rw [r0Rd_returnData]; simp)
  have h2pc : h2.pc = none := hR h2 hRh2
  have hc2 : h2.CompatibleWith s := CompatibleWith.of_union_right hcompat hu12 hd12
  have hMemEq : (applyResult s r).mem = s.mem := by
    by_cases hc : r.code = 0
    · rw [applyResult_mem_success s r hc, hMem s r hCallee]
    · exact applyResult_mem_failure s r hc
  let h1' := r0RdState r.code r.returnData
  have hd' : h1'.Disjoint h2 :=
    { regs := fun reg => by
        by_cases hreg : reg = .r0
        · subst hreg; exact Or.inr h2r0
        · exact Or.inl (r0Rd_regs_other _ _ hreg)
      mem := fun _ => Or.inl (by simp [h1', r0RdState, union_mem_of_left_none])
      pc := Or.inl (by simp [h1', r0RdState, union_pc_of_left_none])
      returnData := Or.inr h2rd
      callStack := Or.inl (by simp [h1', r0RdState]) }
  refine ⟨h1'.union h2, ?_, h1', h2, hd', rfl, r0Rd_sat _ _, hRh2⟩
  refine
    { regs := ?_, mem := ?_, pc := ?_, returnData := ?_, callStack := ?_ }
  · intro reg val hval
    by_cases hreg : reg = .r0
    · subst hreg
      rw [union_regs_of_left_some (r0Rd_regs_r0 _ _)] at hval
      cases hval
      rfl
    · rw [union_regs_of_left_none (r0Rd_regs_other _ _ hreg)] at hval
      rw [← hc2.regs reg val hval]
      cases reg <;> first | exact absurd rfl hreg | rfl
  · intro addr val hval
    rw [union_mem_of_left_none (by simp [h1', r0RdState, union_mem_of_left_none])] at hval
    rw [hMemEq]
    exact hc2.mem addr val hval
  · intro val hval
    rw [union_pc_of_left_none (by simp [h1', r0RdState, union_pc_of_left_none]), h2pc] at hval
    cases hval
  · intro val hval
    rw [union_returnData_of_left_some (r0Rd_returnData _ _)] at hval
    cases hval
    rfl
  · intro cs hval
    rw [union_callStack_of_left_none (by simp [h1', r0RdState])] at hval
    exact hc2.callStack cs hval

/-- A caller path across one CPI: prefix from `entry` to the invoke at
    `invokePc`, the CPI transition, and a suffix from `invokePc + 1` to
    `exit_`. For every transition the callee contract admits there is a
    result `r`; whenever `r` satisfies the path guard `G` (e.g. `r.code = 0`
    for the success path) and the remaining budget covers the suffix, the
    suffix reaches `exit_` in `Post r ** R`. The suffix budget is stated on
    the post-CPI state because the callee's compute usage is part of `r`. -/
def cpiPathWithinMem (N1 M1 entry invokePc N2 M2 exit_ : Nat) (cr1 cr2 : CodeReq)
    (P : Assertion) (Post : CalleeResult → Assertion)
    (rr1 rr2 : Memory.RegionTable → Prop) (sc : Syscall)
    (callee : CalleeSemantics) (G : CalleeResult → Prop) : Prop :=
  ∀ (R : Assertion), R.pcFree →
  ∀ (fetch : Nat → Option Insn),
    (cr1.union (CodeReq.singleton invokePc (.call sc))).SatisfiedBy fetch →
    cr2.SatisfiedBy fetch →
  ∀ (s : State), (P ** R).holdsFor s → s.pc = entry → s.exitCode = none →
    s.cuConsumed + N1 + M1 ≤ s.cuBudget → rr1 s.regions → rr2 s.regions →
    ∃ k1, k1 ≤ N1 ∧
      (executeFn fetch s k1).pc = invokePc ∧
      fetch invokePc = some (.call sc) ∧
      (executeFn fetch s k1).exitCode = none ∧
      ∀ s', Transitions callee (executeFn fetch s k1) s' →
        ∃ r, callee (executeFn fetch s k1) r ∧ s' = applyResult (executeFn fetch s k1) r ∧
          (G r → s'.cuConsumed + N2 + M2 ≤ s'.cuBudget →
            ∃ k2, k2 ≤ N2 ∧
              (executeFn fetch s' k2).pc = exit_ ∧
              (executeFn fetch s' k2).exitCode = none ∧
              (executeFn fetch s' k2).cuConsumed ≤ s'.cuConsumed + N2 + M2 ∧
              (Post r ** R).holdsFor (executeFn fetch s' k2))

/-- Compose a prefix triple ending at the invoke (post `Pc ** F`), a CPI
    contract `cpiTriple callee Pc Qc`, and a guarded suffix triple from
    `invokePc + 1` (pre `Qc r ** F`) into one caller path across the CPI. -/
theorem cpi_path_compose
    {N1 M1 entry invokePc N2 M2 exit_ : Nat} {cr1 cr2 : CodeReq}
    {P Pc F : Assertion} {Qc Post : CalleeResult → Assertion}
    {rr1 rr2 : Memory.RegionTable → Prop} {callee : CalleeSemantics}
    {G : CalleeResult → Prop}
    (hPre : cuTripleWithinMem N1 M1 entry invokePc cr1 P (Pc ** F) rr1)
    (hFresh : cr1 invokePc = none) (hF : F.pcFree)
    (hC : cpiTriple callee Pc Qc)
    (hSuf : ∀ r, G r →
      cuTripleWithinMem N2 M2 (invokePc + 1) exit_ cr2 (Qc r ** F) (Post r) rr2)
    (sc : Syscall) :
    cpiPathWithinMem N1 M1 entry invokePc N2 M2 exit_ cr1 cr2 P Post rr1 rr2 sc callee G := by
  intro R hR fetch hcr1 hcr2 s hP hpc hex hbud hrr1 hrr2
  have hInv : fetch invokePc = some (.call sc) := by
    apply hcr1 invokePc
    show (match cr1 invokePc with | some i => some i | none => _) = _
    rw [hFresh]
    exact CodeReq.singleton_self
  obtain ⟨k1, hk1, hpc1, hex1, _, hQ⟩ :=
    hPre R hR fetch (CodeReq.SatisfiedBy_of_union_left hcr1) s hP hpc hex hbud hrr1
  refine ⟨k1, hk1, hpc1, hInv, hex1, ?_⟩
  rintro s' ⟨r, hr, rfl⟩
  refine ⟨r, hr, rfl, fun hG hbud2 => ?_⟩
  have hMid := hC (F ** R) (pcFree_sepConj hF hR) _ r (holdsFor_sepConj_assoc.mp hQ) hr
  exact hSuf r hG R hR fetch hcr2 _ (holdsFor_sepConj_assoc.mpr hMid)
    (by simp [applyResult, hpc1]) (by simp [applyResult, hex1]) hbud2
    (by simp [applyResult, executeFn_preserves_regions, hrr2])

end Cpi
end SVM.SBPF
