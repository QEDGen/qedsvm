import SVM.SBPF.InstructionSpecs.Syscalls.Pda

namespace SVM.SBPF

open Memory

/-! ## Generic fixed-payload-write helper: `cuTripleWithin_syscall_writesR1Bytes`

The 6 fixed-payload sysvars (rent/last_restart_slot/fees/clock/epoch_rewards/
epoch_schedule) share one Hoare shape: write a fixed `ByteArray` of size `N` at
`*r1`, set `r0 := 0`. Parametric in `(sc, bsNew)` via the generic `↦Bytes` atom,
so the proof scales to 17B / 40B / 81B without per-byte case ladders. Zero-fill
case is `bsNew := zerosByteArray N`. -/

/-- `ByteArray` of `n` copies of byte `b` (generalizes `zerosByteArray`).
    Post-state payload for `sol_memset_` Hoare triples. -/
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

-- `Mem_read_default` is hoisted to the top of the file (shared by sysvar specs).

/-- For any syscall `sc` whose `step` writes 0 to r0, writes `bsNew` at
    `[r1, r1+bsNew.size)`, leaves other mem/exit untouched, and advances pc, the
    Hoare triple

      `(r0 ↦ᵣ r0Old) ** (r1 ↦ᵣ r1V) ** (r1V ↦Bytes bsOld)`
      ↓
      `(r0 ↦ᵣ 0)     ** (r1 ↦ᵣ r1V) ** (r1V ↦Bytes bsNew)`

    holds for any `bsOld` of `bsNew`'s size. Concrete sysvar specs supply the
    step-projection lemmas via `simp [step, execSyscall, Sysvar.execX]`. -/
theorem cuTripleWithin_syscall_writesR1Bytes
    (sc : Syscall) (bsNew : ByteArray) (pc : Nat) (nCu : Nat)
    (h_step_regs : ∀ s : State, (step (.call sc) s).regs = s.regs.set .r0 0)
    (h_step_mem_in  : ∀ s : State, ∀ i, i < bsNew.size →
        (step (.call sc) s).mem (s.regs.r1 + i) = (bsNew.get! i).toNat)
    (h_step_mem_out : ∀ s : State, ∀ a,
        (a < s.regs.r1 ∨ a ≥ s.regs.r1 + bsNew.size) →
        (step (.call sc) s).mem a = s.mem a)
    (h_step_pc   : ∀ s : State, (step (.call sc) s).pc = s.pc + 1)
    (h_step_exit : ∀ s : State, s.exitCode = none →
        (step (.call sc) s).exitCode = none)
    (h_step_returnData :
      ∀ s : State, (step (.call sc) s).returnData = s.returnData)
    (h_step_callStack :
      ∀ s : State, (step (.call sc) s).callStack = s.callStack)
    (h_step_cu : ∀ s : State,
        (step (.call sc) s).cuConsumed ≤ s.cuConsumed + nCu) :
    ∀ r0Old r1V (bsOld : ByteArray), bsOld.size = bsNew.size →
      cuTripleWithin 1 nCu pc (pc + 1)
        (CodeReq.singleton pc (.call sc))
        ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1V) ** (r1V ↦Bytes bsOld))
        ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ r1V) ** (r1V ↦Bytes bsNew)) := by
  intro r0Old r1V bsOld hbsSize R hRfree fetch hcr s hPR hpc hex hbud
  let N : Nat := bsNew.size
  obtain ⟨hp, hcompat, h_P, h_R, hd_PR, hu_PR, h_P_sat, h_R_sat⟩ := hPR
  obtain ⟨h_r0, h_T1, hd_r0_T1, hu_r0_T1, h_r0_pred, h_T1_sat⟩ := h_P_sat
  obtain ⟨h_r1, h_b, hd_r1_b, hu_r1_b, h_r1_pred, h_b_pred⟩ := h_T1_sat
  rw [h_r0_pred] at hu_r0_T1 hd_r0_T1
  rw [h_r1_pred] at hu_r1_b hd_r1_b
  rw [h_b_pred] at hu_r1_b hd_r1_b
  clear h_r0_pred h_r1_pred h_b_pred h_r0 h_r1 h_b
  have hcr_regs := hcompat.regs
  have hcm_mem := hcompat.mem
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
  have hfetch : fetch s.pc = some (.call sc) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hstep_eq : executeFn fetch s 1 = chargeCu (step (.call sc) s) := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch, executeFn_zero]
  have hexec_pc : (executeFn fetch s 1).pc = s.pc + 1 := by
    rw [hstep_eq]; exact h_step_pc s
  have hexec_exit : (executeFn fetch s 1).exitCode = none := by
    rw [hstep_eq]; exact h_step_exit s hex
  have hexec_cu : (executeFn fetch s 1).cuConsumed ≤ s.cuConsumed + 1 + nCu := by
    rw [hstep_eq]
    show (step (.call sc) s).cuConsumed + 1 ≤ s.cuConsumed + 1 + nCu
    have := h_step_cu s; omega
  have hexec_regs : (executeFn fetch s 1).regs = s.regs.set .r0 0 := by
    rw [hstep_eq]; exact h_step_regs s
  have hexec_mem_in (i : Nat) (hi : i < N) :
      (executeFn fetch s 1).mem (r1V + i) = (bsNew.get! i).toNat := by
    rw [hstep_eq, ← hs_r1_field]; exact h_step_mem_in s i hi
  have hexec_mem_out (a : Nat) (h : a < r1V ∨ a ≥ r1V + N) :
      (executeFn fetch s 1).mem a = s.mem a := by
    rw [hstep_eq]; apply h_step_mem_out s a
    rw [hs_r1_field]; exact h
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
  have h_R_no_pc : h_R.pc = none := hRfree _ h_R_sat
  have h_R_no_mem_in (i : Nat) (hi : i < N) : h_R.mem (r1V + i) = none := by
    obtain ⟨v, hatom⟩ := PartialState.singletonMemBytes_mem_isSome r1V bsOld
      (r1V + i) ⟨Nat.le_add_right _ _, by rw [hbsSize]; show r1V + i < r1V + N; omega⟩
    have h_P_some : h_P.mem (r1V + i) = some v := by
      rw [h_P_mem_eq_b]; exact hatom
    rcases hd_PR_mem (r1V + i) with hl | hr
    · rw [h_P_some] at hl; nomatch hl
    · exact hr
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
    refine ⟨fun r => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
    · right; exact PartialState.singletonMemBytes_regs r
    · left; exact PartialState.singletonReg_mem a
    · left; exact PartialState.singletonReg_pc
  have hd_r0_T1_new : h_r0_new.Disjoint h_T1_new := by
    refine ⟨fun r => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
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
  have hd_PnewR : h_P_new.Disjoint h_R := by
    refine ⟨fun r => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
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
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_, ?_⟩
  · rw [hexec_pc, hpc]
  · exact hexec_exit
  · exact hexec_cu
  · refine ⟨h_P_new.union h_R, ?_, h_P_new, h_R, hd_PnewR, rfl,
            ⟨h_r0_new, h_T1_new, hd_r0_T1_new, rfl, rfl,
             h_r1_new, h_b_new, hd_r1_b_new, rfl, rfl, rfl⟩,
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
    · intro rd hva
      have h_P_new_rd : h_P_new.returnData = none := by rfl
      rw [PartialState.union_returnData_of_left_none h_P_new_rd] at hva
      have h_P_rd : h_P.returnData = none := by
        rw [← hu_r0_T1, ← hu_r1_b]; rfl
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
        rw [← hu_r0_T1, ← hu_r1_b]; rfl
      have hp_cs : hp.callStack = some cs := by
        rw [← hu_PR, PartialState.union_callStack_of_left_none h_P_cs]
        exact hva
      have hexec_cs : (executeFn fetch s 1).callStack = s.callStack := by
        rw [hstep_eq]; exact h_step_callStack s
      rw [hexec_cs]
      exact hcompat.callStack cs hp_cs
/-! ## 5-atom mem-write helper: `cuTripleWithin_syscall_writesR1Bytes_r2r3`

Generalizes the fixed-payload helper for syscalls whose mem-write payload
depends on `r2V`/`r3V` (memset, memcpy, memmove, memcmp). The precondition adds
`r2 ↦ᵣ r2V` + `r3 ↦ᵣ r3V` so the body extracts those values for the
register-pinned step-projection hyps. `bsNew` is the post payload computed from
`r2V`/`r3V` (e.g. `replicateByte (r2V % 256) r3V` for memset). -/

theorem cuTripleWithin_syscall_writesR1Bytes_r2r3
    (sc : Syscall) (bsNew : ByteArray) (pc : Nat) (nCu : Nat) (r2V r3V : Nat)
    (h_step_regs : ∀ s : State,
        s.regions.containsWritable s.regs.r1 s.regs.r3 = true →
        (step (.call sc) s).regs = s.regs.set .r0 0)
    (h_step_mem_in  : ∀ s : State, s.regs.r2 = r2V → s.regs.r3 = r3V →
        s.regions.containsWritable s.regs.r1 s.regs.r3 = true →
        ∀ i, i < bsNew.size →
        (step (.call sc) s).mem (s.regs.r1 + i) = (bsNew.get! i).toNat)
    (h_step_mem_out : ∀ s : State, s.regs.r3 = r3V →
        s.regions.containsWritable s.regs.r1 s.regs.r3 = true →
        ∀ a, (a < s.regs.r1 ∨ a ≥ s.regs.r1 + bsNew.size) →
        (step (.call sc) s).mem a = s.mem a)
    (h_step_pc   : ∀ s : State, (step (.call sc) s).pc = s.pc + 1)
    (h_step_exit : ∀ s : State, s.exitCode = none →
        s.regions.containsWritable s.regs.r1 s.regs.r3 = true →
        (step (.call sc) s).exitCode = none)
    (h_step_returnData :
      ∀ s : State, (step (.call sc) s).returnData = s.returnData)
    (h_step_callStack :
      ∀ s : State, (step (.call sc) s).callStack = s.callStack)
    (h_step_cu : ∀ s : State,
        (step (.call sc) s).cuConsumed ≤ s.cuConsumed + nCu) :
    ∀ r0Old r1V (bsOld : ByteArray), bsOld.size = bsNew.size →
      -- H6: dest slice `[r1V, r1V+r3V)` must be writable (`guardWrite` in
      -- `execSet`); carried as the `rr` requirement, discharged by the bullets.
      cuTripleWithinMem 1 nCu pc (pc + 1)
        (CodeReq.singleton pc (.call sc))
        ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V)
         ** (r1V ↦Bytes bsOld))
        ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V)
         ** (r1V ↦Bytes bsNew))
        (fun rt => rt.containsWritable r1V r3V = true) := by
  intro r0Old r1V bsOld hbsSize R hRfree fetch hcr s hPR hpc hex hbud h_region
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
  -- `rr` specialised to this state's regs, collapsing `guardWrite` in step.
  have hreg : s.regions.containsWritable s.regs.r1 s.regs.r3 = true := by
    rw [hs_r1_field, hs_r3_field]; exact h_region
  have hfetch : fetch s.pc = some (.call sc) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hstep_eq : executeFn fetch s 1 = chargeCu (step (.call sc) s) := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch, executeFn_zero]
  have hexec_pc : (executeFn fetch s 1).pc = s.pc + 1 := by
    rw [hstep_eq]; exact h_step_pc s
  have hexec_exit : (executeFn fetch s 1).exitCode = none := by
    rw [hstep_eq]; exact h_step_exit s hex hreg
  have hexec_cu : (executeFn fetch s 1).cuConsumed ≤ s.cuConsumed + 1 + nCu := by
    rw [hstep_eq]
    show (step (.call sc) s).cuConsumed + 1 ≤ s.cuConsumed + 1 + nCu
    have := h_step_cu s; omega
  have hexec_regs : (executeFn fetch s 1).regs = s.regs.set .r0 0 := by
    rw [hstep_eq]; exact h_step_regs s hreg
  have hexec_mem_in (i : Nat) (hi : i < N) :
      (executeFn fetch s 1).mem (r1V + i) = (bsNew.get! i).toNat := by
    rw [hstep_eq, ← hs_r1_field]
    exact h_step_mem_in s hs_r2_field hs_r3_field hreg i hi
  have hexec_mem_out (a : Nat) (h : a < r1V ∨ a ≥ r1V + N) :
      (executeFn fetch s 1).mem a = s.mem a := by
    rw [hstep_eq]
    apply h_step_mem_out s hs_r3_field hreg a
    rw [hs_r1_field]; exact h
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
  have h_R_no_mem_in (i : Nat) (hi : i < N) : h_R.mem (r1V + i) = none := by
    obtain ⟨v, hatom⟩ := PartialState.singletonMemBytes_mem_isSome r1V bsOld
      (r1V + i) ⟨Nat.le_add_right _ _, by rw [hbsSize]; show r1V + i < r1V + N; omega⟩
    have h_P_some : h_P.mem (r1V + i) = some v := by
      rw [h_P_mem_eq_b]; exact hatom
    rcases hd_PR_mem (r1V + i) with hl | hr
    · rw [h_P_some] at hl; nomatch hl
    · exact hr
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
/-! ## Syscall: `sol_memset_`

`sol_memset_(dst, val, n)`: write `r2 % 256` into `n = r3` bytes at `dst = r1`,
set `r0 := 0`. First state-dependent payload syscall, so it uses the 5-atom
helper (bytes written depend on `r2V`/`r3V`). -/

theorem call_sol_memset_spec
    (r0Old r1V r2V r3V pc nCu : Nat) (bsOld : ByteArray) (hbs : bsOld.size = r3V)
    (hCu : ∀ s : State,
        (step (.call .sol_memset) s).cuConsumed ≤ s.cuConsumed + nCu) :
    -- H6: the `[r1V, r1V + r3V)` destination must be in a writable region.
    cuTripleWithinMem 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_memset))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V)
       ** (r1V ↦Bytes bsOld))
      ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V)
       ** (r1V ↦Bytes (replicateByte (r2V % 256).toUInt8 r3V)))
      (fun rt => rt.containsWritable r1V r3V = true) := by
  refine cuTripleWithin_syscall_writesR1Bytes_r2r3
    .sol_memset (replicateByte (r2V % 256).toUInt8 r3V) pc nCu r2V r3V
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hCu r0Old r1V bsOld ?_
  · intro s hreg
    simp only [step, execSyscall, MemOps.execSet, State.guardWrite]
    rw [if_pos (Or.inr hreg)]
  · intro s hr2 hr3 hreg i hi
    rw [replicateByte_size] at hi
    simp only [step, execSyscall, MemOps.execSet, State.guardWrite]
    rw [if_pos (Or.inr hreg)]
    rw [Mem_read_default]
    rw [if_pos ⟨Nat.le_add_right _ _, by rw [hr3]; omega⟩]
    rw [replicateByte_get! _ _ _ hi]
    rw [hr2]
    show r2V % 256 = (UInt8.ofNat (r2V % 256)).toNat
    unfold UInt8.ofNat UInt8.toNat
    simp
  · intro s hr3 hreg a ha
    rw [replicateByte_size] at ha
    simp only [step, execSyscall, MemOps.execSet, State.guardWrite]
    rw [if_pos (Or.inr hreg)]
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
  · intro s hex hreg
    simp only [step, execSyscall, MemOps.execSet, State.guardWrite]
    rw [if_pos (Or.inr hreg)]
    exact hex
  · intro s
    simp only [step, execSyscall, MemOps.execSet, State.guardWrite, State.accessFault]
    split <;> rfl
  · intro s
    simp only [step, execSyscall, MemOps.execSet, State.guardWrite, State.accessFault]
    split <;> rfl
  · rw [replicateByte_size]; exact hbs

/-! ## 6-atom mem-copy helper: `cuTripleWithin_syscall_copiesR2ToR1`

Generalizes the 5-atom helper for syscalls copying `[r2, r2+r3)` → `[r1, r1+r3)`
(`sol_memcpy_`, `sol_memmove_`). Adds a read-only source-bytes atom at `r2V`; the
post keeps it and rewrites the dst-bytes atom to `srcBytes`. `execCopy`'s `% 256`
is a no-op on bytes (`UInt8.toNat _ < 256`), so the post matches `srcBytes`.
Separation logic forces source/dest disjoint (memcpy overlap is UB; overlapping
memmove would need a different spec). -/

theorem cuTripleWithin_syscall_copiesR2ToR1
    (sc : Syscall) (pc : Nat) (nCu : Nat) (r2V r3V : Nat) (srcBytes : ByteArray)
    (hsrcSize : srcBytes.size = r3V)
    (h_step_regs : ∀ s : State,
        s.regions.containsRange s.regs.r2 s.regs.r3 = true →
        s.regions.containsWritable s.regs.r1 s.regs.r3 = true →
        (step (.call sc) s).regs = s.regs.set .r0 0)
    (h_step_mem_in  : ∀ s : State, s.regs.r2 = r2V → s.regs.r3 = r3V →
        s.regions.containsRange s.regs.r2 s.regs.r3 = true →
        s.regions.containsWritable s.regs.r1 s.regs.r3 = true →
        ∀ i, i < r3V →
        (step (.call sc) s).mem (s.regs.r1 + i) = s.mem (s.regs.r2 + i) % 256)
    (h_step_mem_out : ∀ s : State, s.regs.r3 = r3V →
        s.regions.containsRange s.regs.r2 s.regs.r3 = true →
        s.regions.containsWritable s.regs.r1 s.regs.r3 = true →
        ∀ a, (a < s.regs.r1 ∨ a ≥ s.regs.r1 + r3V) →
        (step (.call sc) s).mem a = s.mem a)
    (h_step_pc   : ∀ s : State, (step (.call sc) s).pc = s.pc + 1)
    (h_step_exit : ∀ s : State, s.exitCode = none →
        s.regions.containsRange s.regs.r2 s.regs.r3 = true →
        s.regions.containsWritable s.regs.r1 s.regs.r3 = true →
        (step (.call sc) s).exitCode = none)
    (h_step_returnData :
      ∀ s : State, (step (.call sc) s).returnData = s.returnData)
    (h_step_callStack :
      ∀ s : State, (step (.call sc) s).callStack = s.callStack)
    (h_step_cu : ∀ s : State,
        (step (.call sc) s).cuConsumed ≤ s.cuConsumed + nCu) :
    ∀ r0Old r1V (bsOld : ByteArray), bsOld.size = r3V →
      -- H6: `[r2V, r2V+r3V)` (src) must be readable, `[r1V, r1V+r3V)`
      -- (dst) writable; both ride the `rr` region requirement.
      cuTripleWithinMem 1 nCu pc (pc + 1)
        (CodeReq.singleton pc (.call sc))
        ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V)
         ** (r2V ↦Bytes srcBytes) ** (r1V ↦Bytes bsOld))
        ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V)
         ** (r2V ↦Bytes srcBytes) ** (r1V ↦Bytes srcBytes))
        (fun rt => rt.containsRange r2V r3V = true ∧
                   rt.containsWritable r1V r3V = true) := by
  intro r0Old r1V bsOld hbsSize R hRfree fetch hcr s hPR hpc hex hbud h_region
  obtain ⟨hp, hcompat, h_P, h_R, hd_PR, hu_PR, h_P_sat, h_R_sat⟩ := hPR
  obtain ⟨h_r0, h_T1, hd_r0_T1, hu_r0_T1, h_r0_pred, h_T1_sat⟩ := h_P_sat
  obtain ⟨h_r1, h_T2, hd_r1_T2, hu_r1_T2, h_r1_pred, h_T2_sat⟩ := h_T1_sat
  obtain ⟨h_r2, h_T3, hd_r2_T3, hu_r2_T3, h_r2_pred, h_T3_sat⟩ := h_T2_sat
  obtain ⟨h_r3, h_T4, hd_r3_T4, hu_r3_T4, h_r3_pred, h_T4_sat⟩ := h_T3_sat
  obtain ⟨h_src, h_b, hd_src_b, hu_src_b, h_src_pred, h_b_pred⟩ := h_T4_sat
  rw [h_r0_pred]  at hu_r0_T1 hd_r0_T1
  rw [h_r1_pred]  at hu_r1_T2 hd_r1_T2
  rw [h_r2_pred]  at hu_r2_T3 hd_r2_T3
  rw [h_r3_pred]  at hu_r3_T4 hd_r3_T4
  rw [h_src_pred] at hu_src_b hd_src_b
  rw [h_b_pred]   at hu_src_b hd_src_b
  clear h_r0_pred h_r1_pred h_r2_pred h_r3_pred h_src_pred h_b_pred
        h_r0 h_r1 h_r2 h_r3 h_src h_b
  have hcr_regs := hcompat.regs
  have hcm_mem := hcompat.mem
  -- Source-bytes mem facts:
  have h_T4_mem_src (j : Nat) (hj : j < r3V) :
      h_T4.mem (r2V + j) = some (srcBytes.get! j).toNat := by
    rw [← hu_src_b]
    have hsrcSize_lt : j < srcBytes.size := by rw [hsrcSize]; exact hj
    exact PartialState.union_mem_of_left_some
      (PartialState.singletonMemBytes_mem_at r2V srcBytes j hsrcSize_lt)
  have h_T3_mem_src (j : Nat) (hj : j < r3V) :
      h_T3.mem (r2V + j) = some (srcBytes.get! j).toNat := by
    rw [← hu_r3_T4,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact h_T4_mem_src j hj
  have h_T2_mem_src (j : Nat) (hj : j < r3V) :
      h_T2.mem (r2V + j) = some (srcBytes.get! j).toNat := by
    rw [← hu_r2_T3,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact h_T3_mem_src j hj
  have h_T1_mem_src (j : Nat) (hj : j < r3V) :
      h_T1.mem (r2V + j) = some (srcBytes.get! j).toNat := by
    rw [← hu_r1_T2,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact h_T2_mem_src j hj
  have h_P_mem_src (j : Nat) (hj : j < r3V) :
      h_P.mem (r2V + j) = some (srcBytes.get! j).toNat := by
    rw [← hu_r0_T1,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact h_T1_mem_src j hj
  -- Regs: climb r0/r1/r2/r3 up.
  have h_T3_regs_r3 : h_T3.regs .r3 = some r3V := by
    rw [← hu_r3_T4]
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
  -- Over dst range [r1V, r1V+r3V), h_b carries h_P.mem (src range disjoint).
  have h_P_mem_dst (i : Nat) (hi : i < r3V) :
      h_P.mem (r1V + i) = some (bsOld.get! i).toNat := by
    rw [← hu_r0_T1,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _),
        ← hu_r1_T2,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _),
        ← hu_r2_T3,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _),
        ← hu_r3_T4,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _),
        ← hu_src_b]
    have hbs_lt : i < bsOld.size := by rw [hbsSize]; exact hi
    have h_b_some : (PartialState.singletonMemBytes r1V bsOld).mem (r1V + i) =
        some (bsOld.get! i).toNat :=
      PartialState.singletonMemBytes_mem_at r1V bsOld i hbs_lt
    -- src doesn't own r1V+i (b does), so union takes h_b's value.
    have h_src_none : (PartialState.singletonMemBytes r2V srcBytes).mem (r1V + i) = none := by
      have hd_mem := hd_src_b.mem
      rcases hd_mem (r1V + i) with hl | hr
      · exact hl
      · rw [hr] at h_b_some; nomatch h_b_some
    rw [PartialState.union_mem_of_left_none h_src_none]
    exact h_b_some
  have hp_regs_r0 : hp.regs .r0 = some r0Old := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r0
  have hp_regs_r1 : hp.regs .r1 = some r1V := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r1
  have hp_regs_r2 : hp.regs .r2 = some r2V := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r2
  have hp_regs_r3 : hp.regs .r3 = some r3V := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r3
  have hp_mem_src (j : Nat) (hj : j < r3V) :
      hp.mem (r2V + j) = some (srcBytes.get! j).toNat := by
    rw [← hu_PR]; exact PartialState.union_mem_of_left_some (h_P_mem_src j hj)
  have hs_regs_r0 : s.regs.get .r0 = r0Old := hcr_regs .r0 r0Old hp_regs_r0
  have hs_regs_r1 : s.regs.get .r1 = r1V := hcr_regs .r1 r1V hp_regs_r1
  have hs_regs_r2 : s.regs.get .r2 = r2V := hcr_regs .r2 r2V hp_regs_r2
  have hs_regs_r3 : s.regs.get .r3 = r3V := hcr_regs .r3 r3V hp_regs_r3
  have hs_r1_field : s.regs.r1 = r1V := hs_regs_r1
  have hs_r2_field : s.regs.r2 = r2V := hs_regs_r2
  have hs_r3_field : s.regs.r3 = r3V := hs_regs_r3
  have hs_mem_src (j : Nat) (hj : j < r3V) :
      s.mem (r2V + j) = (srcBytes.get! j).toNat := hcm_mem _ _ (hp_mem_src j hj)
  -- `rr` specialised to this state's regs, collapsing the nested guardRead/Write.
  have hRd : s.regions.containsRange s.regs.r2 s.regs.r3 = true := by
    rw [hs_r2_field, hs_r3_field]; exact h_region.1
  have hWr : s.regions.containsWritable s.regs.r1 s.regs.r3 = true := by
    rw [hs_r1_field, hs_r3_field]; exact h_region.2
  have hfetch : fetch s.pc = some (.call sc) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hstep_eq : executeFn fetch s 1 = chargeCu (step (.call sc) s) := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch, executeFn_zero]
  have hexec_pc : (executeFn fetch s 1).pc = s.pc + 1 := by
    rw [hstep_eq]; exact h_step_pc s
  have hexec_exit : (executeFn fetch s 1).exitCode = none := by
    rw [hstep_eq]; exact h_step_exit s hex hRd hWr
  have hexec_cu : (executeFn fetch s 1).cuConsumed ≤ s.cuConsumed + 1 + nCu := by
    rw [hstep_eq]
    show (step (.call sc) s).cuConsumed + 1 ≤ s.cuConsumed + 1 + nCu
    have := h_step_cu s; omega
  have hexec_regs : (executeFn fetch s 1).regs = s.regs.set .r0 0 := by
    rw [hstep_eq]; exact h_step_regs s hRd hWr
  -- Compose the in-range mem fact with the source-bytes value.
  have hexec_mem_in (i : Nat) (hi : i < r3V) :
      (executeFn fetch s 1).mem (r1V + i) = (srcBytes.get! i).toNat := by
    rw [hstep_eq, ← hs_r1_field]
    show (step (.call sc) s).mem (s.regs.r1 + i) = (srcBytes.get! i).toNat
    have h1 := h_step_mem_in s hs_r2_field hs_r3_field hRd hWr i hi
    rw [hs_r2_field] at h1
    rw [h1, hs_mem_src i hi]
    -- (UInt8.toNat _) < 256, so % 256 is a no-op.
    have hlt : (srcBytes.get! i).toNat < 256 := (srcBytes.get! i).toNat_lt
    exact Nat.mod_eq_of_lt hlt
  have hexec_mem_out (a : Nat) (h : a < r1V ∨ a ≥ r1V + r3V) :
      (executeFn fetch s 1).mem a = s.mem a := by
    rw [hstep_eq]
    apply h_step_mem_out s hs_r3_field hRd hWr a
    rw [hs_r1_field]; exact h
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
  have h_R_no_mem_dst (i : Nat) (hi : i < r3V) :
      h_R.mem (r1V + i) = none := by
    rcases hd_PR_mem (r1V + i) with hl | hr
    · rw [h_P_mem_dst i hi] at hl; nomatch hl
    · exact hr
  have h_R_no_mem_src (j : Nat) (hj : j < r3V) :
      h_R.mem (r2V + j) = none := by
    rcases hd_PR_mem (r2V + j) with hl | hr
    · rw [h_P_mem_src j hj] at hl; nomatch hl
    · exact hr
  let h_r0_new : PartialState := PartialState.singletonReg .r0 0
  let h_r1_new : PartialState := PartialState.singletonReg .r1 r1V
  let h_r2_new : PartialState := PartialState.singletonReg .r2 r2V
  let h_r3_new : PartialState := PartialState.singletonReg .r3 r3V
  let h_src_new : PartialState := PartialState.singletonMemBytes r2V srcBytes
  let h_b_new  : PartialState := PartialState.singletonMemBytes r1V srcBytes
  let h_T4_new : PartialState := h_src_new.union h_b_new
  let h_T3_new : PartialState := h_r3_new.union h_T4_new
  let h_T2_new : PartialState := h_r2_new.union h_T3_new
  let h_T1_new : PartialState := h_r1_new.union h_T2_new
  let h_P_new  : PartialState := h_r0_new.union h_T1_new
  -- Post src ⊥ b: same ranges as pre (sizes equal r3V), transferred from hd_src_b.
  have hd_src_b_new : h_src_new.Disjoint h_b_new := by
    refine ⟨fun r => Or.inl (PartialState.singletonMemBytes_regs r),
            fun a => ?_,
            Or.inl PartialState.singletonMemBytes_pc, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
    have hd_pre_mem := hd_src_b.mem
    rcases hd_pre_mem a with hsrc_none | hb_none
    · left; exact hsrc_none
    · right
      apply PartialState.singletonMemBytes_mem_outside
      by_cases h : r1V ≤ a ∧ a < r1V + srcBytes.size
      · exfalso
        obtain ⟨h1, h2⟩ := h
        have h2' : a < r1V + bsOld.size := by rw [hbsSize, ← hsrcSize]; exact h2
        have hlt : a - r1V < bsOld.size := by omega
        have ha_eq : a = r1V + (a - r1V) := by omega
        rw [ha_eq] at hb_none
        rw [PartialState.singletonMemBytes_mem_at r1V bsOld (a - r1V) hlt] at hb_none
        nomatch hb_none
      · rcases Nat.lt_or_ge a r1V with hl | hge
        · left; exact hl
        · right
          rcases Nat.lt_or_ge a (r1V + srcBytes.size) with hlt | hge'
          · exact absurd ⟨hge, hlt⟩ h
          · exact hge'
  have hd_r3_T4_new : h_r3_new.Disjoint h_T4_new := by
    refine ⟨fun r => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
    · right
      show h_T4_new.regs r = none
      show ((PartialState.singletonMemBytes r2V srcBytes).union h_b_new).regs r = none
      rw [PartialState.union_regs_of_left_none (PartialState.singletonMemBytes_regs r)]
      exact PartialState.singletonMemBytes_regs r
    · left; exact PartialState.singletonReg_mem a
    · left; exact PartialState.singletonReg_pc
  have hd_r2_T3_new : h_r2_new.Disjoint h_T3_new := by
    refine ⟨fun r => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
    · by_cases hr2 : r = .r2
      · right
        show h_T3_new.regs r = none
        show ((PartialState.singletonReg .r3 r3V).union h_T4_new).regs r = none
        rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other
              (hr2 ▸ (by decide : Reg.r2 ≠ Reg.r3)))]
        show ((PartialState.singletonMemBytes r2V srcBytes).union h_b_new).regs r = none
        rw [PartialState.union_regs_of_left_none (PartialState.singletonMemBytes_regs r)]
        exact PartialState.singletonMemBytes_regs r
      · left; exact PartialState.singletonReg_regs_other hr2
    · left; exact PartialState.singletonReg_mem a
    · left; exact PartialState.singletonReg_pc
  have hd_r1_T2_new : h_r1_new.Disjoint h_T2_new := by
    refine ⟨fun r => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
    · by_cases hr1 : r = .r1
      · right
        show h_T2_new.regs r = none
        show ((PartialState.singletonReg .r2 r2V).union h_T3_new).regs r = none
        rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other
              (hr1 ▸ (by decide : Reg.r1 ≠ Reg.r2)))]
        show ((PartialState.singletonReg .r3 r3V).union h_T4_new).regs r = none
        rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other
              (hr1 ▸ (by decide : Reg.r1 ≠ Reg.r3)))]
        show ((PartialState.singletonMemBytes r2V srcBytes).union h_b_new).regs r = none
        rw [PartialState.union_regs_of_left_none (PartialState.singletonMemBytes_regs r)]
        exact PartialState.singletonMemBytes_regs r
      · left; exact PartialState.singletonReg_regs_other hr1
    · left; exact PartialState.singletonReg_mem a
    · left; exact PartialState.singletonReg_pc
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
        show ((PartialState.singletonReg .r3 r3V).union h_T4_new).regs r = none
        rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other
              (hr0 ▸ (by decide : Reg.r0 ≠ Reg.r3)))]
        show ((PartialState.singletonMemBytes r2V srcBytes).union h_b_new).regs r = none
        rw [PartialState.union_regs_of_left_none (PartialState.singletonMemBytes_regs r)]
        exact PartialState.singletonMemBytes_regs r
      · left; exact PartialState.singletonReg_regs_other hr0
    · left; exact PartialState.singletonReg_mem a
    · left; exact PartialState.singletonReg_pc
  -- Project h_P_new on registers.
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
    show ((PartialState.singletonReg .r3 r3V).union h_T4_new).regs .r3 = some r3V
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
    show ((PartialState.singletonReg .r3 r3V).union h_T4_new).regs r = none
    rw [PartialState.union_regs_of_left_none
        (PartialState.singletonReg_regs_other h3)]
    show ((PartialState.singletonMemBytes r2V srcBytes).union h_b_new).regs r = none
    rw [PartialState.union_regs_of_left_none (PartialState.singletonMemBytes_regs r)]
    exact PartialState.singletonMemBytes_regs r
  -- Project h_P_new on mem.
  have h_P_new_mem_eq_T4 (a : Nat) : h_P_new.mem a = h_T4_new.mem a := by
    show ((PartialState.singletonReg .r0 0).union h_T1_new).mem a = h_T4_new.mem a
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    show ((PartialState.singletonReg .r1 r1V).union h_T2_new).mem a = h_T4_new.mem a
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    show ((PartialState.singletonReg .r2 r2V).union h_T3_new).mem a = h_T4_new.mem a
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    show ((PartialState.singletonReg .r3 r3V).union h_T4_new).mem a = h_T4_new.mem a
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
  -- For positions in [r1V, r1V+r3V): src is none (range disjointness), b is some.
  have h_P_new_mem_dst (i : Nat) (hi : i < r3V) :
      h_P_new.mem (r1V + i) = some (srcBytes.get! i).toNat := by
    rw [h_P_new_mem_eq_T4]
    show ((PartialState.singletonMemBytes r2V srcBytes).union h_b_new).mem (r1V + i) =
         some (srcBytes.get! i).toNat
    -- The src atom at the post (range [r2V, r2V+r3V)) is disjoint from dst (r1V+i).
    -- From hd_src_b_new (which we just derived), src.mem (r1V+i) = none.
    have hd_post_mem := hd_src_b_new.mem
    have hbsLt : i < srcBytes.size := by rw [hsrcSize]; exact hi
    have h_b_some : h_b_new.mem (r1V + i) = some (srcBytes.get! i).toNat :=
      PartialState.singletonMemBytes_mem_at r1V srcBytes i hbsLt
    have h_src_none : (PartialState.singletonMemBytes r2V srcBytes).mem (r1V + i) = none := by
      rcases hd_post_mem (r1V + i) with hl | hr
      · exact hl
      · rw [hr] at h_b_some; nomatch h_b_some
    rw [PartialState.union_mem_of_left_none h_src_none]
    exact h_b_some
  -- For positions in [r2V, r2V+r3V) (and not in [r1V, r1V+r3V)): src is some.
  have h_P_new_mem_src (j : Nat) (hj : j < r3V) :
      h_P_new.mem (r2V + j) = some (srcBytes.get! j).toNat := by
    rw [h_P_new_mem_eq_T4]
    show ((PartialState.singletonMemBytes r2V srcBytes).union h_b_new).mem (r2V + j) =
         some (srcBytes.get! j).toNat
    have hbsLt : j < srcBytes.size := by rw [hsrcSize]; exact hj
    exact PartialState.union_mem_of_left_some
      (PartialState.singletonMemBytes_mem_at r2V srcBytes j hbsLt)
  -- For positions outside BOTH ranges: none.
  have h_P_new_mem_outside (a : Nat)
      (hOutDst : a < r1V ∨ a ≥ r1V + r3V)
      (hOutSrc : a < r2V ∨ a ≥ r2V + r3V) :
      h_P_new.mem a = none := by
    rw [h_P_new_mem_eq_T4]
    show ((PartialState.singletonMemBytes r2V srcBytes).union h_b_new).mem a = none
    have h_src_none : (PartialState.singletonMemBytes r2V srcBytes).mem a = none := by
      apply PartialState.singletonMemBytes_mem_outside
      rcases hOutSrc with hl | hr
      · left; exact hl
      · right; rw [hsrcSize]; exact hr
    have h_b_none : h_b_new.mem a = none := by
      apply PartialState.singletonMemBytes_mem_outside
      rcases hOutDst with hl | hr
      · left; exact hl
      · right; rw [hsrcSize]; exact hr
    rw [PartialState.union_mem_of_left_none h_src_none]
    exact h_b_none
  have h_P_new_pc : h_P_new.pc = none := by
    show ((PartialState.singletonReg .r0 0).union h_T1_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    show ((PartialState.singletonReg .r1 r1V).union h_T2_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    show ((PartialState.singletonReg .r2 r2V).union h_T3_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    show ((PartialState.singletonReg .r3 r3V).union h_T4_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    show ((PartialState.singletonMemBytes r2V srcBytes).union h_b_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonMemBytes_pc]
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
    · by_cases h_dst : r1V ≤ a ∧ a < r1V + r3V
      · right
        obtain ⟨h1, h2⟩ := h_dst
        have h_eq : a = r1V + (a - r1V) := by omega
        have h_lt : a - r1V < r3V := by omega
        rw [h_eq]; exact h_R_no_mem_dst _ h_lt
      by_cases h_src : r2V ≤ a ∧ a < r2V + r3V
      · right
        obtain ⟨h1, h2⟩ := h_src
        have h_eq : a = r2V + (a - r2V) := by omega
        have h_lt : a - r2V < r3V := by omega
        rw [h_eq]; exact h_R_no_mem_src _ h_lt
      · left
        apply h_P_new_mem_outside
        · rcases Nat.lt_or_ge a r1V with h | h
          · left; exact h
          · rcases Nat.lt_or_ge a (r1V + r3V) with h' | h'
            · exact absurd ⟨h, h'⟩ h_dst
            · right; exact h'
        · rcases Nat.lt_or_ge a r2V with h | h
          · left; exact h
          · rcases Nat.lt_or_ge a (r2V + r3V) with h' | h'
            · exact absurd ⟨h, h'⟩ h_src
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
             h_r3_new, h_T4_new, hd_r3_T4_new, rfl, rfl,
             h_src_new, h_b_new, hd_src_b_new, rfl, rfl, rfl⟩,
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
      by_cases h_dst : r1V ≤ a ∧ a < r1V + r3V
      · obtain ⟨h1, h2⟩ := h_dst
        have h_eq : a = r1V + (a - r1V) := by omega
        have h_lt : a - r1V < r3V := by omega
        rw [h_eq] at hvm ⊢
        rw [PartialState.union_mem_of_left_some
            (h_P_new_mem_dst _ h_lt)] at hvm
        have hvmEq : vm = (srcBytes.get! (a - r1V)).toNat :=
          (Option.some.inj hvm).symm
        rw [hexec_mem_in _ h_lt, hvmEq]
      by_cases h_src : r2V ≤ a ∧ a < r2V + r3V
      · obtain ⟨h1, h2⟩ := h_src
        have h_eq : a = r2V + (a - r2V) := by omega
        have h_lt : a - r2V < r3V := by omega
        rw [h_eq] at hvm ⊢
        rw [PartialState.union_mem_of_left_some
            (h_P_new_mem_src _ h_lt)] at hvm
        have hvmEq : vm = (srcBytes.get! (a - r2V)).toNat :=
          (Option.some.inj hvm).symm
        -- r2V+(a-r2V) is in src, not dst: use hexec_mem_out + hs_mem_src.
        have h_not_dst : (r2V + (a - r2V)) < r1V ∨ (r2V + (a - r2V)) ≥ r1V + r3V := by
          have h_eq' : r2V + (a - r2V) = a := by omega
          rw [h_eq']
          rcases Nat.lt_or_ge a r1V with h | h
          · left; exact h
          · rcases Nat.lt_or_ge a (r1V + r3V) with h' | h'
            · exact absurd ⟨h, h'⟩ h_dst
            · right; exact h'
        rw [hexec_mem_out _ h_not_dst, hvmEq, hs_mem_src _ h_lt]
      · -- a outside both src and dst ranges.
        have h_out_dst : a < r1V ∨ a ≥ r1V + r3V := by
          rcases Nat.lt_or_ge a r1V with h | h
          · left; exact h
          · rcases Nat.lt_or_ge a (r1V + r3V) with h' | h'
            · exact absurd ⟨h, h'⟩ h_dst
            · right; exact h'
        have h_out_src : a < r2V ∨ a ≥ r2V + r3V := by
          rcases Nat.lt_or_ge a r2V with h | h
          · left; exact h
          · rcases Nat.lt_or_ge a (r2V + r3V) with h' | h'
            · exact absurd ⟨h, h'⟩ h_src
            · right; exact h'
        rw [PartialState.union_mem_of_left_none
            (h_P_new_mem_outside a h_out_dst h_out_src)] at hvm
        rw [hexec_mem_out a h_out_dst]
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
        rw [← hu_r0_T1, ← hu_r1_T2, ← hu_r2_T3, ← hu_r3_T4, ← hu_src_b]; rfl
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
        rw [← hu_r0_T1, ← hu_r1_T2, ← hu_r2_T3, ← hu_r3_T4, ← hu_src_b]; rfl
      have hp_cs : hp.callStack = some cs := by
        rw [← hu_PR, PartialState.union_callStack_of_left_none h_P_cs]
        exact hva
      have hexec_cs : (executeFn fetch s 1).callStack = s.callStack := by
        rw [hstep_eq]; exact h_step_callStack s
      rw [hexec_cs]
      exact hcompat.callStack cs hp_cs
/-! ## Syscall: `sol_memcpy` / `sol_memmove`

Both share `MemOps.execCopy` semantics (no overlap-handling distinction): copy
`n = r3` bytes from `src = r2` to `dst = r1`, set `r0 := 0`. The two `↦Bytes`
atoms force src/dest disjoint, so memcpy's UB-on-overlap and memmove's
overlap support are both off the SL spec. -/

theorem call_sol_memcpy_spec
    (r0Old r1V r2V r3V pc nCu : Nat) (srcBytes bsOld : ByteArray)
    (hsrc : srcBytes.size = r3V) (hbs : bsOld.size = r3V)
    (hCu : ∀ s : State,
        (step (.call .sol_memcpy) s).cuConsumed ≤ s.cuConsumed + nCu) :
    -- H6: `[r2V, r2V+r3V)` (src) readable, `[r1V, r1V+r3V)` (dst) writable.
    cuTripleWithinMem 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_memcpy))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V)
       ** (r2V ↦Bytes srcBytes) ** (r1V ↦Bytes bsOld))
      ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V)
       ** (r2V ↦Bytes srcBytes) ** (r1V ↦Bytes srcBytes))
      (fun rt => rt.containsRange r2V r3V = true ∧
                 rt.containsWritable r1V r3V = true) := by
  refine cuTripleWithin_syscall_copiesR2ToR1
    .sol_memcpy pc nCu r2V r3V srcBytes hsrc
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hCu r0Old r1V bsOld hbs
  · intro s hRd hWr
    simp only [step, execSyscall, MemOps.execCopy, State.guardRead, State.guardWrite]
    rw [if_pos (Or.inr hRd), if_pos (Or.inr hWr)]
  · intro s hr2 hr3 hRd hWr i hi
    simp only [step, execSyscall, MemOps.execCopy, State.guardRead, State.guardWrite]
    rw [if_pos (Or.inr hRd), if_pos (Or.inr hWr)]
    rw [Mem_read_default]
    rw [if_pos ⟨Nat.le_add_right _ _, by rw [hr3]; omega⟩]
    have : s.regs.r1 + i - s.regs.r1 = i := by omega
    rw [this]
  · intro s hr3 hRd hWr a ha
    simp only [step, execSyscall, MemOps.execCopy, State.guardRead, State.guardWrite]
    rw [if_pos (Or.inr hRd), if_pos (Or.inr hWr)]
    rw [Mem_read_default]
    have hneg : ¬(a ≥ s.regs.r1 ∧ a - s.regs.r1 < s.regs.r3) := by
      rintro ⟨h1, h2⟩
      rw [hr3] at h2
      rcases ha with hl | hr
      · omega
      · omega
    rw [if_neg hneg]
  · intro s
    simp only [step, execSyscall, MemOps.execCopy]
  · intro s hex hRd hWr
    simp only [step, execSyscall, MemOps.execCopy, State.guardRead, State.guardWrite]
    rw [if_pos (Or.inr hRd), if_pos (Or.inr hWr)]
    exact hex
  · intro s
    simp only [step, execSyscall, MemOps.execCopy, State.guardRead, State.guardWrite,
      State.accessFault]
    (repeat' split) <;> rfl
  · intro s
    simp only [step, execSyscall, MemOps.execCopy, State.guardRead, State.guardWrite,
      State.accessFault]
    (repeat' split) <;> rfl

theorem call_sol_memmove_spec
    (r0Old r1V r2V r3V pc nCu : Nat) (srcBytes bsOld : ByteArray)
    (hsrc : srcBytes.size = r3V) (hbs : bsOld.size = r3V)
    (hCu : ∀ s : State,
        (step (.call .sol_memmove) s).cuConsumed ≤ s.cuConsumed + nCu) :
    -- H6: `[r2V, r2V+r3V)` (src) readable, `[r1V, r1V+r3V)` (dst) writable.
    cuTripleWithinMem 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_memmove))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V)
       ** (r2V ↦Bytes srcBytes) ** (r1V ↦Bytes bsOld))
      ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V)
       ** (r2V ↦Bytes srcBytes) ** (r1V ↦Bytes srcBytes))
      (fun rt => rt.containsRange r2V r3V = true ∧
                 rt.containsWritable r1V r3V = true) := by
  refine cuTripleWithin_syscall_copiesR2ToR1
    .sol_memmove pc nCu r2V r3V srcBytes hsrc
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hCu r0Old r1V bsOld hbs
  · intro s hRd hWr
    simp only [step, execSyscall, MemOps.execCopy, State.guardRead, State.guardWrite]
    rw [if_pos (Or.inr hRd), if_pos (Or.inr hWr)]
  · intro s hr2 hr3 hRd hWr i hi
    simp only [step, execSyscall, MemOps.execCopy, State.guardRead, State.guardWrite]
    rw [if_pos (Or.inr hRd), if_pos (Or.inr hWr)]
    rw [Mem_read_default]
    rw [if_pos ⟨Nat.le_add_right _ _, by rw [hr3]; omega⟩]
    have : s.regs.r1 + i - s.regs.r1 = i := by omega
    rw [this]
  · intro s hr3 hRd hWr a ha
    simp only [step, execSyscall, MemOps.execCopy, State.guardRead, State.guardWrite]
    rw [if_pos (Or.inr hRd), if_pos (Or.inr hWr)]
    rw [Mem_read_default]
    have hneg : ¬(a ≥ s.regs.r1 ∧ a - s.regs.r1 < s.regs.r3) := by
      rintro ⟨h1, h2⟩
      rw [hr3] at h2
      rcases ha with hl | hr
      · omega
      · omega
    rw [if_neg hneg]
  · intro s
    simp only [step, execSyscall, MemOps.execCopy]
  · intro s hex hRd hWr
    simp only [step, execSyscall, MemOps.execCopy, State.guardRead, State.guardWrite]
    rw [if_pos (Or.inr hRd), if_pos (Or.inr hWr)]
    exact hex
  · intro s
    simp only [step, execSyscall, MemOps.execCopy, State.guardRead, State.guardWrite,
      State.accessFault]
    (repeat' split) <;> rfl
  · intro s
    simp only [step, execSyscall, MemOps.execCopy, State.guardRead, State.guardWrite,
      State.accessFault]
    (repeat' split) <;> rfl

/-! ## Syscall: `sol_memcmp`

`sol_memcmp(p1, p2, n, out)`: lexicographically compare `n = r3` bytes at
`[r1, r1+n)` / `[r2, r2+n)`, write the u32-encoded i32 result to `*r4`, set
`r0 := 0`. The most complex mem-op spec: 8 atoms (r0..r4, two ↦Bytes inputs, one
↦U32 output at r4V); the post pins the written value via `memcmpResultU32`. The
proof needs `execCmp_fold_eq` relating the `s.mem` fold to the ByteArray
`memcmpFold` under the `↦Bytes` coherence hyps. -/

/-- ByteArray analogue of the `s.mem`-based fold in `MemOps.execCmp`. Returns
    the i32 difference of the first differing byte pair (`[-255,255]`), or 0. -/
def memcmpFold (p1 p2 : ByteArray) (n : Nat) : Int :=
  (List.range n).foldl (fun acc i =>
    if acc ≠ 0 then acc
    else
      let va := (p1.get! i).toNat
      let vb := (p2.get! i).toNat
      (va : Int) - (vb : Int)) 0

/-- The u32 result written at `*r4` by `sol_memcmp`: the i32 difference
    of the first differing byte pair, reinterpreted as a two's-complement
    u32 (0 for equal). -/
def memcmpResultU32 (p1 p2 : ByteArray) (n : Nat) : Nat :=
  let cmp := memcmpFold p1 p2 n
  if cmp ≥ 0 then cmp.toNat else U32_MODULUS - (-cmp).toNat

/-- Under coherence (`s.mem (pV + i) = (pBytes.get! i).toNat`), the `execCmp`
    fold equals `memcmpFold`. Induction on `n`; `UInt8.toNat _ < 256` cancels
    the `s.mem`-side `% 256`. -/
@[simp]
private theorem execCmp_fold_eq (s : State) (p1V p2V n : Nat)
    (p1Bytes p2Bytes : ByteArray)
    (hp1 : ∀ i, i < n → s.mem (p1V + i) = (p1Bytes.get! i).toNat)
    (hp2 : ∀ i, i < n → s.mem (p2V + i) = (p2Bytes.get! i).toNat) :
    (List.range n).foldl (fun acc i =>
      if acc ≠ 0 then acc
      else
        let va := s.mem (p1V + i) % 256
        let vb := s.mem (p2V + i) % 256
        (va : Int) - (vb : Int)) (0 : Int) = memcmpFold p1Bytes p2Bytes n := by
  unfold memcmpFold
  induction n with
  | zero => rfl
  | succ k ih =>
    have hp1' : ∀ i, i < k → s.mem (p1V + i) = (p1Bytes.get! i).toNat :=
      fun i hi => hp1 i (Nat.lt_succ_of_lt hi)
    have hp2' : ∀ i, i < k → s.mem (p2V + i) = (p2Bytes.get! i).toNat :=
      fun i hi => hp2 i (Nat.lt_succ_of_lt hi)
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih hp1' hp2']
    have hpv1 : s.mem (p1V + k) = (p1Bytes.get! k).toNat := hp1 k (Nat.lt_succ_self k)
    have hpv2 : s.mem (p2V + k) = (p2Bytes.get! k).toNat := hp2 k (Nat.lt_succ_self k)
    have h1lt : (p1Bytes.get! k).toNat < 256 := (p1Bytes.get! k).toNat_lt
    have h2lt : (p2Bytes.get! k).toNat < 256 := (p2Bytes.get! k).toNat_lt
    rw [hpv1, hpv2, Nat.mod_eq_of_lt h1lt, Nat.mod_eq_of_lt h2lt]

/-- `sol_memcmp(p1, p2, n, out)` triple. Reads `n = r3` bytes at `[r1, r1+n)` /
    `[r2, r2+n)` (preserved), writes `memcmpResultU32 p1Bytes p2Bytes r3V` to
    `*r4`, sets `r0 := 0`. The three mem regions (p1, p2, output) are pairwise
    disjoint by separation logic. -/
theorem call_sol_memcmp_spec
    (r0Old r1V r2V r3V r4V outOld pc nCu : Nat)
    (p1Bytes p2Bytes : ByteArray)
    (hsz1 : p1Bytes.size = r3V) (hsz2 : p2Bytes.size = r3V)
    (hCu : ∀ s : State,
        (step (.call .sol_memcmp) s).cuConsumed ≤ s.cuConsumed + nCu) :
    -- H6: `[r1V, r1V+r3V)` and `[r2V, r2V+r3V)` (inputs) readable, and the
    -- fixed 4-byte `[r4V, r4V+4)` result must be in a writable region.
    cuTripleWithinMem 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_memcmp))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V) ** (.r4 ↦ᵣ r4V)
       ** (r1V ↦Bytes p1Bytes) ** (r2V ↦Bytes p2Bytes) ** (r4V ↦U32 outOld))
      ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V) ** (.r4 ↦ᵣ r4V)
       ** (r1V ↦Bytes p1Bytes) ** (r2V ↦Bytes p2Bytes)
       ** (r4V ↦U32 (memcmpResultU32 p1Bytes p2Bytes r3V)))
      (fun rt => rt.containsRange r1V r3V = true ∧ rt.containsRange r2V r3V = true ∧
                 rt.containsWritable r4V 4 = true) := by
  intro R hRfree fetch hcr s hPR hpc hex hbud h_region
  let cmpResult := memcmpResultU32 p1Bytes p2Bytes r3V
  obtain ⟨hp, hcompat, h_P, h_R, hd_PR, hu_PR, h_P_sat, h_R_sat⟩ := hPR
  obtain ⟨h_r0, h_T1, hd_r0_T1, hu_r0_T1, h_r0_pred, h_T1_sat⟩ := h_P_sat
  obtain ⟨h_r1, h_T2, hd_r1_T2, hu_r1_T2, h_r1_pred, h_T2_sat⟩ := h_T1_sat
  obtain ⟨h_r2, h_T3, hd_r2_T3, hu_r2_T3, h_r2_pred, h_T3_sat⟩ := h_T2_sat
  obtain ⟨h_r3, h_T4, hd_r3_T4, hu_r3_T4, h_r3_pred, h_T4_sat⟩ := h_T3_sat
  obtain ⟨h_r4, h_T5, hd_r4_T5, hu_r4_T5, h_r4_pred, h_T5_sat⟩ := h_T4_sat
  obtain ⟨h_p1, h_T6, hd_p1_T6, hu_p1_T6, h_p1_pred, h_T6_sat⟩ := h_T5_sat
  obtain ⟨h_p2, h_out, hd_p2_out, hu_p2_out, h_p2_pred, h_out_pred⟩ := h_T6_sat
  rw [h_r0_pred] at hu_r0_T1 hd_r0_T1
  rw [h_r1_pred] at hu_r1_T2 hd_r1_T2
  rw [h_r2_pred] at hu_r2_T3 hd_r2_T3
  rw [h_r3_pred] at hu_r3_T4 hd_r3_T4
  rw [h_r4_pred] at hu_r4_T5 hd_r4_T5
  rw [h_p1_pred] at hu_p1_T6 hd_p1_T6
  rw [h_p2_pred] at hu_p2_out hd_p2_out
  rw [h_out_pred] at hu_p2_out hd_p2_out
  clear h_r0_pred h_r1_pred h_r2_pred h_r3_pred h_r4_pred h_p1_pred h_p2_pred h_out_pred
        h_r0 h_r1 h_r2 h_r3 h_r4 h_p1 h_p2 h_out
  have hcr_regs := hcompat.regs
  have hcm_mem := hcompat.mem
  have h_T4_regs_r4 : h_T4.regs .r4 = some r4V := by
    rw [← hu_r4_T5]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_T3_regs_r3 : h_T3.regs .r3 = some r3V := by
    rw [← hu_r3_T4]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_T3_regs_r4 : h_T3.regs .r4 = some r4V := by
    rw [← hu_r3_T4,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r4 ≠ Reg.r3))]
    exact h_T4_regs_r4
  have h_T2_regs_r2 : h_T2.regs .r2 = some r2V := by
    rw [← hu_r2_T3]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_T2_regs_r3 : h_T2.regs .r3 = some r3V := by
    rw [← hu_r2_T3,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r3 ≠ Reg.r2))]
    exact h_T3_regs_r3
  have h_T2_regs_r4 : h_T2.regs .r4 = some r4V := by
    rw [← hu_r2_T3,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r4 ≠ Reg.r2))]
    exact h_T3_regs_r4
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
  have h_T1_regs_r4 : h_T1.regs .r4 = some r4V := by
    rw [← hu_r1_T2,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r4 ≠ Reg.r1))]
    exact h_T2_regs_r4
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
  have h_P_regs_r4 : h_P.regs .r4 = some r4V := by
    rw [← hu_r0_T1,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r4 ≠ Reg.r0))]
    exact h_T1_regs_r4
  have hp_regs_r0 : hp.regs .r0 = some r0Old := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r0
  have hp_regs_r1 : hp.regs .r1 = some r1V := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r1
  have hp_regs_r2 : hp.regs .r2 = some r2V := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r2
  have hp_regs_r3 : hp.regs .r3 = some r3V := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r3
  have hp_regs_r4 : hp.regs .r4 = some r4V := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r4
  have hs_regs_r0 : s.regs.get .r0 = r0Old := hcr_regs .r0 r0Old hp_regs_r0
  have hs_regs_r1 : s.regs.get .r1 = r1V := hcr_regs .r1 r1V hp_regs_r1
  have hs_regs_r2 : s.regs.get .r2 = r2V := hcr_regs .r2 r2V hp_regs_r2
  have hs_regs_r3 : s.regs.get .r3 = r3V := hcr_regs .r3 r3V hp_regs_r3
  have hs_regs_r4 : s.regs.get .r4 = r4V := hcr_regs .r4 r4V hp_regs_r4
  have hs_r1_field : s.regs.r1 = r1V := hs_regs_r1
  have hs_r2_field : s.regs.r2 = r2V := hs_regs_r2
  have hs_r3_field : s.regs.r3 = r3V := hs_regs_r3
  have hs_r4_field : s.regs.r4 = r4V := hs_regs_r4
  -- The `rr` region requirements, specialised to this state's registers:
  -- collapse the three nested guards in `step (.call .sol_memcmp)`.
  have hRd1 : s.regions.containsRange s.regs.r1 s.regs.r3 = true := by
    rw [hs_r1_field, hs_r3_field]; exact h_region.1
  have hRd2 : s.regions.containsRange s.regs.r2 s.regs.r3 = true := by
    rw [hs_r2_field, hs_r3_field]; exact h_region.2.1
  have hWr : s.regions.containsWritable s.regs.r4 4 = true := by
    rw [hs_r4_field]; exact h_region.2.2
  -- p1 at r1V (sits at h_T5 layer).
  have h_T5_mem_p1 (i : Nat) (hi : i < r3V) :
      h_T5.mem (r1V + i) = some (p1Bytes.get! i).toNat := by
    rw [← hu_p1_T6]
    have hsz_lt : i < p1Bytes.size := by rw [hsz1]; exact hi
    exact PartialState.union_mem_of_left_some
      (PartialState.singletonMemBytes_mem_at r1V p1Bytes i hsz_lt)
  have h_T4_mem_p1 (i : Nat) (hi : i < r3V) :
      h_T4.mem (r1V + i) = some (p1Bytes.get! i).toNat := by
    rw [← hu_r4_T5,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact h_T5_mem_p1 i hi
  have h_T3_mem_p1 (i : Nat) (hi : i < r3V) :
      h_T3.mem (r1V + i) = some (p1Bytes.get! i).toNat := by
    rw [← hu_r3_T4,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact h_T4_mem_p1 i hi
  have h_T2_mem_p1 (i : Nat) (hi : i < r3V) :
      h_T2.mem (r1V + i) = some (p1Bytes.get! i).toNat := by
    rw [← hu_r2_T3,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact h_T3_mem_p1 i hi
  have h_T1_mem_p1 (i : Nat) (hi : i < r3V) :
      h_T1.mem (r1V + i) = some (p1Bytes.get! i).toNat := by
    rw [← hu_r1_T2,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact h_T2_mem_p1 i hi
  have h_P_mem_p1 (i : Nat) (hi : i < r3V) :
      h_P.mem (r1V + i) = some (p1Bytes.get! i).toNat := by
    rw [← hu_r0_T1,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact h_T1_mem_p1 i hi
  -- p2 at r2V (sits at h_T6 layer). Need h_p1.mem (r2V + j) = none first.
  have h_p1_no_p2 (j : Nat) (hj : j < r3V) :
      (PartialState.singletonMemBytes r1V p1Bytes).mem (r2V + j) = none := by
    -- T6 owns (r2V + j) via p2 atom, so by hd_p1_T6, p1 doesn't.
    have hd_mem := hd_p1_T6.mem
    -- T6.mem (r2V + j) = some (p2Bytes.get! j).toNat
    have hsz2_lt : j < p2Bytes.size := by rw [hsz2]; exact hj
    have h_T6_some : h_T6.mem (r2V + j) = some (p2Bytes.get! j).toNat := by
      rw [← hu_p2_out]
      exact PartialState.union_mem_of_left_some
        (PartialState.singletonMemBytes_mem_at r2V p2Bytes j hsz2_lt)
    rcases hd_mem (r2V + j) with hl | hr
    · exact hl
    · rw [h_T6_some] at hr; nomatch hr
  have h_T5_mem_p2 (j : Nat) (hj : j < r3V) :
      h_T5.mem (r2V + j) = some (p2Bytes.get! j).toNat := by
    rw [← hu_p1_T6,
        PartialState.union_mem_of_left_none (h_p1_no_p2 j hj),
        ← hu_p2_out]
    have hsz_lt : j < p2Bytes.size := by rw [hsz2]; exact hj
    exact PartialState.union_mem_of_left_some
      (PartialState.singletonMemBytes_mem_at r2V p2Bytes j hsz_lt)
  have h_T4_mem_p2 (j : Nat) (hj : j < r3V) :
      h_T4.mem (r2V + j) = some (p2Bytes.get! j).toNat := by
    rw [← hu_r4_T5,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact h_T5_mem_p2 j hj
  have h_T3_mem_p2 (j : Nat) (hj : j < r3V) :
      h_T3.mem (r2V + j) = some (p2Bytes.get! j).toNat := by
    rw [← hu_r3_T4,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact h_T4_mem_p2 j hj
  have h_T2_mem_p2 (j : Nat) (hj : j < r3V) :
      h_T2.mem (r2V + j) = some (p2Bytes.get! j).toNat := by
    rw [← hu_r2_T3,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact h_T3_mem_p2 j hj
  have h_T1_mem_p2 (j : Nat) (hj : j < r3V) :
      h_T1.mem (r2V + j) = some (p2Bytes.get! j).toNat := by
    rw [← hu_r1_T2,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact h_T2_mem_p2 j hj
  have h_P_mem_p2 (j : Nat) (hj : j < r3V) :
      h_P.mem (r2V + j) = some (p2Bytes.get! j).toNat := by
    rw [← hu_r0_T1,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact h_T1_mem_p2 j hj
  -- Convert h_P.mem facts to s.mem facts via hcm_mem
  have hp_mem_p1 (i : Nat) (hi : i < r3V) :
      hp.mem (r1V + i) = some (p1Bytes.get! i).toNat := by
    rw [← hu_PR]; exact PartialState.union_mem_of_left_some (h_P_mem_p1 i hi)
  have hp_mem_p2 (j : Nat) (hj : j < r3V) :
      hp.mem (r2V + j) = some (p2Bytes.get! j).toNat := by
    rw [← hu_PR]; exact PartialState.union_mem_of_left_some (h_P_mem_p2 j hj)
  have hs_mem_p1 (i : Nat) (hi : i < r3V) :
      s.mem (r1V + i) = (p1Bytes.get! i).toNat := hcm_mem _ _ (hp_mem_p1 i hi)
  have hs_mem_p2 (j : Nat) (hj : j < r3V) :
      s.mem (r2V + j) = (p2Bytes.get! j).toNat := hcm_mem _ _ (hp_mem_p2 j hj)
  have hfetch : fetch s.pc = some (.call .sol_memcmp) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hnb : ¬ s.cuConsumed > s.cuBudget := by omega
  have hstep_eq : executeFn fetch s 1 = chargeCu (step (.call .sol_memcmp) s) := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch, executeFn_zero]
  have hexec_cu : (executeFn fetch s 1).cuConsumed ≤ s.cuConsumed + 1 + nCu := by
    rw [hstep_eq]
    show (step (.call .sol_memcmp) s).cuConsumed + 1 ≤ s.cuConsumed + 1 + nCu
    have := hCu s; omega
  -- step writes writeU32 s.mem r4V cmpResult and r0 := 0.
  have hexec_pc : (executeFn fetch s 1).pc = s.pc + 1 := by
    rw [hstep_eq]; simp only [step, execSyscall, MemOps.execCmp, chargeCu]
  have hexec_exit : (executeFn fetch s 1).exitCode = none := by
    rw [hstep_eq]
    simp only [step, execSyscall, MemOps.execCmp, chargeCu, State.guardRead, State.guardWrite]
    rw [if_pos (Or.inr hRd1), if_pos (Or.inr hRd2), if_pos (Or.inr hWr)]
    exact hex
  have hexec_regs : (executeFn fetch s 1).regs = s.regs.set .r0 0 := by
    rw [hstep_eq]
    simp only [step, execSyscall, MemOps.execCmp, chargeCu, State.guardRead, State.guardWrite]
    rw [if_pos (Or.inr hRd1), if_pos (Or.inr hRd2), if_pos (Or.inr hWr)]
  -- execCmp_fold_eq converts the s.mem-based fold to memcmpFold under coherence,
  -- yielding memcmpResultU32.
  have hexec_mem_eq :
      (executeFn fetch s 1).mem =
        Memory.writeU32 s.mem r4V cmpResult := by
    rw [hstep_eq]
    simp only [step, execSyscall, MemOps.execCmp, chargeCu, State.guardRead, State.guardWrite]
    rw [if_pos (Or.inr hRd1), if_pos (Or.inr hRd2), if_pos (Or.inr hWr)]
    -- Convert all s.regs.{r1, r2, r3, r4} → fixed parameter values
    rw [hs_r4_field, hs_r1_field, hs_r2_field, hs_r3_field]
    show Memory.writeU32 s.mem r4V _ = Memory.writeU32 s.mem r4V cmpResult
    congr 1
    show _ = memcmpResultU32 p1Bytes p2Bytes r3V
    unfold memcmpResultU32
    rw [execCmp_fold_eq s r1V r2V r3V p1Bytes p2Bytes hs_mem_p1 hs_mem_p2]
  -- Per-byte mem values after the U32 write at r4V (4 LE bytes of cmpResult).
  have hexec_mem_u32_0 : (executeFn fetch s 1).mem r4V = cmpResult % 256 := by
    rw [hexec_mem_eq]
    unfold Memory.writeU32; simp
  have hexec_mem_u32_1 :
      (executeFn fetch s 1).mem (r4V + 1) = cmpResult / 0x100 % 256 := by
    rw [hexec_mem_eq]
    unfold Memory.writeU32
    simp
  have hexec_mem_u32_2 :
      (executeFn fetch s 1).mem (r4V + 2) = cmpResult / 0x10000 % 256 := by
    rw [hexec_mem_eq]
    unfold Memory.writeU32
    simp
  have hexec_mem_u32_3 :
      (executeFn fetch s 1).mem (r4V + 3) = cmpResult / 0x1000000 % 256 := by
    rw [hexec_mem_eq]
    unfold Memory.writeU32
    simp
  -- Outside writeU32 range, mem is unchanged.
  have hexec_mem_outside_u32 (a : Nat) (h : a < r4V ∨ a ≥ r4V + 4) :
      (executeFn fetch s 1).mem a = s.mem a := by
    rw [hexec_mem_eq]
    unfold Memory.writeU32
    simp only [Memory.Mem.read_put]
    have h0 : a ≠ r4V := by rcases h with hl | hr <;> omega
    have h1 : a ≠ r4V + 1 := by rcases h with hl | hr <;> omega
    have h2 : a ≠ r4V + 2 := by rcases h with hl | hr <;> omega
    have h3 : a ≠ r4V + 3 := by rcases h with hl | hr <;> omega
    rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3]
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
  have h_R_no_r4 : h_R.regs .r4 = none := by
    rcases hd_PR_regs .r4 with hl | hr
    · rw [h_P_regs_r4] at hl; nomatch hl
    · exact hr
  have h_R_no_pc : h_R.pc = none := hRfree _ h_R_sat
  have h_R_no_mem_p1 (i : Nat) (hi : i < r3V) : h_R.mem (r1V + i) = none := by
    rcases hd_PR_mem (r1V + i) with hl | hr
    · rw [h_P_mem_p1 i hi] at hl; nomatch hl
    · exact hr
  have h_R_no_mem_p2 (j : Nat) (hj : j < r3V) : h_R.mem (r2V + j) = none := by
    rcases hd_PR_mem (r2V + j) with hl | hr
    · rw [h_P_mem_p2 j hj] at hl; nomatch hl
    · exact hr
  -- For r4V's U32 region: h_P.mem (r4V + k) = some <byte k of outOld>
  -- (derived via h_T6 → h_out atom).
  have h_T6_mem_out (k : Nat) (hk : k < 4) :
      h_T6.mem (r4V + k) = (PartialState.singletonMemU32 r4V outOld).mem (r4V + k) := by
    have h_out_some : ∃ v, (PartialState.singletonMemU32 r4V outOld).mem (r4V + k) = some v := by
      match k, hk with
      | 0, _ => exact ⟨_, by rw [show r4V + 0 = r4V from rfl]; exact PartialState.singletonMemU32_mem_0 _ _⟩
      | 1, _ => exact ⟨_, PartialState.singletonMemU32_mem_1 _ _⟩
      | 2, _ => exact ⟨_, PartialState.singletonMemU32_mem_2 _ _⟩
      | 3, _ => exact ⟨_, PartialState.singletonMemU32_mem_3 _ _⟩
    have h_p2_none : (PartialState.singletonMemBytes r2V p2Bytes).mem (r4V + k) = none := by
      have hd_mem := hd_p2_out.mem
      obtain ⟨v, hv⟩ := h_out_some
      rcases hd_mem (r4V + k) with hl | hr
      · exact hl
      · rw [hv] at hr; nomatch hr
    rw [← hu_p2_out, PartialState.union_mem_of_left_none h_p2_none]
  have h_T5_mem_out (k : Nat) (hk : k < 4) :
      h_T5.mem (r4V + k) = (PartialState.singletonMemU32 r4V outOld).mem (r4V + k) := by
    have h_T6_some : h_T6.mem (r4V + k) ≠ none := by
      rw [h_T6_mem_out k hk]
      match k, hk with
      | 0, _ => rw [show r4V + 0 = r4V from rfl, PartialState.singletonMemU32_mem_0]; exact Option.some_ne_none _
      | 1, _ => rw [PartialState.singletonMemU32_mem_1]; exact Option.some_ne_none _
      | 2, _ => rw [PartialState.singletonMemU32_mem_2]; exact Option.some_ne_none _
      | 3, _ => rw [PartialState.singletonMemU32_mem_3]; exact Option.some_ne_none _
    have h_p1_none : (PartialState.singletonMemBytes r1V p1Bytes).mem (r4V + k) = none := by
      have hd_mem := hd_p1_T6.mem
      rcases hd_mem (r4V + k) with hl | hr
      · exact hl
      · exact absurd hr h_T6_some
    rw [← hu_p1_T6, PartialState.union_mem_of_left_none h_p1_none]
    exact h_T6_mem_out k hk
  have h_T4_mem_out (k : Nat) (hk : k < 4) :
      h_T4.mem (r4V + k) = (PartialState.singletonMemU32 r4V outOld).mem (r4V + k) := by
    rw [← hu_r4_T5,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact h_T5_mem_out k hk
  have h_T3_mem_out (k : Nat) (hk : k < 4) :
      h_T3.mem (r4V + k) = (PartialState.singletonMemU32 r4V outOld).mem (r4V + k) := by
    rw [← hu_r3_T4,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact h_T4_mem_out k hk
  have h_T2_mem_out (k : Nat) (hk : k < 4) :
      h_T2.mem (r4V + k) = (PartialState.singletonMemU32 r4V outOld).mem (r4V + k) := by
    rw [← hu_r2_T3,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact h_T3_mem_out k hk
  have h_T1_mem_out (k : Nat) (hk : k < 4) :
      h_T1.mem (r4V + k) = (PartialState.singletonMemU32 r4V outOld).mem (r4V + k) := by
    rw [← hu_r1_T2,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact h_T2_mem_out k hk
  have h_P_mem_out (k : Nat) (hk : k < 4) :
      h_P.mem (r4V + k) = (PartialState.singletonMemU32 r4V outOld).mem (r4V + k) := by
    rw [← hu_r0_T1,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact h_T1_mem_out k hk
  have h_R_no_mem_out (k : Nat) (hk : k < 4) : h_R.mem (r4V + k) = none := by
    have h_some : ∃ v, h_P.mem (r4V + k) = some v := by
      rw [h_P_mem_out k hk]
      match k, hk with
      | 0, _ => exact ⟨_, by rw [show r4V + 0 = r4V from rfl]; exact PartialState.singletonMemU32_mem_0 _ _⟩
      | 1, _ => exact ⟨_, PartialState.singletonMemU32_mem_1 _ _⟩
      | 2, _ => exact ⟨_, PartialState.singletonMemU32_mem_2 _ _⟩
      | 3, _ => exact ⟨_, PartialState.singletonMemU32_mem_3 _ _⟩
    obtain ⟨v, hv⟩ := h_some
    rcases hd_PR_mem (r4V + k) with hl | hr
    · rw [hv] at hl; nomatch hl
    · exact hr
  let h_r0_new : PartialState := PartialState.singletonReg .r0 0
  let h_r1_new : PartialState := PartialState.singletonReg .r1 r1V
  let h_r2_new : PartialState := PartialState.singletonReg .r2 r2V
  let h_r3_new : PartialState := PartialState.singletonReg .r3 r3V
  let h_r4_new : PartialState := PartialState.singletonReg .r4 r4V
  let h_p1_new : PartialState := PartialState.singletonMemBytes r1V p1Bytes
  let h_p2_new : PartialState := PartialState.singletonMemBytes r2V p2Bytes
  let h_out_new : PartialState := PartialState.singletonMemU32 r4V cmpResult
  let h_T6_new : PartialState := h_p2_new.union h_out_new
  let h_T5_new : PartialState := h_p1_new.union h_T6_new
  let h_T4_new : PartialState := h_r4_new.union h_T5_new
  let h_T3_new : PartialState := h_r3_new.union h_T4_new
  let h_T2_new : PartialState := h_r2_new.union h_T3_new
  let h_T1_new : PartialState := h_r1_new.union h_T2_new
  let h_P_new : PartialState := h_r0_new.union h_T1_new
  -- Inner disjointness: p2_new ⊥ out_new. Same address ranges as pre.
  have hd_p2_out_new : h_p2_new.Disjoint h_out_new := by
    refine ⟨fun r => Or.inl (PartialState.singletonMemBytes_regs r),
            fun a => ?_,
            Or.inl PartialState.singletonMemBytes_pc, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
    -- From hd_p2_out: same ranges (p2_new = p2Bytes, out_new = U32 at r4V).
    have hd_pre_mem := hd_p2_out.mem
    rcases hd_pre_mem a with hl | hr
    · left; exact hl
    · right
      -- none-ness is range-based, so out_old none → out_new none ([r4V, r4V+4)).
      by_cases h : r4V ≤ a ∧ a < r4V + 4
      · exfalso
        obtain ⟨h1, h2⟩ := h
        have h_some : ∃ v : Nat, (PartialState.singletonMemU32 r4V outOld).mem a = some v := by
          rcases Nat.lt_or_ge a (r4V + 1) with hl' | hge'
          · exact ⟨outOld % 256, by rw [show a = r4V from by omega]; exact PartialState.singletonMemU32_mem_0 _ _⟩
          rcases Nat.lt_or_ge a (r4V + 2) with hl' | hge'
          · exact ⟨outOld / 0x100 % 256, by rw [show a = r4V + 1 from by omega]; exact PartialState.singletonMemU32_mem_1 _ _⟩
          rcases Nat.lt_or_ge a (r4V + 3) with hl' | hge'
          · exact ⟨outOld / 0x10000 % 256, by rw [show a = r4V + 2 from by omega]; exact PartialState.singletonMemU32_mem_2 _ _⟩
          · exact ⟨outOld / 0x1000000 % 256, by rw [show a = r4V + 3 from by omega]; exact PartialState.singletonMemU32_mem_3 _ _⟩
        obtain ⟨v, hv⟩ := h_some
        rw [hv] at hr; nomatch hr
      · apply PartialState.singletonMemU32_mem_outside
        rcases Nat.lt_or_ge a r4V with hl' | hge'
        · left; exact hl'
        · right
          rcases Nat.lt_or_ge a (r4V + 4) with hlt | hge''
          · exact absurd ⟨hge', hlt⟩ h
          · exact hge''
  -- p1_new ⊥ T6_new = p2_new ∪ out_new. Same as pre by analogous range argument.
  have hd_p1_T6_new : h_p1_new.Disjoint h_T6_new := by
    refine ⟨fun r => Or.inl (PartialState.singletonMemBytes_regs r),
            fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
    · have hd_pre_mem := hd_p1_T6.mem
      rcases hd_pre_mem a with hl | hr
      · left; exact hl
      · right
        -- T6_pre.mem a = none → T6_new.mem a = none (same p2, same out range).
        show (h_p2_new.union h_out_new).mem a = none
        have h_p2_none : (PartialState.singletonMemBytes r2V p2Bytes).mem a = none := by
          rw [← hu_p2_out] at hr
          have hp2 := PartialState.union_mem_eq_none_iff.mp hr
          exact hp2.1
        have h_out_pre_none : (PartialState.singletonMemU32 r4V outOld).mem a = none := by
          rw [← hu_p2_out] at hr
          have hp2 := PartialState.union_mem_eq_none_iff.mp hr
          exact hp2.2
        rw [PartialState.union_mem_of_left_none h_p2_none]
        -- Goal: h_out_new.mem a = none. Same range as out_pre.
        by_cases h : r4V ≤ a ∧ a < r4V + 4
        · exfalso
          obtain ⟨h1, h2⟩ := h
          have h_some : ∃ v : Nat, (PartialState.singletonMemU32 r4V outOld).mem a = some v := by
            rcases Nat.lt_or_ge a (r4V + 1) with hl' | hge'
            · exact ⟨outOld % 256, by rw [show a = r4V from by omega]; exact PartialState.singletonMemU32_mem_0 _ _⟩
            rcases Nat.lt_or_ge a (r4V + 2) with hl' | hge'
            · exact ⟨outOld / 0x100 % 256, by rw [show a = r4V + 1 from by omega]; exact PartialState.singletonMemU32_mem_1 _ _⟩
            rcases Nat.lt_or_ge a (r4V + 3) with hl' | hge'
            · exact ⟨outOld / 0x10000 % 256, by rw [show a = r4V + 2 from by omega]; exact PartialState.singletonMemU32_mem_2 _ _⟩
            · exact ⟨outOld / 0x1000000 % 256, by rw [show a = r4V + 3 from by omega]; exact PartialState.singletonMemU32_mem_3 _ _⟩
          obtain ⟨v, hv⟩ := h_some
          rw [hv] at h_out_pre_none; nomatch h_out_pre_none
        · apply PartialState.singletonMemU32_mem_outside
          rcases Nat.lt_or_ge a r4V with hl' | hge'
          · left; exact hl'
          · right
            rcases Nat.lt_or_ge a (r4V + 4) with hlt | hge''
            · exact absurd ⟨hge', hlt⟩ h
            · exact hge''
    · left; exact PartialState.singletonMemBytes_pc
  -- Disjointness for the inner reg-mem chain: each reg atom is regs-only, no mem.
  have hd_r4_T5_new : h_r4_new.Disjoint h_T5_new := by
    refine ⟨fun r => ?_, fun a => Or.inl (PartialState.singletonReg_mem a),
            Or.inl PartialState.singletonReg_pc, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
    by_cases hr4 : r = .r4
    · right
      show h_T5_new.regs r = none
      show ((PartialState.singletonMemBytes r1V p1Bytes).union h_T6_new).regs r = none
      rw [PartialState.union_regs_of_left_none (PartialState.singletonMemBytes_regs r)]
      show ((PartialState.singletonMemBytes r2V p2Bytes).union h_out_new).regs r = none
      rw [PartialState.union_regs_of_left_none (PartialState.singletonMemBytes_regs r)]
      exact PartialState.singletonMemU32_regs r
    · left; exact PartialState.singletonReg_regs_other hr4
  have hd_r3_T4_new : h_r3_new.Disjoint h_T4_new := by
    refine ⟨fun r => ?_, fun a => Or.inl (PartialState.singletonReg_mem a),
            Or.inl PartialState.singletonReg_pc, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
    by_cases hr3 : r = .r3
    · right
      show h_T4_new.regs r = none
      show ((PartialState.singletonReg .r4 r4V).union h_T5_new).regs r = none
      rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (hr3 ▸ (by decide : Reg.r3 ≠ Reg.r4)))]
      show ((PartialState.singletonMemBytes r1V p1Bytes).union h_T6_new).regs r = none
      rw [PartialState.union_regs_of_left_none (PartialState.singletonMemBytes_regs r)]
      show ((PartialState.singletonMemBytes r2V p2Bytes).union h_out_new).regs r = none
      rw [PartialState.union_regs_of_left_none (PartialState.singletonMemBytes_regs r)]
      exact PartialState.singletonMemU32_regs r
    · left; exact PartialState.singletonReg_regs_other hr3
  have hd_r2_T3_new : h_r2_new.Disjoint h_T3_new := by
    refine ⟨fun r => ?_, fun a => Or.inl (PartialState.singletonReg_mem a),
            Or.inl PartialState.singletonReg_pc, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
    by_cases hr2 : r = .r2
    · right
      show h_T3_new.regs r = none
      show ((PartialState.singletonReg .r3 r3V).union h_T4_new).regs r = none
      rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (hr2 ▸ (by decide : Reg.r2 ≠ Reg.r3)))]
      show ((PartialState.singletonReg .r4 r4V).union h_T5_new).regs r = none
      rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (hr2 ▸ (by decide : Reg.r2 ≠ Reg.r4)))]
      show ((PartialState.singletonMemBytes r1V p1Bytes).union h_T6_new).regs r = none
      rw [PartialState.union_regs_of_left_none (PartialState.singletonMemBytes_regs r)]
      show ((PartialState.singletonMemBytes r2V p2Bytes).union h_out_new).regs r = none
      rw [PartialState.union_regs_of_left_none (PartialState.singletonMemBytes_regs r)]
      exact PartialState.singletonMemU32_regs r
    · left; exact PartialState.singletonReg_regs_other hr2
  have hd_r1_T2_new : h_r1_new.Disjoint h_T2_new := by
    refine ⟨fun r => ?_, fun a => Or.inl (PartialState.singletonReg_mem a),
            Or.inl PartialState.singletonReg_pc, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
    by_cases hr1 : r = .r1
    · right
      show h_T2_new.regs r = none
      show ((PartialState.singletonReg .r2 r2V).union h_T3_new).regs r = none
      rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (hr1 ▸ (by decide : Reg.r1 ≠ Reg.r2)))]
      show ((PartialState.singletonReg .r3 r3V).union h_T4_new).regs r = none
      rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (hr1 ▸ (by decide : Reg.r1 ≠ Reg.r3)))]
      show ((PartialState.singletonReg .r4 r4V).union h_T5_new).regs r = none
      rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (hr1 ▸ (by decide : Reg.r1 ≠ Reg.r4)))]
      show ((PartialState.singletonMemBytes r1V p1Bytes).union h_T6_new).regs r = none
      rw [PartialState.union_regs_of_left_none (PartialState.singletonMemBytes_regs r)]
      show ((PartialState.singletonMemBytes r2V p2Bytes).union h_out_new).regs r = none
      rw [PartialState.union_regs_of_left_none (PartialState.singletonMemBytes_regs r)]
      exact PartialState.singletonMemU32_regs r
    · left; exact PartialState.singletonReg_regs_other hr1
  have hd_r0_T1_new : h_r0_new.Disjoint h_T1_new := by
    refine ⟨fun r => ?_, fun a => Or.inl (PartialState.singletonReg_mem a),
            Or.inl PartialState.singletonReg_pc, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
    by_cases hr0 : r = .r0
    · right
      show h_T1_new.regs r = none
      show ((PartialState.singletonReg .r1 r1V).union h_T2_new).regs r = none
      rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (hr0 ▸ (by decide : Reg.r0 ≠ Reg.r1)))]
      show ((PartialState.singletonReg .r2 r2V).union h_T3_new).regs r = none
      rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (hr0 ▸ (by decide : Reg.r0 ≠ Reg.r2)))]
      show ((PartialState.singletonReg .r3 r3V).union h_T4_new).regs r = none
      rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (hr0 ▸ (by decide : Reg.r0 ≠ Reg.r3)))]
      show ((PartialState.singletonReg .r4 r4V).union h_T5_new).regs r = none
      rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (hr0 ▸ (by decide : Reg.r0 ≠ Reg.r4)))]
      show ((PartialState.singletonMemBytes r1V p1Bytes).union h_T6_new).regs r = none
      rw [PartialState.union_regs_of_left_none (PartialState.singletonMemBytes_regs r)]
      show ((PartialState.singletonMemBytes r2V p2Bytes).union h_out_new).regs r = none
      rw [PartialState.union_regs_of_left_none (PartialState.singletonMemBytes_regs r)]
      exact PartialState.singletonMemU32_regs r
    · left; exact PartialState.singletonReg_regs_other hr0
  -- h_P_new reg projections
  have h_P_new_regs_r0 : h_P_new.regs .r0 = some 0 :=
    PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_new_regs_climb_r (r : Reg) (h0 : r ≠ .r0) :
      h_P_new.regs r = h_T1_new.regs r := by
    show ((PartialState.singletonReg .r0 0).union h_T1_new).regs r = h_T1_new.regs r
    exact PartialState.union_regs_of_left_none
      (PartialState.singletonReg_regs_other h0)
  have h_P_new_regs_r1 : h_P_new.regs .r1 = some r1V := by
    rw [h_P_new_regs_climb_r .r1 (by decide)]
    show ((PartialState.singletonReg .r1 r1V).union h_T2_new).regs .r1 = some r1V
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_new_regs_r2 : h_P_new.regs .r2 = some r2V := by
    rw [h_P_new_regs_climb_r .r2 (by decide)]
    show ((PartialState.singletonReg .r1 r1V).union h_T2_new).regs .r2 = some r2V
    rw [PartialState.union_regs_of_left_none
        (PartialState.singletonReg_regs_other (by decide : Reg.r2 ≠ Reg.r1))]
    show ((PartialState.singletonReg .r2 r2V).union h_T3_new).regs .r2 = some r2V
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_new_regs_r3 : h_P_new.regs .r3 = some r3V := by
    rw [h_P_new_regs_climb_r .r3 (by decide)]
    show ((PartialState.singletonReg .r1 r1V).union h_T2_new).regs .r3 = some r3V
    rw [PartialState.union_regs_of_left_none
        (PartialState.singletonReg_regs_other (by decide : Reg.r3 ≠ Reg.r1))]
    show ((PartialState.singletonReg .r2 r2V).union h_T3_new).regs .r3 = some r3V
    rw [PartialState.union_regs_of_left_none
        (PartialState.singletonReg_regs_other (by decide : Reg.r3 ≠ Reg.r2))]
    show ((PartialState.singletonReg .r3 r3V).union h_T4_new).regs .r3 = some r3V
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_new_regs_r4 : h_P_new.regs .r4 = some r4V := by
    rw [h_P_new_regs_climb_r .r4 (by decide)]
    show ((PartialState.singletonReg .r1 r1V).union h_T2_new).regs .r4 = some r4V
    rw [PartialState.union_regs_of_left_none
        (PartialState.singletonReg_regs_other (by decide : Reg.r4 ≠ Reg.r1))]
    show ((PartialState.singletonReg .r2 r2V).union h_T3_new).regs .r4 = some r4V
    rw [PartialState.union_regs_of_left_none
        (PartialState.singletonReg_regs_other (by decide : Reg.r4 ≠ Reg.r2))]
    show ((PartialState.singletonReg .r3 r3V).union h_T4_new).regs .r4 = some r4V
    rw [PartialState.union_regs_of_left_none
        (PartialState.singletonReg_regs_other (by decide : Reg.r4 ≠ Reg.r3))]
    show ((PartialState.singletonReg .r4 r4V).union h_T5_new).regs .r4 = some r4V
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_new_regs_other (r : Reg)
      (h0 : r ≠ .r0) (h1 : r ≠ .r1) (h2 : r ≠ .r2) (h3 : r ≠ .r3) (h4 : r ≠ .r4) :
      h_P_new.regs r = none := by
    rw [h_P_new_regs_climb_r r h0]
    show ((PartialState.singletonReg .r1 r1V).union h_T2_new).regs r = none
    rw [PartialState.union_regs_of_left_none
        (PartialState.singletonReg_regs_other h1)]
    show ((PartialState.singletonReg .r2 r2V).union h_T3_new).regs r = none
    rw [PartialState.union_regs_of_left_none
        (PartialState.singletonReg_regs_other h2)]
    show ((PartialState.singletonReg .r3 r3V).union h_T4_new).regs r = none
    rw [PartialState.union_regs_of_left_none
        (PartialState.singletonReg_regs_other h3)]
    show ((PartialState.singletonReg .r4 r4V).union h_T5_new).regs r = none
    rw [PartialState.union_regs_of_left_none
        (PartialState.singletonReg_regs_other h4)]
    show ((PartialState.singletonMemBytes r1V p1Bytes).union h_T6_new).regs r = none
    rw [PartialState.union_regs_of_left_none (PartialState.singletonMemBytes_regs r)]
    show ((PartialState.singletonMemBytes r2V p2Bytes).union h_out_new).regs r = none
    rw [PartialState.union_regs_of_left_none (PartialState.singletonMemBytes_regs r)]
    exact PartialState.singletonMemU32_regs r
  -- h_P_new mem projections: regs contribute nothing.
  have h_P_new_mem_eq_T5 (a : Nat) : h_P_new.mem a = h_T5_new.mem a := by
    show ((PartialState.singletonReg .r0 0).union h_T1_new).mem a = h_T5_new.mem a
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    show ((PartialState.singletonReg .r1 r1V).union h_T2_new).mem a = h_T5_new.mem a
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    show ((PartialState.singletonReg .r2 r2V).union h_T3_new).mem a = h_T5_new.mem a
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    show ((PartialState.singletonReg .r3 r3V).union h_T4_new).mem a = h_T5_new.mem a
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    show ((PartialState.singletonReg .r4 r4V).union h_T5_new).mem a = h_T5_new.mem a
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
  -- Specifically for the 3 mem regions:
  have h_P_new_mem_p1 (i : Nat) (hi : i < r3V) :
      h_P_new.mem (r1V + i) = some (p1Bytes.get! i).toNat := by
    rw [h_P_new_mem_eq_T5]
    show ((PartialState.singletonMemBytes r1V p1Bytes).union h_T6_new).mem (r1V + i) = _
    have hsz_lt : i < p1Bytes.size := by rw [hsz1]; exact hi
    exact PartialState.union_mem_of_left_some
      (PartialState.singletonMemBytes_mem_at r1V p1Bytes i hsz_lt)
  have h_P_new_mem_p2 (j : Nat) (hj : j < r3V) :
      h_P_new.mem (r2V + j) = some (p2Bytes.get! j).toNat := by
    rw [h_P_new_mem_eq_T5]
    show ((PartialState.singletonMemBytes r1V p1Bytes).union h_T6_new).mem (r2V + j) = _
    -- p1 doesn't own r2V + j (from hd_p1_T6_new which we'll derive).
    have hsz_lt : j < p2Bytes.size := by rw [hsz2]; exact hj
    have h_p2_some : (PartialState.singletonMemBytes r2V p2Bytes).mem (r2V + j) =
        some (p2Bytes.get! j).toNat :=
      PartialState.singletonMemBytes_mem_at r2V p2Bytes j hsz_lt
    have h_T6_some : h_T6_new.mem (r2V + j) = some (p2Bytes.get! j).toNat := by
      show ((PartialState.singletonMemBytes r2V p2Bytes).union h_out_new).mem (r2V + j) = _
      exact PartialState.union_mem_of_left_some h_p2_some
    -- p1.mem (r2V + j) = none follows from pre disjointness hd_p1_T6.
    have h_p1_none : (PartialState.singletonMemBytes r1V p1Bytes).mem (r2V + j) = none :=
      h_p1_no_p2 j hj
    rw [PartialState.union_mem_of_left_none h_p1_none]
    exact h_T6_some
  have h_P_new_mem_out (k : Nat) (hk : k < 4) :
      h_P_new.mem (r4V + k) =
        (PartialState.singletonMemU32 r4V cmpResult).mem (r4V + k) := by
    rw [h_P_new_mem_eq_T5]
    show ((PartialState.singletonMemBytes r1V p1Bytes).union h_T6_new).mem (r4V + k) = _
    -- p1.mem (r4V + k) = none from hd_p1_T6 (since T6 owns the addr via out atom).
    have h_T6_some_pre : h_T6.mem (r4V + k) ≠ none := by
      rw [h_T6_mem_out k hk]
      match k, hk with
      | 0, _ => rw [show r4V + 0 = r4V from rfl, PartialState.singletonMemU32_mem_0]; exact Option.some_ne_none _
      | 1, _ => rw [PartialState.singletonMemU32_mem_1]; exact Option.some_ne_none _
      | 2, _ => rw [PartialState.singletonMemU32_mem_2]; exact Option.some_ne_none _
      | 3, _ => rw [PartialState.singletonMemU32_mem_3]; exact Option.some_ne_none _
    have h_p1_none : (PartialState.singletonMemBytes r1V p1Bytes).mem (r4V + k) = none := by
      have hd_mem := hd_p1_T6.mem
      rcases hd_mem (r4V + k) with hl | hr
      · exact hl
      · exact absurd hr h_T6_some_pre
    rw [PartialState.union_mem_of_left_none h_p1_none]
    show ((PartialState.singletonMemBytes r2V p2Bytes).union h_out_new).mem (r4V + k) = _
    -- p2.mem (r4V + k) = none from hd_p2_out similarly.
    have h_out_pre_some : ∃ v, (PartialState.singletonMemU32 r4V outOld).mem (r4V + k) = some v := by
      match k, hk with
      | 0, _ => exact ⟨_, by rw [show r4V + 0 = r4V from rfl]; exact PartialState.singletonMemU32_mem_0 _ _⟩
      | 1, _ => exact ⟨_, PartialState.singletonMemU32_mem_1 _ _⟩
      | 2, _ => exact ⟨_, PartialState.singletonMemU32_mem_2 _ _⟩
      | 3, _ => exact ⟨_, PartialState.singletonMemU32_mem_3 _ _⟩
    have h_p2_none : (PartialState.singletonMemBytes r2V p2Bytes).mem (r4V + k) = none := by
      have hd_mem := hd_p2_out.mem
      obtain ⟨v, hv⟩ := h_out_pre_some
      rcases hd_mem (r4V + k) with hl | hr
      · exact hl
      · rw [hv] at hr; nomatch hr
    rw [PartialState.union_mem_of_left_none h_p2_none]
  have h_P_new_mem_outside (a : Nat)
      (h_dst_p1 : a < r1V ∨ a ≥ r1V + r3V)
      (h_dst_p2 : a < r2V ∨ a ≥ r2V + r3V)
      (h_dst_out : a < r4V ∨ a ≥ r4V + 4) :
      h_P_new.mem a = none := by
    rw [h_P_new_mem_eq_T5]
    show ((PartialState.singletonMemBytes r1V p1Bytes).union h_T6_new).mem a = none
    have h_p1_none : (PartialState.singletonMemBytes r1V p1Bytes).mem a = none := by
      apply PartialState.singletonMemBytes_mem_outside
      rcases h_dst_p1 with hl | hr
      · left; exact hl
      · right; rw [hsz1]; exact hr
    rw [PartialState.union_mem_of_left_none h_p1_none]
    show ((PartialState.singletonMemBytes r2V p2Bytes).union h_out_new).mem a = none
    have h_p2_none : (PartialState.singletonMemBytes r2V p2Bytes).mem a = none := by
      apply PartialState.singletonMemBytes_mem_outside
      rcases h_dst_p2 with hl | hr
      · left; exact hl
      · right; rw [hsz2]; exact hr
    rw [PartialState.union_mem_of_left_none h_p2_none]
    exact PartialState.singletonMemU32_mem_outside r4V cmpResult a h_dst_out
  have h_P_new_pc : h_P_new.pc = none := by
    show ((PartialState.singletonReg .r0 0).union h_T1_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    show ((PartialState.singletonReg .r1 r1V).union h_T2_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    show ((PartialState.singletonReg .r2 r2V).union h_T3_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    show ((PartialState.singletonReg .r3 r3V).union h_T4_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    show ((PartialState.singletonReg .r4 r4V).union h_T5_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    show ((PartialState.singletonMemBytes r1V p1Bytes).union h_T6_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonMemBytes_pc]
    show ((PartialState.singletonMemBytes r2V p2Bytes).union h_out_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonMemBytes_pc]
    exact PartialState.singletonMemU32_pc
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
      by_cases h4 : r = .r4
      · right; rw [h4]; exact h_R_no_r4
      · left; exact h_P_new_regs_other r h0 h1 h2 h3 h4
    · by_cases h_p1 : r1V ≤ a ∧ a < r1V + r3V
      · right
        obtain ⟨h1, h2⟩ := h_p1
        have h_eq : a = r1V + (a - r1V) := by omega
        have h_lt : a - r1V < r3V := by omega
        rw [h_eq]; exact h_R_no_mem_p1 _ h_lt
      by_cases h_p2 : r2V ≤ a ∧ a < r2V + r3V
      · right
        obtain ⟨h1, h2⟩ := h_p2
        have h_eq : a = r2V + (a - r2V) := by omega
        have h_lt : a - r2V < r3V := by omega
        rw [h_eq]; exact h_R_no_mem_p2 _ h_lt
      by_cases h_out : r4V ≤ a ∧ a < r4V + 4
      · right
        obtain ⟨h1, h2⟩ := h_out
        have h_eq : a = r4V + (a - r4V) := by omega
        have h_lt : a - r4V < 4 := by omega
        rw [h_eq]; exact h_R_no_mem_out _ h_lt
      · left
        apply h_P_new_mem_outside
        · rcases Nat.lt_or_ge a r1V with h | h
          · left; exact h
          · rcases Nat.lt_or_ge a (r1V + r3V) with h' | h'
            · exact absurd ⟨h, h'⟩ h_p1
            · right; exact h'
        · rcases Nat.lt_or_ge a r2V with h | h
          · left; exact h
          · rcases Nat.lt_or_ge a (r2V + r3V) with h' | h'
            · exact absurd ⟨h, h'⟩ h_p2
            · right; exact h'
        · rcases Nat.lt_or_ge a r4V with h | h
          · left; exact h
          · rcases Nat.lt_or_ge a (r4V + 4) with h' | h'
            · exact absurd ⟨h, h'⟩ h_out
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
             h_r3_new, h_T4_new, hd_r3_T4_new, rfl, rfl,
             h_r4_new, h_T5_new, hd_r4_T5_new, rfl, rfl,
             h_p1_new, h_T6_new, hd_p1_T6_new, rfl, rfl,
             h_p2_new, h_out_new, hd_p2_out_new, rfl, rfl, rfl⟩,
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
      by_cases h4 : r = .r4
      · rw [h4] at hvr
        rw [PartialState.union_regs_of_left_some h_P_new_regs_r4] at hvr
        have hvr4 : vr = r4V := (Option.some.inj hvr).symm
        rw [h4, hexec_regs, hvr4,
            RegFile.get_set_diff _ _ _ _ (by decide : (.r4 : Reg) ≠ .r0)]
        exact hs_regs_r4
      · rw [PartialState.union_regs_of_left_none
            (h_P_new_regs_other r h0 h1 h2 h3 h4)] at hvr
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
      by_cases h_p1_addr : r1V ≤ a ∧ a < r1V + r3V
      · obtain ⟨h1, h2⟩ := h_p1_addr
        have h_eq : a = r1V + (a - r1V) := by omega
        have h_lt : a - r1V < r3V := by omega
        rw [h_eq] at hvm ⊢
        rw [PartialState.union_mem_of_left_some
            (h_P_new_mem_p1 _ h_lt)] at hvm
        have hvmEq : vm = (p1Bytes.get! (a - r1V)).toNat :=
          (Option.some.inj hvm).symm
        -- (executeFn ...).mem (r1V + (a - r1V)) is preserved (outside the writeU32 range).
        have h_out_range : (r1V + (a - r1V)) < r4V ∨ (r1V + (a - r1V)) ≥ r4V + 4 := by
          -- r1V+(a-r1V) is in p1, and p1 ⊥ T6 ⊇ out, so it's outside the out range.
          have h_p1_some : (PartialState.singletonMemBytes r1V p1Bytes).mem (r1V + (a - r1V)) =
              some (p1Bytes.get! (a - r1V)).toNat := by
            apply PartialState.singletonMemBytes_mem_at
            rw [hsz1]; exact h_lt
          have h_T6_none : h_T6.mem (r1V + (a - r1V)) = none := by
            have hd_mem := hd_p1_T6.mem
            rcases hd_mem (r1V + (a - r1V)) with hl | hr
            · rw [h_p1_some] at hl; nomatch hl
            · exact hr
          -- T6 contains the out U32 atom; T6.mem none at this addr means out is also none.
          have h_out_pre_none : (PartialState.singletonMemU32 r4V outOld).mem (r1V + (a - r1V)) = none := by
            rw [← hu_p2_out] at h_T6_none
            exact (PartialState.union_mem_eq_none_iff.mp h_T6_none).2
          rcases Nat.lt_or_ge (r1V + (a - r1V)) r4V with hlt | hge
          · left; exact hlt
          rcases Nat.lt_or_ge (r1V + (a - r1V)) (r4V + 4) with hlt' | hge'
          · -- Inside [r4V, r4V+4); contradict h_out_pre_none.
            exfalso
            rcases Nat.lt_or_ge (r1V + (a - r1V)) (r4V + 1) with h_a | h_a
            · have hv : (PartialState.singletonMemU32 r4V outOld).mem (r1V + (a - r1V)) = some (outOld % 256) := by
                rw [show r1V + (a - r1V) = r4V from by omega]
                exact PartialState.singletonMemU32_mem_0 _ _
              rw [hv] at h_out_pre_none; nomatch h_out_pre_none
            rcases Nat.lt_or_ge (r1V + (a - r1V)) (r4V + 2) with h_a | h_a
            · have hv : (PartialState.singletonMemU32 r4V outOld).mem (r1V + (a - r1V)) = some (outOld / 0x100 % 256) := by
                rw [show r1V + (a - r1V) = r4V + 1 from by omega]
                exact PartialState.singletonMemU32_mem_1 _ _
              rw [hv] at h_out_pre_none; nomatch h_out_pre_none
            rcases Nat.lt_or_ge (r1V + (a - r1V)) (r4V + 3) with h_a | h_a
            · have hv : (PartialState.singletonMemU32 r4V outOld).mem (r1V + (a - r1V)) = some (outOld / 0x10000 % 256) := by
                rw [show r1V + (a - r1V) = r4V + 2 from by omega]
                exact PartialState.singletonMemU32_mem_2 _ _
              rw [hv] at h_out_pre_none; nomatch h_out_pre_none
            · have hv : (PartialState.singletonMemU32 r4V outOld).mem (r1V + (a - r1V)) = some (outOld / 0x1000000 % 256) := by
                rw [show r1V + (a - r1V) = r4V + 3 from by omega]
                exact PartialState.singletonMemU32_mem_3 _ _
              rw [hv] at h_out_pre_none; nomatch h_out_pre_none
          · right; exact hge'
        rw [hexec_mem_outside_u32 _ h_out_range, hvmEq]
        exact hs_mem_p1 _ h_lt
      by_cases h_p2_addr : r2V ≤ a ∧ a < r2V + r3V
      · obtain ⟨h1, h2⟩ := h_p2_addr
        have h_eq : a = r2V + (a - r2V) := by omega
        have h_lt : a - r2V < r3V := by omega
        rw [h_eq] at hvm ⊢
        rw [PartialState.union_mem_of_left_some
            (h_P_new_mem_p2 _ h_lt)] at hvm
        have hvmEq : vm = (p2Bytes.get! (a - r2V)).toNat :=
          (Option.some.inj hvm).symm
        -- Same logic: r2V + (a-r2V) is in p2 range, disjoint from out range.
        have h_out_range : (r2V + (a - r2V)) < r4V ∨ (r2V + (a - r2V)) ≥ r4V + 4 := by
          have h_p2_some : (PartialState.singletonMemBytes r2V p2Bytes).mem (r2V + (a - r2V)) =
              some (p2Bytes.get! (a - r2V)).toNat := by
            apply PartialState.singletonMemBytes_mem_at
            rw [hsz2]; exact h_lt
          have h_out_pre_none : (PartialState.singletonMemU32 r4V outOld).mem (r2V + (a - r2V)) = none := by
            have hd_mem := hd_p2_out.mem
            rcases hd_mem (r2V + (a - r2V)) with hl | hr
            · rw [h_p2_some] at hl; nomatch hl
            · exact hr
          rcases Nat.lt_or_ge (r2V + (a - r2V)) r4V with hlt | hge
          · left; exact hlt
          rcases Nat.lt_or_ge (r2V + (a - r2V)) (r4V + 4) with hlt' | hge'
          · exfalso
            rcases Nat.lt_or_ge (r2V + (a - r2V)) (r4V + 1) with h_a | h_a
            · have hv : (PartialState.singletonMemU32 r4V outOld).mem (r2V + (a - r2V)) = some (outOld % 256) := by
                rw [show r2V + (a - r2V) = r4V from by omega]
                exact PartialState.singletonMemU32_mem_0 _ _
              rw [hv] at h_out_pre_none; nomatch h_out_pre_none
            rcases Nat.lt_or_ge (r2V + (a - r2V)) (r4V + 2) with h_a | h_a
            · have hv : (PartialState.singletonMemU32 r4V outOld).mem (r2V + (a - r2V)) = some (outOld / 0x100 % 256) := by
                rw [show r2V + (a - r2V) = r4V + 1 from by omega]
                exact PartialState.singletonMemU32_mem_1 _ _
              rw [hv] at h_out_pre_none; nomatch h_out_pre_none
            rcases Nat.lt_or_ge (r2V + (a - r2V)) (r4V + 3) with h_a | h_a
            · have hv : (PartialState.singletonMemU32 r4V outOld).mem (r2V + (a - r2V)) = some (outOld / 0x10000 % 256) := by
                rw [show r2V + (a - r2V) = r4V + 2 from by omega]
                exact PartialState.singletonMemU32_mem_2 _ _
              rw [hv] at h_out_pre_none; nomatch h_out_pre_none
            · have hv : (PartialState.singletonMemU32 r4V outOld).mem (r2V + (a - r2V)) = some (outOld / 0x1000000 % 256) := by
                rw [show r2V + (a - r2V) = r4V + 3 from by omega]
                exact PartialState.singletonMemU32_mem_3 _ _
              rw [hv] at h_out_pre_none; nomatch h_out_pre_none
          · right; exact hge'
        rw [hexec_mem_outside_u32 _ h_out_range, hvmEq]
        exact hs_mem_p2 _ h_lt
      by_cases h_out_addr : r4V ≤ a ∧ a < r4V + 4
      · obtain ⟨h1, h2⟩ := h_out_addr
        -- 4-case split on which byte of the U32 region
        rcases Nat.lt_or_ge a (r4V + 1) with h_a | h_a
        · have h_eq : a = r4V := by omega
          rw [h_eq] at hvm
          have h_pnew_some : h_P_new.mem r4V = some (cmpResult % 256) := by
            have h := h_P_new_mem_out 0 (by omega)
            rw [show r4V + 0 = r4V from rfl] at h
            rw [h]; exact PartialState.singletonMemU32_mem_0 _ _
          rw [PartialState.union_mem_of_left_some h_pnew_some] at hvm
          have hvmEq : vm = cmpResult % 256 := (Option.some.inj hvm).symm
          rw [h_eq, hvmEq]; exact hexec_mem_u32_0
        rcases Nat.lt_or_ge a (r4V + 2) with h_a | h_a
        · have h_eq : a = r4V + 1 := by omega
          rw [h_eq] at hvm
          have h_pnew_some : h_P_new.mem (r4V + 1) = some (cmpResult / 0x100 % 256) := by
            have h := h_P_new_mem_out 1 (by omega)
            rw [h]; exact PartialState.singletonMemU32_mem_1 _ _
          rw [PartialState.union_mem_of_left_some h_pnew_some] at hvm
          have hvmEq : vm = cmpResult / 0x100 % 256 := (Option.some.inj hvm).symm
          rw [h_eq, hvmEq]; exact hexec_mem_u32_1
        rcases Nat.lt_or_ge a (r4V + 3) with h_a | h_a
        · have h_eq : a = r4V + 2 := by omega
          rw [h_eq] at hvm
          have h_pnew_some : h_P_new.mem (r4V + 2) = some (cmpResult / 0x10000 % 256) := by
            have h := h_P_new_mem_out 2 (by omega)
            rw [h]; exact PartialState.singletonMemU32_mem_2 _ _
          rw [PartialState.union_mem_of_left_some h_pnew_some] at hvm
          have hvmEq : vm = cmpResult / 0x10000 % 256 := (Option.some.inj hvm).symm
          rw [h_eq, hvmEq]; exact hexec_mem_u32_2
        · have h_eq : a = r4V + 3 := by omega
          rw [h_eq] at hvm
          have h_pnew_some : h_P_new.mem (r4V + 3) = some (cmpResult / 0x1000000 % 256) := by
            have h := h_P_new_mem_out 3 (by omega)
            rw [h]; exact PartialState.singletonMemU32_mem_3 _ _
          rw [PartialState.union_mem_of_left_some h_pnew_some] at hvm
          have hvmEq : vm = cmpResult / 0x1000000 % 256 := (Option.some.inj hvm).symm
          rw [h_eq, hvmEq]; exact hexec_mem_u32_3
      · -- Outside all three ranges.
        have h_out_p1 : a < r1V ∨ a ≥ r1V + r3V := by
          rcases Nat.lt_or_ge a r1V with h | h
          · left; exact h
          · rcases Nat.lt_or_ge a (r1V + r3V) with h' | h'
            · exact absurd ⟨h, h'⟩ h_p1_addr
            · right; exact h'
        have h_out_p2 : a < r2V ∨ a ≥ r2V + r3V := by
          rcases Nat.lt_or_ge a r2V with h | h
          · left; exact h
          · rcases Nat.lt_or_ge a (r2V + r3V) with h' | h'
            · exact absurd ⟨h, h'⟩ h_p2_addr
            · right; exact h'
        have h_out_out : a < r4V ∨ a ≥ r4V + 4 := by
          rcases Nat.lt_or_ge a r4V with h | h
          · left; exact h
          · rcases Nat.lt_or_ge a (r4V + 4) with h' | h'
            · exact absurd ⟨h, h'⟩ h_out_addr
            · right; exact h'
        rw [PartialState.union_mem_of_left_none
            (h_P_new_mem_outside a h_out_p1 h_out_p2 h_out_out)] at hvm
        rw [hexec_mem_outside_u32 a h_out_out]
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
        rw [← hu_r0_T1, ← hu_r1_T2, ← hu_r2_T3, ← hu_r3_T4, ← hu_r4_T5, ← hu_p1_T6, ← hu_p2_out]; rfl
      have hp_rd : hp.returnData = some rd := by
        rw [← hu_PR, PartialState.union_returnData_of_left_none h_P_rd]
        exact hva
      have hexec_rd : (executeFn fetch s 1).returnData = s.returnData := by
        simp [executeFn, step, execSyscall, MemOps.execCmp, hex, hfetch, hnb,
          hRd1, hRd2, hWr]
      rw [hexec_rd]
      exact hcompat.returnData rd hp_rd
    · intro cs hva
      have h_P_new_cs : h_P_new.callStack = none := by rfl
      rw [PartialState.union_callStack_of_left_none h_P_new_cs] at hva
      have h_P_cs : h_P.callStack = none := by
        rw [← hu_r0_T1, ← hu_r1_T2, ← hu_r2_T3, ← hu_r3_T4, ← hu_r4_T5, ← hu_p1_T6, ← hu_p2_out]; rfl
      have hp_cs : hp.callStack = some cs := by
        rw [← hu_PR, PartialState.union_callStack_of_left_none h_P_cs]
        exact hva
      have hexec_cs : (executeFn fetch s 1).callStack = s.callStack := by
        simp [executeFn, step, execSyscall, MemOps.execCmp, hex, hfetch, hnb,
          hRd1, hRd2, hWr]
      rw [hexec_cs]
      exact hcompat.callStack cs hp_cs

/-! ## Memset with a `↦U64` split tail (qedlift blob read-through)

When the program later READS a dword inside the memset-filled region (p_token
CloseAccount: `ldxdw [acct+88]` inside the zeroing of `[acct+48, +96)`), the
blob post must expose that cell as a `↦U64` atom, else the read's atom overlaps
the blob (unsatisfiable sepConj; audit H8 Phase C). This variant splits the
written blob's last 8 bytes off as a `↦U64` cell of the replicated fill byte. -/

/-- `replicateByte` splits across `+`. -/
theorem replicateByte_split (b : UInt8) (m k : Nat) :
    replicateByte b (m + k) = replicateByte b m ++ replicateByte b k := by
  apply ByteArray.ext
  simp only [replicateByte, ByteArray.data_append]
  apply Array.ext
  · simp
  · intro i h1 h2
    simp only [Array.getElem_replicate]
    rw [Array.getElem_append]
    split <;> simp only [Array.getElem_replicate]

/-- Eight replicated fill bytes are the `u64LE` of any `w` whose eight LE bytes
    each equal the fill byte. Byte equations are parameters so the emitter
    discharges them by `decide` on a concrete `w` (avoiding big-constant `omega`). -/
theorem replicateByte8_eq_u64LE (x w : Nat)
    (h0 : w % 256 = x % 256)
    (h1 : w / 0x100 % 256 = x % 256)
    (h2 : w / 0x10000 % 256 = x % 256)
    (h3 : w / 0x1000000 % 256 = x % 256)
    (h4 : w / 0x100000000 % 256 = x % 256)
    (h5 : w / 0x10000000000 % 256 = x % 256)
    (h6 : w / 0x1000000000000 % 256 = x % 256)
    (h7 : w / 0x100000000000000 % 256 = x % 256) :
    replicateByte (x % 256).toUInt8 8 = PartialState.u64LE w := by
  show (⟨#[(x % 256).toUInt8, (x % 256).toUInt8, (x % 256).toUInt8,
           (x % 256).toUInt8, (x % 256).toUInt8, (x % 256).toUInt8,
           (x % 256).toUInt8, (x % 256).toUInt8]⟩ : ByteArray) = _
  simp only [PartialState.u64LE, h0, h1, h2, h3, h4, h5, h6, h7]

set_option maxHeartbeats 1600000 in
/-- `sol_memset_` whose written blob exposes its last 8 bytes as a
    `↦U64` cell (`hn : r3V = n + 8` fixes the split point). Derived
    from `call_sol_memset_spec` by reshaping the post through
    `memBytesIs_append` + `memU64Is_eq_memBytesIs`. -/
theorem call_sol_memset_split_u64_spec
    (r0Old r1V r2V r3V n w a pc nCu : Nat) (bsOld : ByteArray)
    (hbs : bsOld.size = r3V)
    (hn : r3V = n + 8)
    (ha : a = r1V + n)
    (hw0 : w % 256 = r2V % 256)
    (hw1 : w / 0x100 % 256 = r2V % 256)
    (hw2 : w / 0x10000 % 256 = r2V % 256)
    (hw3 : w / 0x1000000 % 256 = r2V % 256)
    (hw4 : w / 0x100000000 % 256 = r2V % 256)
    (hw5 : w / 0x10000000000 % 256 = r2V % 256)
    (hw6 : w / 0x1000000000000 % 256 = r2V % 256)
    (hw7 : w / 0x100000000000000 % 256 = r2V % 256)
    (hCu : ∀ s : State,
        (step (.call .sol_memset) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithinMem 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_memset))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V)
       ** (r1V ↦Bytes bsOld))
      ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V)
       ** ((r1V ↦Bytes (replicateByte (r2V % 256).toUInt8 n)) **
           (a ↦U64 w)))
      (fun rt => rt.containsWritable r1V r3V = true) := by
  have hsplit : ∀ h',
      memBytesIs r1V (replicateByte (r2V % 256).toUInt8 r3V) h'
      ↔ ((r1V ↦Bytes replicateByte (r2V % 256).toUInt8 n) **
         (a ↦U64 w)) h' := by
    intro h'
    rw [hn, replicateByte_split, ha]
    have happ := memBytesIs_append r1V
      (replicateByte (r2V % 256).toUInt8 n)
      (replicateByte (r2V % 256).toUInt8 8) h'
    rw [replicateByte_size] at happ
    rw [happ]
    exact sepConj_iff_congr_right _ (fun h'' => by
      rw [replicateByte8_eq_u64LE r2V w hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7]
      exact (memU64Is_eq_memBytesIs (r1V + n) _ h'').symm) h'
  refine cuTripleWithinMem_weaken (fun _ x => x) ?_ (fun _ x => x)
    (call_sol_memset_spec r0Old r1V r2V r3V pc nCu bsOld hbs hCu)
  intro h hh
  exact (sepConj_iff_congr_right _ (fun h1 =>
    sepConj_iff_congr_right _ (fun h2 =>
      sepConj_iff_congr_right _ (fun h3 =>
        sepConj_iff_congr_right _ (fun h4 => hsplit h4) h3) h2) h1) h).mp hh

set_option maxHeartbeats 1600000 in
/-- `sol_memset_` over a target whose LAST 8 bytes the lift ALREADY
    owns as a `↦U64` cell (p_token CloseAccount reads the lamports
    dword at `[acct+88]` BEFORE zeroing `[acct+48, +96)`): the pre owns
    the prefix blob + that cell; the post is the shrunk fill blob +
    the cell holding the fill spread across all eight lanes. -/
theorem call_sol_memset_presplit_u64_spec
    (r0Old r1V r2V r3V n w a oldV pc nCu : Nat) (bsOld : ByteArray)
    (hbs : bsOld.size = n)
    (hn : r3V = n + 8)
    (ha : a = r1V + n)
    (hw0 : w % 256 = r2V % 256)
    (hw1 : w / 0x100 % 256 = r2V % 256)
    (hw2 : w / 0x10000 % 256 = r2V % 256)
    (hw3 : w / 0x1000000 % 256 = r2V % 256)
    (hw4 : w / 0x100000000 % 256 = r2V % 256)
    (hw5 : w / 0x10000000000 % 256 = r2V % 256)
    (hw6 : w / 0x1000000000000 % 256 = r2V % 256)
    (hw7 : w / 0x100000000000000 % 256 = r2V % 256)
    (hCu : ∀ s : State,
        (step (.call .sol_memset) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithinMem 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_memset))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V)
       ** ((r1V ↦Bytes bsOld) ** (a ↦U64 oldV)))
      ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V)
       ** ((r1V ↦Bytes (replicateByte (r2V % 256).toUInt8 n)) **
           (a ↦U64 w)))
      (fun rt => rt.containsWritable r1V r3V = true) := by
  have hpre : ∀ h',
      ((r1V ↦Bytes bsOld) ** (a ↦U64 oldV)) h'
      ↔ memBytesIs r1V (bsOld ++ PartialState.u64LE oldV) h' := by
    intro h'
    have happ := memBytesIs_append r1V bsOld (PartialState.u64LE oldV) h'
    rw [hbs, ← ha] at happ
    rw [happ]
    exact sepConj_iff_congr_right _
      (fun h'' => memU64Is_eq_memBytesIs a oldV h'') h'
  have hsplit : ∀ h',
      memBytesIs r1V (replicateByte (r2V % 256).toUInt8 r3V) h'
      ↔ ((r1V ↦Bytes replicateByte (r2V % 256).toUInt8 n) **
         (a ↦U64 w)) h' := by
    intro h'
    rw [hn, replicateByte_split, ha]
    have happ := memBytesIs_append r1V
      (replicateByte (r2V % 256).toUInt8 n)
      (replicateByte (r2V % 256).toUInt8 8) h'
    rw [replicateByte_size] at happ
    rw [happ]
    exact sepConj_iff_congr_right _ (fun h'' => by
      rw [replicateByte8_eq_u64LE r2V w hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7]
      exact (memU64Is_eq_memBytesIs (r1V + n) _ h'').symm) h'
  refine cuTripleWithinMem_weaken ?_ ?_ (fun _ x => x)
    (call_sol_memset_spec r0Old r1V r2V r3V pc nCu
      (bsOld ++ PartialState.u64LE oldV)
      (by simp [ByteArray.size_append, hbs, hn]) hCu)
  · intro h hh
    exact (sepConj_iff_congr_right _ (fun h1 =>
      sepConj_iff_congr_right _ (fun h2 =>
        sepConj_iff_congr_right _ (fun h3 =>
          sepConj_iff_congr_right _ (fun h4 => (hpre h4)) h3) h2) h1) h).mp hh
  · intro h hh
    exact (sepConj_iff_congr_right _ (fun h1 =>
      sepConj_iff_congr_right _ (fun h2 =>
        sepConj_iff_congr_right _ (fun h3 =>
          sepConj_iff_congr_right _ (fun h4 => hsplit h4) h3) h2) h1) h).mp hh

set_option maxHeartbeats 1600000 in
/-- Like `call_sol_memset_presplit_u64_spec`, but the lift owns the
    target's last SIXTEEN bytes as TWO `↦U64` cells (p_token
    CloseAccount reads two account dwords before the zeroing). -/
theorem call_sol_memset_presplit_2u64_spec
    (r0Old r1V r2V r3V n w a1 a2 oldV1 oldV2 pc nCu : Nat) (bsOld : ByteArray)
    (hbs : bsOld.size = n)
    (hn : r3V = n + 16)
    (ha1 : a1 = r1V + n)
    (ha2 : a2 = r1V + n + 8)
    (hw0 : w % 256 = r2V % 256)
    (hw1 : w / 0x100 % 256 = r2V % 256)
    (hw2 : w / 0x10000 % 256 = r2V % 256)
    (hw3 : w / 0x1000000 % 256 = r2V % 256)
    (hw4 : w / 0x100000000 % 256 = r2V % 256)
    (hw5 : w / 0x10000000000 % 256 = r2V % 256)
    (hw6 : w / 0x1000000000000 % 256 = r2V % 256)
    (hw7 : w / 0x100000000000000 % 256 = r2V % 256)
    (hCu : ∀ s : State,
        (step (.call .sol_memset) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithinMem 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_memset))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V)
       ** ((r1V ↦Bytes bsOld) ** ((a1 ↦U64 oldV1) ** (a2 ↦U64 oldV2))))
      ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V)
       ** ((r1V ↦Bytes (replicateByte (r2V % 256).toUInt8 n)) **
           ((a1 ↦U64 w) ** (a2 ↦U64 w))))
      (fun rt => rt.containsWritable r1V r3V = true) := by
  -- Old tail: two adjacent `↦U64` cells ↔ the 16-byte blob of their
  -- LE encodings.
  have htail : ∀ h',
      memBytesIs (r1V + n)
        (PartialState.u64LE oldV1 ++ PartialState.u64LE oldV2) h'
      ↔ ((a1 ↦U64 oldV1) ** (a2 ↦U64 oldV2)) h' := by
    intro h'
    have happ := memBytesIs_append (r1V + n)
      (PartialState.u64LE oldV1) (PartialState.u64LE oldV2) h'
    rw [PartialState.u64LE_size] at happ
    rw [happ, ← ha2, ← ha1]
    exact Iff.trans
      (sepConj_iff_congr_left _
        (fun h'' => (memU64Is_eq_memBytesIs a1 oldV1 h'').symm) h')
      (sepConj_iff_congr_right _
        (fun h'' => (memU64Is_eq_memBytesIs a2 oldV2 h'').symm) h')
  have hpre : ∀ h',
      ((r1V ↦Bytes bsOld) ** ((a1 ↦U64 oldV1) ** (a2 ↦U64 oldV2))) h'
      ↔ memBytesIs r1V
          (bsOld ++ (PartialState.u64LE oldV1 ++ PartialState.u64LE oldV2)) h' := by
    intro h'
    have happ := memBytesIs_append r1V bsOld
      (PartialState.u64LE oldV1 ++ PartialState.u64LE oldV2) h'
    rw [hbs] at happ
    rw [happ]
    exact sepConj_iff_congr_right _ (fun h'' => (htail h'').symm) h'
  -- New tail: two `↦U64 w` cells ↔ the 16 replicated fill bytes.
  have htailw : ∀ h',
      memBytesIs (r1V + n)
        (replicateByte (r2V % 256).toUInt8 8
          ++ replicateByte (r2V % 256).toUInt8 8) h'
      ↔ ((a1 ↦U64 w) ** (a2 ↦U64 w)) h' := by
    intro h'
    have happ := memBytesIs_append (r1V + n)
      (replicateByte (r2V % 256).toUInt8 8)
      (replicateByte (r2V % 256).toUInt8 8) h'
    rw [replicateByte_size] at happ
    rw [happ, ← ha2, ← ha1,
        replicateByte8_eq_u64LE r2V w hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7]
    exact Iff.trans
      (sepConj_iff_congr_left _
        (fun h'' => (memU64Is_eq_memBytesIs a1 w h'').symm) h')
      (sepConj_iff_congr_right _
        (fun h'' => (memU64Is_eq_memBytesIs a2 w h'').symm) h')
  have hsplit : ∀ h',
      memBytesIs r1V (replicateByte (r2V % 256).toUInt8 r3V) h'
      ↔ ((r1V ↦Bytes replicateByte (r2V % 256).toUInt8 n) **
         ((a1 ↦U64 w) ** (a2 ↦U64 w))) h' := by
    intro h'
    rw [hn, replicateByte_split _ n 16,
        (replicateByte_split ((r2V % 256)).toUInt8 8 8 :
          replicateByte _ 16 = _)]
    have happ := memBytesIs_append r1V
      (replicateByte (r2V % 256).toUInt8 n)
      (replicateByte (r2V % 256).toUInt8 8
        ++ replicateByte (r2V % 256).toUInt8 8) h'
    rw [replicateByte_size] at happ
    rw [happ]
    exact sepConj_iff_congr_right _ (fun h'' => htailw h'') h'
  refine cuTripleWithinMem_weaken ?_ ?_ (fun _ x => x)
    (call_sol_memset_spec r0Old r1V r2V r3V pc nCu
      (bsOld ++ (PartialState.u64LE oldV1 ++ PartialState.u64LE oldV2))
      (by simp [ByteArray.size_append, hbs, hn]) hCu)
  · intro h hh
    exact (sepConj_iff_congr_right _ (fun h1 =>
      sepConj_iff_congr_right _ (fun h2 =>
        sepConj_iff_congr_right _ (fun h3 =>
          sepConj_iff_congr_right _ (fun h4 => hpre h4) h3) h2) h1) h).mp hh
  · intro h hh
    exact (sepConj_iff_congr_right _ (fun h1 =>
      sepConj_iff_congr_right _ (fun h2 =>
        sepConj_iff_congr_right _ (fun h3 =>
          sepConj_iff_congr_right _ (fun h4 => hsplit h4) h3) h2) h1) h).mp hh

end SVM.SBPF
