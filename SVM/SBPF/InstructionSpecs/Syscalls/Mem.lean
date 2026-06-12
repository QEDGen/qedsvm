import SVM.SBPF.InstructionSpecs.Syscalls.Pda

namespace SVM.SBPF

open Memory

/-! ## Generic fixed-payload-write helper: `cuTripleWithin_syscall_writesR1Bytes`

The 6 fixed-payload sysvars (4 zero-fill: `sol_get_last_restart_slot`,
`sol_get_fees_sysvar`, `sol_get_clock_sysvar`, `sol_get_epoch_rewards_sysvar`
+ 2 non-zero-fill: `sol_get_rent_sysvar`, `sol_get_epoch_schedule_sysvar`)
all share the same Hoare-triple shape: write a fixed `ByteArray` payload
of size `N` at `*r1`, set `r0 := 0`. This helper captures that pattern
parametrically in `(sc, bsNew)`, using the generic `↦Bytes` atom so the
proof scales to 17B / 40B / 81B without per-byte case ladders.

The zero-fill case is the special instantiation `bsNew := zerosByteArray N`
(defined at the top of this file). -/

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

-- `Mem_read_default` is hoisted to the top of the file (used by both
-- sysvar specs and `call_sol_get_return_data_spec`).

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
  -- ==== Phase 1: destructure the 3-atom (P ** R) split. ====
  obtain ⟨hp, hcompat, h_P, h_R, hd_PR, hu_PR, h_P_sat, h_R_sat⟩ := hPR
  obtain ⟨h_r0, h_T1, hd_r0_T1, hu_r0_T1, h_r0_pred, h_T1_sat⟩ := h_P_sat
  obtain ⟨h_r1, h_b, hd_r1_b, hu_r1_b, h_r1_pred, h_b_pred⟩ := h_T1_sat
  rw [h_r0_pred] at hu_r0_T1 hd_r0_T1
  rw [h_r1_pred] at hu_r1_b hd_r1_b
  rw [h_b_pred] at hu_r1_b hd_r1_b
  clear h_r0_pred h_r1_pred h_b_pred h_r0 h_r1 h_b
  have hcr_regs := hcompat.regs
  have hcm_mem := hcompat.mem
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
  -- ==== Phase 4: facts about h_R from outer disjointness with h_P. ====
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
  -- ==== Phase 6: outer disjointness h_P_new ⊥ h_R. ====
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
  -- ==== Phase 7: assemble the witness for (Q ** R).holdsFor. ====
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
    (sc : Syscall) (bsNew : ByteArray) (pc : Nat) (nCu : Nat) (r2V r3V : Nat)
    (h_step_regs : ∀ s : State, (step (.call sc) s).regs = s.regs.set .r0 0)
    (h_step_mem_in  : ∀ s : State, s.regs.r2 = r2V → s.regs.r3 = r3V →
        ∀ i, i < bsNew.size →
        (step (.call sc) s).mem (s.regs.r1 + i) = (bsNew.get! i).toNat)
    (h_step_mem_out : ∀ s : State, s.regs.r3 = r3V →
        ∀ a, (a < s.regs.r1 ∨ a ≥ s.regs.r1 + bsNew.size) →
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
        ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V)
         ** (r1V ↦Bytes bsOld))
        ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V)
         ** (r1V ↦Bytes bsNew)) := by
  intro r0Old r1V bsOld hbsSize R hRfree fetch hcr s hPR hpc hex hbud
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
  have hcr_regs := hcompat.regs
  have hcm_mem := hcompat.mem
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
    rw [hstep_eq, ← hs_r1_field]
    exact h_step_mem_in s hs_r2_field hs_r3_field i hi
  have hexec_mem_out (a : Nat) (h : a < r1V ∨ a ≥ r1V + N) :
      (executeFn fetch s 1).mem a = s.mem a := by
    rw [hstep_eq]
    apply h_step_mem_out s hs_r3_field a
    rw [hs_r1_field]; exact h
  -- ==== Phase 4: facts about h_R from outer disjointness with h_P. ====
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
  -- ==== Phase 6: outer disjointness h_P_new ⊥ h_R. ====
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
  -- ==== Phase 7: assemble the witness for (Q ** R).holdsFor. ====
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

`sol_memset_(dst, val, n)`: write the low byte of `r2` (`r2 % 256`)
into `n = r3` bytes starting at `dst = r1`. Sets `r0 := 0`. First
state-dependent payload syscall in the SL track — uses the 5-atom
helper `cuTripleWithin_syscall_writesR1Bytes_r2r3` because the
bytes written depend on the register values `r2V` and `r3V`. -/

theorem call_sol_memset_spec
    (r0Old r1V r2V r3V pc nCu : Nat) (bsOld : ByteArray) (hbs : bsOld.size = r3V)
    (hCu : ∀ s : State,
        (step (.call .sol_memset) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_memset))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V)
       ** (r1V ↦Bytes bsOld))
      ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V)
       ** (r1V ↦Bytes (replicateByte (r2V % 256).toUInt8 r3V))) := by
  refine cuTripleWithin_syscall_writesR1Bytes_r2r3
    .sol_memset (replicateByte (r2V % 256).toUInt8 r3V) pc nCu r2V r3V
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hCu r0Old r1V bsOld ?_
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
  · intro s
    simp only [step, execSyscall, MemOps.execSet]
  · intro s
    simp only [step, execSyscall, MemOps.execSet]
  · rw [replicateByte_size]; exact hbs

/-! ## 6-atom mem-copy helper: `cuTripleWithin_syscall_copiesR2ToR1`

Generalization of the 5-atom helper for syscalls that copy bytes
from `[r2, r2 + r3)` to `[r1, r1 + r3)` (`sol_memcpy_`, `sol_memmove_`).
Adds a read-only source-bytes atom at `r2V` to the 5-atom precondition;
the post-state has the same source-bytes atom (read but unmodified)
plus the dst-bytes atom rewritten to `srcBytes`.

`h_step_mem_in` is conditional on `s.regs.r2 = r2V` and `s.regs.r3 = r3V`
(register pinning) and produces the dst-write in terms of `s.mem (r2V + i)`;
the proof body extracts `s.mem (r2V + i) = (srcBytes.get! i).toNat` from
the source-bytes atom in the precondition. The `% 256` in the actual
`execCopy` semantics is a no-op for byte values since
`(UInt8.toNat _) < 256`, so the post value matches `srcBytes` directly.

Separation logic implies the source and destination ranges are
disjoint — this matches the C-level "memcpy with overlap is UB"
assumption. Overlapping memmove would need a different spec. -/

theorem cuTripleWithin_syscall_copiesR2ToR1
    (sc : Syscall) (pc : Nat) (nCu : Nat) (r2V r3V : Nat) (srcBytes : ByteArray)
    (hsrcSize : srcBytes.size = r3V)
    (h_step_regs : ∀ s : State, (step (.call sc) s).regs = s.regs.set .r0 0)
    (h_step_mem_in  : ∀ s : State, s.regs.r2 = r2V → s.regs.r3 = r3V →
        ∀ i, i < r3V →
        (step (.call sc) s).mem (s.regs.r1 + i) = s.mem (s.regs.r2 + i) % 256)
    (h_step_mem_out : ∀ s : State, s.regs.r3 = r3V →
        ∀ a, (a < s.regs.r1 ∨ a ≥ s.regs.r1 + r3V) →
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
    ∀ r0Old r1V (bsOld : ByteArray), bsOld.size = r3V →
      cuTripleWithin 1 nCu pc (pc + 1)
        (CodeReq.singleton pc (.call sc))
        ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V)
         ** (r2V ↦Bytes srcBytes) ** (r1V ↦Bytes bsOld))
        ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V)
         ** (r2V ↦Bytes srcBytes) ** (r1V ↦Bytes srcBytes)) := by
  intro r0Old r1V bsOld hbsSize R hRfree fetch hcr s hPR hpc hex hbud
  -- ==== Phase 1: destructure the 6-atom (P ** R) split. ====
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
  -- ==== Phase 2: climb regs / mem from atoms through hp to s. ====
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
  -- Dest-bytes mem fact: h_P.mem matches bsOld over [r1V, r1V+r3V), via h_b.
  -- The src atom owns [r2V, r2V+r3V); these ranges are disjoint by hd_src_b.
  -- For positions in the dst range, h_b is the carrier.
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
    -- src atom owns [r2V, r2V+r3V); to use h_b's value, src.mem at r1V+i must be none.
    -- That follows from hd_src_b applied at r1V+i, given src.mem isSome at r1V+i iff
    -- r1V+i ∈ [r2V, r2V+r3V). We don't need that direction: union picks h_b if src is none.
    -- We DO need src.mem (r1V + i) = none.
    have h_src_none : (PartialState.singletonMemBytes r2V srcBytes).mem (r1V + i) = none := by
      -- By disjointness hd_src_b: at any address, either src or b owns it, not both.
      -- Pick the side: b owns (r1V + i) (just shown via singletonMemBytes_mem_at on bsOld).
      -- So src must not own it.
      have hd_mem := hd_src_b.mem
      rcases hd_mem (r1V + i) with hl | hr
      · exact hl
      · rw [hr] at h_b_some; nomatch h_b_some
    rw [PartialState.union_mem_of_left_none h_src_none]
    exact h_b_some
  -- Source-bytes regs are empty (sanity): not used directly, but helps later.
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
  -- ==== Phase 3: fetch + per-field facts about (executeFn fetch s 1). ====
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
  -- Compose the in-range mem fact with the source-bytes value.
  have hexec_mem_in (i : Nat) (hi : i < r3V) :
      (executeFn fetch s 1).mem (r1V + i) = (srcBytes.get! i).toNat := by
    rw [hstep_eq, ← hs_r1_field]
    show (step (.call sc) s).mem (s.regs.r1 + i) = (srcBytes.get! i).toNat
    have h1 := h_step_mem_in s hs_r2_field hs_r3_field i hi
    rw [hs_r2_field] at h1
    rw [h1, hs_mem_src i hi]
    -- (UInt8.toNat _) < 256, so % 256 is a no-op.
    have hlt : (srcBytes.get! i).toNat < 256 := (srcBytes.get! i).toNat_lt
    exact Nat.mod_eq_of_lt hlt
  have hexec_mem_out (a : Nat) (h : a < r1V ∨ a ≥ r1V + r3V) :
      (executeFn fetch s 1).mem a = s.mem a := by
    rw [hstep_eq]
    apply h_step_mem_out s hs_r3_field a
    rw [hs_r1_field]; exact h
  -- ==== Phase 4: facts about h_R from outer disjointness with h_P. ====
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
  -- ==== Phase 5: build the new post partial state. ====
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
  -- Disjointness src ⊥ b at the post: same address ranges as pre since both
  -- atoms preserve size (bsOld.size = srcBytes.size = r3V). Derived pointwise
  -- from hd_src_b: at each address, hd_src_b gives "src none OR dst none";
  -- src.mem none transfers directly (same ByteArray); dst.mem none transfers
  -- because bsOld and srcBytes share the same address-range condition.
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
  -- ==== Phase 6: outer disjointness h_P_new ⊥ h_R. ====
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
  -- ==== Phase 7: assemble the witness for (Q ** R).holdsFor. ====
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
        -- Position r2V + (a-r2V) is in the src range, NOT dst (assuming
        -- disjointness). Use hexec_mem_out + hs_mem_src.
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

`sol_memcpy(dst, src, n)` and `sol_memmove(dst, src, n)` share
semantics in our model via `MemOps.execCopy` (no overlap-handling
distinction). Both copy `n = r3` bytes from `src = r2` to `dst = r1`
and set `r0 := 0`. Separation logic implies the source and
destination ranges are disjoint — overlap is undefined behavior at
the C level for memcpy, and memmove's overlap support isn't reachable
from the SL spec (the precondition's two `↦Bytes` atoms force
disjointness). -/

theorem call_sol_memcpy_spec
    (r0Old r1V r2V r3V pc nCu : Nat) (srcBytes bsOld : ByteArray)
    (hsrc : srcBytes.size = r3V) (hbs : bsOld.size = r3V)
    (hCu : ∀ s : State,
        (step (.call .sol_memcpy) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_memcpy))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V)
       ** (r2V ↦Bytes srcBytes) ** (r1V ↦Bytes bsOld))
      ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V)
       ** (r2V ↦Bytes srcBytes) ** (r1V ↦Bytes srcBytes)) := by
  refine cuTripleWithin_syscall_copiesR2ToR1
    .sol_memcpy pc nCu r2V r3V srcBytes hsrc
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hCu r0Old r1V bsOld hbs
  · intro s
    simp only [step, execSyscall, MemOps.execCopy]
  · intro s hr2 hr3 i hi
    simp only [step, execSyscall, MemOps.execCopy]
    rw [Mem_read_default]
    rw [if_pos ⟨Nat.le_add_right _ _, by rw [hr3]; omega⟩]
    have : s.regs.r1 + i - s.regs.r1 = i := by omega
    rw [this]
  · intro s hr3 a ha
    simp only [step, execSyscall, MemOps.execCopy]
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
  · intro s hex
    simp only [step, execSyscall, MemOps.execCopy]
    exact hex
  · intro s
    simp only [step, execSyscall, MemOps.execCopy]

  · intro s
    simp only [step, execSyscall, MemOps.execCopy]

theorem call_sol_memmove_spec
    (r0Old r1V r2V r3V pc nCu : Nat) (srcBytes bsOld : ByteArray)
    (hsrc : srcBytes.size = r3V) (hbs : bsOld.size = r3V)
    (hCu : ∀ s : State,
        (step (.call .sol_memmove) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_memmove))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V)
       ** (r2V ↦Bytes srcBytes) ** (r1V ↦Bytes bsOld))
      ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V)
       ** (r2V ↦Bytes srcBytes) ** (r1V ↦Bytes srcBytes)) := by
  refine cuTripleWithin_syscall_copiesR2ToR1
    .sol_memmove pc nCu r2V r3V srcBytes hsrc
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hCu r0Old r1V bsOld hbs
  · intro s
    simp only [step, execSyscall, MemOps.execCopy]
  · intro s hr2 hr3 i hi
    simp only [step, execSyscall, MemOps.execCopy]
    rw [Mem_read_default]
    rw [if_pos ⟨Nat.le_add_right _ _, by rw [hr3]; omega⟩]
    have : s.regs.r1 + i - s.regs.r1 = i := by omega
    rw [this]
  · intro s hr3 a ha
    simp only [step, execSyscall, MemOps.execCopy]
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
  · intro s hex
    simp only [step, execSyscall, MemOps.execCopy]
    exact hex
  · intro s
    simp only [step, execSyscall, MemOps.execCopy]

  · intro s
    simp only [step, execSyscall, MemOps.execCopy]

/-! ## Syscall: `sol_memcmp`

`sol_memcmp(p1, p2, n, out)`: lexicographically compare `n = r3` bytes
at `[r1, r1+n)` and `[r2, r2+n)`, write the i32 result (encoded as u32:
0, 0xFFFFFFFF for -1, or 1) to `*r4`. Sets `r0 := 0`.

Most complex mem-op spec — 8 atoms total: 5 reg atoms (r0..r4),
2 read-only ↦Bytes atoms (p1Bytes, p2Bytes), 1 write-only ↦U32 atom
at r4V. The post-state characterizes the written value via
`memcmpResultU32`, a pure function of the input ByteArrays.

The proof requires a fold-equality lemma (`execCmp_fold_eq`) that
relates the `s.mem`-based fold in `MemOps.execCmp` to the
ByteArray-based fold in `memcmpFold`, under the coherence hypotheses
provided by the `↦Bytes` atoms in the precondition. -/

/-- ByteArray-based comparison fold. Mirrors the `s.mem`-based fold
    inside `MemOps.execCmp`, but reads bytes from a `ByteArray` instead
    of `State.mem`. Returns the i32 difference `a - b` of the first
    differing byte pair (in `[-255,255]`), or 0 if equal. -/
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

/-- Under coherence (`s.mem (pV + i) = (pBytes.get! i).toNat` for both
    p1 and p2), the `s.mem`-based fold in `execCmp` equals the
    ByteArray-based `memcmpFold`. Proved by induction on `n` using
    the fact that `(UInt8.toNat _) < 256`, so the `% 256` in the
    `s.mem`-side cancels. -/
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

/-- `sol_memcmp(p1, p2, n, out)` Hoare triple. Reads `n = r3` bytes
    at `[r1, r1+n)` and `[r2, r2+n)` (both preserved), writes the u32
    comparison result `memcmpResultU32 p1Bytes p2Bytes r3V` to `*r4`.
    Sets `r0 := 0`. Separation logic implies the three memory regions
    (p1 at r1V, p2 at r2V, output u32 at r4V) are pairwise disjoint. -/
theorem call_sol_memcmp_spec
    (r0Old r1V r2V r3V r4V outOld pc nCu : Nat)
    (p1Bytes p2Bytes : ByteArray)
    (hsz1 : p1Bytes.size = r3V) (hsz2 : p2Bytes.size = r3V)
    (hCu : ∀ s : State,
        (step (.call .sol_memcmp) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_memcmp))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V) ** (.r4 ↦ᵣ r4V)
       ** (r1V ↦Bytes p1Bytes) ** (r2V ↦Bytes p2Bytes) ** (r4V ↦U32 outOld))
      ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V) ** (.r4 ↦ᵣ r4V)
       ** (r1V ↦Bytes p1Bytes) ** (r2V ↦Bytes p2Bytes)
       ** (r4V ↦U32 (memcmpResultU32 p1Bytes p2Bytes r3V))) := by
  intro R hRfree fetch hcr s hPR hpc hex hbud
  let cmpResult := memcmpResultU32 p1Bytes p2Bytes r3V
  -- ==== Phase 1: 8-atom destructure. ====
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
  -- ==== Phase 2: reg climbs (r4 through r0) ====
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
  -- ==== Phase 2 (cont'd): mem facts for p1, p2, out ====
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
  -- ==== Phase 3: fetch + step projections ====
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
  -- Compute (step .sol_memcmp s) symbolically using execCmp_fold_eq.
  -- The mem' is writeU32 s.mem r4V cmpResult; the regs.r0 := 0.
  have hexec_pc : (executeFn fetch s 1).pc = s.pc + 1 := by
    rw [hstep_eq]; simp only [step, execSyscall, MemOps.execCmp, chargeCu]
  have hexec_exit : (executeFn fetch s 1).exitCode = none := by
    rw [hstep_eq]; simp only [step, execSyscall, MemOps.execCmp, chargeCu]; exact hex
  have hexec_regs : (executeFn fetch s 1).regs = s.regs.set .r0 0 := by
    rw [hstep_eq]; simp only [step, execSyscall, MemOps.execCmp, chargeCu]
  -- The mem after step equals writeU32 s.mem s.regs.r4 cmpResult, where cmpResult
  -- is the i32-encoded comparison value derived from execCmp's fold. The fold
  -- equality lemma (execCmp_fold_eq) converts the s.mem-based fold to memcmpFold
  -- under coherence; this gives us memcmpResultU32 at the end.
  have hexec_mem_eq :
      (executeFn fetch s 1).mem =
        Memory.writeU32 s.mem r4V cmpResult := by
    rw [hstep_eq]
    simp only [step, execSyscall, MemOps.execCmp, chargeCu]
    -- Convert all s.regs.{r1, r2, r3, r4} → fixed parameter values
    rw [hs_r4_field, hs_r1_field, hs_r2_field, hs_r3_field]
    show Memory.writeU32 s.mem r4V _ = Memory.writeU32 s.mem r4V cmpResult
    congr 1
    -- Goal: <s.mem-based cmpU32> = cmpResult
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
  -- ==== Phase 4: facts about h_R from outer disjointness with h_P. ====
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
  -- ==== Phase 5: build the new post partial state. ====
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
    -- Pointwise mem disjointness derived from hd_p2_out (pre): same ranges since
    -- p2_new is p2Bytes (same as pre) and out_new is U32 at r4V (same range).
    have hd_pre_mem := hd_p2_out.mem
    rcases hd_pre_mem a with hl | hr
    · left; exact hl
    · right
      -- (singletonMemU32 r4V outOld).mem a = none → (singletonMemU32 r4V cmpResult).mem a = none
      -- Both atoms have same range [r4V, r4V+4); none-ness is range-based.
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
        -- T6_pre.mem a = none → T6_new.mem a = none
        -- T6_pre = p2 ∪ out_pre; T6_new = p2 ∪ out_new (same p2, same out range).
        -- T6_pre.mem a = none means both p2 and out_pre are none at a.
        -- T6_new.mem a = union of p2 and out_new. Both atoms same range conditions.
        show (h_p2_new.union h_out_new).mem a = none
        -- Reduce T6_pre.mem a = none to "p2.mem a = none ∧ out_pre.mem a = none".
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
  -- ==== Phase 6: outer disjointness h_P_new ⊥ h_R. ====
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
  -- ==== Phase 7: assemble the witness for (Q ** R).holdsFor. ====
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
          -- The U32 region at r4V is disjoint from the p1 region at r1V (from pre disjointness).
          -- Specifically, the p1 atom has (r1V + (a - r1V)) since (a - r1V) < r3V = p1Bytes.size.
          -- p1 ⊥ T6 ⊇ out. So (r1V + (a - r1V)) is outside the out range.
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
        simp [executeFn, step, execSyscall, MemOps.execCmp, hex, hfetch, hnb]
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
        simp [executeFn, step, execSyscall, MemOps.execCmp, hex, hfetch, hnb]
      rw [hexec_cs]
      exact hcompat.callStack cs hp_cs

/-! ## Memset with a `↦U64` split tail (qedlift blob read-through)

When the program later READS a dword inside the memset-filled region
(p_token CloseAccount: `ldxdw [acct+88]` inside the 48-byte zeroing at
`[acct+48, +96)`), the blob post must expose that cell as a `↦U64`
atom or the read's atom would overlap the blob (an unsatisfiable
sepConj — soundness audit H8 Phase C,
`docs/QEDLIFT_ALIASING_DESIGN.md`). This variant splits the written
blob's LAST 8 bytes off as a `↦U64` cell holding the fill byte
replicated (`fill * 0x0101010101010101`). -/

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

/-- Eight replicated fill bytes are the `u64LE` encoding of any `w`
    whose eight LE bytes each equal the fill byte. The byte equations
    are parameters so the emitter can discharge them by `decide` on a
    concrete `w` (avoiding big-constant `omega`). -/
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
    cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_memset))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V)
       ** (r1V ↦Bytes bsOld))
      ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V)
       ** ((r1V ↦Bytes (replicateByte (r2V % 256).toUInt8 n)) **
           (a ↦U64 w))) := by
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
  -- (the `ha` rewrite above moved the split-cell address to `a`)
  refine cuTripleWithin_weaken (fun _ x => x) ?_
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
    cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_memset))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V)
       ** ((r1V ↦Bytes bsOld) ** (a ↦U64 oldV)))
      ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V)
       ** ((r1V ↦Bytes (replicateByte (r2V % 256).toUInt8 n)) **
           (a ↦U64 w))) := by
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
  refine cuTripleWithin_weaken ?_ ?_
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
    cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_memset))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V)
       ** ((r1V ↦Bytes bsOld) ** ((a1 ↦U64 oldV1) ** (a2 ↦U64 oldV2))))
      ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ r1V) ** (.r2 ↦ᵣ r2V) ** (.r3 ↦ᵣ r3V)
       ** ((r1V ↦Bytes (replicateByte (r2V % 256).toUInt8 n)) **
           ((a1 ↦U64 w) ** (a2 ↦U64 w)))) := by
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
  refine cuTripleWithin_weaken ?_ ?_
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
