import SVM.SBPF.InstructionSpecs.CallReturn

namespace SVM.SBPF

open Memory

/-! ## Tier-1 crypto syscall bookkeeping triples

Trust statements for the 10 FFI-bridged crypto syscalls live in
`SVM/SBPF/CryptoTrust.lean` (one axiom per syscall, pinning output size
or boolean totality of the opaque `@[extern]` function). Consumer-facing
Hoare triples mostly need richer SL infrastructure than this worktree
provides; see `CryptoTrust.lean`'s closing docstring and
`docs/deferred-arch-lifts.md` §5 for the deferral rationale.

`sol_curve_validate_point` is the one that fits `writes_r0_only`: its body
(`Curve25519.execValidate`) is a pure regs update (`r0 := errCode`,
`s.mem` untouched). Below: an `r0`-only helper that pins `r1` (so the
output errCode is computable at proof time), plus the unsupported-curveId
triple. -/

/-- `writes_r0_only` plus a pinned register `r ↦ᵣ rV` (kept in the post);
updates `r0 := vNew`. For syscalls whose r0 output depends on one fixed
input register (e.g. `sol_curve_validate_point`'s errCode dispatch on the
curve_id in r1). -/
theorem cuTripleWithin_syscall_writes_r0_only_pinned
    (sc : Syscall) (r : Reg) (rV vNew : Nat) (pc : Nat) (nCu : Nat)
    (hr_ne : r ≠ .r0)
    (h_step_regs : ∀ s : State, s.regs.get r = rV →
        (step (.call sc) s).regs = s.regs.set .r0 vNew)
    (h_step_mem  : ∀ s : State, s.regs.get r = rV →
        (step (.call sc) s).mem = s.mem)
    (h_step_pc   : ∀ s : State, (step (.call sc) s).pc = s.pc + 1)
    -- Pinned on `r = rV` (H4/M9): syscalls that fail closed for *some*
    -- inputs still preserve `exitCode = none` on the pinned input.
    (h_step_exit : ∀ s : State, s.regs.get r = rV → s.exitCode = none →
        (step (.call sc) s).exitCode = none)
    (h_step_returnData :
      ∀ s : State, (step (.call sc) s).returnData = s.returnData)
    (h_step_callStack :
      ∀ s : State, (step (.call sc) s).callStack = s.callStack)
    (h_step_cu : ∀ s : State,
        (step (.call sc) s).cuConsumed ≤ s.cuConsumed + nCu) :
    ∀ r0Old, cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call sc))
      ((.r0 ↦ᵣ r0Old) ** (r ↦ᵣ rV))
      ((.r0 ↦ᵣ vNew) ** (r ↦ᵣ rV)) := by
  intro r0Old R hRfree fetch hcr s hPR hpc hex hbud
  obtain ⟨hp, hcompat, hP, hR, hd_PR, hu_PR, hPsat, hRsat⟩ := hPR
  obtain ⟨h_r0, h_r, hd_r0_r, hu_r0_r, h_r0_pred, h_r_pred⟩ := hPsat
  rw [h_r0_pred] at hu_r0_r hd_r0_r
  rw [h_r_pred] at hu_r0_r hd_r0_r
  clear h_r0_pred h_r_pred h_r0 h_r
  have hcr_regs := hcompat.regs
  have hcm_mem := hcompat.mem
  have hd_PR_regs := hd_PR.regs
  have hd_PR_mem := hd_PR.mem
  have hP_regs_r0 : hP.regs .r0 = some r0Old := by
    rw [← hu_r0_r]; exact PartialState.union_regs_of_left_some
      PartialState.singletonReg_regs_self
  have hP_regs_r : hP.regs r = some rV := by
    rw [← hu_r0_r,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other hr_ne)]
    exact PartialState.singletonReg_regs_self
  have hP_regs_other (r' : Reg) (h0 : r' ≠ .r0) (h1 : r' ≠ r) :
      hP.regs r' = none := by
    rw [← hu_r0_r,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other h0)]
    exact PartialState.singletonReg_regs_other h1
  have hP_mem_none (a : Nat) : hP.mem a = none := by
    rw [← hu_r0_r,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact PartialState.singletonReg_mem a
  have hP_pc_none : hP.pc = none := by
    rw [← hu_r0_r,
        PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    exact PartialState.singletonReg_pc
  have hp_regs_r0 : hp.regs .r0 = some r0Old := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some hP_regs_r0
  have hp_regs_r : hp.regs r = some rV := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some hP_regs_r
  have hs_regs_r : s.regs.get r = rV := hcr_regs r rV hp_regs_r
  have hR_no_r0 : hR.regs .r0 = none := by
    rcases hd_PR_regs .r0 with hl | hr_'
    · rw [hP_regs_r0] at hl; nomatch hl
    · exact hr_'
  have hR_no_r : hR.regs r = none := by
    rcases hd_PR_regs r with hl | hr_'
    · rw [hP_regs_r] at hl; nomatch hl
    · exact hr_'
  have hR_no_pc : hR.pc = none := hRfree _ hRsat
  have hfetch : fetch s.pc = some (.call sc) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hstep_eq : executeFn fetch s 1 = chargeCu (step (.call sc) s) := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch,
        executeFn_zero]
  have hexec_regs : (executeFn fetch s 1).regs = s.regs.set .r0 vNew := by
    rw [hstep_eq]; exact h_step_regs s hs_regs_r
  have hexec_mem : (executeFn fetch s 1).mem = s.mem := by
    rw [hstep_eq]; exact h_step_mem s hs_regs_r
  have hexec_pc : (executeFn fetch s 1).pc = s.pc + 1 := by
    rw [hstep_eq]; exact h_step_pc s
  have hexec_exit : (executeFn fetch s 1).exitCode = none := by
    rw [hstep_eq]; exact h_step_exit s hs_regs_r hex
  have hexec_cu : (executeFn fetch s 1).cuConsumed ≤ s.cuConsumed + 1 + nCu := by
    rw [hstep_eq]
    show (step (.call sc) s).cuConsumed + 1 ≤ s.cuConsumed + 1 + nCu
    have := h_step_cu s; omega
  let h_r0_new : PartialState := PartialState.singletonReg .r0 vNew
  let h_r_new : PartialState := PartialState.singletonReg r rV
  let h_P_new : PartialState := h_r0_new.union h_r_new
  have hd_r0_r_new : h_r0_new.Disjoint h_r_new := by
    refine ⟨fun r' => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
    · by_cases hr' : r' = .r0
      · right
        show h_r_new.regs r' = none
        rw [hr']; exact PartialState.singletonReg_regs_other (Ne.symm hr_ne)
      · left; exact PartialState.singletonReg_regs_other hr'
    · left; exact PartialState.singletonReg_mem a
    · left; exact PartialState.singletonReg_pc
  have h_P_new_regs_r0 : h_P_new.regs .r0 = some vNew :=
    PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_new_regs_r : h_P_new.regs r = some rV := by
    show ((PartialState.singletonReg .r0 vNew).union h_r_new).regs r = some rV
    rw [PartialState.union_regs_of_left_none
        (PartialState.singletonReg_regs_other hr_ne)]
    exact PartialState.singletonReg_regs_self
  have h_P_new_regs_other (r' : Reg) (h0 : r' ≠ .r0) (h1 : r' ≠ r) :
      h_P_new.regs r' = none := by
    show ((PartialState.singletonReg .r0 vNew).union h_r_new).regs r' = none
    rw [PartialState.union_regs_of_left_none
        (PartialState.singletonReg_regs_other h0)]
    exact PartialState.singletonReg_regs_other h1
  have h_P_new_mem_none (a : Nat) : h_P_new.mem a = none := by
    show ((PartialState.singletonReg .r0 vNew).union h_r_new).mem a = none
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact PartialState.singletonReg_mem a
  have h_P_new_pc_none : h_P_new.pc = none := by
    show ((PartialState.singletonReg .r0 vNew).union h_r_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    exact PartialState.singletonReg_pc
  have hd_PnewR : h_P_new.Disjoint hR := by
    refine ⟨fun r' => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
    · by_cases h0 : r' = .r0
      · right; rw [h0]; exact hR_no_r0
      · by_cases h1 : r' = r
        · right; rw [h1]; exact hR_no_r
        · left; exact h_P_new_regs_other r' h0 h1
    · left; exact h_P_new_mem_none a
    · left; exact h_P_new_pc_none
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_, ?_⟩
  · rw [hexec_pc, hpc]
  · exact hexec_exit
  · exact hexec_cu
  · refine ⟨h_P_new.union hR, ?_, h_P_new, hR, hd_PnewR, rfl, ?_, hRsat⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro r' v hvr
        rw [hexec_regs]
        by_cases h0 : r' = .r0
        · rw [h0] at hvr
          rw [PartialState.union_regs_of_left_some h_P_new_regs_r0] at hvr
          have : v = vNew := (Option.some.inj hvr).symm
          rw [h0, this]
          exact RegFile.get_set_self _ _ _ (by decide : (.r0 : Reg) ≠ .r10)
        · by_cases h1 : r' = r
          · rw [h1] at hvr
            rw [PartialState.union_regs_of_left_some h_P_new_regs_r] at hvr
            have hv : v = rV := (Option.some.inj hvr).symm
            rw [h1, hv, RegFile.get_set_diff _ _ _ _ hr_ne]
            exact hs_regs_r
          · rw [PartialState.union_regs_of_left_none
                (h_P_new_regs_other r' h0 h1)] at hvr
            rw [RegFile.get_set_diff _ _ _ _ h0]
            have h_P_old_none : hP.regs r' = none := hP_regs_other r' h0 h1
            have hp_eq : hp.regs r' = some v := by
              rw [← hu_PR,
                  PartialState.union_regs_of_left_none h_P_old_none]
              exact hvr
            exact hcr_regs r' v hp_eq
      · intro a v hva
        rw [PartialState.union_mem_of_left_none (h_P_new_mem_none a)] at hva
        rw [hexec_mem]
        have h_P_old_none : hP.mem a = none := hP_mem_none a
        have hp_eq : hp.mem a = some v := by
          rw [← hu_PR, PartialState.union_mem_of_left_none h_P_old_none]
          exact hva
        exact hcm_mem a v hp_eq
      · intro v hvp
        rw [PartialState.union_pc_of_left_none h_P_new_pc_none] at hvp
        rw [hR_no_pc] at hvp
        nomatch hvp
      · intro rd hva
        have h_P_new_rd : h_P_new.returnData = none := by rfl
        rw [PartialState.union_returnData_of_left_none h_P_new_rd] at hva
        have h_P_rd : hP.returnData = none := by
          rw [← hu_r0_r]; rfl
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
        have h_P_cs : hP.callStack = none := by
          rw [← hu_r0_r]; rfl
        have hp_cs : hp.callStack = some cs := by
          rw [← hu_PR, PartialState.union_callStack_of_left_none h_P_cs]
          exact hva
        have hexec_cs : (executeFn fetch s 1).callStack = s.callStack := by
          rw [hstep_eq]; exact h_step_callStack s
        rw [hexec_cs]
        exact hcompat.callStack cs hp_cs
    · refine ⟨h_r0_new, h_r_new, hd_r0_r_new, rfl, rfl, rfl⟩

/-! ## `sol_curve_validate_point` (unsupported curve_id) — fails closed

For an unsupported curve_id (≠ EDWARDS=0, ≠ RISTRETTO=1) `execValidate`
aborts with `ERR_INVALID_ATTRIBUTE`, matching agave when
`abort_on_invalid_curve` is active (it is, under `FeatureSet::all_enabled`,
agave-syscalls lib.rs:999). The former "writes r0 := 2" triple was removed:
it was provable over a behaviour the chain rejects (M7). A
`cuTripleAbortsWithin` spec can be added on demand by mirroring
`call_abort_aborts_spec`. -/

/-! ## H6 — crypto short-circuit bookkeeping triples retired

Four short-circuit triples that used to live here
(`call_sol_secp256k1_recover_invalid_recid_spec`,
`call_sol_curve_multiscalar_mul_zero_n_spec`,
`call_sol_curve_decompress_unsupported_spec`,
`call_sol_curve_pairing_map_unsupported_spec`) pinned the no-FFI error
paths (recovery_id > 3, n = 0, unsupported BLS curve_id) to
`r0 := errCode, mem unchanged`. Under H6 those paths sit behind the
syscall's region guards (`State.guardRead`/`guardWrite`), so "mem unchanged"
no longer holds for an out-of-region buffer — agave traps there too. The
triples were UNCONSUMED (cited only by name in `CryptoTrust.lean`'s prose,
never composed), so rather than thread region requirements through the old
PartialState proofs they are retired in favour of the model-side
`*_faults_oob` lemmas in
`SVM/Syscalls/{Curve25519,Bls12_381,AltBn128,BigModExp,Secp256k1}.lean`
(out-of-region access => typed `accessViolation`). The generic
`writes_r0_only_pinned` helper above is kept for any future unguarded
syscall. See docs/SOUNDNESS_AUDIT_* (H6).
-/

/-! ## H6 OOB-fault triple (Phase 7 sub-item 3, accessViolation family)

The `cuTripleFaultsWithinMem` analog of `call_abort_faults_spec`, but for an
out-of-bounds SYSCALL: `sol_secp256k1_recover` reads its 32-byte hash input
`[r1, r1+32)` through `State.guardRead`, so an out-of-region `r1` traps with a
typed `.accessViolation` (`Secp256k1.exec_faults_oob{,_exitCode}`). Unlike
abort/panic (which fault from ANY precondition), this fault DEPENDS on `r1`: the
pre pins `r1 = r1V` and the region requirement `rr` says `[r1V, r1V+32)` is out
of bounds. The `*_fault_correct` emitter composes a running prefix into this
tail via `cuTripleWithinMem_seq_fault` (the Mem-Mem variant: the combined `rr`
is `fun rt => prefixRR rt ∧ rt.containsRange r1V 32 = false`). -/

theorem call_sol_secp256k1_recover_faults_oob_spec (r1V : Nat) (pc : Nat) (nCu : Nat)
    (hCu : ∀ s : State,
        (step (.call .sol_secp256k1_recover) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleFaultsWithinMem 1 nCu pc
      (CodeReq.singleton pc (.call .sol_secp256k1_recover))
      (.r1 ↦ᵣ r1V)
      (fun rt => rt.containsRange r1V 32 = false)
      .accessViolation := by
  intro R hRfree fetch hcr s hPR hpc hex hbud h_region
  -- Extract `s.regs.r1 = r1V` from the single-atom precondition.
  obtain ⟨hp, hcompat, h_P, h_R, hd_PR, hu_PR, h_P_pred, h_R_sat⟩ := hPR
  have hcr_regs := hcompat.regs
  have h_P_regs_r1 : h_P.regs .r1 = some r1V := by
    rw [h_P_pred]; exact PartialState.singletonReg_regs_self
  have hp_regs_r1 : hp.regs .r1 = some r1V := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r1
  have hr1 : s.regs.r1 = r1V := hcr_regs .r1 r1V hp_regs_r1
  -- Specialise the OOB region condition to this state's `r1`.
  have hoob : s.regions.containsRange s.regs.r1 32 = false := by rw [hr1]; exact h_region
  have hfetch : fetch s.pc = some (.call .sol_secp256k1_recover) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hstep_eq : executeFn fetch s 1
      = chargeCu (step (.call .sol_secp256k1_recover) s) := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch, executeFn_zero]
  have hexec : executeFn fetch s 1 =
      chargeCu { (Secp256k1.exec s) with
                 pc := s.pc + 1
                 cuConsumed := (Secp256k1.exec s).cuConsumed
                   + syscallCu .sol_secp256k1_recover s } := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch, executeFn_zero]
    simp only [step, execSyscall]
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_⟩
  · rw [hexec]
    -- VmError.accessViolation.toSentinel = ERR_ACCESS_VIOLATION
    show (Secp256k1.exec s).exitCode = some VmError.accessViolation.toSentinel
    exact Secp256k1.exec_faults_oob_exitCode s hoob
  · rw [hexec]
    show (Secp256k1.exec s).vmError = some .accessViolation
    exact Secp256k1.exec_faults_oob s hoob
  · rw [hstep_eq]
    show (step (.call .sol_secp256k1_recover) s).cuConsumed + 1
      ≤ s.cuConsumed + 1 + nCu
    have := hCu s; omega

/-- The per-lift fault-corollary shape for the OOB family (mirrors
    `mov_then_abort_fault_correct_mem`): a register-setup prefix sequenced into
    the OOB syscall fault via `cuTripleWithinMem_seq_fault`. The combined `rr`
    carries the prefix requirement (`True` here) AND the OOB condition. This is
    the shape the `*_fault_correct` emitter mechanizes for an OOB terminal. -/
theorem mov_r1_then_secp_oob_fault_correct (vR1Old : Nat) (nCu : Nat)
    (hCu : ∀ s : State,
        (step (.call .sol_secp256k1_recover) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleFaultsWithinMem (1 + 1) (0 + nCu) 0
      ((CodeReq.singleton 0 (.mov64 .r1 (.imm 5))).union
        (CodeReq.singleton 1 (.call .sol_secp256k1_recover)))
      (.r1 ↦ᵣ vR1Old)
      (fun rt => True ∧ rt.containsRange (toU64 5) 32 = false)
      .accessViolation :=
  cuTripleWithinMem_seq_fault
    (CodeReq.singleton_disjoint_singleton _ _ (by decide))
    (mov64_imm_spec .r1 5 vR1Old 0 (by decide)).toMem
    (call_sol_secp256k1_recover_faults_oob_spec (toU64 5) 1 nCu hCu)

end SVM.SBPF
