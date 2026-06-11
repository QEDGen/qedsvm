import SVM.SBPF.InstructionSpecs.CallReturn

namespace SVM.SBPF

open Memory

/-! ## Tier-1 crypto syscall bookkeeping triples

The trust statements for the 10 FFI-bridged crypto syscalls live in
`SVM/SBPF/CryptoTrust.lean` — one axiom per syscall, each pinning
down the output size (or boolean totality) of the opaque `@[extern]`
function. Consumer-facing Hoare triples mostly need richer SL
infrastructure than this stale worktree provides (the PDA n=0 proof
template is ~400 lines of byte-region disjointness reasoning, which
each crypto syscall would mirror). See `CryptoTrust.lean`'s closing
docstring and `docs/deferred-arch-lifts.md` §5 for the deferral
rationale.

The one crypto syscall that fits the existing `writes_r0_only`
helper template is `sol_curve_validate_point`: its body
(`Curve25519.execValidate`) is a pure regs update — `r0 := errCode`
— with `s.mem` untouched. Below: a generalized `r0`-only helper
that pins `r1` to a known value (so the output errCode is computable
at proof time), plus the unsupported-curveId triple. -/

/-- `writes_r0_only` extended with a single extra pinned register
`r ↦ᵣ rV` in the precondition. Postcondition keeps `r ↦ᵣ rV` and
updates `r0 := vNew`. Used by syscalls whose r0 output depends on
one fixed input register's value (e.g. `sol_curve_validate_point`'s
errCode dispatch on the curve_id in r1). -/
theorem cuTripleWithin_syscall_writes_r0_only_pinned
    (sc : Syscall) (r : Reg) (rV vNew : Nat) (pc : Nat) (nCu : Nat)
    (hr_ne : r ≠ .r0)
    (h_step_regs : ∀ s : State, s.regs.get r = rV →
        (step (.call sc) s).regs = s.regs.set .r0 vNew)
    (h_step_mem  : ∀ s : State, s.regs.get r = rV →
        (step (.call sc) s).mem = s.mem)
    (h_step_pc   : ∀ s : State, (step (.call sc) s).pc = s.pc + 1)
    -- Pinned on `r = rV` (H4/M9): syscalls that fail closed for *some*
    -- inputs (e.g. `sol_curve_multiscalar_mul` with n > 512) still
    -- preserve `exitCode = none` on the pinned input the spec is about.
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
  -- Destructure ((.r0 ↦ᵣ r0Old) ** (r ↦ᵣ rV)) ** R.
  obtain ⟨hp, hcompat, hP, hR, hd_PR, hu_PR, hPsat, hRsat⟩ := hPR
  obtain ⟨h_r0, h_r, hd_r0_r, hu_r0_r, h_r0_pred, h_r_pred⟩ := hPsat
  rw [h_r0_pred] at hu_r0_r hd_r0_r
  rw [h_r_pred] at hu_r0_r hd_r0_r
  clear h_r0_pred h_r_pred h_r0 h_r
  have hcr_regs := hcompat.regs
  have hcm_mem := hcompat.mem
  have hd_PR_regs := hd_PR.regs
  have hd_PR_mem := hd_PR.mem
  -- hP.regs at r0 and r.
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
  -- Climb to hp / s.
  have hp_regs_r0 : hp.regs .r0 = some r0Old := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some hP_regs_r0
  have hp_regs_r : hp.regs r = some rV := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some hP_regs_r
  have hs_regs_r : s.regs.get r = rV := hcr_regs r rV hp_regs_r
  -- R doesn't own r0 or r.
  have hR_no_r0 : hR.regs .r0 = none := by
    rcases hd_PR_regs .r0 with hl | hr_'
    · rw [hP_regs_r0] at hl; nomatch hl
    · exact hr_'
  have hR_no_r : hR.regs r = none := by
    rcases hd_PR_regs r with hl | hr_'
    · rw [hP_regs_r] at hl; nomatch hl
    · exact hr_'
  have hR_no_pc : hR.pc = none := hRfree _ hRsat
  -- Execute one step.
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
  -- Assemble Q ** R.
  let h_r0_new : PartialState := PartialState.singletonReg .r0 vNew
  let h_r_new : PartialState := PartialState.singletonReg r rV
  let h_P_new : PartialState := h_r0_new.union h_r_new
  -- Disjointness h_r0_new ⊥ h_r_new (r0 ≠ r).
  have hd_r0_r_new : h_r0_new.Disjoint h_r_new := by
    refine ⟨fun r' => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
    · by_cases hr' : r' = .r0
      · right
        show h_r_new.regs r' = none
        rw [hr']; exact PartialState.singletonReg_regs_other (Ne.symm hr_ne)
      · left; exact PartialState.singletonReg_regs_other hr'
    · left; exact PartialState.singletonReg_mem a
    · left; exact PartialState.singletonReg_pc
  -- h_P_new owns regs.
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
  -- Outer disjointness h_P_new ⊥ hR.
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
    -- Compatibility.
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      -- regs
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
      -- mem
      · intro a v hva
        rw [PartialState.union_mem_of_left_none (h_P_new_mem_none a)] at hva
        rw [hexec_mem]
        have h_P_old_none : hP.mem a = none := hP_mem_none a
        have hp_eq : hp.mem a = some v := by
          rw [← hu_PR, PartialState.union_mem_of_left_none h_P_old_none]
          exact hva
        exact hcm_mem a v hp_eq
      -- pc
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
    -- Witness for Q.
    · refine ⟨h_r0_new, h_r_new, hd_r0_r_new, rfl, rfl, rfl⟩

/-! ## `sol_curve_validate_point` (unsupported curve_id) — fails closed

For an unsupported curve_id (≠ EDWARDS=0, ≠ RISTRETTO=1) `execValidate`
now aborts with `ERR_INVALID_ATTRIBUTE`, matching agave when
`abort_on_invalid_curve` is active (it is, under `FeatureSet::all_enabled`
— agave-syscalls lib.rs:999). The former "writes r0 := 2" triple was
removed: it was provable over a behaviour the chain rejects (M7). A
`cuTripleAbortsWithin` spec for this arm can be added on demand by
mirroring `call_abort_aborts_spec`. -/

/-! ## Tier-1 triple: `sol_secp256k1_recover` (invalid recovery_id)

Pinning `r2 = recId` with `recId > 3` forces
`result = .invalidRecoveryId`, hence `errCode = 2`, and the writeBytes
arm is bypassed (`mem' = s.mem`). The opaque
`Secp256k1.recover` is *not called* on this path, so no axiom is
consumed.

Trust statement: none required for this branch. -/

theorem call_sol_secp256k1_recover_invalid_recid_spec
    (r0Old r2V : Nat) (pc : Nat) (nCu : Nat) (h_bad : r2V > 3)
    (h_step_cu : ∀ s : State,
        (step (.call .sol_secp256k1_recover) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_secp256k1_recover))
      ((.r0 ↦ᵣ r0Old) ** (.r2 ↦ᵣ r2V))
      ((.r0 ↦ᵣ 2) ** (.r2 ↦ᵣ r2V)) := by
  apply cuTripleWithin_syscall_writes_r0_only_pinned
    .sol_secp256k1_recover .r2 r2V 2 pc nCu (by decide : (.r2 : Reg) ≠ .r0)
  · -- regs
    intro s hr2
    have hr2' : s.regs.r2 = r2V := by show s.regs.get .r2 = r2V; exact hr2
    simp only [step, execSyscall, Secp256k1.exec]
    rw [hr2', if_pos h_bad]
  · -- mem
    intro s hr2
    have hr2' : s.regs.r2 = r2V := by show s.regs.get .r2 = r2V; exact hr2
    simp only [step, execSyscall, Secp256k1.exec]
    rw [hr2', if_pos h_bad]
  · -- pc
    intro s
    simp [step, execSyscall, Secp256k1.exec]
  · -- exitCode preservation
    intro s _ hex
    simp only [step, execSyscall, Secp256k1.exec]
    show s.exitCode = none
    exact hex
  · -- returnData unchanged
    intro s
    simp [step, execSyscall, Secp256k1.exec]
  · -- callStack unchanged
    intro s
    simp [step, execSyscall, Secp256k1.exec]
  · -- cuConsumed bound
    exact h_step_cu

/-! ## `sol_curve_group_op` (unsupported curve_id) - fails closed

An unsupported curve_id now aborts (`ERR_INVALID_ATTRIBUTE`) in
`execGroupOp`, matching agave under `abort_on_invalid_curve`; the former
"r0 := 1" triple was removed (it was provable-over). A valid curve with a
failed/invalid op still returns r0 := 1 (commitOptional none). See M7. -/

/-! ## Tier-1 triple: `sol_curve_multiscalar_mul` (zero-length input)

Pinning `r4 = 0` (pointsLen = 0) forces `result = none`, hence
commitOptional yields `r0 := 1, mem unchanged`. The opaque MSM
function is *not called* on this path.

Trust statement: none required for this branch. -/

theorem call_sol_curve_multiscalar_mul_zero_n_spec
    (r0Old : Nat) (pc : Nat) (nCu : Nat)
    (h_step_cu : ∀ s : State,
        (step (.call .sol_curve_multiscalar_mul) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_curve_multiscalar_mul))
      ((.r0 ↦ᵣ r0Old) ** (.r4 ↦ᵣ 0))
      ((.r0 ↦ᵣ 1) ** (.r4 ↦ᵣ 0)) := by
  apply cuTripleWithin_syscall_writes_r0_only_pinned
    .sol_curve_multiscalar_mul .r4 0 1 pc nCu (by decide : (.r4 : Reg) ≠ .r0)
  · -- regs (pinned r4 = 0 ⇒ no n>512 abort; result none ⇒ r0 := 1)
    intro s hr4
    have hr4' : s.regs.r4 = 0 := by show s.regs.get .r4 = 0; exact hr4
    simp [step, execSyscall, Curve25519.execMSM, commitOptional, hr4']
  · -- mem
    intro s hr4
    have hr4' : s.regs.r4 = 0 := by show s.regs.get .r4 = 0; exact hr4
    simp [step, execSyscall, Curve25519.execMSM, commitOptional, hr4']
  · -- pc
    intro s
    show (step (Insn.call Syscall.sol_curve_multiscalar_mul) s).pc = s.pc + 1
    rfl
  · -- exitCode preservation (pinned r4 = 0 excludes the n>512 abort)
    intro s hr4 hex
    have hr4' : s.regs.r4 = 0 := by show s.regs.get .r4 = 0; exact hr4
    simp [step, execSyscall, Curve25519.execMSM, commitOptional, hr4', hex]
  · -- returnData unchanged. `commitOptional` never touches returnData
    -- (either branch), and neither does the n>512 abort.
    intro s
    have hco : ∀ (a l : Nat) (r : Option ByteArray) (st : State),
        (commitOptional st a l r).returnData = st.returnData := fun a l r st => by
      cases r <;> simp [commitOptional]
    simp only [step, execSyscall, Curve25519.execMSM]
    split <;> simp [hco]
  · -- callStack unchanged (commitOptional + abort both preserve it)
    intro s
    have hco : ∀ (a l : Nat) (r : Option ByteArray) (st : State),
        (commitOptional st a l r).callStack = st.callStack := fun a l r st => by
      cases r <;> simp [commitOptional]
    simp only [step, execSyscall, Curve25519.execMSM]
    split <;> simp [hco]
  · -- cuConsumed bound
    exact h_step_cu

/-! ## Tier-1 triple: `sol_curve_decompress` (BLS12-381, unsupported curve_id)

Pinning `r1 = curveId` with curveId ∉ {5, 6, 0x85, 0x86} forces
`result = none`, hence commitOptional yields `r0 := 1, mem unchanged`.
No FFI call to `g1Decompress` / `g2Decompress` happens. -/

theorem call_sol_curve_decompress_unsupported_spec
    (r0Old r1V : Nat) (pc : Nat) (nCu : Nat)
    (h_unsup : r1V ≠ 5 ∧ r1V ≠ 6 ∧ r1V ≠ 133 ∧ r1V ≠ 134)
    (h_step_cu : ∀ s : State,
        (step (.call .sol_curve_decompress) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_curve_decompress))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1V))
      ((.r0 ↦ᵣ 1) ** (.r1 ↦ᵣ r1V)) := by
  apply cuTripleWithin_syscall_writes_r0_only_pinned
    .sol_curve_decompress .r1 r1V 1 pc nCu (by decide : (.r1 : Reg) ≠ .r0)
  · -- regs
    intro s hr1
    have hr1' : s.regs.r1 = r1V := by show s.regs.get .r1 = r1V; exact hr1
    have h1 : (5 : Nat) ||| 128 = 133 := by decide
    have h2 : (6 : Nat) ||| 128 = 134 := by decide
    simp only [step, execSyscall, Bls12_381.execDecompress, commitOptional,
               Bls12_381.BLS12_381_G1_LE, Bls12_381.BLS12_381_G1_BE,
               Bls12_381.BLS12_381_G2_LE, Bls12_381.BLS12_381_G2_BE, h1, h2]
    rw [hr1', if_neg h_unsup.1, if_neg h_unsup.2.2.1,
        if_neg h_unsup.2.1, if_neg h_unsup.2.2.2]
  · -- mem
    intro s hr1
    have hr1' : s.regs.r1 = r1V := by show s.regs.get .r1 = r1V; exact hr1
    have h1 : (5 : Nat) ||| 128 = 133 := by decide
    have h2 : (6 : Nat) ||| 128 = 134 := by decide
    simp only [step, execSyscall, Bls12_381.execDecompress, commitOptional,
               Bls12_381.BLS12_381_G1_LE, Bls12_381.BLS12_381_G1_BE,
               Bls12_381.BLS12_381_G2_LE, Bls12_381.BLS12_381_G2_BE, h1, h2]
    rw [hr1', if_neg h_unsup.1, if_neg h_unsup.2.2.1,
        if_neg h_unsup.2.1, if_neg h_unsup.2.2.2]
  · -- pc
    intro s
    show (step (Insn.call Syscall.sol_curve_decompress) s).pc = s.pc + 1
    rfl
  · -- exitCode preservation
    intro s _ hex
    show (step (Insn.call Syscall.sol_curve_decompress) s).exitCode = none
    simp only [step, execSyscall, Bls12_381.execDecompress]
    generalize h_res :
        (if s.regs.r1 = Bls12_381.BLS12_381_G1_LE then
            Bls12_381.g1Decompress (readBytes s.mem s.regs.r2 48) 1
          else if s.regs.r1 = Bls12_381.BLS12_381_G1_BE then
            Bls12_381.g1Decompress (readBytes s.mem s.regs.r2 48) 0
          else if s.regs.r1 = Bls12_381.BLS12_381_G2_LE then
            Bls12_381.g2Decompress (readBytes s.mem s.regs.r2 96) 1
          else if s.regs.r1 = Bls12_381.BLS12_381_G2_BE then
            Bls12_381.g2Decompress (readBytes s.mem s.regs.r2 96) 0
          else none) = res
    cases res <;> (simp only [commitOptional]; exact hex)
  · -- returnData unchanged
    intro s
    simp [step, execSyscall, Bls12_381.execDecompress]
  · -- callStack unchanged
    intro s
    simp [step, execSyscall, Bls12_381.execDecompress]
  · -- cuConsumed bound
    exact h_step_cu

/-! ## Tier-1 triple: `sol_curve_pairing_map` (BLS12-381, unsupported curve_id)

Pinning `r1 = curveId` with curveId ∉ {4, 0x84} forces
`result = none`, hence commitOptional yields `r0 := 1, mem unchanged`.
No FFI call to `pairingMap` happens. -/

theorem call_sol_curve_pairing_map_unsupported_spec
    (r0Old r1V : Nat) (pc : Nat) (nCu : Nat) (h_unsup : r1V ≠ 4 ∧ r1V ≠ 132)
    (h_step_cu : ∀ s : State,
        (step (.call .sol_curve_pairing_map) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_curve_pairing_map))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1V))
      ((.r0 ↦ᵣ 1) ** (.r1 ↦ᵣ r1V)) := by
  apply cuTripleWithin_syscall_writes_r0_only_pinned
    .sol_curve_pairing_map .r1 r1V 1 pc nCu (by decide : (.r1 : Reg) ≠ .r0)
  · -- regs
    intro s hr1
    have hr1' : s.regs.r1 = r1V := by show s.regs.get .r1 = r1V; exact hr1
    have heq : (4 : Nat) ||| 128 = 132 := by decide
    simp only [step, execSyscall, Bls12_381.execPairing, commitOptional,
               Bls12_381.BLS12_381_LE, Bls12_381.BLS12_381_BE, heq]
    rw [hr1', if_neg h_unsup.1, if_neg h_unsup.2]
  · -- mem
    intro s hr1
    have hr1' : s.regs.r1 = r1V := by show s.regs.get .r1 = r1V; exact hr1
    have heq : (4 : Nat) ||| 128 = 132 := by decide
    simp only [step, execSyscall, Bls12_381.execPairing, commitOptional,
               Bls12_381.BLS12_381_LE, Bls12_381.BLS12_381_BE, heq]
    rw [hr1', if_neg h_unsup.1, if_neg h_unsup.2]
  · -- pc
    intro s
    show (step (Insn.call Syscall.sol_curve_pairing_map) s).pc = s.pc + 1
    rfl
  · -- exitCode preservation
    intro s _ hex
    show (step (Insn.call Syscall.sol_curve_pairing_map) s).exitCode = none
    simp only [step, execSyscall, Bls12_381.execPairing]
    generalize h_res :
        (if s.regs.r1 = Bls12_381.BLS12_381_LE then
            Bls12_381.pairingMap (readBytes s.mem s.regs.r3 (96 * s.regs.r2))
                                  (readBytes s.mem s.regs.r4 (192 * s.regs.r2))
                                  s.regs.r2.toUInt64 1
          else if s.regs.r1 = Bls12_381.BLS12_381_BE then
            Bls12_381.pairingMap (readBytes s.mem s.regs.r3 (96 * s.regs.r2))
                                  (readBytes s.mem s.regs.r4 (192 * s.regs.r2))
                                  s.regs.r2.toUInt64 0
          else none) = res
    cases res <;> (simp only [commitOptional]; exact hex)
  · -- returnData unchanged
    intro s
    simp [step, execSyscall, Bls12_381.execPairing]
  · -- callStack unchanged
    intro s
    simp [step, execSyscall, Bls12_381.execPairing]
  · -- cuConsumed bound
    exact h_step_cu



end SVM.SBPF
