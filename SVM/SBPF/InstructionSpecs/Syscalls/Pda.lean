import SVM.SBPF.InstructionSpecs.Syscalls.ReturnData

namespace SVM.SBPF

open Memory

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
  have hcr_regs := hcompat.regs
  have hcm_mem := hcompat.mem
  -- ==== Phase 2: range disjointness between [r3V..r3V+32) and [r4V..r4V+32). ====
  -- Derive the strong "ranges fully disjoint" statement from hd_b3_b4 by
  -- specializing on a concrete in-range address.
  have h_ranges_disjoint : r3V + 32 ≤ r4V ∨ r4V + 32 ≤ r3V := by
    have hd_mem := hd_b3_b4.mem
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
    have hd_PR_regs := hd_PR.regs
    have hd_PR_mem := hd_PR.mem
    have hd_PR_pc := hd_PR.pc
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
      refine ⟨fun r => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
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
      refine ⟨fun r => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
      · right
        show h_T4_new.regs r = none
        show ((PartialState.singletonMem32Bytes r3V pidBytes).union _).regs r = none
        rw [PartialState.union_regs_of_left_none (PartialState.singletonMem32Bytes_regs r)]
        exact PartialState.singletonMem32Bytes_regs r
      · left; exact PartialState.singletonReg_mem a
      · left; exact PartialState.singletonReg_pc
    have hd_r3_T3_new : h_r3_new.Disjoint h_T3_new := by
      refine ⟨fun r => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
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
      refine ⟨fun r => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
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
      refine ⟨fun r => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
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
      refine ⟨fun r => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
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
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
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
      · intro rd hva
        have h_P_new_rd : h_P_new.returnData = none := by rfl
        rw [PartialState.union_returnData_of_left_none h_P_new_rd] at hva
        have h_P_rd : h_P.returnData = none := by
          rw [← hu_r0_T1, ← hu_r2_T2, ← hu_r3_T3, ← hu_r4_T4, ← hu_b3_b4]; rfl
        have hp_rd : hp.returnData = some rd := by
          rw [← hu_PR, PartialState.union_returnData_of_left_none h_P_rd]
          exact hva
        -- The post-state's returnData reduces to s.returnData via simp.
        simp only [hs'_def, commitOptional_preserves_returnData]
        exact hcompat.returnData rd hp_rd
      · intro cs hva
        have h_P_new_cs : h_P_new.callStack = none := by rfl
        rw [PartialState.union_callStack_of_left_none h_P_new_cs] at hva
        have h_P_cs : h_P.callStack = none := by
          rw [← hu_r0_T1, ← hu_r2_T2, ← hu_r3_T3, ← hu_r4_T4, ← hu_b3_b4]; rfl
        have hp_cs : hp.callStack = some cs := by
          rw [← hu_PR, PartialState.union_callStack_of_left_none h_P_cs]
          exact hva
        -- The post-state's returnData reduces to s.callStack via simp.
        simp only [hs'_def, commitOptional_preserves_callStack]
        exact hcompat.callStack cs hp_cs
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
  have hcr_regs := hcompat.regs
  have hcm_mem := hcompat.mem
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
    have hd_mem := hd_D0_S.mem
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
    have hd_mem := hd_D0_S.mem
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
    have hd_mem := hd_D0_B3.mem
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
    have hd_mem := hd_D0_B3.mem
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
    have hd_mem := hd_D0_B4.mem
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
    have hd_mem := hd_D0_B4.mem
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
    have hd_mem := hd_D1_S.mem
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
    have hd_mem := hd_D1_S.mem
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
    have hd_mem := hd_D1_B3.mem
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
    have hd_mem := hd_D1_B3.mem
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
    have hd_mem := hd_D1_B4.mem
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
    have hd_mem := hd_D1_B4.mem
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
    have hd_mem := hd_S_B3.mem
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
    have hd_mem := hd_S_B3.mem
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
    have hd_mem := hd_S_B4.mem
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
    have hd_mem := hd_S_B4.mem
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
    have hd_mem := hd_b3_b4.mem
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
    have hd_mem := hd_b3_b4.mem
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
      rcases hd_PR.regs .r0 with hl | hr
      · rw [h_P_regs_r0] at hl; nomatch hl
      · exact hr
    have h_R_no_r1 : h_R.regs .r1 = none := by
      rcases hd_PR.regs .r1 with hl | hr
      · rw [h_P_regs_r1] at hl; nomatch hl
      · exact hr
    have h_R_no_r2 : h_R.regs .r2 = none := by
      rcases hd_PR.regs .r2 with hl | hr
      · rw [h_P_regs_r2] at hl; nomatch hl
      · exact hr
    have h_R_no_r3 : h_R.regs .r3 = none := by
      rcases hd_PR.regs .r3 with hl | hr
      · rw [h_P_regs_r3] at hl; nomatch hl
      · exact hr
    have h_R_no_r4 : h_R.regs .r4 = none := by
      rcases hd_PR.regs .r4 with hl | hr
      · rw [h_P_regs_r4] at hl; nomatch hl
      · exact hr
    have h_R_no_pc : h_R.pc = none := hRfree _ h_R_sat
    -- h_R doesn't own mem in any of the 5 regions. Pattern: pick a sentinel
    -- in the atom's range; the SL-disjointness via hd_PR rules out h_R.
    have h_R_no_mem_d0 (a : Nat) (h : r1V ≤ a ∧ a < r1V + 8) : h_R.mem a = none := by
      rcases hd_PR.mem a with hl | hr
      · obtain ⟨v, hv⟩ := PartialState.singletonMemU64_mem_isSome r1V seedPtr a h
        have hT5 : h_T5.mem a = some v := by
          rw [← hu_d0_T6]; exact PartialState.union_mem_of_left_some hv
        rw [h_P_mem_eq_T5 a, hT5] at hl; nomatch hl
      · exact hr
    have h_R_no_mem_d1 (a : Nat) (h : r1V + 8 ≤ a ∧ a < r1V + 16) : h_R.mem a = none := by
      rcases hd_PR.mem a with hl | hr
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
      rcases hd_PR.mem a with hl | hr
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
      rcases hd_PR.mem a with hl | hr
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
      rcases hd_PR.mem a with hl | hr
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
              Or.inl PartialState.singletonMem32Bytes_pc, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
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
              Or.inl PartialState.singletonMemBytes_pc, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
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
              Or.inl PartialState.singletonMemU64_pc, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
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
              Or.inl PartialState.singletonMemU64_pc, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
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
              Or.inl PartialState.singletonReg_pc, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
    have hd_a3_T4_new : h_a3_new.Disjoint h_T4_new := by
      refine ⟨fun r => ?_,
              fun a => Or.inl (PartialState.singletonReg_mem a),
              Or.inl PartialState.singletonReg_pc, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
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
              Or.inl PartialState.singletonReg_pc, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
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
              Or.inl PartialState.singletonReg_pc, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
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
              Or.inl PartialState.singletonReg_pc, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
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
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
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
            rcases hd_PR.regs r with hl | hr
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
            rcases hd_PR.mem a with hl | hr
            · exact hl
            · rw [hr] at hvm; nomatch hvm
          exact hcm_mem a vm (by rw [← hu_PR,
              PartialState.union_mem_of_left_none h_P_none]; exact hvm)
      -- pc
      · intro vp hvp
        rw [PartialState.union_pc_of_left_none h_P_new_pc] at hvp
        rw [h_R_no_pc] at hvp
        nomatch hvp
      · intro rd hva
        have h_P_new_rd : h_P_new.returnData = none := by rfl
        rw [PartialState.union_returnData_of_left_none h_P_new_rd] at hva
        have h_P_rd : h_P.returnData = none := by
          rw [← hu_a0_T1, ← hu_a1_T2, ← hu_a2_T3, ← hu_a3_T4, ← hu_a4_T5,
              ← hu_d0_T6, ← hu_d1_T7, ← hu_s_T8, ← hu_b3_b4]; rfl
        have hp_rd : hp.returnData = some rd := by
          rw [← hu_PR, PartialState.union_returnData_of_left_none h_P_rd]
          exact hva
        simp only [hs'_def, commitOptional_preserves_returnData]
        exact hcompat.returnData rd hp_rd
      · intro cs hva
        have h_P_new_cs : h_P_new.callStack = none := by rfl
        rw [PartialState.union_callStack_of_left_none h_P_new_cs] at hva
        have h_P_cs : h_P.callStack = none := by
          rw [← hu_a0_T1, ← hu_a1_T2, ← hu_a2_T3, ← hu_a3_T4, ← hu_a4_T5,
              ← hu_d0_T6, ← hu_d1_T7, ← hu_s_T8, ← hu_b3_b4]; rfl
        have hp_cs : hp.callStack = some cs := by
          rw [← hu_PR, PartialState.union_callStack_of_left_none h_P_cs]
          exact hva
        simp only [hs'_def, commitOptional_preserves_callStack]
        exact hcompat.callStack cs hp_cs
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


end SVM.SBPF
