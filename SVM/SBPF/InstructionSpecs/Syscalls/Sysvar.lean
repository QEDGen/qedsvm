import SVM.SBPF.InstructionSpecs.Syscalls.Mem

namespace SVM.SBPF

open Memory

/-! ## Syscall: `sol_get_clock_sysvar`

Writes 40 bytes of zeros at `*r1`, sets `r0 := 0`. First multi-region
sysvar spec driven by the generic
`cuTripleWithin_syscall_writesR1Bytes` helper — proves the same
shape as `sol_get_last_restart_slot` but at 40 bytes without a
per-byte case ladder. -/

theorem call_sol_get_clock_sysvar_spec
    (r0Old r1V pc : Nat) (bsOld : ByteArray) (hbs : bsOld.size = 40) (nCu : Nat)
      (h_step_cu : ∀ s : State,
          (step (.call .sol_get_clock_sysvar) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_get_clock_sysvar))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1V) ** (r1V ↦Bytes bsOld))
      ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ r1V) ** (r1V ↦Bytes (zerosByteArray 40))) := by
  refine cuTripleWithin_syscall_writesR1Bytes
    .sol_get_clock_sysvar (zerosByteArray 40) pc nCu
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ h_step_cu r0Old r1V bsOld ?_
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
  · intro s
    simp only [step, execSyscall, Sysvar.execClock, Sysvar.zeroFillR1]
  · intro s
    simp only [step, execSyscall, Sysvar.execClock, Sysvar.zeroFillR1]
  · rw [zerosByteArray_size]; exact hbs

/-! ## Syscall: `sol_get_epoch_rewards_sysvar`

Writes 81 bytes of zeros at `*r1`, sets `r0 := 0`. Mainnet default
EpochRewards struct under `active = false`. -/

theorem call_sol_get_epoch_rewards_sysvar_spec
    (r0Old r1V pc : Nat) (bsOld : ByteArray) (hbs : bsOld.size = 81) (nCu : Nat)
      (h_step_cu : ∀ s : State,
          (step (.call .sol_get_epoch_rewards_sysvar) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_get_epoch_rewards_sysvar))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1V) ** (r1V ↦Bytes bsOld))
      ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ r1V) ** (r1V ↦Bytes (zerosByteArray 81))) := by
  refine cuTripleWithin_syscall_writesR1Bytes
    .sol_get_epoch_rewards_sysvar (zerosByteArray 81) pc nCu
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ h_step_cu r0Old r1V bsOld ?_
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
  · intro s
    simp only [step, execSyscall, Sysvar.execEpochRewards, Sysvar.zeroFillR1]
  · intro s
    simp only [step, execSyscall, Sysvar.execEpochRewards, Sysvar.zeroFillR1]
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
    (r0Old r1V pc : Nat) (bsOld : ByteArray) (hbs : bsOld.size = 17) (nCu : Nat)
      (h_step_cu : ∀ s : State,
          (step (.call .sol_get_rent_sysvar) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_get_rent_sysvar))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1V) ** (r1V ↦Bytes bsOld))
      ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ r1V) ** (r1V ↦Bytes rentBytes)) := by
  refine cuTripleWithin_syscall_writesR1Bytes
    .sol_get_rent_sysvar rentBytes pc nCu
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ h_step_cu r0Old r1V bsOld ?_
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
  · intro s
    simp only [step, execSyscall, Sysvar.execRent]
  · intro s
    simp only [step, execSyscall, Sysvar.execRent]
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
    (r0Old r1V pc : Nat) (bsOld : ByteArray) (hbs : bsOld.size = 40) (nCu : Nat)
      (h_step_cu : ∀ s : State,
          (step (.call .sol_get_epoch_schedule_sysvar) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_get_epoch_schedule_sysvar))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ r1V) ** (r1V ↦Bytes bsOld))
      ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ r1V) ** (r1V ↦Bytes epochScheduleBytes)) := by
  refine cuTripleWithin_syscall_writesR1Bytes
    .sol_get_epoch_schedule_sysvar epochScheduleBytes pc nCu
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ h_step_cu r0Old r1V bsOld ?_
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
  · intro s
    simp only [step, execSyscall, Sysvar.execEpochSchedule]
  · intro s
    simp only [step, execSyscall, Sysvar.execEpochSchedule]
  · rw [epochScheduleBytes_size]; exact hbs

/-! ## Syscall: `sol_get_last_restart_slot`

Writes 8 bytes of zeros at `*r1`, sets `r0 := 0`. First memory-writing
syscall triple in the SL track — exercises the basic "r0-and-8-byte-mem"
shape that the U64-sized sysvar zero-fills (this and `sol_get_fees_sysvar`)
share. Memory is owned only at `[r1V, r1V+8)` by the precondition. -/

theorem call_sol_get_last_restart_slot_spec
    (r0Old r1V vOld pc : Nat) (nCu : Nat)
      (h_step_cu : ∀ s : State,
          (step (.call .sol_get_last_restart_slot) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithin 1 nCu pc (pc + 1)
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
  have hexec_cu : (executeFn fetch s 1).cuConsumed ≤ s.cuConsumed + nCu := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch, executeFn_zero]
    exact h_step_cu s
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
    refine ⟨fun r => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
    · right; exact PartialState.singletonMemU64_regs r
    · left; exact PartialState.singletonReg_mem a
    · left; exact PartialState.singletonReg_pc
  -- Inner disjointness: r0_new ⊥ (r1_new ⊎ b_new).
  have hd_r0_T1_new : h_r0_new.Disjoint h_T1_new := by
    refine ⟨fun r => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
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
    refine ⟨fun r => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
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
    · intro rd hva
      have h_P_new_rd : h_P_new.returnData = none := by rfl
      rw [PartialState.union_returnData_of_left_none h_P_new_rd] at hva
      have h_P_rd : h_P.returnData = none := by
        rw [← hu_r0_T1, ← hu_r1_b]; rfl
      have hp_rd : hp.returnData = some rd := by
        rw [← hu_PR, PartialState.union_returnData_of_left_none h_P_rd]
        exact hva
      have hexec_rd : (executeFn fetch s 1).returnData = s.returnData := by
        rw [show (1 : Nat) = 0 + 1 from rfl,
            executeFn_step fetch s 0 _ hex hfetch, executeFn_zero]
        rfl
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
        rw [show (1 : Nat) = 0 + 1 from rfl,
            executeFn_step fetch s 0 _ hex hfetch, executeFn_zero]
        rfl
      rw [hexec_cs]
      exact hcompat.callStack cs hp_cs
/-! ## Syscall: `sol_get_fees_sysvar`

Deprecated sysvar; identical 8-byte zero-fill body to `sol_get_last_restart_slot`
via `Sysvar.execFees s = Sysvar.zeroFillR1 s 8`. Same precondition,
same postcondition, same proof up to the syscall-variant name and the
unfold target. -/

theorem call_sol_get_fees_sysvar_spec
    (r0Old r1V vOld pc : Nat) (nCu : Nat)
      (h_step_cu : ∀ s : State,
          (step (.call .sol_get_fees_sysvar) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithin 1 nCu pc (pc + 1)
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
  have hexec_cu : (executeFn fetch s 1).cuConsumed ≤ s.cuConsumed + nCu := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch, executeFn_zero]
    exact h_step_cu s
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
    refine ⟨fun r => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
    · right; exact PartialState.singletonMemU64_regs r
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
    refine ⟨fun r => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
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
    · intro rd hva
      have h_P_new_rd : h_P_new.returnData = none := by rfl
      rw [PartialState.union_returnData_of_left_none h_P_new_rd] at hva
      have h_P_rd : h_P.returnData = none := by
        rw [← hu_r0_T1, ← hu_r1_b]; rfl
      have hp_rd : hp.returnData = some rd := by
        rw [← hu_PR, PartialState.union_returnData_of_left_none h_P_rd]
        exact hva
      have hexec_rd : (executeFn fetch s 1).returnData = s.returnData := by
        rw [show (1 : Nat) = 0 + 1 from rfl,
            executeFn_step fetch s 0 _ hex hfetch, executeFn_zero]
        rfl
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
        rw [show (1 : Nat) = 0 + 1 from rfl,
            executeFn_step fetch s 0 _ hex hfetch, executeFn_zero]
        rfl
      rw [hexec_cs]
      exact hcompat.callStack cs hp_cs

end SVM.SBPF
