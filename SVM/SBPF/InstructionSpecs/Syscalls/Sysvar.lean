import SVM.SBPF.InstructionSpecs.Syscalls.Mem

namespace SVM.SBPF

open Memory


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

end SVM.SBPF
