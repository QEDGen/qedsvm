import SVM.SBPF.InstructionSpecs.Syscalls.Helper

namespace SVM.SBPF

open Memory

/-! ## Syscall: `sol_log_`

`sol_log_(ptr, len)`: log a byte slice from `[r1..r1+r2)`, set `r0 := 0`.
Memory is read but not written; r1 and r2 are unchanged. `State.log` is
silent in `PartialState` by design. -/

theorem call_sol_log_spec (r0Old : Nat) (pc : Nat) (nCu : Nat)
    (h_step_cu : ∀ s : State,
        (step (.call .sol_log_) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_log_))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ 0) :=
  cuTripleWithin_syscall_writes_r0_only .sol_log_ 0 pc nCu
    (fun s => by simp [step, execSyscall, Logging.execLog])
    (fun s => by simp [step, execSyscall, Logging.execLog])
    (fun s => by simp [step, execSyscall, Logging.execLog])
    (fun s hex => by simp [step, execSyscall, Logging.execLog]; exact hex)
    (fun s => by simp [step, execSyscall, Logging.execLog])
    (fun s => by simp [step, execSyscall, Logging.execLog])
    (fun s => h_step_cu s)
    r0Old

/-! ## Syscall: `sol_log_pubkey`

`sol_log_pubkey(ptr)`: log 32 bytes from `[r1..r1+32)`, set `r0 := 0`.
Same single-atom shape as `sol_log_`. -/

theorem call_sol_log_pubkey_spec (r0Old : Nat) (pc : Nat) (nCu : Nat)
    (h_step_cu : ∀ s : State,
        (step (.call .sol_log_pubkey) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_log_pubkey))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ 0) :=
  cuTripleWithin_syscall_writes_r0_only .sol_log_pubkey 0 pc nCu
    (fun s => by simp [step, execSyscall, Logging.execLogPubkey])
    (fun s => by simp [step, execSyscall, Logging.execLogPubkey])
    (fun s => by simp [step, execSyscall, Logging.execLogPubkey])
    (fun s hex => by simp [step, execSyscall, Logging.execLogPubkey]; exact hex)
    (fun s => by simp [step, execSyscall, Logging.execLogPubkey])
    (fun s => by simp [step, execSyscall, Logging.execLogPubkey])
    (fun s => h_step_cu s)
    r0Old

/-! ## Syscall: `sol_get_stack_height`

Returns the current CPI depth in `r0`. Our model fixes this to `1`
(top-level) regardless of `State.callStack` — see `Misc.execGetStackHeight`. -/

theorem call_sol_get_stack_height_spec (r0Old : Nat) (pc : Nat) (nCu : Nat)
    (h_step_cu : ∀ s : State,
        (step (.call .sol_get_stack_height) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_get_stack_height))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ 1) :=
  cuTripleWithin_syscall_writes_r0_only .sol_get_stack_height 1 pc nCu
    (fun s => by simp [step, execSyscall, Misc.execGetStackHeight])
    (fun s => by simp [step, execSyscall, Misc.execGetStackHeight])
    (fun s => by simp [step, execSyscall, Misc.execGetStackHeight])
    (fun s hex => by simp [step, execSyscall, Misc.execGetStackHeight]; exact hex)
    (fun s => by simp [step, execSyscall, Misc.execGetStackHeight])
    (fun s => by simp [step, execSyscall, Misc.execGetStackHeight])
    (fun s => h_step_cu s)
    r0Old

/-! ## Syscall: `sol_log_64_`

`sol_log_64_(r1..r5)`: emit hex-formatted register dump. r0 := 0.
Memory unchanged. -/

theorem call_sol_log_64_spec (r0Old : Nat) (pc : Nat) (nCu : Nat)
    (h_step_cu : ∀ s : State,
        (step (.call .sol_log_64_) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_log_64_))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ 0) :=
  cuTripleWithin_syscall_writes_r0_only .sol_log_64_ 0 pc nCu
    (fun s => by simp [step, execSyscall, Logging.execLog64])
    (fun s => by simp [step, execSyscall, Logging.execLog64])
    (fun s => by simp [step, execSyscall, Logging.execLog64])
    (fun s hex => by simp [step, execSyscall, Logging.execLog64]; exact hex)
    (fun s => by simp [step, execSyscall, Logging.execLog64])
    (fun s => by simp [step, execSyscall, Logging.execLog64])
    (fun s => h_step_cu s)
    r0Old

/-! ## Syscall: `sol_log_compute_units_`

Emit "Program consumption: <remaining> units remaining". r0 := 0. -/

theorem call_sol_log_compute_units_spec (r0Old : Nat) (pc : Nat) (nCu : Nat)
    (h_step_cu : ∀ s : State,
        (step (.call .sol_log_compute_units_) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_log_compute_units_))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ 0) :=
  cuTripleWithin_syscall_writes_r0_only .sol_log_compute_units_ 0 pc nCu
    (fun s => by simp [step, execSyscall, Logging.execLogComputeUnits])
    (fun s => by simp [step, execSyscall, Logging.execLogComputeUnits])
    (fun s => by simp [step, execSyscall, Logging.execLogComputeUnits])
    (fun s hex => by simp [step, execSyscall, Logging.execLogComputeUnits]; exact hex)
    (fun s => by simp [step, execSyscall, Logging.execLogComputeUnits])
    (fun s => by simp [step, execSyscall, Logging.execLogComputeUnits])
    (fun s => h_step_cu s)
    r0Old

/-! ## Syscall: `sol_log_data`

`sol_log_data(fields_ptr, count)`: read `count` SliceDesc descriptors
from r1, base64-encode each slice they point to, emit joined message.
Memory is read (descriptors + each slice) but not written. r0 := 0. -/

theorem call_sol_log_data_spec (r0Old : Nat) (pc : Nat) (nCu : Nat)
    (h_step_cu : ∀ s : State,
        (step (.call .sol_log_data) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_log_data))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ 0) :=
  cuTripleWithin_syscall_writes_r0_only .sol_log_data 0 pc nCu
    (fun s => by simp [step, execSyscall, Logging.execLogData])
    (fun s => by simp [step, execSyscall, Logging.execLogData])
    (fun s => by simp [step, execSyscall, Logging.execLogData])
    (fun s hex => by simp [step, execSyscall, Logging.execLogData]; exact hex)
    (fun s => by simp [step, execSyscall, Logging.execLogData])
    (fun s => by simp [step, execSyscall, Logging.execLogData])
    (fun s => h_step_cu s)
    r0Old

/-! ## Syscall: `sol_get_epoch_stake`

Returns 0 in `r0` (stake not modeled). Memory unchanged. -/

theorem call_sol_get_epoch_stake_spec (r0Old : Nat) (pc : Nat) (nCu : Nat)
    (h_step_cu : ∀ s : State,
        (step (.call .sol_get_epoch_stake) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_get_epoch_stake))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ 0) :=
  cuTripleWithin_syscall_writes_r0_only .sol_get_epoch_stake 0 pc nCu
    (fun s => by simp [step, execSyscall, Sysvar.execEpochStake])
    (fun s => by simp [step, execSyscall, Sysvar.execEpochStake])
    (fun s => by simp [step, execSyscall, Sysvar.execEpochStake])
    (fun s hex => by simp [step, execSyscall, Sysvar.execEpochStake]; exact hex)
    (fun s => by simp [step, execSyscall, Sysvar.execEpochStake])
    (fun s => by simp [step, execSyscall, Sysvar.execEpochStake])
    (fun s => h_step_cu s)
    r0Old

/-! ## Syscall: `sol_get_processed_sibling_instruction`

Sibling-instruction tracking is not modeled; the syscall returns 0
in `r0` and otherwise leaves state unchanged. -/

theorem call_sol_get_processed_sibling_instruction_spec
    (r0Old : Nat) (pc : Nat) (nCu : Nat)
    (h_step_cu : ∀ s : State,
        (step (.call .sol_get_processed_sibling_instruction) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_get_processed_sibling_instruction))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ 0) :=
  cuTripleWithin_syscall_writes_r0_only
    .sol_get_processed_sibling_instruction 0 pc nCu
    (fun s => by simp [step, execSyscall, Misc.execProcessedSibling])
    (fun s => by simp [step, execSyscall, Misc.execProcessedSibling])
    (fun s => by simp [step, execSyscall, Misc.execProcessedSibling])
    (fun s hex => by simp [step, execSyscall, Misc.execProcessedSibling]; exact hex)
    (fun s => by simp [step, execSyscall, Misc.execProcessedSibling])
    (fun s => by simp [step, execSyscall, Misc.execProcessedSibling])
    (fun s => h_step_cu s)
    r0Old

/-! ## Syscall: `sol_get_sysvar` (generic accessor)

Returns 0 in `r0`; per-sysvar getters (`sol_get_{clock,rent,...}_sysvar`)
are the modeled path that actually populates the output buffer. -/

theorem call_sol_get_sysvar_spec (r0Old : Nat) (pc : Nat) (nCu : Nat)
    (h_step_cu : ∀ s : State,
        (step (.call .sol_get_sysvar) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_get_sysvar))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ 0) :=
  cuTripleWithin_syscall_writes_r0_only .sol_get_sysvar 0 pc nCu
    (fun s => by simp [step, execSyscall, Misc.execGetSysvar])
    (fun s => by simp [step, execSyscall, Misc.execGetSysvar])
    (fun s => by simp [step, execSyscall, Misc.execGetSysvar])
    (fun s hex => by simp [step, execSyscall, Misc.execGetSysvar]; exact hex)
    (fun s => by simp [step, execSyscall, Misc.execGetSysvar])
    (fun s => by simp [step, execSyscall, Misc.execGetSysvar])
    (fun s => h_step_cu s)
    r0Old

/-! ## Syscall: `.unknown` (unrecognized hash)

For any unrecognized / unregistered syscall hash agave rejects the
program; we fail closed with the same effect (`exitCode :=
ERR_UNSUPPORTED_INSTRUCTION`) rather than fabricate success. A lift that
reaches an unknown syscall therefore proves an ABORT. See
docs/SOUNDNESS_AUDIT_* (H7). -/

theorem call_sol_unknown_aborts_spec (hash : Nat) (pc : Nat) (nCu : Nat)
    (hCu : ∀ s : State,
        (step (.call (.unknown hash)) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleAbortsWithin 1 nCu pc
      (CodeReq.singleton pc (.call (.unknown hash)))
      emp ERR_UNSUPPORTED_INSTRUCTION := by
  intro R hRfree fetch hcr s hPR hpc hex hbud
  obtain ⟨hp, hcompat, h1, hR, hd, hu, hP1, hRsat⟩ := hPR
  rw [hP1, PartialState.union_empty_left] at hu
  rw [hP1] at hd
  clear hP1 h1
  have hfetch : fetch s.pc = some (.call (.unknown hash)) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hstep_eq : executeFn fetch s 1 = chargeCu (step (.call (.unknown hash)) s) := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch, executeFn_zero]
  have hexec : executeFn fetch s 1 = chargeCu
      { (Misc.execUnknown s) with pc := s.pc + 1
                                  cuConsumed := (Misc.execUnknown s).cuConsumed
                                    + syscallCu (.unknown hash) s } := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch, executeFn_zero]
    simp only [step, execSyscall]
  refine ⟨1, Nat.le_refl 1, ?_, ?_⟩
  · rw [hexec]
    show (Misc.execUnknown s).exitCode = some ERR_UNSUPPORTED_INSTRUCTION
    rfl
  · rw [hstep_eq]
    show (step (.call (.unknown hash)) s).cuConsumed + 1 ≤ s.cuConsumed + 1 + nCu
    have := hCu s; omega


end SVM.SBPF
