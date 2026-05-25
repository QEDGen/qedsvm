import SVM.SBPF.InstructionSpecs.Syscalls.Helper

namespace SVM.SBPF

open Memory

/-! ## Syscall: `sol_log_`

`sol_log_(ptr, len)`: log a byte slice from `[r1..r1+r2)`, set `r0 := 0`.
Memory is read but not written; r1 and r2 are unchanged. `State.log` is
silent in `PartialState` by design. -/

theorem call_sol_log_spec (r0Old : Nat) (pc : Nat) :
    cuTripleWithin 1 pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_log_))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ 0) :=
  cuTripleWithin_syscall_writes_r0_only .sol_log_ 0 pc
    (fun s => by simp [step, execSyscall, Logging.execLog])
    (fun s => by simp [step, execSyscall, Logging.execLog])
    (fun s => by simp [step, execSyscall, Logging.execLog])
    (fun s hex => by simp [step, execSyscall, Logging.execLog]; exact hex)
    (fun s => by simp [step, execSyscall, Logging.execLog])
    (fun s => by simp [step, execSyscall, Logging.execLog])
    r0Old

/-! ## Syscall: `sol_log_pubkey`

`sol_log_pubkey(ptr)`: log 32 bytes from `[r1..r1+32)`, set `r0 := 0`.
Same single-atom shape as `sol_log_`. -/

theorem call_sol_log_pubkey_spec (r0Old : Nat) (pc : Nat) :
    cuTripleWithin 1 pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_log_pubkey))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ 0) :=
  cuTripleWithin_syscall_writes_r0_only .sol_log_pubkey 0 pc
    (fun s => by simp [step, execSyscall, Logging.execLogPubkey])
    (fun s => by simp [step, execSyscall, Logging.execLogPubkey])
    (fun s => by simp [step, execSyscall, Logging.execLogPubkey])
    (fun s hex => by simp [step, execSyscall, Logging.execLogPubkey]; exact hex)
    (fun s => by simp [step, execSyscall, Logging.execLogPubkey])
    (fun s => by simp [step, execSyscall, Logging.execLogPubkey])
    r0Old

/-! ## Syscall: `sol_get_stack_height`

Returns the current CPI depth in `r0`. Our model fixes this to `1`
(top-level) regardless of `State.callStack` — see `Misc.execGetStackHeight`. -/

theorem call_sol_get_stack_height_spec (r0Old : Nat) (pc : Nat) :
    cuTripleWithin 1 pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_get_stack_height))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ 1) :=
  cuTripleWithin_syscall_writes_r0_only .sol_get_stack_height 1 pc
    (fun s => by simp [step, execSyscall, Misc.execGetStackHeight])
    (fun s => by simp [step, execSyscall, Misc.execGetStackHeight])
    (fun s => by simp [step, execSyscall, Misc.execGetStackHeight])
    (fun s hex => by simp [step, execSyscall, Misc.execGetStackHeight]; exact hex)
    (fun s => by simp [step, execSyscall, Misc.execGetStackHeight])
    (fun s => by simp [step, execSyscall, Misc.execGetStackHeight])
    r0Old

/-! ## Syscall: `sol_log_64_`

`sol_log_64_(r1..r5)`: emit hex-formatted register dump. r0 := 0.
Memory unchanged. -/

theorem call_sol_log_64_spec (r0Old : Nat) (pc : Nat) :
    cuTripleWithin 1 pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_log_64_))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ 0) :=
  cuTripleWithin_syscall_writes_r0_only .sol_log_64_ 0 pc
    (fun s => by simp [step, execSyscall, Logging.execLog64])
    (fun s => by simp [step, execSyscall, Logging.execLog64])
    (fun s => by simp [step, execSyscall, Logging.execLog64])
    (fun s hex => by simp [step, execSyscall, Logging.execLog64]; exact hex)
    (fun s => by simp [step, execSyscall, Logging.execLog64])
    (fun s => by simp [step, execSyscall, Logging.execLog64])
    r0Old

/-! ## Syscall: `sol_log_compute_units_`

Emit "Program consumption: <remaining> units remaining". r0 := 0. -/

theorem call_sol_log_compute_units_spec (r0Old : Nat) (pc : Nat) :
    cuTripleWithin 1 pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_log_compute_units_))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ 0) :=
  cuTripleWithin_syscall_writes_r0_only .sol_log_compute_units_ 0 pc
    (fun s => by simp [step, execSyscall, Logging.execLogComputeUnits])
    (fun s => by simp [step, execSyscall, Logging.execLogComputeUnits])
    (fun s => by simp [step, execSyscall, Logging.execLogComputeUnits])
    (fun s hex => by simp [step, execSyscall, Logging.execLogComputeUnits]; exact hex)
    (fun s => by simp [step, execSyscall, Logging.execLogComputeUnits])
    (fun s => by simp [step, execSyscall, Logging.execLogComputeUnits])
    r0Old

/-! ## Syscall: `sol_log_data`

`sol_log_data(fields_ptr, count)`: read `count` SliceDesc descriptors
from r1, base64-encode each slice they point to, emit joined message.
Memory is read (descriptors + each slice) but not written. r0 := 0. -/

theorem call_sol_log_data_spec (r0Old : Nat) (pc : Nat) :
    cuTripleWithin 1 pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_log_data))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ 0) :=
  cuTripleWithin_syscall_writes_r0_only .sol_log_data 0 pc
    (fun s => by simp [step, execSyscall, Logging.execLogData])
    (fun s => by simp [step, execSyscall, Logging.execLogData])
    (fun s => by simp [step, execSyscall, Logging.execLogData])
    (fun s hex => by simp [step, execSyscall, Logging.execLogData]; exact hex)
    (fun s => by simp [step, execSyscall, Logging.execLogData])
    (fun s => by simp [step, execSyscall, Logging.execLogData])
    r0Old

/-! ## Syscall: `sol_get_epoch_stake`

Returns 0 in `r0` (stake not modeled). Memory unchanged. -/

theorem call_sol_get_epoch_stake_spec (r0Old : Nat) (pc : Nat) :
    cuTripleWithin 1 pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_get_epoch_stake))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ 0) :=
  cuTripleWithin_syscall_writes_r0_only .sol_get_epoch_stake 0 pc
    (fun s => by simp [step, execSyscall, Sysvar.execEpochStake])
    (fun s => by simp [step, execSyscall, Sysvar.execEpochStake])
    (fun s => by simp [step, execSyscall, Sysvar.execEpochStake])
    (fun s hex => by simp [step, execSyscall, Sysvar.execEpochStake]; exact hex)
    (fun s => by simp [step, execSyscall, Sysvar.execEpochStake])
    (fun s => by simp [step, execSyscall, Sysvar.execEpochStake])
    r0Old

/-! ## Syscall: `sol_get_processed_sibling_instruction`

Sibling-instruction tracking is not modeled; the syscall returns 0
in `r0` and otherwise leaves state unchanged. -/

theorem call_sol_get_processed_sibling_instruction_spec
    (r0Old : Nat) (pc : Nat) :
    cuTripleWithin 1 pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_get_processed_sibling_instruction))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ 0) :=
  cuTripleWithin_syscall_writes_r0_only
    .sol_get_processed_sibling_instruction 0 pc
    (fun s => by simp [step, execSyscall, Misc.execProcessedSibling])
    (fun s => by simp [step, execSyscall, Misc.execProcessedSibling])
    (fun s => by simp [step, execSyscall, Misc.execProcessedSibling])
    (fun s hex => by simp [step, execSyscall, Misc.execProcessedSibling]; exact hex)
    (fun s => by simp [step, execSyscall, Misc.execProcessedSibling])
    (fun s => by simp [step, execSyscall, Misc.execProcessedSibling])
    r0Old

/-! ## Syscall: `sol_get_sysvar` (generic accessor)

Returns 0 in `r0`; per-sysvar getters (`sol_get_{clock,rent,...}_sysvar`)
are the modeled path that actually populates the output buffer. -/

theorem call_sol_get_sysvar_spec (r0Old : Nat) (pc : Nat) :
    cuTripleWithin 1 pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_get_sysvar))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ 0) :=
  cuTripleWithin_syscall_writes_r0_only .sol_get_sysvar 0 pc
    (fun s => by simp [step, execSyscall, Misc.execGetSysvar])
    (fun s => by simp [step, execSyscall, Misc.execGetSysvar])
    (fun s => by simp [step, execSyscall, Misc.execGetSysvar])
    (fun s hex => by simp [step, execSyscall, Misc.execGetSysvar]; exact hex)
    (fun s => by simp [step, execSyscall, Misc.execGetSysvar])
    (fun s => by simp [step, execSyscall, Misc.execGetSysvar])
    r0Old

/-! ## Syscall: `.unknown` (unrecognized hash)

For any unrecognized syscall hash, agave aborts; we return 0 in `r0`
so programs that test against opaque hashes don't spuriously fail. -/

theorem call_sol_unknown_spec (hash r0Old : Nat) (pc : Nat) :
    cuTripleWithin 1 pc (pc + 1)
      (CodeReq.singleton pc (.call (.unknown hash)))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ 0) :=
  cuTripleWithin_syscall_writes_r0_only (.unknown hash) 0 pc
    (fun s => by simp [step, execSyscall, Misc.execUnknown])
    (fun s => by simp [step, execSyscall, Misc.execUnknown])
    (fun s => by simp [step, execSyscall, Misc.execUnknown])
    (fun s hex => by simp [step, execSyscall, Misc.execUnknown]; exact hex)
    (fun s => by simp [step, execSyscall, Misc.execUnknown])
    (fun s => by simp [step, execSyscall, Misc.execUnknown])
    r0Old


end SVM.SBPF
