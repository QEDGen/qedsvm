-- Solana logging syscalls: `sol_log_`, `sol_log_pubkey`, `sol_log_64_`,
-- `sol_log_compute_units_`, `sol_log_data`.
--
-- Side effect: push a `ByteArray` entry onto `State.log`. We keep
-- the bytes verbatim for `sol_log_` and `sol_log_pubkey`; the other
-- three push an empty marker since their formatted encoding is TODO.

import Svm.SBPF.Machine

namespace Svm.SBPF
namespace Logging

/-! ## CU charges (agave's `SVMTransactionExecutionCost::default()`). -/

/-- `sol_log_`: `max(syscall_base_cost = 100, message_length / cpi_bytes_per_unit)`.
    Per agave: `syscall_base_cost.max(message_byte_count / cpi_bytes_per_unit)`
    where `cpi_bytes_per_unit = 250`. Messages under 25_000 bytes round to 0,
    so the floor of 100 always wins for typical `msg!()` calls; the
    division is what makes very large logs still tractable. -/
@[simp] def cuLog (s : State) : Nat := Nat.max 100 (s.regs.r2 / 250)
/-- `sol_log_64_units`. -/
def cuLog64 : Nat := 100
/-- `sol_log_compute_units` baseline (`syscall_base_cost`). -/
def cuLogComputeUnits : Nat := 100
/-- `log_pubkey_units`. -/
def cuLogPubkey : Nat := 100
/-- Approximation for `sol_log_data` (real cost is per-field variable). -/
def cuLogData : Nat := 100

/-! ## Bodies -/

/-- `sol_log_(ptr, len)`: log the byte slice verbatim, set r0 = 0. -/
@[simp] def execLog (s : State) : State :=
  let ptr := s.regs.r1
  let len := s.regs.r2
  { s with regs := s.regs.set .r0 0
           log  := s.log.push (readBytes s.mem ptr len) }

/-- `sol_log_pubkey(ptr)`: log 32 bytes from `*r1`, set r0 = 0. -/
@[simp] def execLogPubkey (s : State) : State :=
  let ptr := s.regs.r1
  { s with regs := s.regs.set .r0 0
           log  := s.log.push (readBytes s.mem ptr 32) }

/-- Shared body for `sol_log_64_`, `sol_log_compute_units_`, and
    `sol_log_data` — push an empty marker; r0 = 0. -/
@[simp] def execLogMarker (s : State) : State :=
  { s with regs := s.regs.set .r0 0
           log  := s.log.push ByteArray.empty }

end Logging
end Svm.SBPF
