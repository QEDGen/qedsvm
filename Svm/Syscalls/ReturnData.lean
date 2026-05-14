-- Return-data syscalls: `sol_set_return_data`, `sol_get_return_data`.
-- Both use `State.returnData` as backing storage.

import Svm.SBPF.Machine

namespace Svm.SBPF
namespace ReturnData

/-- `sol_set_return_data(ptr, len)`: `syscall_base_cost (100) +
    len / cpi_bytes_per_unit (250)`. Source:
    `blueshift/sbpf/crates/runtime/src/syscalls/return_data.rs:19-23`. -/
@[simp] def cuSet (s : State) : Nat := 100 + s.regs.r2 / 250

/-- `sol_get_return_data(out, max_len, pubkey_out)`: `syscall_base_cost
    (100) + (min(max_len, data_len) + 32) / cpi_bytes_per_unit (250)`
    when the copy length is non-zero — else just the base. Source:
    `blueshift/sbpf/crates/runtime/src/syscalls/return_data.rs:52-66`. -/
@[simp] def cuGet (s : State) : Nat :=
  let copyLen := Nat.min s.regs.r2 s.returnData.size
  if copyLen = 0 then 100
  else 100 + (copyLen + 32) / 250

/-- `sol_set_return_data(ptr, len)`: replace returnData with `ptr[..len]`. -/
@[simp] def execSet (s : State) : State :=
  let ptr := s.regs.r1
  let len := s.regs.r2
  { s with regs := s.regs.set .r0 0
           returnData := readBytes s.mem ptr len }

/-- `sol_get_return_data(out, maxLen, pubkeyOut)`. Copies up to
    `maxLen` bytes of returnData to `*out`, writes 32 zero-bytes
    (program-id placeholder; not tracked) to `*pubkeyOut`. Returns the
    ACTUAL length (not the truncated length) in r0. -/
@[simp] def execGet (s : State) : State :=
  let outA    := s.regs.r1
  let maxLen  := s.regs.r2
  let pkA     := s.regs.r3
  let dataLen := s.returnData.size
  let copyLen := if dataLen ≤ maxLen then dataLen else maxLen
  let mem' : Memory.Mem := fun a =>
    if a ≥ outA ∧ a - outA < copyLen then
      (s.returnData.get! (a - outA)).toNat
    else if a ≥ pkA ∧ a - pkA < 32 then 0
    else s.mem a
  { s with regs := s.regs.set .r0 dataLen, mem := mem' }

end ReturnData
end Svm.SBPF
