-- Return-data syscalls (`sol_{set,get}_return_data`), backed by `State.returnData`.

import SVM.SBPF.Machine

namespace SVM.SBPF
namespace ReturnData

/-- `sol_set_return_data` CU: `100 + len/250`. Source:
    `blueshift/sbpf/crates/runtime/src/syscalls/return_data.rs:19-23`. -/
@[simp] def cuSet (s : State) : Nat := 100 + s.regs.r2 / 250

/-- `sol_get_return_data` CU: `100 + (min(max_len,data_len) + 32)/250` when copy
    length > 0, else just 100. Source:
    `blueshift/sbpf/crates/runtime/src/syscalls/return_data.rs:52-66`. -/
@[simp] def cuGet (s : State) : Nat :=
  let copyLen := Nat.min s.regs.r2 s.returnData.size
  if copyLen = 0 then 100
  else 100 + (copyLen + 32) / 250

/-- `sol_set_return_data(ptr, len)`: set returnData := `ptr[..len]` and record the
    caller as setter (agave stores the `(program_id, data)` pair). Fails closed for
    `len > MAX_RETURN_DATA` (1024), matching `ReturnDataTooLarge` (H7). -/
@[simp] def execSet (s : State) : State :=
  let ptr := s.regs.r1
  let len := s.regs.r2
  if len > MAX_RETURN_DATA then
    { s with exitCode := some ERR_RETURN_DATA_TOO_LARGE, vmError := some .returnDataTooLarge }
  else
    -- H6: after the length check, guardRead the input slice `[ptr, ptr+len)`
    -- (single slice → plain `if`, MemOps pattern; no mem write).
    s.guardRead ptr len fun s =>
      { s with regs := s.regs.set .r0 0
               returnData := readBytes s.mem ptr len
               returnDataProgId := s.progIdBytes }

/-- Fault direction for `sol_set_return_data`: a non-empty in-limit input slice
    `[r1, r1+r2)` out of region traps with a typed access violation. -/
theorem execSet_faults_oob (s : State)
    (hle : s.regs.r2 ≤ MAX_RETURN_DATA) (hne : s.regs.r2 ≠ 0)
    (hoob : s.regions.containsRange s.regs.r1 s.regs.r2 = false) :
    (execSet s).vmError = some .accessViolation := by
  simp only [execSet, State.guardRead]
  rw [if_neg (Nat.not_lt.mpr hle), if_neg (by
    rintro (h | h)
    · exact hne h
    · rw [hoob] at h; exact absurd h (by decide))]
  rfl

/-- Companion to `execSet_faults_oob`: the same out-of-region input slice pins
    the `exitCode` sentinel (guardRead sets both). Discharges the exitCode
    conjunct of the lifted setter's `cuTripleFaultsWithinMem` corollary. -/
theorem execSet_faults_oob_exitCode (s : State)
    (hle : s.regs.r2 ≤ MAX_RETURN_DATA) (hne : s.regs.r2 ≠ 0)
    (hoob : s.regions.containsRange s.regs.r1 s.regs.r2 = false) :
    (execSet s).exitCode = some ERR_ACCESS_VIOLATION := by
  simp only [execSet, State.guardRead]
  rw [if_neg (Nat.not_lt.mpr hle), if_neg (by
    rintro (h | h)
    · exact hne h
    · rw [hoob] at h; exact absurd h (by decide))]
  rfl

/-- `sol_get_return_data(out, maxLen, pubkeyOut)`: r0 := ACTUAL returnData length
    (not truncated). When `copyLen = min maxLen dataLen ≠ 0`, copy `copyLen` bytes
    to `*out` and the setter's 32-byte program id to `*pubkeyOut`; when 0, write
    NOTHING (agave guards both copies behind `if length != 0`). H7: previously
    wrote a fabricated 32-zero pubkey even when `copyLen = 0`. -/
@[simp] def execGet (s : State) : State :=
  let outA    := s.regs.r1
  let maxLen  := s.regs.r2
  let pkA     := s.regs.r3
  let dataLen := s.returnData.size
  let copyLen := if dataLen ≤ maxLen then dataLen else maxLen
  if copyLen = 0 then
    { s with regs := s.regs.set .r0 dataLen }
  else
    -- H6: when copyLen>0, guardWrite both the data output `[r1,+copyLen)` and
    -- the 32-byte program-id output `[r3,+32)`.
    s.guardWrite outA copyLen fun s =>
    s.guardWrite pkA 32 fun s =>
      let mem' : Memory.Mem := fun a =>
        if a ≥ outA ∧ a - outA < copyLen then
          (s.returnData.get! (a - outA)).toNat
        else if a ≥ pkA ∧ a - pkA < 32 then
          (s.returnDataProgId.get! (a - pkA)).toNat
        else s.mem a
      { s with regs := s.regs.set .r0 dataLen, mem := mem' }

/-- Fault direction for `sol_get_return_data`: a non-empty copy whose data output
    `[r1, r1+copyLen)` (`copyLen = min(dataLen,maxLen)`) is not in a writable region
    traps — the data-buffer guardWrite fires before the program-id write. -/
theorem execGet_faults_oob (s : State)
    (hne : (if s.returnData.size ≤ s.regs.r2 then s.returnData.size else s.regs.r2) ≠ 0)
    (hoob : s.regions.containsWritable s.regs.r1
              (if s.returnData.size ≤ s.regs.r2 then s.returnData.size else s.regs.r2)
            = false) :
    (execGet s).vmError = some .accessViolation := by
  simp only [execGet, State.guardWrite]
  rw [if_neg hne, if_neg (by
    rintro (h | h)
    · exact hne h
    · rw [hoob] at h; exact absurd h (by decide))]
  rfl

end ReturnData
end SVM.SBPF
