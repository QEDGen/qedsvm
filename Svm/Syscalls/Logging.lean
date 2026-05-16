-- Solana logging syscalls: `sol_log_`, `sol_log_pubkey`, `sol_log_64_`,
-- `sol_log_compute_units_`, `sol_log_data`.
--
-- Side effect: push a `ByteArray` entry onto `State.log`. We keep
-- the bytes verbatim for `sol_log_` and `sol_log_pubkey`. For the
-- other three syscalls we now emit a formatted message body. The
-- formats are observable but diverge slightly from agave's
-- `stable_log` output:
--
-- - `sol_log_64_`: hex-formats r1..r5 as `0x<hex>, 0x<hex>, 0x<hex>,
--    0x<hex>, 0x<hex>`. Matches agave's `format!("{:#x}, {:#x},
--    {:#x}, {:#x}, {:#x}", a, b, c, d, e)` exactly modulo the leading
--    "Program log: " prefix that agave's `stable_log::program_log`
--    would add (we store raw message bodies, no prefix).
-- - `sol_log_compute_units_`: emits `Program consumption: <cuConsumed>
--    CU consumed`. Agave's wording is `<remaining> units remaining` —
--    we don't track `cuBudget` in `State`, so we report consumed
--    instead. Observable, just inverted.
-- - `sol_log_data`: reads the array of `SliceDesc { ptr, len }`
--    descriptors at r1 (count r2) and emits each slice hex-encoded,
--    joined by single-space. Agave emits base64; we emit hex because
--    Lean core has no base64 and dragging one in for a debug-only
--    syscall is over-investment. Observable and deterministic.

import Svm.SBPF.Machine

namespace Svm.SBPF
namespace Logging

/-! ## CU charges (agave's `SVMTransactionExecutionCost::default()`). -/

/-- `sol_log_`: `max(syscall_base_cost = 100, msg_len)`. Per agave's
    syscall (mirrored in `blueshift/sbpf::syscalls/log.rs::sol_log`):
    `compute.consume(costs.syscall_base_cost.max(msg_len))`. Note this is
    `max(BASE, msg_len)` — *not* `msg_len / cpi_bytes_per_unit`; only the
    memory-op and CPI paths divide by 250. -/
@[simp] def cuLog (s : State) : Nat := Nat.max 100 s.regs.r2
/-- `sol_log_64_units`. -/
def cuLog64 : Nat := 100
/-- `sol_log_compute_units` baseline (`syscall_base_cost`). -/
def cuLogComputeUnits : Nat := 100
/-- `log_pubkey_units`. -/
def cuLogPubkey : Nat := 100
/-- Approximation for `sol_log_data` (real cost is per-field variable). -/
def cuLogData : Nat := 100

/-! ## Formatting helpers (lowercase hex, decimal) -/

/-- One lowercase hex digit for `n < 16`. -/
private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (n + 0x30)        -- '0'..'9'
  else            Char.ofNat (n - 10 + 0x61)  -- 'a'..'f'

/-- Lowercase hex of a `Nat`, no padding, no `0x` prefix. `0 ↦ "0"`. -/
partial def natToHex (n : Nat) : String :=
  if n = 0 then "0"
  else
    let rec go (n : Nat) (acc : String) : String :=
      if n = 0 then acc
      else go (n / 16) (String.singleton (hexDigit (n % 16)) ++ acc)
    go n ""

/-- Two-digit lowercase hex of a `UInt8`. -/
private def byteToHex2 (b : UInt8) : String :=
  let n := b.toNat
  String.singleton (hexDigit (n / 16)) ++ String.singleton (hexDigit (n % 16))

/-- Hex-encode a `ByteArray` as a string of `2 * bs.size` chars. -/
def bytesToHex (bs : ByteArray) : String :=
  bs.foldl (fun acc b => acc ++ byteToHex2 b) ""

/-- Decimal of a `Nat`. Thin wrapper over `Nat.toDigits 10`. -/
private def natToDec (n : Nat) : String :=
  String.ofList (Nat.toDigits 10 n)

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

/-- `sol_log_64_(a, b, c, d, e)`: emit "0x<a>, 0x<b>, 0x<c>, 0x<d>,
    0x<e>" as the log message body. -/
@[simp] def execLog64 (s : State) : State :=
  let msg :=
    "0x" ++ natToHex s.regs.r1 ++ ", " ++
    "0x" ++ natToHex s.regs.r2 ++ ", " ++
    "0x" ++ natToHex s.regs.r3 ++ ", " ++
    "0x" ++ natToHex s.regs.r4 ++ ", " ++
    "0x" ++ natToHex s.regs.r5
  { s with regs := s.regs.set .r0 0
           log  := s.log.push msg.toUTF8 }

/-- `sol_log_compute_units_`: emit "Program consumption: <consumed>
    CU consumed". Agave reports `<remaining> units remaining`; we
    can't reconstruct `remaining` without `cuBudget` in `State`, so
    we report `cuConsumed` instead. Observable, format diverges. -/
@[simp] def execLogComputeUnits (s : State) : State :=
  let msg := "Program consumption: " ++ natToDec s.cuConsumed ++ " CU consumed"
  { s with regs := s.regs.set .r0 0
           log  := s.log.push msg.toUTF8 }

/-- `sol_log_data(fields_ptr, count)`: read the `count`-long array of
    `SliceDesc { u64 ptr, u64 len }` descriptors at r1, dereference
    each, and emit hex-encoded slices joined by single space.

    Format diverges from agave's `Program data: <base64> <base64> …`:
    we hex-encode (not base64) and emit raw bytes without the
    "Program data: " prefix that `stable_log::program_data` would
    add. Observable for differential debugging; not strict parity. -/
@[simp] def execLogData (s : State) : State :=
  let descsAddr := s.regs.r1
  let count     := s.regs.r2
  let fields : Array ByteArray :=
    (List.range count).foldl (fun acc i =>
      let descAddr := descsAddr + i * 16
      let ptr := Memory.readU64 s.mem descAddr
      let len := Memory.readU64 s.mem (descAddr + 8)
      acc.push (readBytes s.mem ptr len)) #[]
  let joined : String :=
    fields.foldl (fun acc bs =>
      if acc.isEmpty then bytesToHex bs
      else acc ++ " " ++ bytesToHex bs) ""
  { s with regs := s.regs.set .r0 0
           log  := s.log.push joined.toUTF8 }

/-- Shared body retained for backwards compatibility — pushes an
    empty marker. No longer called from the dispatcher; kept so older
    proofs referencing it elsewhere don't break (none currently do).
    Will be removed once the deprecation grace period elapses. -/
@[simp] def execLogMarker (s : State) : State :=
  { s with regs := s.regs.set .r0 0
           log  := s.log.push ByteArray.empty }

end Logging
end Svm.SBPF
