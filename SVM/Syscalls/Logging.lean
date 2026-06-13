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
-- - `sol_log_compute_units_`: emits `Program consumption: <remaining>
--    units remaining` where `remaining = State.cuBudget - cuConsumed`
--    (saturating to 0). Matches agave's `stable_log::program_compute_units`
--    body byte-for-byte modulo the "Program consumption: " prefix
--    that `stable_log` would prepend.
-- - `sol_log_data`: reads the array of `SliceDesc { ptr, len }`
--    descriptors at r1 (count r2) and emits each slice base64-encoded
--    (RFC 4648, with `=` padding), joined by single-space. Matches
--    agave's `stable_log::program_data` body byte-for-byte modulo the
--    "Program data: " prefix that `stable_log` would prepend.

import SVM.SBPF.Machine

namespace SVM.SBPF
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

/-- Standard base64 alphabet (RFC 4648): `A-Z` `a-z` `0-9` `+` `/`. -/
private def base64Char (n : Nat) : Char :=
  if n < 26       then Char.ofNat (n + 0x41)            -- 'A'..'Z'
  else if n < 52  then Char.ofNat (n - 26 + 0x61)       -- 'a'..'z'
  else if n < 62  then Char.ofNat (n - 52 + 0x30)       -- '0'..'9'
  else if n = 62  then '+'
  else                 '/'

/-- Standard base64 encoding with `=` padding (RFC 4648). Three input
    bytes → four output chars; trailing 1 or 2 bytes are emitted with
    one or two `=` pads respectively. Matches agave's
    `bs58::engine::general_purpose::STANDARD` default that
    `sol_log_data` uses (debug-helper formatter, not a primitive). -/
partial def base64Encode (bs : ByteArray) : String :=
  let n := bs.size
  let rec go (i : Nat) (acc : String) : String :=
    if i + 3 ≤ n then
      let b0 := (bs.get! i).toNat
      let b1 := (bs.get! (i + 1)).toNat
      let b2 := (bs.get! (i + 2)).toNat
      let acc := acc.push (base64Char (b0 / 4))
                    |>.push (base64Char ((b0 % 4) * 16 + b1 / 16))
                    |>.push (base64Char ((b1 % 16) * 4 + b2 / 64))
                    |>.push (base64Char (b2 % 64))
      go (i + 3) acc
    else if i + 2 = n then
      let b0 := (bs.get! i).toNat
      let b1 := (bs.get! (i + 1)).toNat
      acc.push (base64Char (b0 / 4))
        |>.push (base64Char ((b0 % 4) * 16 + b1 / 16))
        |>.push (base64Char ((b1 % 16) * 4))
        |>.push '='
    else if i + 1 = n then
      let b0 := (bs.get! i).toNat
      acc.push (base64Char (b0 / 4))
        |>.push (base64Char ((b0 % 4) * 16))
        |>.push '='
        |>.push '='
    else
      acc
  go 0 ""

/-! ## Bodies -/

/-- `sol_log_(ptr, len)`: log the byte slice verbatim, set r0 = 0.
    H6: agave's `translate_string_and_do` reads `[ptr, ptr+len)` via
    `translate_slice` (Load); out of region traps with `AccessViolation`,
    `len = 0` is allowed. -/
@[simp] def execLog (s : State) : State :=
  let ptr := s.regs.r1
  let len := s.regs.r2
  s.guardRead ptr len fun s =>
    { s with regs := s.regs.set .r0 0
             log  := s.log.push (readBytes s.mem ptr len) }

/-- `sol_log_pubkey(ptr)`: log 32 bytes from `*r1`, set r0 = 0.
    H6: agave reads the 32-byte pubkey via `translate_type::<Pubkey>`
    (Load, fixed size, always checked); out of region traps with
    `AccessViolation`. -/
@[simp] def execLogPubkey (s : State) : State :=
  let ptr := s.regs.r1
  s.guardRead ptr 32 fun s =>
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

/-- `sol_log_compute_units_`: emit "Program consumption: <remaining>
    units remaining" with `remaining = State.cuBudget - cuConsumed`
    (saturating to 0 if `cuConsumed` already exceeds the budget — Nat
    subtraction). Matches agave's `stable_log::program_compute_units`
    body. -/
@[simp] def execLogComputeUnits (s : State) : State :=
  let remaining := s.cuBudget - s.cuConsumed
  let msg := "Program consumption: " ++ natToDec remaining ++ " units remaining"
  { s with regs := s.regs.set .r0 0
           log  := s.log.push msg.toUTF8 }

/-- `sol_log_data(fields_ptr, count)`: read the `count`-long array of
    `SliceDesc { u64 ptr, u64 len }` descriptors at r1, dereference
    each, and emit base64-encoded slices joined by single space.

    Matches agave's `stable_log::program_data` body byte-for-byte
    modulo the "Program data: " prefix that `stable_log` would
    prepend (we store raw message bodies, no prefix).

    H6: agave reads the descriptor array `[r1, r1 + count*16)` via
    `translate_slice::<VmSlice<u8>>` (Load), then dereferences each
    descriptor's slice `[ptr, ptr+len)` via `translate_vm_slice` (Load).
    Both routes are region-checked, so an out-of-region descriptor array
    OR any out-of-region slice traps with `AccessViolation`. The model
    mirrors this: `guardRead` on the descriptor array, then `guardSlices`
    over the per-descriptor slices. (Unlike the single-slice log syscalls
    this read region cannot be surfaced as an `rr : RegionTable → Prop`
    side-condition — the per-slice ranges are read FROM memory the
    precondition does not own — so `sol_log_data` keeps no register-only
    happy-path triple; the boundary is pinned by the `oob_log_data.so`
    diff fixture and `execLogData_faults_oob` below.)

    NOT `@[simp]`: unfolding it re-exposes the recursive `guardSlices` walk that
    blanket syscall `simp` sweeps cannot discharge (and blew `guardSlices_eq`'s
    own elaboration up to ~10GB before that proof was de-simp'd). Specs that
    need the body unfold it explicitly with `simp only [execLogData]`; the
    field-preservation `@[simp]` lemmas below keep it folded for the sweeps. -/
def execLogData (s : State) : State :=
  let descsAddr := s.regs.r1
  let count     := s.regs.r2
  s.guardRead descsAddr (count * 16) fun s =>
    s.guardSlices descsAddr count fun s =>
      let fields : Array ByteArray :=
        (List.range count).foldl (fun acc i =>
          let descAddr := descsAddr + i * 16
          let ptr := Memory.readU64 s.mem descAddr
          let len := Memory.readU64 s.mem (descAddr + 8)
          acc.push (readBytes s.mem ptr len)) #[]
      let joined : String :=
        fields.foldl (fun acc bs =>
          if acc.isEmpty then base64Encode bs
          else acc ++ " " ++ base64Encode bs) ""
      { s with regs := s.regs.set .r0 0
               log  := s.log.push joined.toUTF8 }

/-- `execLogData` never writes memory (it only reads slices and pushes to
    the log), so its `mem` is unchanged whether it faults or succeeds. The
    `Bounded` `mem_lt` sweep closes the `sol_log_data` arm with this. -/
theorem execLogData_mem (s : State) : (execLogData s).mem = s.mem := by
  simp only [execLogData]
  apply State.guardRead_mem_eq_of_k; intro s'
  apply State.guardSlices_mem_eq_of_k; intro s''
  rfl

/-- `execLogData` only ever rewrites `regs` (to set `r0`) and pushes to `log`;
    every other `State` field is preserved on BOTH the fault branch
    (`accessFault`) and the success branch. `@[simp]` so the blanket
    `execSyscall_preserves_*` (Execute.lean) and
    `execSyscall_{callStack,cuBudget,heapNext_le,returnData_le}` (Bounded.lean)
    sweeps discharge the `sol_log_data` arm with `execLogData` left FOLDED —
    each is a two-line `guardRead`/`guardSlices` projection collapse. -/
@[simp] theorem execLogData_preserves_callStack (s : State) :
    (execLogData s).callStack = s.callStack := by
  simp only [execLogData]
  refine State.guardRead_proj_eq_of_k (·.callStack) s _ _ _ rfl ?_
  exact State.guardSlices_proj_eq_of_k (·.callStack) s _ _ _ rfl rfl

@[simp] theorem execLogData_preserves_regions (s : State) :
    (execLogData s).regions = s.regions := by
  simp only [execLogData]
  refine State.guardRead_proj_eq_of_k (·.regions) s _ _ _ rfl ?_
  exact State.guardSlices_proj_eq_of_k (·.regions) s _ _ _ rfl rfl

@[simp] theorem execLogData_preserves_cuBudget (s : State) :
    (execLogData s).cuBudget = s.cuBudget := by
  simp only [execLogData]
  refine State.guardRead_proj_eq_of_k (·.cuBudget) s _ _ _ rfl ?_
  exact State.guardSlices_proj_eq_of_k (·.cuBudget) s _ _ _ rfl rfl

@[simp] theorem execLogData_preserves_heapNext (s : State) :
    (execLogData s).heapNext = s.heapNext := by
  simp only [execLogData]
  refine State.guardRead_proj_eq_of_k (·.heapNext) s _ _ _ rfl ?_
  exact State.guardSlices_proj_eq_of_k (·.heapNext) s _ _ _ rfl rfl

@[simp] theorem execLogData_preserves_returnData (s : State) :
    (execLogData s).returnData = s.returnData := by
  simp only [execLogData]
  refine State.guardRead_proj_eq_of_k (·.returnData) s _ _ _ rfl ?_
  exact State.guardSlices_proj_eq_of_k (·.returnData) s _ _ _ rfl rfl

@[simp] theorem execLogData_preserves_r10 (s : State) :
    (execLogData s).regs.r10 = s.regs.r10 := by
  simp only [execLogData]
  refine State.guardRead_proj_eq_of_k (·.regs.r10) s _ _ _ rfl ?_
  refine State.guardSlices_proj_eq_of_k (·.regs.r10) s _ _ _ rfl ?_
  exact RegFile.set_preserves_r10 s.regs .r0 0

/-- `execLogData` either faults (leaving `regs = s.regs`) or sets only `r0`.
    `Bounded`'s `regs_lt` sweep closes the `sol_log_data` arm via this. -/
theorem execLogData_regs_of_k {motive : RegFile → Prop} (s : State)
    (h0 : motive s.regs) (hk : motive (s.regs.set .r0 0)) :
    motive (execLogData s).regs := by
  simp only [execLogData]
  apply State.guardRead_regs_of_k (motive := motive) (h0 := h0)
  apply State.guardSlices_regs_of_k (motive := motive) (h0 := h0)
  exact hk

/-- Fault direction (replaces the now-false unconditional happy-path
    triple): when the descriptor array `[r1, r1 + r2*16)` is not within any
    mapped region (and is non-empty), `sol_log_data` traps with a typed
    access violation. The contrapositive of the `guardRead` on the
    descriptor array; complements the cross-engine `oob_log_data.so` pin. -/
theorem execLogData_faults_oob (s : State)
    (hne : s.regs.r2 ≠ 0)
    (hoob : s.regions.containsRange s.regs.r1 (s.regs.r2 * 16) = false) :
    (execLogData s).vmError = some .accessViolation := by
  simp only [execLogData, State.guardRead]
  rw [if_neg (by
    rintro (h | h)
    · exact hne (by omega)
    · rw [hoob] at h; exact absurd h (by decide))]
  rfl

/-- Shared body retained for backwards compatibility — pushes an
    empty marker. No longer called from the dispatcher; kept so older
    proofs referencing it elsewhere don't break (none currently do).
    Will be removed once the deprecation grace period elapses. -/
@[simp] def execLogMarker (s : State) : State :=
  { s with regs := s.regs.set .r0 0
           log  := s.log.push ByteArray.empty }

end Logging
end SVM.SBPF
