-- Sysvar-getter syscalls: fill the output buffer at `*r1` with the
-- canonical mainnet-default contents of the sysvar. Most sysvars
-- (clock, epoch_schedule, last_restart_slot, …) zero-fill — their
-- real values vary per slot/epoch and zero is a safe default that
-- lets dependent programs continue. Rent is *not* zero-filled,
-- because real programs (notably SPL Token) feed its fields into
-- a software-f64 `is_exempt` computation; mainnet's
-- `lamports_per_byte_year=3480` / `exemption_threshold=2.0` /
-- `burn_percent=50` produce a different number of executed
-- instructions than the zero-value short-circuit, and the
-- cross-engine CU diff against mollusk depends on matching that
-- path. CU charge for all sysvar getters is `sysvar_base_cost = 100`.

import SVM.SBPF.Machine

namespace SVM.SBPF
namespace Sysvar

/-- Base CU charge: `sysvar_base_cost = 100`. The "typed" sysvar
    getters (`sol_get_clock_sysvar`, `sol_get_rent_sysvar`, …) charge
    `base + size_of::<T>()` per agave's `get_sysvar` helper in
    `agave-syscalls/src/sysvar.rs`. The runtime size_of is the
    Rust struct's full layout (with trailing padding), not the
    minimal field bytes. -/
def cu : Nat := 100

/-- Per-sysvar CU = `base + size_of::<T>()`. Rust `size_of` includes
    trailing alignment padding, so e.g. `Rent` (u64 + f64 + u8) is
    24 bytes, not 17. Mirrors
    `agave-syscalls::sysvar::get_sysvar`. -/
@[simp] def cuClock          : Nat := cu + 40
@[simp] def cuRent           : Nat := cu + 24
@[simp] def cuEpochSchedule  : Nat := cu + 40
@[simp] def cuLastRestartSlot : Nat := cu + 8
@[simp] def cuFees           : Nat := cu + 8
@[simp] def cuEpochRewards   : Nat := cu + 81

/-- Build a state where `n` bytes at `*r1` are zeroed and r0 := 0. -/
@[simp] def zeroFillR1 (s : State) (n : Nat) : State :=
  let outA := s.regs.r1
  let mem' : Memory.Mem := fun a =>
    if a ≥ outA ∧ a - outA < n then 0 else s.mem a
  { s with regs := s.regs.set .r0 0, mem := mem' }

/-- `sol_get_clock_sysvar`: 40 bytes
    (slot, epoch_start_ts, epoch, leader_epoch, unix_ts). -/
@[simp] def execClock          (s : State) : State := zeroFillR1 s 40

/-- `sol_get_rent_sysvar`: write the 17-byte mainnet-default `Rent`
    struct at `*r1`. Layout (LE):
      [0..8)   lamports_per_byte_year : u64 = 3480 (0xD98)
      [8..16)  exemption_threshold    : f64 = 2.0  (raw bits 0x4000_0000_0000_0000)
      [16]     burn_percent           : u8  = 50   (0x32)
    Constants mirror `solana_rent::DEFAULT_*` (still the values on
    mainnet at the time of writing). SPL Token's
    `Rent::is_exempt(lamports, data_len)` compiles to a software-f64
    `(data_len + 128) * lamports_per_byte_year * exemption_threshold`
    that takes a meaningfully different number of sBPF instructions
    on zero vs. non-zero inputs — agave's interpreter under
    `FeatureSet::all_enabled()` always sees the real values, so we
    must too for CU equality to hold. -/
@[simp] def execRent           (s : State) : State :=
  let outA := s.regs.r1
  -- Construct the 17 bytes byte-by-byte; the address-keyed `if`
  -- chain stays decidable for proofs without dragging in
  -- `writeU64`'s axioms.
  let mem' : Memory.Mem := fun a =>
    if      a = outA + 0  then 0x98  -- lamports_per_byte_year = 3480 = 0x0000_0000_0000_0D98
    else if a = outA + 1  then 0x0D
    else if a = outA + 2  then 0
    else if a = outA + 3  then 0
    else if a = outA + 4  then 0
    else if a = outA + 5  then 0
    else if a = outA + 6  then 0
    else if a = outA + 7  then 0
    else if a = outA + 8  then 0     -- exemption_threshold = 2.0 (f64 bits = 0x4000_0000_0000_0000)
    else if a = outA + 9  then 0
    else if a = outA + 10 then 0
    else if a = outA + 11 then 0
    else if a = outA + 12 then 0
    else if a = outA + 13 then 0
    else if a = outA + 14 then 0
    else if a = outA + 15 then 0x40
    else if a = outA + 16 then 50    -- burn_percent = 50
    else s.mem a
  { s with regs := s.regs.set .r0 0, mem := mem' }
/-- `sol_get_epoch_schedule_sysvar`: 40 bytes (`size_of::<EpochSchedule>()`
    with repr(C) alignment padding). Mollusk's default is
    `EpochSchedule::without_warmup()` — `slots_per_epoch =
    DEFAULT_SLOTS_PER_EPOCH = 432_000`, `leader_schedule_slot_offset =
    DEFAULT_LEADER_SCHEDULE_SLOT_OFFSET = 432_000`, `warmup = false`,
    `first_normal_epoch = 0`, `first_normal_slot = 0`. Layout:
    ```
    [0..8)   slots_per_epoch              : u64 LE = 432_000
    [8..16)  leader_schedule_slot_offset  : u64 LE = 432_000
    [16]     warmup                        : u8 = 0
    [17..24) padding                       : 7 bytes of zero
    [24..32) first_normal_epoch            : u64 LE = 0
    [32..40) first_normal_slot             : u64 LE = 0
    ```
    432_000 = 0x69780 → little-endian bytes `[0x80, 0x97, 0x06, 0, 0, 0, 0, 0]`. -/
@[simp] def execEpochSchedule  (s : State) : State :=
  let outA := s.regs.r1
  -- 432_000 = 0x69780 → 0x80, 0x97, 0x06 in LE; remaining 5 bytes zero.
  let mem' : Memory.Mem := fun a =>
    if      a = outA + 0  then 0x80
    else if a = outA + 1  then 0x97
    else if a = outA + 2  then 0x06
    else if a = outA + 3  then 0
    else if a = outA + 4  then 0
    else if a = outA + 5  then 0
    else if a = outA + 6  then 0
    else if a = outA + 7  then 0
    else if a = outA + 8  then 0x80
    else if a = outA + 9  then 0x97
    else if a = outA + 10 then 0x06
    else if a = outA + 11 then 0
    else if a = outA + 12 then 0
    else if a = outA + 13 then 0
    else if a = outA + 14 then 0
    else if a = outA + 15 then 0
    else if a ≥ outA + 16 ∧ a < outA + 40 then 0  -- warmup + padding + remaining u64s
    else s.mem a
  { s with regs := s.regs.set .r0 0, mem := mem' }
/-- `sol_get_last_restart_slot`: u64. -/
@[simp] def execLastRestartSlot (s : State) : State := zeroFillR1 s 8
/-- `sol_get_fees_sysvar` (deprecated): 8 bytes. -/
@[simp] def execFees           (s : State) : State := zeroFillR1 s 8
/-- `sol_get_epoch_rewards_sysvar`: 81 bytes (active = false). -/
@[simp] def execEpochRewards   (s : State) : State := zeroFillR1 s 81

/-- `sol_get_epoch_stake`: r1 = `*const Pubkey` vote account.
    Returns 0 in r0 (no stake modeled). -/
@[simp] def execEpochStake (s : State) : State :=
  { s with regs := s.regs.set .r0 0 }

end Sysvar
end SVM.SBPF
