-- Sysvar-getter syscalls: fill the buffer at `*r1` with the sysvar's
-- mainnet-default contents. Most (clock, epoch_schedule, …) zero-fill. Rent does
-- NOT: SPL Token feeds its real fields (lamports_per_byte_year=3480,
-- exemption_threshold=2.0, burn_percent=50) into a software-f64 `is_exempt`,
-- which executes a different instruction count than zero-values — the cross-engine
-- CU diff against mollusk depends on matching it. All getters charge base 100.

import SVM.SBPF.Machine

namespace SVM.SBPF
namespace Sysvar

/-- Base CU `sysvar_base_cost = 100`. Typed getters charge `base + size_of::<T>()`
    (agave's `get_sysvar`), where `size_of` is the full repr-padded layout, not
    minimal field bytes. -/
def cu : Nat := 100

/-- `sol_get_sysvar` (SIMD-0127) CU: `100 + 32/250 (=0) + max(len/250, 10)`,
    len = r4 (agave `SyscallGetSysvar`). -/
@[simp] def cuGetSysvar (s : State) : Nat :=
  cu + Nat.max (s.regs.r4 / 250) 10

/-- Per-sysvar CU = `base + size_of::<T>()`, with trailing padding (e.g. `Rent`
    is 24 bytes, not 17). Mirrors `agave-syscalls::sysvar::get_sysvar`. -/
@[simp] def cuClock          : Nat := cu + 40
@[simp] def cuRent           : Nat := cu + 24
@[simp] def cuEpochSchedule  : Nat := cu + 40
@[simp] def cuLastRestartSlot : Nat := cu + 8
@[simp] def cuFees           : Nat := cu + 8
@[simp] def cuEpochRewards   : Nat := cu + 81

/-- Zero `n` bytes at `*r1`, r0 := 0. H6: `guardWrite r1 n` region-checks the
    output (agave's `translate_type_mut`) before filling; a plain `if`, so it
    unfolds + `repeat' split`s in the Bounded sweeps (MemOps pattern), `@[simp]`. -/
@[simp] def zeroFillR1 (s : State) (n : Nat) : State :=
  let outA := s.regs.r1
  s.guardWrite outA n fun s =>
    let mem' : Memory.Mem := fun a =>
      if a ≥ outA ∧ a - outA < n then 0 else s.mem a
    { s with regs := s.regs.set .r0 0, mem := mem' }

/-- `sol_get_clock_sysvar`: 40 bytes
    (slot, epoch_start_ts, epoch, leader_epoch, unix_ts). -/
@[simp] def execClock          (s : State) : State := zeroFillR1 s 40

/-- `sol_get_rent_sysvar`: write the 17-byte mainnet-default `Rent` at `*r1`. LE:
      [0..8)   lamports_per_byte_year : u64 = 3480 (0xD98)
      [8..16)  exemption_threshold    : f64 = 2.0  (bits 0x4000_0000_0000_0000)
      [16]     burn_percent           : u8  = 50
    Must be real, not zero: SPL Token's software-f64 `is_exempt` runs a different
    instruction count on these vs zero, and agave sees them, so CU equality needs it. -/
-- H6: `guardWrite r1 17` region-checks the output before filling. NOT `@[simp]`:
-- the 17-byte `if`-chain `mem'` chokes the blanket Execute sweeps (simp can't push
-- field projections through the big record); the `@[simp]` field lemmas below +
-- `execRent_regs_of_k`/`_mem_lt` close those sweeps with `execRent` folded.
def execRent           (s : State) : State :=
  let outA := s.regs.r1
  s.guardWrite outA 17 fun s =>
    -- Byte-by-byte: the address-keyed `if` chain stays decidable without `writeU64`'s axioms.
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
/-- `sol_get_epoch_schedule_sysvar`: 40 bytes (repr-padded), mollusk default
    `EpochSchedule::without_warmup()`. Layout:
    ```
    [0..8)   slots_per_epoch              : u64 LE = 432_000
    [8..16)  leader_schedule_slot_offset  : u64 LE = 432_000
    [16]     warmup                        : u8 = 0
    [17..24) padding                       : 7 zero bytes
    [24..32) first_normal_epoch            : u64 LE = 0
    [32..40) first_normal_slot             : u64 LE = 0
    ```
    432_000 = 0x69780 → LE `[0x80, 0x97, 0x06, 0, 0, 0, 0, 0]`. -/
-- H6: `guardWrite r1 40`; same de-simp treatment as `execRent` (multi-`if` `mem'`),
-- closed by the `@[simp]` field lemmas + `execEpochSchedule_regs_of_k`/`_mem_lt`.
def execEpochSchedule  (s : State) : State :=
  let outA := s.regs.r1
  s.guardWrite outA 40 fun s =>
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

/-- Fault direction for the `zeroFillR1` getters (clock / last_restart_slot / fees
    / epoch_rewards): a non-empty output `[r1,n)` outside a writable region traps.
    H6 model-side boundary pin; complements the cross-engine `oob_clock_sysvar.so`. -/
theorem zeroFillR1_faults_oob (s : State) (n : Nat) (hne : n ≠ 0)
    (hoob : s.regions.containsWritable s.regs.r1 n = false) :
    (zeroFillR1 s n).vmError = some .accessViolation := by
  simp only [zeroFillR1, State.guardWrite]
  rw [if_neg (by
    rintro (h | h)
    · exact hne h
    · rw [hoob] at h; exact absurd h (by decide))]
  rfl

/-- Companion to `zeroFillR1_faults_oob`: the same out-of-region output pins the
    `exitCode` sentinel (guardWrite sets both). Lets a `cuTripleFaultsWithin`
    corollary discharge its exitCode AND vmError conjuncts (used by the lifted
    clock/last_restart_slot/fees/epoch_rewards getters). -/
theorem zeroFillR1_faults_oob_exitCode (s : State) (n : Nat) (hne : n ≠ 0)
    (hoob : s.regions.containsWritable s.regs.r1 n = false) :
    (zeroFillR1 s n).exitCode = some ERR_ACCESS_VIOLATION := by
  simp only [zeroFillR1, State.guardWrite]
  rw [if_neg (by
    rintro (h | h)
    · exact hne h
    · rw [hoob] at h; exact absurd h (by decide))]
  rfl

/-! `execRent`/`execEpochSchedule` field lemmas (they're not `@[simp]`; their
multi-`if` `mem'` chokes the blanket sweeps). These + the `regs_of_k` closers
discharge the sweeps with the exec folded. -/

@[simp] theorem execRent_callStack (s : State) :
    (execRent s).callStack = s.callStack := by
  simp only [execRent]; exact State.guardWrite_proj_eq_of_k (·.callStack) s _ _ _ rfl rfl
@[simp] theorem execRent_regions (s : State) :
    (execRent s).regions = s.regions := by
  simp only [execRent]; exact State.guardWrite_proj_eq_of_k (·.regions) s _ _ _ rfl rfl
@[simp] theorem execRent_cuBudget (s : State) :
    (execRent s).cuBudget = s.cuBudget := by
  simp only [execRent]; exact State.guardWrite_proj_eq_of_k (·.cuBudget) s _ _ _ rfl rfl
@[simp] theorem execRent_heapNext (s : State) :
    (execRent s).heapNext = s.heapNext := by
  simp only [execRent]; exact State.guardWrite_proj_eq_of_k (·.heapNext) s _ _ _ rfl rfl
@[simp] theorem execRent_returnData (s : State) :
    (execRent s).returnData = s.returnData := by
  simp only [execRent]; exact State.guardWrite_proj_eq_of_k (·.returnData) s _ _ _ rfl rfl
@[simp] theorem execRent_r10 (s : State) :
    (execRent s).regs.r10 = s.regs.r10 := by
  simp only [execRent]
  exact State.guardWrite_proj_eq_of_k (·.regs.r10) s _ _ _ rfl
    (RegFile.set_preserves_r10 s.regs .r0 0)
theorem execRent_regs_of_k {motive : RegFile → Prop} (s : State)
    (h0 : motive s.regs) (hk : motive (s.regs.set .r0 0)) :
    motive (execRent s).regs := by
  simp only [execRent]
  apply State.guardWrite_regs_of_k (motive := motive) (h0 := h0); exact hk
theorem execRent_faults_oob (s : State)
    (hoob : s.regions.containsWritable s.regs.r1 17 = false) :
    (execRent s).vmError = some .accessViolation := by
  simp only [execRent, State.guardWrite]
  rw [if_neg (by
    rintro (h | h)
    · exact absurd h (by decide)
    · rw [hoob] at h; exact absurd h (by decide))]
  rfl

/-- Companion to `execRent_faults_oob`: the same out-of-region output pins the
    `exitCode` sentinel (guardWrite sets both). Discharges the exitCode conjunct
    of the lifted rent getter's `cuTripleFaultsWithinMem` corollary. -/
theorem execRent_faults_oob_exitCode (s : State)
    (hoob : s.regions.containsWritable s.regs.r1 17 = false) :
    (execRent s).exitCode = some ERR_ACCESS_VIOLATION := by
  simp only [execRent, State.guardWrite]
  rw [if_neg (by
    rintro (h | h)
    · exact absurd h (by decide)
    · rw [hoob] at h; exact absurd h (by decide))]
  rfl

@[simp] theorem execEpochSchedule_callStack (s : State) :
    (execEpochSchedule s).callStack = s.callStack := by
  simp only [execEpochSchedule]; exact State.guardWrite_proj_eq_of_k (·.callStack) s _ _ _ rfl rfl
@[simp] theorem execEpochSchedule_regions (s : State) :
    (execEpochSchedule s).regions = s.regions := by
  simp only [execEpochSchedule]; exact State.guardWrite_proj_eq_of_k (·.regions) s _ _ _ rfl rfl
@[simp] theorem execEpochSchedule_cuBudget (s : State) :
    (execEpochSchedule s).cuBudget = s.cuBudget := by
  simp only [execEpochSchedule]; exact State.guardWrite_proj_eq_of_k (·.cuBudget) s _ _ _ rfl rfl
@[simp] theorem execEpochSchedule_heapNext (s : State) :
    (execEpochSchedule s).heapNext = s.heapNext := by
  simp only [execEpochSchedule]; exact State.guardWrite_proj_eq_of_k (·.heapNext) s _ _ _ rfl rfl
@[simp] theorem execEpochSchedule_returnData (s : State) :
    (execEpochSchedule s).returnData = s.returnData := by
  simp only [execEpochSchedule]; exact State.guardWrite_proj_eq_of_k (·.returnData) s _ _ _ rfl rfl
@[simp] theorem execEpochSchedule_r10 (s : State) :
    (execEpochSchedule s).regs.r10 = s.regs.r10 := by
  simp only [execEpochSchedule]
  exact State.guardWrite_proj_eq_of_k (·.regs.r10) s _ _ _ rfl
    (RegFile.set_preserves_r10 s.regs .r0 0)
theorem execEpochSchedule_regs_of_k {motive : RegFile → Prop} (s : State)
    (h0 : motive s.regs) (hk : motive (s.regs.set .r0 0)) :
    motive (execEpochSchedule s).regs := by
  simp only [execEpochSchedule]
  apply State.guardWrite_regs_of_k (motive := motive) (h0 := h0); exact hk
theorem execEpochSchedule_faults_oob (s : State)
    (hoob : s.regions.containsWritable s.regs.r1 40 = false) :
    (execEpochSchedule s).vmError = some .accessViolation := by
  simp only [execEpochSchedule, State.guardWrite]
  rw [if_neg (by
    rintro (h | h)
    · exact absurd h (by decide)
    · rw [hoob] at h; exact absurd h (by decide))]
  rfl

/-- `sol_get_epoch_stake`: r1 = `*const Pubkey` vote account.
    Returns 0 in r0 (no stake modeled). -/
@[simp] def execEpochStake (s : State) : State :=
  { s with regs := s.regs.set .r0 0 }

end Sysvar
end SVM.SBPF
