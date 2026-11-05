-- Sysvar-getter syscalls: write the mollusk-default (agave 4.3) sysvar contents
-- at `*r1`. Clock carries mollusk's `DEFAULT_CLOCK_SLOT = 1`. Rent is real: SPL
-- Token feeds its fields (SIMD-0194: lamports_per_byte=6960,
-- exemption_threshold=1.0, burn_percent=50) into `is_exempt`, which executes a
-- different instruction count per threshold value, so the cross-engine CU diff
-- against mollusk depends on matching it. All getters charge base 100.

import SVM.SBPF.Machine
import SVM.Syscalls.SysvarData

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
@[simp] def cuEpochRewards   : Nat := cu + 96

/-- `sol_get_epoch_stake` CU (SIMD-0133): `syscall_base` on a null `r1`, else
    `syscall_base + 32/250 (=0) + mem_op_base`. -/
@[simp] def cuEpochStake (s : State) : Nat :=
  if s.regs.r1 = 0 then cu else cu + 10

/-- A typed getter's check-then-write, agave's `get_sysvar` after its charge:
    the output must lie below the input region
    (`syscall_parameter_address_restrictions`, active under `all_enabled()`),
    `[r1, r1+size)` must be writable, and `r1` aligned for `T`. Then `bytes` is
    written and r0 := 0. agave checks alignment on the host pointer; host
    buffers are allocated aligned and regions start at aligned virtual
    addresses, so this checks the virtual address, as `MemOps.execCmp` does. -/
@[simp] def execTyped (align size : Nat) (bytes : ByteArray) (s : State) : State :=
  let outA := s.regs.r1
  if outA ≥ Memory.INPUT_START then s.accessFault
  else s.guardWrite outA size fun s =>
  if outA % align ≠ 0 then
    { s with exitCode := some ERR_UNALIGNED_POINTER, vmError := some .unalignedPointer }
  else
    let mem' : Memory.Mem := fun a =>
      if a ≥ outA ∧ a - outA < size then (bytes.get! (a - outA)).toNat else s.mem a
    { s with regs := s.regs.set .r0 0, mem := mem' }

/-- Mollusk default `Clock`, `repr(C)`: same layout as its bincode. -/
def clockBytes : ByteArray := SysvarData.clockBuf
/-- Mollusk default `Rent`, `repr(C)`: the 17 field bytes, then 7 zeroed padding. -/
def rentBytes : ByteArray := SysvarData.rentBuf ++ SysvarData.zeros 7
/-- `EpochSchedule::without_warmup()`, `repr(C)`, with the `warmup` bool's padding
    (bincode has none). 432_000 = 0x69780 LE `[0x80, 0x97, 0x06, ..]`. -/
def epochScheduleBytes : ByteArray :=
  ⟨#[0x80, 0x97, 0x06, 0, 0, 0, 0, 0, 0x80, 0x97, 0x06, 0, 0, 0, 0, 0] ++ Array.replicate 24 0⟩

@[simp] def execClock (s : State) : State := execTyped 8 40 clockBytes s
@[simp] def execRent (s : State) : State := execTyped 8 24 rentBytes s
@[simp] def execEpochSchedule (s : State) : State := execTyped 8 40 epochScheduleBytes s
/-- `sol_get_last_restart_slot`: u64. -/
@[simp] def execLastRestartSlot (s : State) : State := execTyped 8 8 (SysvarData.zeros 8) s
/-- `sol_get_epoch_rewards_sysvar`: `repr(C, align(16))`, so 96 bytes aligned to 16
    (active = false: all zero). -/
@[simp] def execEpochRewards (s : State) : State := execTyped 16 96 (SysvarData.zeros 96) s

/-- A typed getter's output outside a writable region faults, whichever check
    catches it. Complements the cross-engine `oob_*_sysvar.so`. -/
theorem execTyped_faults_oob (align size : Nat) (bytes : ByteArray) (s : State) (hne : size ≠ 0)
    (hoob : s.regions.containsWritable s.regs.r1 size = false) :
    (execTyped align size bytes s).vmError = some .accessViolation ∧
    (execTyped align size bytes s).exitCode = some ERR_ACCESS_VIOLATION := by
  simp only [execTyped, State.guardWrite, State.accessFault]
  split
  · exact ⟨rfl, rfl⟩
  · rw [if_neg (by
      rintro (h | h)
      · exact hne h
      · rw [hoob] at h; exact absurd h (by decide))]
    exact ⟨rfl, rfl⟩

/-- `sol_get_epoch_stake`, r1 = `*const Pubkey` vote account. Null returns the
    total stake, else the account's stake once the key is readable. No stake is
    modeled, so both are 0. -/
@[simp] def execEpochStake (s : State) : State :=
  if s.regs.r1 = 0 then { s with regs := s.regs.set .r0 0 }
  else s.guardRead s.regs.r1 32 fun s => { s with regs := s.regs.set .r0 0 }

end Sysvar
end SVM.SBPF
