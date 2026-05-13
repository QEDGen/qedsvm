-- Sysvar-getter syscalls: zero-fill the output buffer at `*r1` to a
-- length appropriate for the sysvar layout. Real values vary per
-- slot/epoch and aren't tracked; zero is the safe default that lets
-- dependent programs continue. CU charge is `sysvar_base_cost = 100`
-- for all of them.

import Svm.SBPF.Machine

namespace Svm.SBPF
namespace Sysvar

/-- Shared CU charge: `sysvar_base_cost = 100`. -/
def cu : Nat := 100

/-- Build a state where `n` bytes at `*r1` are zeroed and r0 := 0. -/
@[simp] def zeroFillR1 (s : State) (n : Nat) : State :=
  let outA := s.regs.r1
  let mem' : Memory.Mem := fun a =>
    if a ≥ outA ∧ a - outA < n then 0 else s.mem a
  { s with regs := s.regs.set .r0 0, mem := mem' }

/-- `sol_get_clock_sysvar`: 40 bytes
    (slot, epoch_start_ts, epoch, leader_epoch, unix_ts). -/
@[simp] def execClock          (s : State) : State := zeroFillR1 s 40
/-- `sol_get_rent_sysvar`: 17 bytes
    (lamports_per_byte_year, exemption_threshold, burn_percent). -/
@[simp] def execRent           (s : State) : State := zeroFillR1 s 17
/-- `sol_get_epoch_schedule_sysvar`: 33 bytes. -/
@[simp] def execEpochSchedule  (s : State) : State := zeroFillR1 s 33
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
end Svm.SBPF
