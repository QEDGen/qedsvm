-- The default environment's sysvar-cache buffers, as literals for lifts to name
-- (`molluskDefaults_bincode` below ties them to `SysvarEnv.molluskDefaults`).
--
-- agave's `SyscallGetSysvar` serves slices of the BINCODE-serialized sysvars in
-- the sysvar cache (exactly seven: clock, epoch_schedule, epoch_rewards, rent,
-- slot_hashes, stake_history, last_restart_slot; else in-band `SYSVAR_NOT_FOUND`).
-- Contents are the MOLLUSK DEFAULTS (`Mollusk::default().sysvars`, agave 4.3), pinned against
-- `bincode::serialize` in `qedsvm-rs/tests/sysvar_buffer_pins.rs` so a default
-- bump fails in Rust rather than silently diverging the model.
--
-- NOTE bincode layouts (no padding), NOT the repr(C) layouts the typed getters
-- write: e.g. EpochSchedule is 33 bytes here vs 40 there.

import SVM.SBPF.Machine
import SVM.Syscalls.SysvarEnv

namespace SVM.SBPF
namespace SysvarData

/-- `n` zero bytes (local copy; `zerosByteArray` lives downstream). -/
def zeros (n : Nat) : ByteArray := ⟨Array.replicate n 0⟩

/-! ## Serialized buffers (mollusk defaults, bincode) -/

/-- Mollusk default `Clock`: `slot = 1` (`DEFAULT_CLOCK_SLOT`), the other four
    u64/i64 fields 0. 40 bytes. -/
def clockBuf : ByteArray :=
  ⟨#[0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] ++ Array.replicate 32 0⟩

/-- `EpochSchedule::without_warmup()`: slots_per_epoch = leader_schedule_slot_offset
    = 432_000 (0x69780 → LE `80 97 06 ..`), warmup = false, rest 0. bincode bool is
    ONE byte (33 total, vs the typed getter's 40-byte repr(C)). -/
def epochScheduleBuf : ByteArray :=
  ⟨#[0x80, 0x97, 0x06, 0x00, 0x00, 0x00, 0x00, 0x00,
     0x80, 0x97, 0x06, 0x00, 0x00, 0x00, 0x00, 0x00,
     0x00] ++ Array.replicate 16 0⟩

/-- `EpochRewards::default()` (active = false): 81 zero bytes
    (u64 + u64 + 32-byte hash + u128 + u64 + u64 + bool). -/
def epochRewardsBuf : ByteArray := zeros 81

/-- `Rent::default()` (SIMD-0194): `lamports_per_byte = 6960` (0x1B30),
    `exemption_threshold = 1.0` (f64 bits `0x3FF0_0000_0000_0000`),
    `burn_percent = 50`. 17 bytes. -/
def rentBuf : ByteArray :=
  ⟨#[0x30, 0x1b, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xf0, 0x3f,
     0x32]⟩

/-- Mollusk default `SlotHashes`. -/
def slotHashesBuf : ByteArray := SysvarEnv.defaultSlotHashes

/-- Mollusk default `StakeHistory`. -/
def stakeHistoryBuf : ByteArray := SysvarEnv.defaultStakeHistory

/-- `LastRestartSlot::default()`: one zero u64. -/
def lastRestartSlotBuf : ByteArray := zeros 8

/-- Sysvar cache: 32-byte id → serialized buffer (agave's `sysvar_id_to_buffer`).
    Anything outside these seven is `none` → `SYSVAR_NOT_FOUND = 2` in-band. -/
def sysvarBuffer (id : ByteArray) : Option ByteArray :=
  if      id == clockId           then some clockBuf
  else if id == epochScheduleId   then some epochScheduleBuf
  else if id == epochRewardsId    then some epochRewardsBuf
  else if id == rentId            then some rentBuf
  else if id == slotHashesId      then some slotHashesBuf
  else if id == stakeHistoryId    then some stakeHistoryBuf
  else if id == lastRestartSlotId then some lastRestartSlotBuf
  else none

/-! ## Evaluation lemmas

Proved by `rfl` BEFORE the irreducible seal below (the `rfl`s force only the
32-byte id comparisons, never the buffer contents). Call sites rewrite with these. -/

@[simp] theorem sysvarBuffer_clock :
    sysvarBuffer clockId = some clockBuf := rfl
@[simp] theorem sysvarBuffer_epochSchedule :
    sysvarBuffer epochScheduleId = some epochScheduleBuf := rfl
@[simp] theorem sysvarBuffer_epochRewards :
    sysvarBuffer epochRewardsId = some epochRewardsBuf := rfl
@[simp] theorem sysvarBuffer_rent :
    sysvarBuffer rentId = some rentBuf := rfl
@[simp] theorem sysvarBuffer_slotHashes :
    sysvarBuffer slotHashesId = some slotHashesBuf := rfl
@[simp] theorem sysvarBuffer_stakeHistory :
    sysvarBuffer stakeHistoryId = some stakeHistoryBuf := rfl
@[simp] theorem sysvarBuffer_lastRestartSlot :
    sysvarBuffer lastRestartSlotId = some lastRestartSlotBuf := rfl

/-- `slotHashesBuf.size`, recorded before sealing (the `execGetSysvar` OOB branch
    compares against it). By rewriting, not evaluation: whnf of a 20488-element
    array blows `maxRecDepth`. -/
@[simp] theorem slotHashesBuf_size : slotHashesBuf.size = 20488 := by
  unfold slotHashesBuf SysvarEnv.defaultSlotHashes
  show ((Array.replicate 20488 (0 : UInt8)).setIfInBounds 1 0x02).size = 20488
  rw [Array.size_setIfInBounds, Array.size_replicate]

/-! ## The Mollusk-defaults instance

The literals above are the default environment's encodings. -/

theorem molluskDefaults_clock : SysvarEnv.molluskDefaults.clock.reprC = clockBuf := by decide
theorem molluskDefaults_rent : SysvarEnv.molluskDefaults.rent.bincode = rentBuf := by decide
theorem molluskDefaults_epochSchedule :
    SysvarEnv.molluskDefaults.epochSchedule.bincode = epochScheduleBuf := by decide
theorem molluskDefaults_epochRewards :
    SysvarEnv.molluskDefaults.epochRewards.bincode = epochRewardsBuf := by decide
theorem molluskDefaults_lastRestartSlot :
    SysvarEnv.molluskDefaults.lastRestartBytes = lastRestartSlotBuf := by decide

/-- The builtin buffers are the Mollusk-defaults instance of the environment. -/
theorem molluskDefaults_bincode (id : ByteArray) :
    SysvarEnv.molluskDefaults.bincode id = sysvarBuffer id := by
  unfold SysvarEnv.bincode sysvarBuffer
  rw [molluskDefaults_clock, molluskDefaults_rent, molluskDefaults_epochSchedule,
    molluskDefaults_epochRewards, molluskDefaults_lastRestartSlot]
  rfl

/-- The default environment's rent, as the lift's literal. -/
@[simp] theorem molluskDefaults_bincode_rent :
    SysvarEnv.molluskDefaults.bincode rentId = some rentBuf := by
  rw [SysvarEnv.bincode_rent, molluskDefaults_rent]

-- Sealed for the reason given on `SysvarEnv.defaultSlotHashes`.
attribute [irreducible] sysvarBuffer slotHashesBuf

end SysvarData
end SVM.SBPF
