-- Baked sysvar-cache buffers for the generic `sol_get_sysvar` syscall.
--
-- agave's `SyscallGetSysvar` serves slices of the BINCODE-serialized sysvars in
-- the sysvar cache (exactly seven: clock, epoch_schedule, epoch_rewards, rent,
-- slot_hashes, stake_history, last_restart_slot; else in-band `SYSVAR_NOT_FOUND`).
-- Contents are the MOLLUSK DEFAULTS (`Sysvars::default()`), pinned against
-- `bincode::serialize` in `qedsvm-rs/tests/sysvar_buffer_pins.rs` so a default
-- bump fails in Rust rather than silently diverging the model.
--
-- NOTE bincode layouts (no padding), NOT the repr(C) layouts the typed getters
-- write: e.g. EpochSchedule is 33 bytes here vs 40 there.

import SVM.SBPF.Machine

namespace SVM.SBPF
namespace SysvarData

/-- `n` zero bytes (local copy; `zerosByteArray` lives downstream). -/
def zeros (n : Nat) : ByteArray := ⟨Array.replicate n 0⟩

/-! ## Sysvar ids (32-byte pubkeys, from `solana_sdk_ids::sysvar`) -/

/-- `SysvarC1ock11111111111111111111111111111111` -/
def clockId : ByteArray :=
  ⟨#[0x06, 0xa7, 0xd5, 0x17, 0x18, 0xc7, 0x74, 0xc9,
     0x28, 0x56, 0x63, 0x98, 0x69, 0x1d, 0x5e, 0xb6,
     0x8b, 0x5e, 0xb8, 0xa3, 0x9b, 0x4b, 0x6d, 0x5c,
     0x73, 0x55, 0x5b, 0x21, 0x00, 0x00, 0x00, 0x00]⟩

/-- `SysvarEpochSchedu1e111111111111111111111111` -/
def epochScheduleId : ByteArray :=
  ⟨#[0x06, 0xa7, 0xd5, 0x17, 0x18, 0xdc, 0x3f, 0xee,
     0x02, 0xd3, 0xe4, 0x7f, 0x01, 0x00, 0xf8, 0xb0,
     0x54, 0xf7, 0x94, 0x2e, 0x60, 0x59, 0x1e, 0x3f,
     0x50, 0x87, 0x19, 0xa8, 0x05, 0x00, 0x00, 0x00]⟩

/-- `SysvarEpochRewards1111111111111111111111111` -/
def epochRewardsId : ByteArray :=
  ⟨#[0x06, 0xa7, 0xd5, 0x17, 0x18, 0xdc, 0x3f, 0xee,
     0x02, 0xa5, 0x58, 0xbf, 0x83, 0xce, 0x66, 0xe1,
     0x44, 0x42, 0x2a, 0x1c, 0x34, 0x95, 0x0b, 0x27,
     0xc1, 0x86, 0x9b, 0x5a, 0x9c, 0x00, 0x00, 0x00]⟩

/-- `SysvarRent111111111111111111111111111111111` -/
def rentId : ByteArray :=
  ⟨#[0x06, 0xa7, 0xd5, 0x17, 0x19, 0x2c, 0x5c, 0x51,
     0x21, 0x8c, 0xc9, 0x4c, 0x3d, 0x4a, 0xf1, 0x7f,
     0x58, 0xda, 0xee, 0x08, 0x9b, 0xa1, 0xfd, 0x44,
     0xe3, 0xdb, 0xd9, 0x8a, 0x00, 0x00, 0x00, 0x00]⟩

/-- `SysvarS1otHashes111111111111111111111111111` -/
def slotHashesId : ByteArray :=
  ⟨#[0x06, 0xa7, 0xd5, 0x17, 0x19, 0x2f, 0x0a, 0xaf,
     0xc6, 0xf2, 0x65, 0xe3, 0xfb, 0x77, 0xcc, 0x7a,
     0xda, 0x82, 0xc5, 0x29, 0xd0, 0xbe, 0x3b, 0x13,
     0x6e, 0x2d, 0x00, 0x55, 0x20, 0x00, 0x00, 0x00]⟩

/-- `SysvarStakeHistory1111111111111111111111111` -/
def stakeHistoryId : ByteArray :=
  ⟨#[0x06, 0xa7, 0xd5, 0x17, 0x19, 0x35, 0x84, 0xd0,
     0xfe, 0xed, 0x9b, 0xb3, 0x43, 0x1d, 0x13, 0x20,
     0x6b, 0xe5, 0x44, 0x28, 0x1b, 0x57, 0xb8, 0x56,
     0x6c, 0xc5, 0x37, 0x5f, 0xf4, 0x00, 0x00, 0x00]⟩

/-- `SysvarLastRestartS1ot1111111111111111111111` -/
def lastRestartSlotId : ByteArray :=
  ⟨#[0x06, 0xa7, 0xd5, 0x17, 0x19, 0x06, 0xdd, 0xe1,
     0xcd, 0x3f, 0x94, 0x7d, 0xca, 0xb4, 0xc8, 0xf4,
     0xf4, 0xf5, 0x1b, 0xad, 0x0f, 0x98, 0x13, 0xb8,
     0x00, 0xd2, 0x89, 0x47, 0x1f, 0xc0, 0x00, 0x00]⟩

/-! ## Serialized buffers (mollusk defaults, bincode) -/

/-- `Clock::default()`: 5 zero u64/i64 fields = 40 zero bytes. -/
def clockBuf : ByteArray := zeros 40

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

/-- `Rent::default()`: `lamports_per_byte_year = 3480` (0x0D98),
    `exemption_threshold = 2.0` (f64 bits `0x4000_0000_0000_0000`),
    `burn_percent = 50`. 17 bytes. -/
def rentBuf : ByteArray :=
  ⟨#[0x98, 0x0d, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x40,
     0x32]⟩

/-- Mollusk default `SlotHashes`: 512 × `(slot 0, Hash::default())`. bincode `Vec`:
    8-byte LE length (0x200) + 512 × 40 zeros = 20488 bytes, all zero except
    `buf[1] = 0x02`. Built via `setIfInBounds` on `replicate`, NOT `#[..] ++
    replicate` (whose whnf model is a quadratic `Array.push` chain). -/
def slotHashesBuf : ByteArray :=
  ⟨(Array.replicate 20488 0).setIfInBounds 1 0x02⟩

/-- Mollusk default `StakeHistory`: one `(epoch 0, default())`. bincode `Vec`:
    8-byte LE length (1) + 32 zeros = 40 bytes. -/
def stakeHistoryBuf : ByteArray :=
  ⟨#[0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
    ++ Array.replicate 32 0⟩

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
  show ((Array.replicate 20488 (0 : UInt8)).setIfInBounds 1 0x02).size = 20488
  rw [Array.size_setIfInBounds, Array.size_replicate]

-- Sealed: `slotHashesBuf`'s logical value whnf-evaluates via the QUADRATIC
-- `Array.push` model (~2×10⁸ steps), timing out any simp/whnf that wanders into a
-- `sysvarBuffer` branch (e.g. `execSyscall_preserves_*`). Compiled code
-- (runner, native_decide) is unaffected. Use the evaluation lemmas above.
attribute [irreducible] sysvarBuffer slotHashesBuf

end SysvarData
end SVM.SBPF
