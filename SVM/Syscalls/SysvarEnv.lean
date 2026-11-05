-- The sysvars a program can read, as an environment (#105).
--
-- `s.regions.sysvars` holds it, so a proof states which environment it assumes
-- as an ordinary `rr` clause (`rt.sysvars = env`) and the region table's
-- immutability (`executeFn_preserves_regions`) carries that through a run. Proofs
-- that read no sysvar hold for every environment.
--
-- Two layouts come out of one environment: the typed getters write `reprC`
-- (Rust's `repr(C)`, padding zeroed) and `sol_get_sysvar` serves `bincode` (no
-- padding), so a warped clock reads the same through both.

namespace SVM.SBPF

namespace SysvarData

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

end SysvarData

/-- `width` little-endian bytes of `n`. Each byte reduces mod 256, so the encoders
    need no bound on a field. -/
def leBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | w + 1, n => UInt8.ofNat n :: leBytes w (n / 256)

private def boolByte (b : Bool) : List UInt8 := [if b then 1 else 0]

/-- `n` zero bytes. -/
private def pad (n : Nat) : List UInt8 := List.replicate n 0

/-- `Clock`. i64 fields hold their u64 two's complement. -/
structure ClockEnv where
  slot : Nat
  epochStartTimestamp : Nat
  epoch : Nat
  leaderScheduleEpoch : Nat
  unixTimestamp : Nat

/-- `Clock`'s 40 bytes: `repr(C)` and bincode agree. -/
def ClockEnv.reprC (c : ClockEnv) : ByteArray :=
  ⟨⟨leBytes 8 c.slot ++ leBytes 8 c.epochStartTimestamp ++ leBytes 8 c.epoch ++
    leBytes 8 c.leaderScheduleEpoch ++ leBytes 8 c.unixTimestamp⟩⟩

/-- `Rent`. -/
structure RentEnv where
  lamportsPerByte : Nat
  exemptionThresholdBits : Nat
  burnPercent : Nat

private def RentEnv.fields (r : RentEnv) : List UInt8 :=
  leBytes 8 r.lamportsPerByte ++ leBytes 8 r.exemptionThresholdBits ++ leBytes 1 r.burnPercent

/-- `size_of::<Rent>() = 24`: the 17 field bytes, then zeroed padding. -/
def RentEnv.reprC (r : RentEnv) : ByteArray := ⟨⟨r.fields ++ pad 7⟩⟩
def RentEnv.bincode (r : RentEnv) : ByteArray := ⟨⟨r.fields⟩⟩

/-- `EpochSchedule`. -/
structure EpochScheduleEnv where
  slotsPerEpoch : Nat
  leaderScheduleSlotOffset : Nat
  warmup : Bool
  firstNormalEpoch : Nat
  firstNormalSlot : Nat

/-- `size_of::<EpochSchedule>() = 40`: 7 padding bytes follow the bool. -/
def EpochScheduleEnv.reprC (e : EpochScheduleEnv) : ByteArray :=
  ⟨⟨leBytes 8 e.slotsPerEpoch ++ leBytes 8 e.leaderScheduleSlotOffset ++ boolByte e.warmup ++
    pad 7 ++ leBytes 8 e.firstNormalEpoch ++ leBytes 8 e.firstNormalSlot⟩⟩

/-- 33 bytes: bincode has no padding. -/
def EpochScheduleEnv.bincode (e : EpochScheduleEnv) : ByteArray :=
  ⟨⟨leBytes 8 e.slotsPerEpoch ++ leBytes 8 e.leaderScheduleSlotOffset ++ boolByte e.warmup ++
    leBytes 8 e.firstNormalEpoch ++ leBytes 8 e.firstNormalSlot⟩⟩

/-- `EpochRewards`. `parentBlockhash` is its 32 bytes, as a little-endian `Nat`. -/
structure EpochRewardsEnv where
  distributionStartingBlockHeight : Nat
  numPartitions : Nat
  parentBlockhash : Nat
  totalPoints : Nat
  totalRewards : Nat
  distributedRewards : Nat
  active : Bool

private def EpochRewardsEnv.fields (e : EpochRewardsEnv) : List UInt8 :=
  leBytes 8 e.distributionStartingBlockHeight ++ leBytes 8 e.numPartitions ++
    leBytes 32 e.parentBlockhash ++ leBytes 16 e.totalPoints ++ leBytes 8 e.totalRewards ++
    leBytes 8 e.distributedRewards ++ boolByte e.active

/-- `repr(C, align(16))`, so `size_of::<EpochRewards>() = 96`. -/
def EpochRewardsEnv.reprC (e : EpochRewardsEnv) : ByteArray := ⟨⟨e.fields ++ pad 15⟩⟩
def EpochRewardsEnv.bincode (e : EpochRewardsEnv) : ByteArray := ⟨⟨e.fields⟩⟩

/-- The sysvars and epoch stake a program can read. `fees` is absent: its getter is
    unregistered under `all_enabled()`. -/
structure SysvarEnv where
  clock : ClockEnv
  rent : RentEnv
  epochSchedule : EpochScheduleEnv
  epochRewards : EpochRewardsEnv
  lastRestartSlot : Nat
  /-- Served only by `sol_get_sysvar`, so kept as their bincode. -/
  slotHashes : ByteArray
  stakeHistory : ByteArray
  totalStake : Nat
  /-- Stake per vote account. A key not listed has none. -/
  voteStake : List (ByteArray × Nat)

/-- `sol_get_epoch_stake`'s answer for a vote account: 0 if it isn't one. -/
def SysvarEnv.stakeOf (env : SysvarEnv) (vote : ByteArray) : Nat :=
  match env.voteStake.find? (fun e => e.1 == vote) with
  | some e => e.2
  | none => 0

/-- `last_restart_slot`'s 8 bytes: `repr(C)` and bincode agree. -/
def SysvarEnv.lastRestartBytes (env : SysvarEnv) : ByteArray :=
  ⟨⟨leBytes 8 env.lastRestartSlot⟩⟩

/-- agave's `sysvar_id_to_buffer`: id to bincode. Anything outside these seven is
    `none`, which `sol_get_sysvar` reports in-band as `SYSVAR_NOT_FOUND`. -/
def SysvarEnv.bincode (env : SysvarEnv) (id : ByteArray) : Option ByteArray :=
  if      id == SysvarData.clockId           then some env.clock.reprC
  else if id == SysvarData.epochScheduleId   then some env.epochSchedule.bincode
  else if id == SysvarData.epochRewardsId    then some env.epochRewards.bincode
  else if id == SysvarData.rentId            then some env.rent.bincode
  else if id == SysvarData.slotHashesId      then some env.slotHashes
  else if id == SysvarData.stakeHistoryId    then some env.stakeHistory
  else if id == SysvarData.lastRestartSlotId then some env.lastRestartBytes
  else none

/-! ## Encoding sizes -/

@[simp] theorem leBytes_length (w n : Nat) : (leBytes w n).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [leBytes, ih]

private theorem size_mk (l : List UInt8) : (ByteArray.mk (Array.mk l)).size = l.length := rfl

@[simp] theorem ClockEnv.reprC_size (c : ClockEnv) : c.reprC.size = 40 := by
  simp [ClockEnv.reprC, size_mk]
@[simp] theorem RentEnv.reprC_size (r : RentEnv) : r.reprC.size = 24 := by
  simp [RentEnv.reprC, RentEnv.fields, size_mk, pad]
@[simp] theorem EpochScheduleEnv.reprC_size (e : EpochScheduleEnv) : e.reprC.size = 40 := by
  simp [EpochScheduleEnv.reprC, size_mk, pad, boolByte]
@[simp] theorem EpochRewardsEnv.reprC_size (e : EpochRewardsEnv) : e.reprC.size = 96 := by
  simp [EpochRewardsEnv.reprC, EpochRewardsEnv.fields, size_mk, pad, boolByte]
@[simp] theorem SysvarEnv.lastRestartBytes_size (env : SysvarEnv) :
    env.lastRestartBytes.size = 8 := by
  simp [SysvarEnv.lastRestartBytes, size_mk]

/-! Evaluation lemmas, proved before the seal below. Call sites rewrite with these. -/

@[simp] theorem SysvarEnv.bincode_clock (env : SysvarEnv) :
    env.bincode SysvarData.clockId = some env.clock.reprC := rfl
@[simp] theorem SysvarEnv.bincode_epochSchedule (env : SysvarEnv) :
    env.bincode SysvarData.epochScheduleId = some env.epochSchedule.bincode := rfl
@[simp] theorem SysvarEnv.bincode_epochRewards (env : SysvarEnv) :
    env.bincode SysvarData.epochRewardsId = some env.epochRewards.bincode := rfl
@[simp] theorem SysvarEnv.bincode_rent (env : SysvarEnv) :
    env.bincode SysvarData.rentId = some env.rent.bincode := rfl
@[simp] theorem SysvarEnv.bincode_slotHashes (env : SysvarEnv) :
    env.bincode SysvarData.slotHashesId = some env.slotHashes := rfl
@[simp] theorem SysvarEnv.bincode_stakeHistory (env : SysvarEnv) :
    env.bincode SysvarData.stakeHistoryId = some env.stakeHistory := rfl
@[simp] theorem SysvarEnv.bincode_lastRestartSlot (env : SysvarEnv) :
    env.bincode SysvarData.lastRestartSlotId = some env.lastRestartBytes := rfl

/-- Mollusk default `SlotHashes`: 512 × `(slot 0, Hash::default())`. bincode `Vec`:
    8-byte LE length (0x200) + 512 × 40 zeros = 20488 bytes, all zero except
    `buf[1] = 0x02`. Built via `setIfInBounds` on `replicate`, NOT `#[..] ++
    replicate` (whose whnf model is a quadratic `Array.push` chain). -/
def SysvarEnv.defaultSlotHashes : ByteArray :=
  ⟨(Array.replicate 20488 0).setIfInBounds 1 0x02⟩

/-- Mollusk default `StakeHistory`: one `(epoch 0, default())`. bincode `Vec`:
    8-byte LE length (1) + 32 zeros = 40 bytes. -/
def SysvarEnv.defaultStakeHistory : ByteArray :=
  ⟨#[0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] ++ Array.replicate 32 0⟩

/-- `Mollusk::default().sysvars` (agave 4.3) with no epoch stake: clock at
    `DEFAULT_CLOCK_SLOT = 1`, SIMD-0194 rent (6960, f64 bits of 1.0, 50),
    `EpochSchedule::without_warmup()` (432_000 slots), default rewards. Pinned
    against mollusk in `qedsvm-rs/tests/sysvar_buffer_pins.rs`. -/
def SysvarEnv.molluskDefaults : SysvarEnv where
  clock := ⟨1, 0, 0, 0, 0⟩
  rent := ⟨6960, 0x3FF0000000000000, 50⟩
  epochSchedule := ⟨432000, 432000, false, 0, 0⟩
  epochRewards := ⟨0, 0, 0, 0, 0, 0, false⟩
  lastRestartSlot := 0
  slotHashes := SysvarEnv.defaultSlotHashes
  stakeHistory := SysvarEnv.defaultStakeHistory
  totalStake := 0
  voteStake := []

instance : Inhabited SysvarEnv := ⟨SysvarEnv.molluskDefaults⟩

-- Sealed: `defaultSlotHashes`'s logical value whnf-evaluates via the QUADRATIC
-- `Array.push` model (~2×10⁸ steps), timing out any simp/whnf that wanders into a
-- `bincode` branch (e.g. `execSyscall_preserves_*`). Compiled code (runner,
-- native_decide) is unaffected. Use the evaluation lemmas above.
attribute [irreducible] SysvarEnv.bincode SysvarEnv.defaultSlotHashes

/-! ## Wire format

`qedsvm_run_with_sysvars` takes the environment as bytes: u32-LE-length-prefixed
bincode for clock, rent, epoch schedule, epoch rewards, last restart slot, slot
hashes and stake history, then the total stake (u64) and a u32 count of
`(32-byte vote key, u64 stake)` entries. -/

/-- The little-endian `Nat` of `b[off, off+width)`. -/
def SysvarEnv.leRead (b : ByteArray) (off : Nat) : Nat → Nat
  | 0 => 0
  | w + 1 => (b.get! off).toNat + 256 * SysvarEnv.leRead b (off + 1) w

private def readChunk (b : ByteArray) (off : Nat) : Option (ByteArray × Nat) :=
  let len := SysvarEnv.leRead b off 4
  let start := off + 4
  if start + len ≤ b.size then some (b.extract start (start + len), start + len) else none

private def readBool (b : ByteArray) (off : Nat) : Option Bool :=
  match (b.get! off).toNat with
  | 0 => some false
  | 1 => some true
  | _ => none

private def readVoteStake (b : ByteArray) : Nat → Nat → Option (List (ByteArray × Nat))
  | 0, off => if off = b.size then some [] else none
  | n + 1, off =>
    if off + 40 ≤ b.size then do
      let rest ← readVoteStake b n (off + 40)
      some ((b.extract off (off + 32), SysvarEnv.leRead b (off + 32) 8) :: rest)
    else none

/-- Parse the wire format. `none` on any malformed field, which the FFI reports
    rather than running under a default. -/
def SysvarEnv.ofWire (b : ByteArray) : Option SysvarEnv := do
  let (clock, off) ← readChunk b 0
  let (rent, off) ← readChunk b off
  let (schedule, off) ← readChunk b off
  let (rewards, off) ← readChunk b off
  let (restart, off) ← readChunk b off
  let (slotHashes, off) ← readChunk b off
  let (stakeHistory, off) ← readChunk b off
  guard (clock.size = 40 ∧ rent.size = 17 ∧ schedule.size = 33 ∧ rewards.size = 81 ∧
    restart.size = 8 ∧ off + 12 ≤ b.size)
  let le := SysvarEnv.leRead
  let warmup ← readBool schedule 16
  let active ← readBool rewards 80
  let voteStake ← readVoteStake b (le b (off + 8) 4) (off + 12)
  some
    { clock := ⟨le clock 0 8, le clock 8 8, le clock 16 8, le clock 24 8, le clock 32 8⟩
      rent := ⟨le rent 0 8, le rent 8 8, le rent 16 1⟩
      epochSchedule := ⟨le schedule 0 8, le schedule 8 8, warmup, le schedule 17 8, le schedule 25 8⟩
      epochRewards := ⟨le rewards 0 8, le rewards 8 8, le rewards 16 32, le rewards 48 16,
        le rewards 64 8, le rewards 72 8, active⟩
      lastRestartSlot := le restart 0 8
      slotHashes := slotHashes
      stakeHistory := stakeHistory
      totalStake := le b off 8
      voteStake := voteStake }

end SVM.SBPF
