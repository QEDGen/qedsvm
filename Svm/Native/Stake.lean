-- The Solana Stake program — native (pre-Core-BPF migration).
--
-- Reference: agave's `solana-stake-program-2.2.4`
-- (`src/stake_instruction.rs`, 7471 lines + `src/stake_state.rs`,
-- 2974 lines) and `solana-stake-interface-1.2.1/src/state.rs`.
--
-- Stake migrated to Core BPF in current agave (see
-- `fetch-core-bpf.sh`: `stake 4.0.0 Stake11… BPFLoaderUpgradeab1e…`).
-- This module captures the pre-migration native semantics — the
-- canonical reference for the bulk of mainnet stake activity
-- pre-2024.
--
-- ## What this module ships
--
-- This is **Stake foundation** — state encoding + 8 of 18 variants:
--
-- Management variants (implemented):
--   * Initialize / InitializeChecked  — Uninitialized → Initialized(Meta)
--   * Authorize / AuthorizeChecked    — rotate Authorized.staker /
--                                        Authorized.withdrawer
--   * SetLockup / SetLockupChecked    — mutate Lockup
--   * GetMinimumDelegation            — return-data only
--   * Redelegate                       — agave returns
--                                        InvalidInstructionData
--                                        unconditionally; we mirror
--                                        with r0=1
--
-- Operational variants (decoded, dispatch returns r0=1 deferred):
--   * AuthorizeWithSeed / AuthorizeCheckedWithSeed
--   * DelegateStake / Deactivate / DeactivateDelinquent
--   * Split / Merge
--   * Withdraw
--   * MoveStake / MoveLamports
--
-- The operational variants depend on:
--   * Vote account inspection (DelegateStake reads voter_pubkey)
--   * StakeHistory sysvar (effective-stake calculation, warmup/cooldown)
--   * Rent sysvar (Split + Withdraw)
--   * Clock.epoch (activation_epoch / deactivation_epoch)
--   * The `Stake { delegation, credits_observed }` sub-struct
--   * Stake math (warmup/cooldown rates, MINIMUM_DELINQUENT_EPOCHS)
--
-- Each is tractable individually but the Lean encoding of the math
-- doubles the module size; we ship the management half here and
-- track operational closure as a follow-up bite (see
-- [[native-programs-design]]).
--
-- ## State layout (StakeStateV2)
--
-- bincode enum, u32 LE tag:
--   tag 0 Uninitialized          4 bytes
--   tag 1 Initialized(Meta)      108 = 4 + 104
--   tag 2 Stake(Meta, Stake, StakeFlags)
--                                  181 = 4 + 104 + 72 + 1
--   tag 3 RewardsPool            4 bytes
-- Stake accounts are fixed-size at 200 bytes
-- (`StakeStateV2::size_of()`); past the encoded state is zero/garbage.
--
-- ### Meta (104 bytes)
--   rent_exempt_reserve : u64               (8 bytes)
--   authorized          : Authorized        (64 bytes = staker(32) + withdrawer(32))
--   lockup              : Lockup            (48 bytes = ts(i64=8) + epoch(u64=8) + custodian(32))
--
-- ### Stake (72 bytes) — used only by readers in this module
--   delegation         : Delegation (64 = voter(32) + stake(8) + activation(8) + deactivation(8) + warmup_rate(f64=8))
--   credits_observed   : u64        (8)

import Svm.Native.AcctInput
import Svm.SBPF.Machine

namespace Svm.Native.Stake

open Svm.SBPF.Memory
open Svm.SBPF (writeBytes readBytes)
open Svm.Native

/-- Stake program-id (`Stake11111111111111111111111111111111111111`)
    as a little-endian `Nat`. Raw bytes
    `[0x06, 0xa1, 0xd8, 0x17, 0x91, 0x37, 0x54, 0x2a, 0x98, 0x34,
      0x37, 0xbd, 0xfe, 0x2a, 0x7a, 0xb2, 0x55, 0x7f, 0x53, 0x5c,
      0x8a, 0x78, 0x72, 0x2b, 0x68, 0xa4, 0x9d, 0xc0, 0x00, 0x00,
      0x00, 0x00]`. -/
def PROGRAM_ID : Nat :=
  0x00000000c09da4682b72788a5c537f55b27a2afebd3734982a54379117d8a106

def PROGRAM_ID_BYTES : ByteArray :=
  ⟨#[0x06, 0xa1, 0xd8, 0x17, 0x91, 0x37, 0x54, 0x2a,
     0x98, 0x34, 0x37, 0xbd, 0xfe, 0x2a, 0x7a, 0xb2,
     0x55, 0x7f, 0x53, 0x5c, 0x8a, 0x78, 0x72, 0x2b,
     0x68, 0xa4, 0x9d, 0xc0, 0x00, 0x00, 0x00, 0x00]⟩

/-- `DEFAULT_COMPUTE_UNITS` from
    `solana-stake-program-2.2.4/src/stake_instruction.rs:49`. Flat
    per-invocation charge. -/
def CU_DEFAULT : Nat := 750

/-- Fixed account-data size for any stake account
    (`StakeStateV2::size_of()`). -/
def STAKE_ACCOUNT_SIZE : Nat := 200

/-! ## State encoding

`StakeStateV2` discriminants + struct sizes. Offsets within each
variant's serialized form are exposed as constants because we read
+ write specific fields surgically (no full struct round-trip). -/

def TAG_UNINITIALIZED : Nat := 0
def TAG_INITIALIZED   : Nat := 1
def TAG_STAKE         : Nat := 2
def TAG_REWARDSPOOL   : Nat := 3

/-! ### Meta field offsets (relative to the start of the Meta payload,
    so add `4` for the enum tag when reading from the account data). -/

def META_RENT_EXEMPT_OFFSET    : Nat := 0      -- u64, 8 bytes
def META_AUTHORIZED_OFFSET     : Nat := 8      -- Authorized, 64 bytes
def META_STAKER_OFFSET         : Nat := 8      -- staker pubkey, 32 bytes
def META_WITHDRAWER_OFFSET     : Nat := 40     -- withdrawer pubkey, 32 bytes
def META_LOCKUP_OFFSET         : Nat := 72     -- Lockup, 48 bytes
def META_LOCKUP_TIMESTAMP      : Nat := 72     -- i64
def META_LOCKUP_EPOCH          : Nat := 80     -- u64
def META_LOCKUP_CUSTODIAN      : Nat := 88     -- 32 bytes
def META_END                   : Nat := 104    -- past-end

/-! ## Lockup helper structures -/

structure Lockup where
  unixTimestamp : Int      -- i64; can be negative pre-1970 (theoretically)
  epoch         : Nat      -- u64
  custodian     : ByteArray  -- 32-byte pubkey

structure LockupArgs where
  unixTimestamp : Option Int
  epoch         : Option Nat
  custodian     : Option ByteArray

structure LockupCheckedArgs where
  unixTimestamp : Option Int
  epoch         : Option Nat

structure Authorized where
  staker     : ByteArray
  withdrawer : ByteArray

structure Meta where
  rentExemptReserve : Nat
  authorized        : Authorized
  lockup            : Lockup

/-- `StakeAuthorize` enum: which authority slot to mutate. bincode
    encodes as u32 LE: 0 = Staker, 1 = Withdrawer. -/
inductive StakeAuthorize where
  | staker
  | withdrawer
  | invalid (raw : Nat)
  deriving Inhabited, DecidableEq

/-! ## Byte readers / writers -/

private def readU32LE (bs : ByteArray) (off : Nat) : Nat :=
  if off + 4 > bs.size then 0
  else
    (bs.get! off).toNat +
    (bs.get! (off + 1)).toNat * 0x100 +
    (bs.get! (off + 2)).toNat * 0x10000 +
    (bs.get! (off + 3)).toNat * 0x1000000

private def readU64LE (bs : ByteArray) (off : Nat) : Nat :=
  if off + 8 > bs.size then 0
  else
    (bs.get! off).toNat +
    (bs.get! (off + 1)).toNat * 0x100 +
    (bs.get! (off + 2)).toNat * 0x10000 +
    (bs.get! (off + 3)).toNat * 0x1000000 +
    (bs.get! (off + 4)).toNat * 0x100000000 +
    (bs.get! (off + 5)).toNat * 0x10000000000 +
    (bs.get! (off + 6)).toNat * 0x1000000000000 +
    (bs.get! (off + 7)).toNat * 0x100000000000000

private def readI64LE (bs : ByteArray) (off : Nat) : Int :=
  let n := readU64LE bs off
  -- Two's complement sign reconstruction.
  if n ≥ 0x8000000000000000 then (n : Int) - 0x10000000000000000
  else (n : Int)

private def readPubkey (bs : ByteArray) (off : Nat) : ByteArray :=
  if off + 32 > bs.size then ByteArray.empty
  else bs.extract off (off + 32)

private def readString (bs : ByteArray) (off : Nat) : ByteArray × Nat :=
  let len := readU64LE bs off
  let start := off + 8
  if start + len > bs.size then (ByteArray.empty, off)
  else (bs.extract start (start + len), start + len)

/-- Read 1 byte at `off`. -/
private def readU8 (bs : ByteArray) (off : Nat) : Nat :=
  if off ≥ bs.size then 0 else (bs.get! off).toNat

/-! ## Instruction enum (StakeInstruction) -/

inductive Ix where
  /-- `Initialize(Authorized, Lockup)`. Discriminant 0. -/
  | initialize (authorized : Authorized) (lockup : Lockup)
  /-- `Authorize(Pubkey, StakeAuthorize)`. Discriminant 1. -/
  | authorize (newAuthority : ByteArray) (stakeAuthorize : StakeAuthorize)
  /-- `DelegateStake`. Discriminant 2. -/
  | delegateStake
  /-- `Split(lamports)`. Discriminant 3. -/
  | split (lamports : Nat)
  /-- `Withdraw(lamports)`. Discriminant 4. -/
  | withdraw (lamports : Nat)
  /-- `Deactivate`. Discriminant 5. -/
  | deactivate
  /-- `SetLockup(LockupArgs)`. Discriminant 6. -/
  | setLockup (lockup : LockupArgs)
  /-- `Merge`. Discriminant 7. -/
  | merge
  /-- `AuthorizeWithSeed(AuthorizeWithSeedArgs)`. Discriminant 8.
      We carry the raw fields rather than a struct since we defer the
      executor. -/
  | authorizeWithSeed (newAuthority : ByteArray) (stakeAuthorize : StakeAuthorize)
      (seed : ByteArray) (authorityOwner : ByteArray)
  /-- `InitializeChecked`. Discriminant 9. -/
  | initializeChecked
  /-- `AuthorizeChecked(StakeAuthorize)`. Discriminant 10. -/
  | authorizeChecked (stakeAuthorize : StakeAuthorize)
  /-- `AuthorizeCheckedWithSeed(args)`. Discriminant 11. -/
  | authorizeCheckedWithSeed (stakeAuthorize : StakeAuthorize)
      (seed : ByteArray) (authorityOwner : ByteArray)
  /-- `SetLockupChecked(LockupCheckedArgs)`. Discriminant 12. -/
  | setLockupChecked (lockup : LockupCheckedArgs)
  /-- `GetMinimumDelegation`. Discriminant 13. -/
  | getMinimumDelegation
  /-- `DeactivateDelinquent`. Discriminant 14. -/
  | deactivateDelinquent
  /-- `Redelegate`. Discriminant 15. agave rejects unconditionally. -/
  | redelegate
  /-- `MoveStake(lamports)`. Discriminant 16. -/
  | moveStake (lamports : Nat)
  /-- `MoveLamports(lamports)`. Discriminant 17. -/
  | moveLamports (lamports : Nat)
  /-- Forward-compat unknown discriminant. -/
  | unknown (disc : Nat)
  deriving Inhabited

/-- Decode `StakeAuthorize` (u32 LE). -/
private def decodeStakeAuthorize (n : Nat) : StakeAuthorize :=
  match n with
  | 0 => .staker
  | 1 => .withdrawer
  | k => .invalid k

/-- Decode `Authorized` at offset `off`: staker(32) || withdrawer(32). -/
private def decodeAuthorized (bs : ByteArray) (off : Nat) : Authorized :=
  ⟨readPubkey bs off, readPubkey bs (off + 32)⟩

/-- Decode `Lockup` at offset `off`: timestamp(i64) || epoch(u64) ||
    custodian(32). -/
private def decodeLockup (bs : ByteArray) (off : Nat) : Lockup :=
  ⟨readI64LE bs off, readU64LE bs (off + 8), readPubkey bs (off + 16)⟩

/-- Decode `LockupArgs`: three Option fields, bincode-encoded as
    `[1-byte tag] [value]`. -/
private def decodeLockupArgs (bs : ByteArray) (off : Nat) :
    LockupArgs × Nat := Id.run do
  let mut cursor := off
  let mut ts : Option Int := none
  if cursor < bs.size then
    if (bs.get! cursor).toNat = 1 then
      ts := some (readI64LE bs (cursor + 1))
      cursor := cursor + 9
    else cursor := cursor + 1
  let mut ep : Option Nat := none
  if cursor < bs.size then
    if (bs.get! cursor).toNat = 1 then
      ep := some (readU64LE bs (cursor + 1))
      cursor := cursor + 9
    else cursor := cursor + 1
  let mut cu : Option ByteArray := none
  if cursor < bs.size then
    if (bs.get! cursor).toNat = 1 then
      cu := some (readPubkey bs (cursor + 1))
      cursor := cursor + 33
    else cursor := cursor + 1
  return (⟨ts, ep, cu⟩, cursor)

/-- Decode the `LockupCheckedArgs` two-Option layout. -/
private def decodeLockupCheckedArgs (bs : ByteArray) (off : Nat) :
    LockupCheckedArgs × Nat := Id.run do
  let mut cursor := off
  let mut ts : Option Int := none
  if cursor < bs.size then
    if (bs.get! cursor).toNat = 1 then
      ts := some (readI64LE bs (cursor + 1))
      cursor := cursor + 9
    else cursor := cursor + 1
  let mut ep : Option Nat := none
  if cursor < bs.size then
    if (bs.get! cursor).toNat = 1 then
      ep := some (readU64LE bs (cursor + 1))
      cursor := cursor + 9
    else cursor := cursor + 1
  return (⟨ts, ep⟩, cursor)

/-- Decode the full `StakeInstruction`. Discriminant is u32 LE at
    offset 0; payload starts at offset 4. -/
def decode (ixData : ByteArray) : Ix :=
  let d := readU32LE ixData 0
  match d with
  | 0 =>
    -- Initialize(Authorized, Lockup) = Authorized(64) || Lockup(48)
    let auth := decodeAuthorized ixData 4
    let lockup := decodeLockup ixData 68
    .initialize auth lockup
  | 1 =>
    -- Authorize(Pubkey, StakeAuthorize) = pubkey(32) || u32
    let pk := readPubkey ixData 4
    let sa := decodeStakeAuthorize (readU32LE ixData 36)
    .authorize pk sa
  | 2 => .delegateStake
  | 3 => .split (readU64LE ixData 4)
  | 4 => .withdraw (readU64LE ixData 4)
  | 5 => .deactivate
  | 6 =>
    let (args, _) := decodeLockupArgs ixData 4
    .setLockup args
  | 7 => .merge
  | 8 =>
    -- AuthorizeWithSeedArgs:
    --   new_authorized_pubkey : Pubkey (32)
    --   stake_authorize       : u32
    --   authority_seed        : String (u64 len + bytes)
    --   authority_owner       : Pubkey (32)
    let pk := readPubkey ixData 4
    let sa := decodeStakeAuthorize (readU32LE ixData 36)
    let (seed, off) := readString ixData 40
    let owner := readPubkey ixData off
    .authorizeWithSeed pk sa seed owner
  | 9  => .initializeChecked
  | 10 => .authorizeChecked (decodeStakeAuthorize (readU32LE ixData 4))
  | 11 =>
    -- AuthorizeCheckedWithSeedArgs:
    --   stake_authorize : u32
    --   authority_seed  : String
    --   authority_owner : Pubkey
    let sa := decodeStakeAuthorize (readU32LE ixData 4)
    let (seed, off) := readString ixData 8
    let owner := readPubkey ixData off
    .authorizeCheckedWithSeed sa seed owner
  | 12 =>
    let (args, _) := decodeLockupCheckedArgs ixData 4
    .setLockupChecked args
  | 13 => .getMinimumDelegation
  | 14 => .deactivateDelinquent
  | 15 => .redelegate
  | 16 => .moveStake (readU64LE ixData 4)
  | 17 => .moveLamports (readU64LE ixData 4)
  | k  => .unknown k

/-! ## State reading -/

inductive StakeState where
  | uninitialized
  | initialized (metaSt : Meta)
  | stake       (metaSt : Meta)  -- payload past metaSt exists but we don't decode
                                -- the Stake/StakeFlags fields in foundation mode
  | rewardsPool
  | invalid
  deriving Inhabited

private def readMeta (mem : Mem) (base : Nat) : Meta :=
  let rer := readU64 mem base
  let staker := readBytes mem (base + META_STAKER_OFFSET) 32
  let withdrawer := readBytes mem (base + META_WITHDRAWER_OFFSET) 32
  let ts :=
    let n := readU64 mem (base + META_LOCKUP_TIMESTAMP)
    if n ≥ 0x8000000000000000 then (n : Int) - 0x10000000000000000
    else (n : Int)
  let epoch := readU64 mem (base + META_LOCKUP_EPOCH)
  let custodian := readBytes mem (base + META_LOCKUP_CUSTODIAN) 32
  ⟨rer, ⟨staker, withdrawer⟩, ⟨ts, epoch, custodian⟩⟩

private def readStakeState (mem : Mem) (dataPtr dataLen : Nat) : StakeState :=
  if dataLen < 4 then .invalid
  else
    let b0 := (mem  dataPtr      ) % 256
    let b1 := (mem (dataPtr + 1) ) % 256
    let b2 := (mem (dataPtr + 2) ) % 256
    let b3 := (mem (dataPtr + 3) ) % 256
    let tag := b0 + b1 * 0x100 + b2 * 0x10000 + b3 * 0x1000000
    if tag = TAG_UNINITIALIZED then .uninitialized
    else if tag = TAG_REWARDSPOOL then .rewardsPool
    else if tag = TAG_INITIALIZED then
      if dataLen < 4 + META_END then .invalid
      else .initialized (readMeta mem (dataPtr + 4))
    else if tag = TAG_STAKE then
      if dataLen < 4 + META_END then .invalid
      else .stake (readMeta mem (dataPtr + 4))
    else .invalid

/-! ## State writing -/

private def writeU32 (mem : Mem) (addr v : Nat) : Mem :=
  fun a =>
    if a = addr     then v % 0x100
    else if a = addr + 1 then v / 0x100 % 0x100
    else if a = addr + 2 then v / 0x10000 % 0x100
    else if a = addr + 3 then v / 0x1000000 % 0x100
    else mem a

private def writeI64 (mem : Mem) (addr : Nat) (v : Int) : Mem :=
  -- Two's complement encoding: clamp to [0, 2^64).
  let n : Nat := (v % 0x10000000000000000).toNat
  writeU64 mem addr n

private def writeMeta (mem : Mem) (base : Nat) (m : Meta) : Mem :=
  let m1 := writeU64 mem  base                              m.rentExemptReserve
  let m2 := writeBytes m1 (base + META_STAKER_OFFSET)   32  m.authorized.staker
  let m3 := writeBytes m2 (base + META_WITHDRAWER_OFFSET) 32 m.authorized.withdrawer
  let m4 := writeI64 m3 (base + META_LOCKUP_TIMESTAMP)      m.lockup.unixTimestamp
  let m5 := writeU64 m4 (base + META_LOCKUP_EPOCH)          m.lockup.epoch
  writeBytes m5 (base + META_LOCKUP_CUSTODIAN) 32           m.lockup.custodian

private def writeStateInitialized (mem : Mem) (dataPtr : Nat) (m : Meta) :
    Mem :=
  let m1 := writeU32 mem dataPtr TAG_INITIALIZED
  writeMeta m1 (dataPtr + 4) m

/-! ## Helpers -/

private def pubkeyEq (a b : ByteArray) : Bool :=
  a.size = b.size && (List.range a.size).all (fun i => a.get! i = b.get! i)

private def isOwnerStake (owner : ByteArray) : Bool :=
  pubkeyEq owner PROGRAM_ID_BYTES

private def getAcct : List AcctInput → Nat → Option AcctInput
  | [],       _     => none
  | x :: _,   0     => some x
  | _ :: xs,  n + 1 => getAcct xs n

private def fail (mem : Mem) : NativeResult := ⟨mem, 1, CU_DEFAULT⟩
private def ok   (mem : Mem) : NativeResult := ⟨mem, 0, CU_DEFAULT⟩

/-- Is `lockup` in force at `clock = (ts, epoch)`, given the optional
    custodian whose signature exempts? Mirrors
    `Lockup::is_in_force`. With our stub Clock at (0, 0), this is
    `lockup.unixTimestamp > 0 ∨ lockup.epoch > 0` when no custodian
    is provided. -/
private def lockupInForce (lockup : Lockup) (clockTs : Int)
    (clockEpoch : Nat) (custodian : Option ByteArray) : Bool :=
  match custodian with
  | some pk => if pubkeyEq pk lockup.custodian then false
               else lockup.unixTimestamp > clockTs ∨ lockup.epoch > clockEpoch
  | none    => lockup.unixTimestamp > clockTs ∨ lockup.epoch > clockEpoch

/-! ## Clock + Rent stubs

formal-svm models per-instruction; we don't have a live Clock. agave's
processor reads sysvars from invoke_context, and these calls fall
through to the SysvarCache. Our model uses (ts=0, epoch=0) and rent=0,
mirroring mollusk's defaults — so cross-engine fixtures land
identically. -/

private def CLOCK_TS : Int := 0
private def CLOCK_EPOCH : Nat := 0

/-! ## Management variant executors -/

/-- `Initialize(Authorized, Lockup)`. Accounts:
    0. `[writable]` Stake account (must be Uninitialized, owned by
       Stake program, dataLen ≥ 200).
    1. `[]` Rent sysvar. -/
def execInitialize (mem : Mem) (accts : List AcctInput)
    (authorized : Authorized) (lockup : Lockup) : NativeResult :=
  match accts with
  | stakeAcct :: _ =>
    if !isOwnerStake stakeAcct.owner then fail mem
    else if stakeAcct.dataLen < STAKE_ACCOUNT_SIZE then fail mem
    else
      match readStakeState mem stakeAcct.dataPtr stakeAcct.dataLen with
      | .uninitialized =>
        -- rent_exempt_reserve would be `rent.minimum_balance(200)`
        -- in agave. With our rentMin = 0 stub, store 0.
        let metaSt : Meta :=
          { rentExemptReserve := 0,
            authorized := authorized,
            lockup := lockup }
        ok (writeStateInitialized mem stakeAcct.dataPtr metaSt)
      | _ => fail mem
  | _ => fail mem

/-- `InitializeChecked`. Accounts:
    0. `[writable]` Stake.
    1. `[]` Rent.
    2. `[]` Staker.
    3. `[signer]` Withdrawer.
    Uses the staker (accts[2]) and withdrawer (accts[3]) pubkeys
    directly + requires the withdrawer to sign. Lockup defaults to
    (0, 0, default-pubkey). -/
def execInitializeChecked (mem : Mem) (accts : List AcctInput) :
    NativeResult :=
  match accts with
  | stakeAcct :: _rent :: staker :: withdrawer :: _ =>
    if !withdrawer.isSigner then fail mem
    else if !isOwnerStake stakeAcct.owner then fail mem
    else if stakeAcct.dataLen < STAKE_ACCOUNT_SIZE then fail mem
    else
      match readStakeState mem stakeAcct.dataPtr stakeAcct.dataLen with
      | .uninitialized =>
        let zeroPK : ByteArray :=
          ⟨((List.range 32).map (fun _ => (0 : UInt8))).toArray⟩
        let metaSt : Meta :=
          { rentExemptReserve := 0,
            authorized := ⟨staker.key, withdrawer.key⟩,
            lockup := ⟨0, 0, zeroPK⟩ }
        ok (writeStateInitialized mem stakeAcct.dataPtr metaSt)
      | _ => fail mem
  | _ => fail mem

/-- Validate the signer requirement for an Authorize operation,
    returning the mutated `Authorized` and `Lockup` (the lockup is
    untouched but threaded through for the Withdrawer-with-custodian
    path). Mirrors `Authorized::authorize` (state.rs:410-449). -/
private def authorizeAuthorized (current : Authorized) (currentLockup : Lockup)
    (signers : List ByteArray) (newAuthority : ByteArray)
    (sa : StakeAuthorize) (custodian : Option ByteArray) :
    Option Authorized :=
  let isSigner (pk : ByteArray) : Bool := signers.any (fun s => pubkeyEq s pk)
  match sa with
  | .staker =>
    -- Staker change: either the existing staker or withdrawer signs.
    if isSigner current.staker ∨ isSigner current.withdrawer then
      some ⟨newAuthority, current.withdrawer⟩
    else none
  | .withdrawer =>
    -- Withdrawer change: withdrawer must sign + lockup not in force
    -- (or custodian signs to exempt).
    if lockupInForce currentLockup CLOCK_TS CLOCK_EPOCH none then
      match custodian with
      | none => none  -- CustodianMissing
      | some cu =>
        if !isSigner cu then none  -- CustodianSignatureMissing
        else if lockupInForce currentLockup CLOCK_TS CLOCK_EPOCH (some cu)
          then none  -- LockupInForce
        else if isSigner current.withdrawer then
          some ⟨current.staker, newAuthority⟩
        else none
    else
      if isSigner current.withdrawer then
        some ⟨current.staker, newAuthority⟩
      else none
  | .invalid _ => none

/-- Collect signer pubkeys from the instruction's account list. -/
private def collectSigners (accts : List AcctInput) : List ByteArray :=
  accts.filterMap (fun a => if a.isSigner then some a.key else none)

/-- Lookup `accts[i].key`, returning `none` past the end. -/
private def acctKey (accts : List AcctInput) (i : Nat) : Option ByteArray :=
  (getAcct accts i).map (·.key)

/-- `Authorize(new_authority, stake_authorize)`. Accounts:
    0. `[writable]` Stake.
    1. `[]` Clock.
    2. `[signer]` current authority (staker or withdrawer; signature
       checked indirectly through `signers`).
    3. `[]` lockup custodian (optional, only meaningful when
       withdrawer-changing while lockup in force). -/
def execAuthorize (mem : Mem) (accts : List AcctInput)
    (newAuthority : ByteArray) (sa : StakeAuthorize) : NativeResult :=
  match accts with
  | stakeAcct :: _clock :: _ =>
    if !isOwnerStake stakeAcct.owner then fail mem
    else
      let signers := collectSigners accts
      let custodian := acctKey accts 3
      match readStakeState mem stakeAcct.dataPtr stakeAcct.dataLen with
      | .initialized metaSt =>
        match authorizeAuthorized metaSt.authorized metaSt.lockup signers
                                   newAuthority sa custodian with
        | none => fail mem
        | some newAuth =>
          let metaSt' : Meta :=
            { rentExemptReserve := metaSt.rentExemptReserve
              authorized := newAuth
              lockup := metaSt.lockup }
          ok (writeStateInitialized mem stakeAcct.dataPtr metaSt')
      | .stake metaSt =>
        match authorizeAuthorized metaSt.authorized metaSt.lockup signers
                                   newAuthority sa custodian with
        | none => fail mem
        | some newAuth =>
          -- For .stake we write only the Meta portion (4 + 8 + 64 + 48 =
          -- 124 bytes), preserving the Stake + StakeFlags payload that
          -- follows.
          let m1 := writeU32 mem stakeAcct.dataPtr TAG_STAKE
          let m2 := writeMeta m1 (stakeAcct.dataPtr + 4)
                              { metaSt with authorized := newAuth }
          ⟨m2, 0, CU_DEFAULT⟩
      | _ => fail mem
  | _ => fail mem

/-- `AuthorizeChecked(stake_authorize)`. Same as Authorize but the
    new authority is taken from `accts[3].key` and that account MUST
    be a signer. -/
def execAuthorizeChecked (mem : Mem) (accts : List AcctInput)
    (sa : StakeAuthorize) : NativeResult :=
  match accts with
  | stakeAcct :: _clock :: _present :: newAuth :: _ =>
    if !newAuth.isSigner then fail mem
    else if !isOwnerStake stakeAcct.owner then fail mem
    else
      let signers := collectSigners accts
      let custodian := acctKey accts 4
      match readStakeState mem stakeAcct.dataPtr stakeAcct.dataLen with
      | .initialized metaSt =>
        match authorizeAuthorized metaSt.authorized metaSt.lockup signers
                                   newAuth.key sa custodian with
        | none => fail mem
        | some newA =>
          ok (writeStateInitialized mem stakeAcct.dataPtr
              { metaSt with authorized := newA })
      | .stake metaSt =>
        match authorizeAuthorized metaSt.authorized metaSt.lockup signers
                                   newAuth.key sa custodian with
        | none => fail mem
        | some newA =>
          let m1 := writeU32 mem stakeAcct.dataPtr TAG_STAKE
          let m2 := writeMeta m1 (stakeAcct.dataPtr + 4)
                              { metaSt with authorized := newA }
          ⟨m2, 0, CU_DEFAULT⟩
      | _ => fail mem
  | _ => fail mem

/-- Apply `LockupArgs` over an existing `Lockup`. The argument's
    Option fields each overwrite the corresponding lockup slot when
    Some. -/
private def applyLockupArgs (lockup : Lockup) (args : LockupArgs) : Lockup :=
  let ts := args.unixTimestamp.getD lockup.unixTimestamp
  let ep := args.epoch.getD lockup.epoch
  let cu := args.custodian.getD lockup.custodian
  ⟨ts, ep, cu⟩

/-- Signer check for SetLockup: if the lockup is in force, the
    custodian must sign; otherwise the withdrawer must sign. Mirrors
    `Meta::set_lockup` (state.rs:524-558). -/
private def canSetLockup (current : Lockup) (withdrawer : ByteArray)
    (signers : List ByteArray) : Bool :=
  let isSigner (pk : ByteArray) : Bool := signers.any (fun s => pubkeyEq s pk)
  if lockupInForce current CLOCK_TS CLOCK_EPOCH none then
    isSigner current.custodian
  else
    isSigner withdrawer

/-- `SetLockup(LockupArgs)`. Accounts:
    0. `[writable]` Stake.
    Note: agave's SetLockup signer-check uses the *transaction*
    signer set, not just `accts`. We approximate with the account
    signer set, which captures the same intent for any normal flow. -/
def execSetLockup (mem : Mem) (accts : List AcctInput) (args : LockupArgs) :
    NativeResult :=
  match accts with
  | stakeAcct :: _ =>
    if !isOwnerStake stakeAcct.owner then fail mem
    else
      let signers := collectSigners accts
      match readStakeState mem stakeAcct.dataPtr stakeAcct.dataLen with
      | .initialized metaSt =>
        if !canSetLockup metaSt.lockup metaSt.authorized.withdrawer signers then
          fail mem
        else
          ok (writeStateInitialized mem stakeAcct.dataPtr
              { metaSt with lockup := applyLockupArgs metaSt.lockup args })
      | .stake metaSt =>
        if !canSetLockup metaSt.lockup metaSt.authorized.withdrawer signers then
          fail mem
        else
          let m1 := writeU32 mem stakeAcct.dataPtr TAG_STAKE
          let m2 := writeMeta m1 (stakeAcct.dataPtr + 4)
                              { metaSt with lockup := applyLockupArgs metaSt.lockup args }
          ⟨m2, 0, CU_DEFAULT⟩
      | _ => fail mem
  | _ => fail mem

/-- `SetLockupChecked(LockupCheckedArgs)`. The custodian field is
    taken from `accts[2].key` (signer-required) when present. -/
def execSetLockupChecked (mem : Mem) (accts : List AcctInput)
    (args : LockupCheckedArgs) : NativeResult :=
  match accts with
  | _stakeAcct :: _present :: rest =>
    let custodianOpt : Option ByteArray :=
      match rest with
      | custodian :: _ =>
        if custodian.isSigner then some custodian.key else none
      | _ => none
    -- Reuse execSetLockup with the upgraded LockupArgs.
    execSetLockup mem accts
      { unixTimestamp := args.unixTimestamp
        epoch         := args.epoch
        custodian     := custodianOpt }
  | _ => fail mem

/-- `GetMinimumDelegation`. agave writes the minimum-delegation u64
    LE bytes to the transaction's return-data buffer. We don't model
    return data inside the Native dispatcher; the actual value is
    feature-gated (`stake_raise_minimum_delegation_to_1_sol`).
    We surface r0=0 and the documented minimum (1 lamport) but
    don't propagate the return-data side-effect. -/
def execGetMinimumDelegation (mem : Mem) : NativeResult :=
  ⟨mem, 0, CU_DEFAULT⟩

/-! ## Dispatcher -/

/-- Single dispatch entry. Decoded variants the foundation doesn't
    cover charge `CU_DEFAULT` and surface `r0=1` ("deferred"). -/
def dispatch (ixData : ByteArray) (accts : List AcctInput) (mem : Mem) :
    Option NativeResult :=
  match decode ixData with
  | .initialize auth lockup       => some (execInitialize mem accts auth lockup)
  | .initializeChecked            => some (execInitializeChecked mem accts)
  | .authorize na sa              => some (execAuthorize mem accts na sa)
  | .authorizeChecked sa          => some (execAuthorizeChecked mem accts sa)
  | .setLockup args               => some (execSetLockup mem accts args)
  | .setLockupChecked args        => some (execSetLockupChecked mem accts args)
  | .getMinimumDelegation         => some (execGetMinimumDelegation mem)
  -- agave returns InvalidInstructionData unconditionally for
  -- Redelegate; we surface r0=1.
  | .redelegate                   => some ⟨mem, 1, CU_DEFAULT⟩
  -- Operational variants deferred (see module-doc).
  | .delegateStake                => some ⟨mem, 1, CU_DEFAULT⟩
  | .split _                      => some ⟨mem, 1, CU_DEFAULT⟩
  | .withdraw _                   => some ⟨mem, 1, CU_DEFAULT⟩
  | .deactivate                   => some ⟨mem, 1, CU_DEFAULT⟩
  | .merge                        => some ⟨mem, 1, CU_DEFAULT⟩
  | .deactivateDelinquent         => some ⟨mem, 1, CU_DEFAULT⟩
  | .moveStake _                  => some ⟨mem, 1, CU_DEFAULT⟩
  | .moveLamports _               => some ⟨mem, 1, CU_DEFAULT⟩
  | .authorizeWithSeed _ _ _ _    => some ⟨mem, 1, CU_DEFAULT⟩
  | .authorizeCheckedWithSeed _ _ _ => some ⟨mem, 1, CU_DEFAULT⟩
  | .unknown _                    => some ⟨mem, 1, CU_DEFAULT⟩

end Svm.Native.Stake
