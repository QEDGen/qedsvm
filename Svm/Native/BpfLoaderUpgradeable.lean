-- The Upgradeable BPF Loader (BPF Loader v3) — native, not BPF.
--
-- Reference: agave's `solana-bpf-loader-program/src/lib.rs`
-- (`process_loader_upgradeable_instruction`, ~600 lines covering 8
-- variants) and `solana-loader-v3-interface-6.1.1/src/{state,instruction}.rs`.
--
-- PROGRAM_ID = `BPFLoaderUpgradeab1e11111111111111111111111`.
-- CU = `UPGRADEABLE_LOADER_COMPUTE_UNITS = 2370` (flat per invocation,
-- charged at the *outer* `process_instruction_inner` boundary in
-- agave; we charge it uniformly in `dispatch`).
--
-- ## What this module ships
--
-- All 8 variants decode and dispatch end-to-end:
--
--   * InitializeBuffer     — Uninitialized → Buffer { authority }
--   * Write                — bounds-checked copy into buffer payload
--   * DeployWithMaxDataLen — PDA verify + buffer→payer drain +
--                             inline System::CreateAccount + buffer
--                             payload copy → programdata + state writes
--   * Upgrade              — state verify + buffer→programdata copy +
--                             tail-zero + lamport spill
--   * SetAuthority         — Buffer / ProgramData authority rotation
--   * Close                — all three target states (Uninit / Buffer /
--                             ProgramData), full lamport-drain semantics
--   * ExtendProgram        — data_len grow + inline System::Transfer
--                             for rent gap (when rent_min > 0)
--   * SetAuthorityChecked  — same as SetAuthority + new-authority signer
--
-- ## Model simplifications (documented gaps)
--
-- These come from agave-side machinery we don't replicate, all of
-- which are described in the project charter as "spec where
-- meaningful, skip when machinery is harness-only":
--
--   * **ELF verification.** agave's `deploy_program!` macro
--     verifies the ELF and stashes the JIT-compiled program in the
--     transaction's program cache for subsequent invocations. We
--     have no program cache, so Deploy / Upgrade / Extend skip the
--     verify side-effect. Future code paths that load the freshly-
--     deployed program will go through `Decode.decodeProgram` at
--     invocation time anyway.
--   * **Rent::minimum_balance.** We model `rent_min(len) = 0` (the
--     same simplification documented in the project's Tier-2 deferred
--     items). Affected branches:
--     - Deploy's payer-pays-rent step charges 1 lamport (the
--       `max(1, rent_min)` lower bound).
--     - Upgrade's spill formula leaves 1 lamport on programdata.
--     - ExtendProgram skips the System::Transfer top-up when
--       programdata already has ≥ 1 lamport.
--   * **executable flag on Deploy.** agave's `program.set_executable(true)`
--     mutates the TransactionContext's view; the BPF caller's
--     `AccountInfo` exec bit is not writable from within a Native in
--     our model (AcctInput doesn't expose its slot). The harness
--     surfaces executable=true via the resulting_accounts builder
--     for accounts owned by the loader; the Lean dispatch itself
--     leaves the bit alone.
--   * **Inter-Native CPI (closed 2026-05-15).** Deploy and
--     ExtendProgram do `native_invoke_signed(system_instruction::…)`
--     in agave, which charges `Cpi.cu = 946` per call. The earlier
--     Loader v3 closure (commit 2c1c1ab) inlined the System
--     side-effects to avoid building inter-Native CPI plumbing. This
--     module now composes via `System.dispatch` directly with
--     synthetic `isSigner = true` on the PDA-derived account
--     (mirrors agave's `invoke_signed` where seeds authorize the
--     PDA). Deploy's CU = 2370 + 946 + 150 = 3466, matching agave;
--     ExtendProgram's rent-gap Transfer (only fires when
--     `rent_min > 0`) charges the same `946 + 150` premium.
--   * **Close ProgramData same-slot freshness.** agave rejects
--     Close when `clock.slot == programdata.slot`. With both = 0
--     in our model the gate would always fire; we bypass it.
--
-- ## State layout (agave's `UpgradeableLoaderState`)
--
-- bincode enum, u32 LE tag. Pubkey `Option` is 1-byte presence flag
-- followed by 32 bytes (regardless of presence; the trailing slot
-- isn't read when the tag is `None`, but the *account-data size* is
-- fixed at `size_of_*_metadata`).
--
--   tag 0  Uninitialized        4 bytes
--   tag 1  Buffer               37 bytes  [4 tag | 1 Some/None | 32 pubkey]
--   tag 2  Program              36 bytes  [4 tag | 32 programdata pubkey]
--   tag 3  ProgramData          45 bytes  [4 tag | 8 slot | 1 Some/None | 32 pubkey]
--
-- After the metadata, the buffer / programdata payload (ELF bytes)
-- continues to `accts[i].dataLen`.

import Svm.Native.AcctInput
import Svm.Native.System
import Svm.SBPF.Machine
import Svm.Syscalls.Pda
import Svm.Syscalls.Cpi

namespace Svm.Native.BpfLoaderUpgradeable

open Svm.SBPF.Memory
open Svm.SBPF (writeBytes readBytes)
open Svm.Native

/-- BPFLoaderUpgradeable program-id as a little-endian `Nat`.
    Raw bytes
    `[0x02, 0xa8, 0xf6, 0x91, 0x4e, 0x88, 0xa1, 0xb0, 0xe2, 0x10,
      0x15, 0x3e, 0xf7, 0x63, 0xae, 0x2b, 0x00, 0xc2, 0xb9, 0x3d,
      0x16, 0xc1, 0x24, 0xd2, 0xc0, 0x53, 0x7a, 0x10, 0x04, 0x80,
      0x00, 0x00]`. -/
def PROGRAM_ID : Nat :=
  0x00008004107a53c0d224c1163db9c2002bae63f73e1510e2b0a1884e91f6a802

/-- The 32-byte BPF Loader v3 program-id (used as an owner-field
    comparison on Close / ExtendProgram / Upgrade). -/
def PROGRAM_ID_BYTES : ByteArray :=
  ⟨#[0x02, 0xa8, 0xf6, 0x91, 0x4e, 0x88, 0xa1, 0xb0,
     0xe2, 0x10, 0x15, 0x3e, 0xf7, 0x63, 0xae, 0x2b,
     0x00, 0xc2, 0xb9, 0x3d, 0x16, 0xc1, 0x24, 0xd2,
     0xc0, 0x53, 0x7a, 0x10, 0x04, 0x80, 0x00, 0x00]⟩

/-- `UPGRADEABLE_LOADER_COMPUTE_UNITS` from
    `programs/bpf_loader/src/lib.rs:37`. Flat charge for every
    management instruction; the cost is consumed before dispatch in
    agave (`process_instruction_inner`), so it accrues whether the
    inner match succeeds or not. -/
def CU_DEFAULT : Nat := 2370

/-! ## State enum -/

def TAG_UNINITIALIZED : Nat := 0
def TAG_BUFFER        : Nat := 1
def TAG_PROGRAM       : Nat := 2
def TAG_PROGRAMDATA   : Nat := 3

def SIZE_UNINITIALIZED      : Nat := 4
def SIZE_BUFFER_METADATA    : Nat := 37
def SIZE_PROGRAM            : Nat := 36
def SIZE_PROGRAMDATA_META   : Nat := 45

inductive LoaderState where
  | uninitialized
  | buffer       (authority : Option ByteArray)
  | program      (programdataAddr : ByteArray)
  | programData  (slot : Nat) (upgradeAuthority : Option ByteArray)
  | invalid
  deriving Inhabited

/-! ## Wire decode -/

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

inductive LoaderIx where
  /-- `InitializeBuffer`. Discriminant 0. -/
  | initializeBuffer
  /-- `Write { offset: u32, bytes: Vec<u8> }`. Discriminant 1. -/
  | write (offset : Nat) (bytes : ByteArray)
  /-- `DeployWithMaxDataLen { max_data_len: usize }`. Discriminant 2. -/
  | deployWithMaxDataLen (maxDataLen : Nat)
  /-- `Upgrade`. Discriminant 3. -/
  | upgrade
  /-- `SetAuthority`. Discriminant 4. -/
  | setAuthority
  /-- `Close`. Discriminant 5. -/
  | close
  /-- `ExtendProgram { additional_bytes: u32 }`. Discriminant 6. -/
  | extendProgram (additionalBytes : Nat)
  /-- `SetAuthorityChecked`. Discriminant 7. -/
  | setAuthorityChecked
  /-- Any discriminant agave doesn't know — dispatch fails. -/
  | unknown (disc : Nat)
  deriving Inhabited

/-- Decode `ix.data`. Bincode enum: u32 LE discriminant + payload. -/
def decode (ixData : ByteArray) : LoaderIx :=
  let d := readU32LE ixData 0
  match d with
  | 0 => .initializeBuffer
  | 1 =>
    -- Write: offset(u32) | bytes(Vec<u8>): u64 LE len + bytes
    let off    := readU32LE ixData 4
    let bytesLen := readU64LE ixData 8
    let start  := 16
    let bytes  :=
      if start + bytesLen > ixData.size then ByteArray.empty
      else ixData.extract start (start + bytesLen)
    .write off bytes
  | 2 =>
    -- DeployWithMaxDataLen: max_data_len(u64) -- usize serialised as u64
    let n := readU64LE ixData 4
    .deployWithMaxDataLen n
  | 3 => .upgrade
  | 4 => .setAuthority
  | 5 => .close
  | 6 =>
    let n := readU32LE ixData 4
    .extendProgram n
  | 7 => .setAuthorityChecked
  | d => .unknown d

/-! ## State read/write -/

/-- Read the `LoaderState` stored at `acct.dataPtr` in caller memory.
    `acct.dataLen` is the full account data length (which must be at
    least the metadata size for the variant). Truncated reads return
    `.invalid`. -/
private def readState (mem : Mem) (dataPtr dataLen : Nat) : LoaderState :=
  if dataLen < SIZE_UNINITIALIZED then .invalid
  else
    let b0 := (mem  dataPtr      ) % 256
    let b1 := (mem (dataPtr + 1) ) % 256
    let b2 := (mem (dataPtr + 2) ) % 256
    let b3 := (mem (dataPtr + 3) ) % 256
    let tag := b0 + b1 * 0x100 + b2 * 0x10000 + b3 * 0x1000000
    if tag = TAG_UNINITIALIZED then .uninitialized
    else if tag = TAG_BUFFER then
      if dataLen < SIZE_BUFFER_METADATA then .invalid
      else
        let opt := (mem (dataPtr + 4)) % 256
        if opt = 0 then .buffer none
        else if opt = 1 then
          let pk := readBytes mem (dataPtr + 5) 32
          .buffer (some pk)
        else .invalid
    else if tag = TAG_PROGRAM then
      if dataLen < SIZE_PROGRAM then .invalid
      else
        let pk := readBytes mem (dataPtr + 4) 32
        .program pk
    else if tag = TAG_PROGRAMDATA then
      if dataLen < SIZE_PROGRAMDATA_META then .invalid
      else
        let slot := readU64 mem (dataPtr + 4)
        let opt := (mem (dataPtr + 12)) % 256
        if opt = 0 then .programData slot none
        else if opt = 1 then
          let pk := readBytes mem (dataPtr + 13) 32
          .programData slot (some pk)
        else .invalid
    else .invalid

/-- Write a u32 LE at `addr`. -/
private def writeU32 (mem : Mem) (addr v : Nat) : Mem :=
  fun a =>
    if a = addr     then v % 0x100
    else if a = addr + 1 then v / 0x100 % 0x100
    else if a = addr + 2 then v / 0x10000 % 0x100
    else if a = addr + 3 then v / 0x1000000 % 0x100
    else mem a

/-- Write `0x00`s into `[addr, addr+len)`. -/
private def writeZeros (mem : Mem) (addr len : Nat) : Mem :=
  fun a => if a ≥ addr ∧ a - addr < len then 0 else mem a

/-- Serialize `Buffer { authority }` into the 37-byte metadata slot at
    `dataPtr`. Bytes past the metadata are untouched. -/
private def writeBufferState (mem : Mem) (dataPtr : Nat)
    (authority : Option ByteArray) : Mem :=
  let m1 := writeU32 mem dataPtr TAG_BUFFER
  match authority with
  | none =>
    -- Option tag = 0; agave pads remaining 32 bytes with whatever was
    -- there. We zero the slot to keep behaviour reproducible.
    let m2 := writeU32 m1 (dataPtr + 4) 0  -- writes the option byte +
                                              -- 3 surrounding bytes; the
                                              -- option byte is what
                                              -- matters
    writeZeros m2 (dataPtr + 5) 32
  | some pk =>
    let m2 := fun a => if a = dataPtr + 4 then 1 else m1 a
    writeBytes m2 (dataPtr + 5) 32 pk

/-- Serialize `ProgramData { slot, upgrade_authority }` into the
    45-byte metadata slot at `dataPtr`. Payload past the metadata is
    untouched. -/
private def writeProgramDataState (mem : Mem) (dataPtr : Nat)
    (slot : Nat) (auth : Option ByteArray) : Mem :=
  let m1 := writeU32 mem dataPtr TAG_PROGRAMDATA
  let m2 := writeU64 m1 (dataPtr + 4) slot
  match auth with
  | none =>
    let m3 := fun a => if a = dataPtr + 12 then 0 else m2 a
    writeZeros m3 (dataPtr + 13) 32
  | some pk =>
    let m3 := fun a => if a = dataPtr + 12 then 1 else m2 a
    writeBytes m3 (dataPtr + 13) 32 pk

/-! ## Helpers -/

private def pubkeyEq (a b : ByteArray) : Bool :=
  a.size = b.size && (List.range a.size).all (fun i => a.get! i = b.get! i)

private def isOwnerLoader (owner : ByteArray) : Bool :=
  pubkeyEq owner PROGRAM_ID_BYTES

/-- `Option ByteArray` equality on pubkeys. -/
private def authorityEq (a b : Option ByteArray) : Bool :=
  match a, b with
  | none,    none    => true
  | some x,  some y  => pubkeyEq x y
  | _, _ => false

/-- Lookup `accts[i]`. -/
private def getAcct : List AcctInput → Nat → Option AcctInput
  | [],       _     => none
  | x :: _,   0     => some x
  | _ :: xs,  n + 1 => getAcct xs n

private def U64_MODULUS : Nat := 0x10000000000000000

private def fail (mem : Mem) : NativeResult := ⟨mem, 1, CU_DEFAULT⟩
private def ok   (mem : Mem) : NativeResult := ⟨mem, 0, CU_DEFAULT⟩

/-! ## Variant executors -/

/-- `InitializeBuffer`. Accounts:
    0. `[writable]` source account to initialize (must be Uninit).
    1. `[]` buffer authority (Some(authority_key) if present, else immutable). -/
def execInitializeBuffer (mem : Mem) (accts : List AcctInput) : NativeResult :=
  match accts with
  | buffer :: authority :: _ =>
    match readState mem buffer.dataPtr buffer.dataLen with
    | .uninitialized =>
      if buffer.dataLen < SIZE_BUFFER_METADATA then fail mem
      else
        let mem' := writeBufferState mem buffer.dataPtr (some authority.key)
        ok mem'
    | _ => fail mem  -- AccountAlreadyInitialized
  | _ => fail mem    -- check_number_of_instruction_accounts(2)

/-- `Write { offset, bytes }`. Accounts:
    0. `[writable]` buffer.
    1. `[signer]` buffer authority. -/
def execWrite (mem : Mem) (accts : List AcctInput) (offset : Nat)
    (bytes : ByteArray) : NativeResult :=
  match accts with
  | buffer :: authority :: _ =>
    match readState mem buffer.dataPtr buffer.dataLen with
    | .buffer authorityAddr =>
      if authorityAddr.isNone then fail mem  -- Immutable
      else if !authorityEq authorityAddr (some authority.key) then fail mem
      else if !authority.isSigner then fail mem
      else
        -- Effective payload region begins after `size_of_buffer_metadata` (37).
        let absoluteOffset := SIZE_BUFFER_METADATA + offset
        let writeEnd := absoluteOffset + bytes.size
        if writeEnd > buffer.dataLen then fail mem  -- AccountDataTooSmall
        else
          let mem' := writeBytes mem (buffer.dataPtr + absoluteOffset)
                                  bytes.size bytes
          ok mem'
    | _ => fail mem
  | _ => fail mem

/-- `SetAuthority`. Accounts:
    0. `[writable]` Buffer or ProgramData account.
    1. `[signer]` current authority.
    2. `[]` new authority (optional, omitted = immutable). -/
def execSetAuthority (mem : Mem) (accts : List AcctInput) : NativeResult :=
  match accts with
  | account :: present :: rest =>
    let newAuthority : Option ByteArray :=
      match rest with
      | newAuth :: _ => some newAuth.key
      | []           => none
    match readState mem account.dataPtr account.dataLen with
    | .buffer authorityAddr =>
      if newAuthority.isNone then fail mem  -- IncorrectAuthority
      else if authorityAddr.isNone then fail mem  -- Immutable
      else if !authorityEq authorityAddr (some present.key) then fail mem
      else if !present.isSigner then fail mem
      else
        let mem' := writeBufferState mem account.dataPtr newAuthority
        ok mem'
    | .programData slot upgradeAuth =>
      if upgradeAuth.isNone then fail mem
      else if !authorityEq upgradeAuth (some present.key) then fail mem
      else if !present.isSigner then fail mem
      else
        let mem' := writeProgramDataState mem account.dataPtr slot newAuthority
        ok mem'
    | _ => fail mem
  | _ => fail mem

/-- `SetAuthorityChecked`. Same as `SetAuthority` but the new
    authority MUST be a signer. -/
def execSetAuthorityChecked (mem : Mem) (accts : List AcctInput) :
    NativeResult :=
  match accts with
  | account :: present :: newAuth :: _ =>
    match readState mem account.dataPtr account.dataLen with
    | .buffer authorityAddr =>
      if authorityAddr.isNone then fail mem
      else if !authorityEq authorityAddr (some present.key) then fail mem
      else if !present.isSigner then fail mem
      else if !newAuth.isSigner then fail mem
      else
        let mem' := writeBufferState mem account.dataPtr (some newAuth.key)
        ok mem'
    | .programData slot upgradeAuth =>
      if upgradeAuth.isNone then fail mem
      else if !authorityEq upgradeAuth (some present.key) then fail mem
      else if !present.isSigner then fail mem
      else if !newAuth.isSigner then fail mem
      else
        let mem' := writeProgramDataState mem account.dataPtr slot
                                          (some newAuth.key)
        ok mem'
    | _ => fail mem
  | _ => fail mem

/-- Common helper for closing a Buffer / ProgramData account:
    - Sets data_length to size_of_uninitialized (4).
    - Drains lamports from `target` into `recipient`.
    - Requires `authority.is_signer` and matches the stored authority. -/
private def commonCloseAccount (mem : Mem) (target recipient authority : AcctInput)
    (authorityAddr : Option ByteArray) : NativeResult :=
  if authorityAddr.isNone then fail mem  -- Immutable
  else if !authorityEq authorityAddr (some authority.key) then fail mem
  else if !authority.isSigner then fail mem
  else if target.lamports + recipient.lamports ≥ U64_MODULUS then fail mem
  else
    -- Drain lamports.
    let newR := recipient.lamports + target.lamports
    let m1 := writeU64 mem target.lamportsRefAddr 0
    let m2 := writeU64 m1 recipient.lamportsRefAddr newR
    -- Shrink data_len to SIZE_UNINITIALIZED in both buffer-side and
    -- BPF input-buffer slots (mirrors System::CreateAccount's pair).
    let m3 := writeU64 m2 target.dataLenRefAddr SIZE_UNINITIALIZED
    let m4 := writeU64 m3 (target.dataPtr - 8) SIZE_UNINITIALIZED
    -- Reset the tag to Uninitialized.
    let m5 := writeU32 m4 target.dataPtr TAG_UNINITIALIZED
    ⟨m5, 0, CU_DEFAULT⟩

/-- `Close`. Three cases depending on the state of `accts[0]`:
    - Uninitialized: 2 accounts. Drain lamports, no auth check.
    - Buffer: 3 accounts (close, recipient, authority).
    - ProgramData: 4 accounts (close, recipient, authority, program).
      The program account must satisfy:
      writable, owned by the loader, and reference the closing
      ProgramData via `Program.programdata_address`. -/
def execClose (mem : Mem) (accts : List AcctInput) : NativeResult :=
  match accts with
  | closeAcct :: recipient :: rest =>
    -- agave guards `close.key == recipient.key` rejection. We mirror.
    if pubkeyEq closeAcct.key recipient.key then fail mem
    else
      match readState mem closeAcct.dataPtr closeAcct.dataLen with
      | .uninitialized =>
        -- Drain lamports straight into recipient.
        if recipient.lamports + closeAcct.lamports ≥ U64_MODULUS then fail mem
        else
          let m1 := writeU64 mem closeAcct.lamportsRefAddr 0
          let m2 := writeU64 m1 recipient.lamportsRefAddr
                              (recipient.lamports + closeAcct.lamports)
          -- data_length stays at SIZE_UNINITIALIZED; the state already
          -- says Uninitialized so no rewrite needed (agave does
          -- `set_data_length(size_of_uninitialized())`).
          let m3 := writeU64 m2 closeAcct.dataLenRefAddr SIZE_UNINITIALIZED
          let m4 := writeU64 m3 (closeAcct.dataPtr - 8) SIZE_UNINITIALIZED
          ⟨m4, 0, CU_DEFAULT⟩
      | .buffer authorityAddr =>
        match rest with
        | authority :: _ => commonCloseAccount mem closeAcct recipient authority
                                               authorityAddr
        | _ => fail mem
      | .programData _ upgradeAuth =>
        match rest with
        | authority :: program :: _ =>
          if !program.isWritable then fail mem
          else if !isOwnerLoader program.owner then fail mem
          else
            -- Slot freshness check: agave rejects Close if the program
            -- was deployed *in this slot*. Our currentSlot is 0; the
            -- stored slot is whatever was serialised, which is also 0
            -- for any fixture using mollusk defaults. Agave's check is
            -- `clock.slot == slot`; with both = 0 the check fires
            -- (Close fails). We document this as a known divergence
            -- and bypass the freshness gate here — programs deployed
            -- in the same slot can still be closed in our model.
            match readState mem program.dataPtr program.dataLen with
            | .program programdataAddr =>
              if !pubkeyEq programdataAddr closeAcct.key then fail mem
              else commonCloseAccount mem closeAcct recipient authority
                                       upgradeAuth
            | _ => fail mem
        | _ => fail mem
      | _ => fail mem
  | _ => fail mem

/-! ## Deploy / Upgrade / Extend

These three variants share the pattern "verify state-chain →
manipulate lamports → copy buffer payload → write state". They also
share two model simplifications (see top-doc):

  * `rent_min(_) = 0` — agave's Rent sysvar would compute per-byte
    lamports; we don't model the Rent sysvar's value, so the
    `1.max(rent_min)` clamp always lands at 1.
  * The internal `native_invoke_signed(system_instruction::...)` is
    inlined (lamport / data_len / owner writes done directly) rather
    than re-entering the System dispatcher. This saves a Cpi.cu
    charge of 946 + 150 vs agave; net CU figures will differ by
    that amount per inner invocation. -/

/-- The MAX_PERMITTED_DATA_LENGTH constant agave clamps deploys
    against. Matches `solana_system_interface::MAX_PERMITTED_DATA_LENGTH`. -/
private def MAX_PERMITTED_DATA_LENGTH : Nat := 10 * 1024 * 1024

/-- Stub for `Rent::minimum_balance(_)`. Our model treats every
    rent-exempt computation as 0 lamports. The downstream
    `1.max(rent_min)` formula then clamps to 1. -/
private def rentMin (_dataLen : Nat) : Nat := 0

/-- SIMD-0431: a successful Extend must add at least 10 KiB unless
    the account is within 10 KiB of MAX_PERMITTED_DATA_LENGTH. We
    enforce the bound directly (agave gates this behind a feature
    flag; we treat the gate as always-active since modern fixtures
    won't run pre-SIMD-0431 paths). -/
private def MINIMUM_EXTEND_PROGRAM_BYTES : Nat := 10240

/-! ### Inter-Native CPI composition

Build the bincode ix data for a few `SystemInstruction` variants we
invoke as inner CPI calls, then dispatch through `System.dispatch`.
`Cpi.cu = 946` is added to the cu figure to mirror agave's
`invoke_units` charge — System contributes its own `System.CU_DEFAULT
= 150` on top via its result. -/

private def U64_BYTES (n : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let mut v := n
  for _ in [0:8] do
    out := out.push (UInt8.ofNat (v % 256))
    v := v / 256
  return out

private def U32_BYTES (n : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let mut v := n
  for _ in [0:4] do
    out := out.push (UInt8.ofNat (v % 256))
    v := v / 256
  return out

/-- Build the bincode-encoded `SystemInstruction::CreateAccount`
    payload: u32(0) || u64(lamports) || u64(space) || 32B(owner). -/
private def encodeSystemCreateAccount (lamports space : Nat) (owner : ByteArray)
    : ByteArray :=
  U32_BYTES 0 ++ U64_BYTES lamports ++ U64_BYTES space ++ owner

/-- Build the bincode-encoded `SystemInstruction::Transfer` payload:
    u32(2) || u64(lamports). -/
private def encodeSystemTransfer (lamports : Nat) : ByteArray :=
  U32_BYTES 2 ++ U64_BYTES lamports

/-- Compose an inner `System.dispatch` call from within a Loader v3
    executor. Adds `Cpi.cu = 946` to the inner CU charge; returns
    `none` if the dispatch fails (unknown variant) or the inner call
    returned a non-zero r0. Successful returns expose the composed
    (mem, cu) pair so the caller can fold them into its NativeResult. -/
private def invokeSystem (ixData : ByteArray) (subAccts : List AcctInput)
    (mem : Mem) : Option (Mem × Nat) :=
  match System.dispatch ixData subAccts mem with
  | none => none
  | some r => if r.r0 = 0 then some (r.mem, Svm.SBPF.Cpi.cu + r.cu)
              else none

/-- `DeployWithMaxDataLen { max_data_len }`. Accounts (per
    `solana-loader-v3-interface-6.1.1/src/instruction.rs:86-97`):
    0. `[writable, signer]` payer
    1. `[writable]` uninitialized ProgramData (the PDA)
    2. `[writable]` uninitialized Program
    3. `[writable]` Buffer
    4. `[]` Rent sysvar
    5. `[]` Clock sysvar
    6. `[]` System program
    7. `[signer]` upgrade authority -/
def execDeployWithMaxDataLen (mem : Mem) (accts : List AcctInput)
    (maxDataLen : Nat) : NativeResult :=
  match accts with
  | payer :: pdAcct :: program :: buffer :: _rent :: _clock :: _sys ::
    authority :: _ =>
    -- Verify Program account: Uninitialized + large enough + rent-exempt
    -- (we skip the rent check, per `rentMin = 0`).
    match readState mem program.dataPtr program.dataLen with
    | .uninitialized =>
      if program.dataLen < SIZE_PROGRAM then fail mem
      else
        -- Verify Buffer account: Buffer state + authority matches +
        -- authority signed.
        match readState mem buffer.dataPtr buffer.dataLen with
        | .buffer authorityAddr =>
          if !authorityEq authorityAddr (some authority.key) then fail mem
          else if !authority.isSigner then fail mem
          else
            let bufferDataOffset := SIZE_BUFFER_METADATA  -- 37
            if buffer.dataLen < bufferDataOffset then fail mem
            else
              let bufferDataLen := buffer.dataLen - bufferDataOffset
              let programDataLen := SIZE_PROGRAMDATA_META + maxDataLen
              if bufferDataLen = 0 then fail mem
              else if maxDataLen < bufferDataLen then fail mem
              else if programDataLen > MAX_PERMITTED_DATA_LENGTH then fail mem
              else
                -- PDA verify: find_program_address([program.key], LOADER)
                -- == pdAcct.key.
                match Svm.SBPF.Pda.tryFindProgramAddress
                        [program.key] PROGRAM_ID_BYTES with
                | none => fail mem
                | some (derived, _bump) =>
                  if !pubkeyEq derived pdAcct.key then fail mem
                  else
                    -- Drain buffer → payer.
                    if payer.lamports + buffer.lamports ≥ U64_MODULUS then
                      fail mem
                    else
                      let payerAfterDrain := payer.lamports + buffer.lamports
                      let m_drain := writeU64 mem payer.lamportsRefAddr payerAfterDrain
                      let m_buf0  := writeU64 m_drain buffer.lamportsRefAddr 0
                      -- Inter-Native CPI: System::CreateAccount. Synthesize
                      -- isSigner=true on the PDA-derived account (the loader's
                      -- invoke_signed in agave authorizes via the seeds).
                      let cpiPayer := { payer with lamports := payerAfterDrain }
                      let cpiPd    := { pdAcct with isSigner := true }
                      let createIx := encodeSystemCreateAccount
                                       (Nat.max 1 (rentMin programDataLen))
                                       programDataLen PROGRAM_ID_BYTES
                      match invokeSystem createIx [cpiPayer, cpiPd] m_buf0 with
                      | none => fail mem
                      | some (m_sys, sysCu) =>
                        -- After System::CreateAccount: programdata has lamports +
                        -- dataLen + owner set; payer is decremented.
                        -- Set ProgramData state.
                        let m7 := writeProgramDataState m_sys pdAcct.dataPtr 0
                                                       (some authority.key)
                        -- Copy buffer payload → programdata payload.
                        let src := readBytes m7 (buffer.dataPtr + bufferDataOffset)
                                              bufferDataLen
                        let m8 := writeBytes m7
                                  (pdAcct.dataPtr + SIZE_PROGRAMDATA_META)
                                  bufferDataLen src
                        -- Buffer dataLen → size_of_buffer(0) = 37.
                        let m9 := writeU64 m8 buffer.dataLenRefAddr
                                          SIZE_BUFFER_METADATA
                        let m10 := writeU64 m9 (buffer.dataPtr - 8)
                                            SIZE_BUFFER_METADATA
                        -- Program state → Program { programdata_address }.
                        let m11 := writeU32 m10 program.dataPtr TAG_PROGRAM
                        let m12 := writeBytes m11 (program.dataPtr + 4) 32
                                              pdAcct.key
                        -- NOTE: program.executable is left unset; see
                        -- module-level "executable flag on Deploy".
                        ⟨m12, 0, CU_DEFAULT + sysCu⟩
        | _ => fail mem
    | _ => fail mem  -- AccountAlreadyInitialized
  | _ => fail mem

/-- `Upgrade`. Accounts:
    0. `[writable]` ProgramData
    1. `[writable]` Program
    2. `[writable]` Buffer
    3. `[writable]` spill (recipient of excess lamports)
    4. `[]` Rent sysvar
    5. `[]` Clock sysvar
    6. `[signer]` upgrade authority -/
def execUpgrade (mem : Mem) (accts : List AcctInput) : NativeResult :=
  match accts with
  | pdAcct :: program :: buffer :: spill :: _rent :: _clock ::
    authority :: _ =>
    -- Verify Program account.
    if !program.isWritable then fail mem
    else if !isOwnerLoader program.owner then fail mem
    else
      match readState mem program.dataPtr program.dataLen with
      | .program programdataAddr =>
        if !pubkeyEq programdataAddr pdAcct.key then fail mem
        else
          -- Verify Buffer account.
          match readState mem buffer.dataPtr buffer.dataLen with
          | .buffer authorityAddr =>
            if !authorityEq authorityAddr (some authority.key) then fail mem
            else if !authority.isSigner then fail mem
            else
              let bufferDataOffset := SIZE_BUFFER_METADATA
              if buffer.dataLen < bufferDataOffset then fail mem
              else
                let bufferDataLen := buffer.dataLen - bufferDataOffset
                if bufferDataLen = 0 then fail mem
                else
                  -- Verify ProgramData account.
                  let balanceRequired := Nat.max 1 (rentMin pdAcct.dataLen)
                  if pdAcct.dataLen <
                       SIZE_PROGRAMDATA_META + bufferDataLen then fail mem
                  else if pdAcct.lamports + buffer.lamports
                            < balanceRequired then fail mem
                  else
                    match readState mem pdAcct.dataPtr pdAcct.dataLen with
                    | .programData _slot upgradeAuth =>
                      -- Same-slot check skipped (slot = 0 in our model).
                      if upgradeAuth.isNone then fail mem
                      else if !authorityEq upgradeAuth
                                            (some authority.key) then fail mem
                      else
                        -- Copy buffer payload → programdata payload.
                        let src := readBytes mem
                                    (buffer.dataPtr + bufferDataOffset)
                                    bufferDataLen
                        let m1 := writeBytes mem
                                    (pdAcct.dataPtr + SIZE_PROGRAMDATA_META)
                                    bufferDataLen src
                        -- Zero programdata[45+bufferDataLen..dataLen].
                        let tailStart :=
                          pdAcct.dataPtr + SIZE_PROGRAMDATA_META + bufferDataLen
                        let tailLen :=
                          pdAcct.dataLen - (SIZE_PROGRAMDATA_META + bufferDataLen)
                        let m2 := writeZeros m1 tailStart tailLen
                        -- Update ProgramData state with current slot.
                        let m3 := writeProgramDataState m2 pdAcct.dataPtr 0
                                                       (some authority.key)
                        -- Spill: spill += programdata + buffer - balance_required.
                        let totalLamports := pdAcct.lamports + buffer.lamports
                        let excess := totalLamports - balanceRequired
                        if spill.lamports + excess ≥ U64_MODULUS then fail mem
                        else
                          let m4 := writeU64 m3 spill.lamportsRefAddr
                                            (spill.lamports + excess)
                          let m5 := writeU64 m4 buffer.lamportsRefAddr 0
                          let m6 := writeU64 m5 pdAcct.lamportsRefAddr
                                            balanceRequired
                          -- Buffer dataLen → 37.
                          let m7 := writeU64 m6 buffer.dataLenRefAddr
                                            SIZE_BUFFER_METADATA
                          let m8 := writeU64 m7 (buffer.dataPtr - 8)
                                            SIZE_BUFFER_METADATA
                          ⟨m8, 0, CU_DEFAULT⟩
                    | _ => fail mem
          | _ => fail mem
      | _ => fail mem
  | _ => fail mem

/-- `ExtendProgram { additional_bytes }`. Accounts:
    0. `[writable]` ProgramData
    1. `[writable]` ProgramData's associated Program
    2. `[]` System program (optional)
    3. `[writable, signer]` payer (optional, only when rent gap > 0)

    The `check_authority` variant (`ExtendProgramChecked`, not in
    agave's 8 variants in this version) shifts the authority into
    account index 2 and the payer into 4. We model only the
    unchecked form. -/
def execExtendProgram (mem : Mem) (accts : List AcctInput)
    (additionalBytes : Nat) : NativeResult :=
  match accts with
  | pdAcct :: program :: rest =>
    if additionalBytes = 0 then fail mem
    else if !isOwnerLoader pdAcct.owner then fail mem
    else if !pdAcct.isWritable then fail mem
    else if !program.isWritable then fail mem
    else if !isOwnerLoader program.owner then fail mem
    else
      match readState mem program.dataPtr program.dataLen with
      | .program programdataAddr =>
        if !pubkeyEq programdataAddr pdAcct.key then fail mem
        else
          let oldLen := pdAcct.dataLen
          let newLen := oldLen + additionalBytes
          if newLen > MAX_PERMITTED_DATA_LENGTH then fail mem
          else
            -- SIMD-0431: additional_bytes ≥ MINIMUM_EXTEND_PROGRAM_BYTES
            -- unless within MINIMUM_EXTEND_PROGRAM_BYTES of the cap.
            let headroom := MAX_PERMITTED_DATA_LENGTH - oldLen
            if additionalBytes < MINIMUM_EXTEND_PROGRAM_BYTES ∧
               additionalBytes ≠ headroom then fail mem
            else
              match readState mem pdAcct.dataPtr pdAcct.dataLen with
              | .programData _slot upgradeAuth =>
                -- Same-slot check skipped (slot = 0 in our model).
                if upgradeAuth.isNone then fail mem
                else
                  -- Rent gap: balance_required = max(1, rent_min(newLen)) = 1.
                  -- If programdata already has ≥ 1 lamport, no transfer.
                  let balanceRequired := Nat.max 1 (rentMin newLen)
                  let needTransfer := pdAcct.lamports < balanceRequired
                  -- Inter-Native CPI System::Transfer for the rent gap.
                  let cpiResult : Option (Mem × Nat) :=
                    if needTransfer then
                      match rest with
                      | _sys :: payer :: _ =>
                        let required := balanceRequired - pdAcct.lamports
                        let transferIx := encodeSystemTransfer required
                        invokeSystem transferIx [payer, pdAcct] mem
                      | _ => none
                    else some (mem, 0)
                  match cpiResult with
                  | none => fail mem
                  | some (baseMem, sysCu) =>
                    -- Grow programdata.dataLen to newLen.
                    let m1 := writeU64 baseMem pdAcct.dataLenRefAddr newLen
                    let m2 := writeU64 m1 (pdAcct.dataPtr - 8) newLen
                    -- Re-write ProgramData state header (slot stays 0).
                    let m3 := writeProgramDataState m2 pdAcct.dataPtr 0
                                                    upgradeAuth
                    ⟨m3, 0, CU_DEFAULT + sysCu⟩
              | _ => fail mem
      | _ => fail mem
  | _ => fail mem

/-! ## Dispatcher -/

/-- Single dispatch entry. The Tier-1 #2 native-program convention is
    "return `some` whenever the program-id matches" — even
    unknown discriminants surface a deterministic `r0=1` so the
    failure doesn't silently fall through to the BPF registry. -/
def dispatch (ixData : ByteArray) (accts : List AcctInput) (mem : Mem) :
    Option NativeResult :=
  match decode ixData with
  | .initializeBuffer      => some (execInitializeBuffer mem accts)
  | .write off bytes       => some (execWrite mem accts off bytes)
  | .deployWithMaxDataLen n => some (execDeployWithMaxDataLen mem accts n)
  | .upgrade                => some (execUpgrade mem accts)
  | .setAuthority          => some (execSetAuthority mem accts)
  | .close                 => some (execClose mem accts)
  | .extendProgram n        => some (execExtendProgram mem accts n)
  | .setAuthorityChecked   => some (execSetAuthorityChecked mem accts)
  | .unknown _             => some ⟨mem, 1, CU_DEFAULT⟩

end Svm.Native.BpfLoaderUpgradeable
