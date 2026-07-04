-- The Upgradeable BPF Loader (BPF Loader v3) — native, not BPF.
--
-- Reference: agave's `solana-bpf-loader-program/src/lib.rs`
-- (`process_loader_upgradeable_instruction`) and
-- `solana-loader-v3-interface-6.1.1/src/{state,instruction}.rs`.
-- PROGRAM_ID = `BPFLoaderUpgradeab1e11111111111111111111111`.
-- CU = `UPGRADEABLE_LOADER_COMPUTE_UNITS = 2370`, flat per invocation
-- (agave charges at the outer `process_instruction_inner` boundary; we
-- charge uniformly in `dispatch`).
--
-- All 8 variants decode and dispatch end-to-end (InitializeBuffer, Write,
-- DeployWithMaxDataLen, Upgrade, SetAuthority, Close, ExtendProgram,
-- SetAuthorityChecked).
--
-- ## Model simplifications (documented gaps)
--
-- agave-side machinery we don't replicate (charter: "spec where
-- meaningful, skip when machinery is harness-only"):
--
--   * **ELF verification.** agave's `deploy_program!` verifies the ELF
--     and caches the JIT program; we have no program cache, so
--     Deploy/Upgrade/Extend skip the verify side-effect. Loads go
--     through `Decode.decodeProgram` at invocation time anyway.
--   * **Rent::minimum_balance.** We model `rent_min(len) = 0` (Tier-2
--     deferred). So Deploy charges 1 lamport (the `max(1, rent_min)`
--     floor), Upgrade's spill leaves 1 lamport on programdata, and
--     ExtendProgram skips the top-up when programdata already has ≥ 1.
--   * **executable flag on Deploy.** agave's `set_executable(true)`
--     mutates the TransactionContext; AcctInput doesn't expose that
--     slot, so the harness surfaces executable=true via the
--     resulting_accounts builder and the Lean dispatch leaves it alone.
--   * **Inter-Native CPI (closed 2026-05-15).** Deploy/ExtendProgram do
--     `native_invoke_signed(system_instruction::…)` in agave (Cpi.cu =
--     946/call). We compose via `System.dispatch` directly with
--     synthetic `isSigner = true` on the PDA-derived account (agave's
--     invoke_signed authorizes via seeds). Deploy's CU = 2370+946+150 =
--     3466 matches agave; ExtendProgram's rent-gap Transfer (only when
--     `rent_min > 0`) charges the same 946+150 premium.
--   * **Close ProgramData same-slot freshness.** agave rejects Close
--     when `clock.slot == programdata.slot`; both = 0 in our model
--     would always fire, so we bypass the gate.
--
-- ## State layout (agave's `UpgradeableLoaderState`)
--
-- bincode enum, u32 LE tag. Pubkey `Option` = 1-byte presence flag + 32
-- bytes (account-data size fixed at `size_of_*_metadata` regardless).
--
--   tag 0  Uninitialized        4 bytes
--   tag 1  Buffer               37 bytes  [4 tag | 1 Some/None | 32 pubkey]
--   tag 2  Program              36 bytes  [4 tag | 32 programdata pubkey]
--   tag 3  ProgramData          45 bytes  [4 tag | 8 slot | 1 Some/None | 32 pubkey]
--
-- Buffer/programdata ELF payload follows the metadata to `accts[i].dataLen`.

import SVM.Native.AcctInput
import SVM.Native.System
import SVM.SBPF.Machine
import SVM.Syscalls.Pda
import SVM.Syscalls.Cpi

namespace SVM.Native.BpfLoaderUpgradeable

open SVM.SBPF.Memory
open SVM.SBPF (writeBytes readBytes)
open SVM.Native

/-- BPFLoaderUpgradeable program-id as a little-endian `Nat`.
    Raw bytes
    `[0x02, 0xa8, 0xf6, 0x91, 0x4e, 0x88, 0xa1, 0xb0, 0xe2, 0x10,
      0x15, 0x3e, 0xf7, 0x63, 0xae, 0x2b, 0x00, 0xc2, 0xb9, 0x3d,
      0x16, 0xc1, 0x24, 0xd2, 0xc0, 0x53, 0x7a, 0x10, 0x04, 0x80,
      0x00, 0x00]`. -/
def PROGRAM_ID : Nat :=
  0x00008004107a53c0d224c1163db9c2002bae63f73e1510e2b0a1884e91f6a802

/-- The 32-byte BPF Loader v3 program-id (owner-field check on Close/ExtendProgram/Upgrade). -/
def PROGRAM_ID_BYTES : ByteArray :=
  ⟨#[0x02, 0xa8, 0xf6, 0x91, 0x4e, 0x88, 0xa1, 0xb0,
     0xe2, 0x10, 0x15, 0x3e, 0xf7, 0x63, 0xae, 0x2b,
     0x00, 0xc2, 0xb9, 0x3d, 0x16, 0xc1, 0x24, 0xd2,
     0xc0, 0x53, 0x7a, 0x10, 0x04, 0x80, 0x00, 0x00]⟩

/-- `UPGRADEABLE_LOADER_COMPUTE_UNITS` from `programs/bpf_loader/src/lib.rs:37`.
    Flat charge consumed before dispatch in agave, so it accrues even when
    the inner match fails. -/
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

/-- Read the `LoaderState` at `dataPtr`. `dataLen` must be ≥ the
    variant's metadata size; truncated reads return `.invalid`. -/
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
    -- Option tag = 0; we zero the slot (agave leaves stale bytes) for reproducibility.
    let m2 := writeU32 m1 (dataPtr + 4) 0  -- only the option byte matters here
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
    let newR := recipient.lamports + target.lamports
    let m1 := writeU64 mem target.lamportsRefAddr 0
    let m2 := writeU64 m1 recipient.lamportsRefAddr newR
    -- Shrink data_len in both buffer-side and BPF input-buffer slots.
    let m3 := writeU64 m2 target.dataLenRefAddr SIZE_UNINITIALIZED
    let m4 := writeU64 m3 (target.dataPtr - 8) SIZE_UNINITIALIZED
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
    -- agave rejects `close.key == recipient.key`.
    if pubkeyEq closeAcct.key recipient.key then fail mem
    else
      match readState mem closeAcct.dataPtr closeAcct.dataLen with
      | .uninitialized =>
        if recipient.lamports + closeAcct.lamports ≥ U64_MODULUS then fail mem
        else
          let m1 := writeU64 mem closeAcct.lamportsRefAddr 0
          let m2 := writeU64 m1 recipient.lamportsRefAddr
                              (recipient.lamports + closeAcct.lamports)
          -- Tag stays Uninitialized; only data_len is set (agave's set_data_length).
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
            -- Slot-freshness gate bypassed: agave's `clock.slot == slot`
            -- would always fire with both = 0 in our model (known divergence).
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

Share the pattern "verify state-chain → manipulate lamports → copy
buffer payload → write state", and two simplifications (see top-doc):
`rent_min(_) = 0` (so `1.max(rent_min)` clamps to 1) and the inner
System CPI composed via `System.dispatch`. -/

/-- `solana_system_interface::MAX_PERMITTED_DATA_LENGTH`; deploy clamp. -/
private def MAX_PERMITTED_DATA_LENGTH : Nat := 10 * 1024 * 1024

/-- Stub for `Rent::minimum_balance(_)` = 0; `1.max(rent_min)` clamps to 1. -/
private def rentMin (_dataLen : Nat) : Nat := 0

/-- SIMD-0431: Extend must add ≥ 10 KiB unless within 10 KiB of
    MAX_PERMITTED_DATA_LENGTH. We treat agave's feature gate as always-active. -/
private def MINIMUM_EXTEND_PROGRAM_BYTES : Nat := 10240

/-! ### Inter-Native CPI composition

Build bincode ix data for the `SystemInstruction` variants we invoke as
inner CPI calls, then dispatch through `System.dispatch`. `Cpi.cu = 946`
is added (agave's `invoke_units`); System adds its own 150 via its result. -/

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

/-- Inner `System.dispatch` call adding `Cpi.cu = 946`. Returns `none` on
    dispatch failure or non-zero inner r0; otherwise the composed (mem, cu). -/
private def invokeSystem (ixData : ByteArray) (subAccts : List AcctInput)
    (mem : Mem) : Option (Mem × Nat) :=
  match System.dispatch ixData subAccts mem with
  | none => none
  | some r => if r.r0 = 0 then some (r.mem, SVM.SBPF.Cpi.cu + r.cu)
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
    -- Verify Program: Uninitialized + large enough (rent check skipped, `rentMin = 0`).
    match readState mem program.dataPtr program.dataLen with
    | .uninitialized =>
      if program.dataLen < SIZE_PROGRAM then fail mem
      else
        -- Verify Buffer: Buffer state + authority matches + signed.
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
                -- PDA verify: find_program_address([program.key], LOADER) == pdAcct.key.
                match SVM.SBPF.Pda.tryFindProgramAddress
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
                      -- CPI System::CreateAccount; synthetic isSigner on the
                      -- PDA (agave's invoke_signed authorizes via seeds).
                      let cpiPayer := { payer with lamports := payerAfterDrain }
                      let cpiPd    := { pdAcct with isSigner := true }
                      let createIx := encodeSystemCreateAccount
                                       (Nat.max 1 (rentMin programDataLen))
                                       programDataLen PROGRAM_ID_BYTES
                      match invokeSystem createIx [cpiPayer, cpiPd] m_buf0 with
                      | none => fail mem
                      | some (m_sys, sysCu) =>
                        -- Set ProgramData state.
                        let m7 := writeProgramDataState m_sys pdAcct.dataPtr 0
                                                       (some authority.key)
                        -- Copy buffer payload → programdata payload.
                        let src := readBytes m7 (buffer.dataPtr + bufferDataOffset)
                                              bufferDataLen
                        let m8 := writeBytes m7
                                  (pdAcct.dataPtr + SIZE_PROGRAMDATA_META)
                                  bufferDataLen src
                        -- Buffer dataLen → size_of_buffer = 37.
                        let m9 := writeU64 m8 buffer.dataLenRefAddr
                                          SIZE_BUFFER_METADATA
                        let m10 := writeU64 m9 (buffer.dataPtr - 8)
                                            SIZE_BUFFER_METADATA
                        -- Program state → Program { programdata_address }.
                        let m11 := writeU32 m10 program.dataPtr TAG_PROGRAM
                        let m12 := writeBytes m11 (program.dataPtr + 4) 32
                                              pdAcct.key
                        -- program.executable left unset; see "executable flag on Deploy".
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
    if !program.isWritable then fail mem
    else if !isOwnerLoader program.owner then fail mem
    else
      match readState mem program.dataPtr program.dataLen with
      | .program programdataAddr =>
        if !pubkeyEq programdataAddr pdAcct.key then fail mem
        else
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
                        let m3 := writeProgramDataState m2 pdAcct.dataPtr 0
                                                       (some authority.key)
                        -- Spill = programdata + buffer - balance_required.
                        let totalLamports := pdAcct.lamports + buffer.lamports
                        let excess := totalLamports - balanceRequired
                        if spill.lamports + excess ≥ U64_MODULUS then fail mem
                        else
                          let m4 := writeU64 m3 spill.lamportsRefAddr
                                            (spill.lamports + excess)
                          let m5 := writeU64 m4 buffer.lamportsRefAddr 0
                          let m6 := writeU64 m5 pdAcct.lamportsRefAddr
                                            balanceRequired
                          let m7 := writeU64 m6 buffer.dataLenRefAddr
                                            SIZE_BUFFER_METADATA
                          let m8 := writeU64 m7 (buffer.dataPtr - 8)
                                            SIZE_BUFFER_METADATA
                          ⟨m8, 0, CU_DEFAULT⟩
                    | _ => fail mem
          | _ => fail mem
      | _ => fail mem
  | _ => fail mem

/-- Rent-gap CPI for `ExtendProgram`: System::Transfer from the payer when
    the grown ProgramData needs lamports; `some (mem, 0)` (no-op) when it
    already holds enough. Named (not an inline `let`) so the boundedness
    sweep below sees a clean `extendRentCpi … = some …` case equation. -/
private def extendRentCpi (rest : List AcctInput) (pdAcct : AcctInput)
    (balanceRequired : Nat) (mem : Mem) : Option (Mem × Nat) :=
  if pdAcct.lamports < balanceRequired then
    match rest with
    | _sys :: payer :: _ =>
      invokeSystem (encodeSystemTransfer (balanceRequired - pdAcct.lamports))
        [payer, pdAcct] mem
    | _ => none
  else some (mem, 0)

/-- `ExtendProgram { additional_bytes }`. Accounts:
    0. `[writable]` ProgramData
    1. `[writable]` ProgramData's associated Program
    2. `[]` System program (optional)
    3. `[writable, signer]` payer (optional, only when rent gap > 0)

    We model only the unchecked form (`ExtendProgramChecked` isn't in
    agave's 8 variants this version). -/
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
                  -- Rent gap = max(1, rent_min(newLen)) = 1; no transfer if already ≥ 1.
                  let balanceRequired := Nat.max 1 (rentMin newLen)
                  match extendRentCpi rest pdAcct balanceRequired mem with
                  | none => fail mem
                  | some (baseMem, sysCu) =>
                    -- Grow programdata.dataLen to newLen.
                    let m1 := writeU64 baseMem pdAcct.dataLenRefAddr newLen
                    let m2 := writeU64 m1 (pdAcct.dataPtr - 8) newLen
                    let m3 := writeProgramDataState m2 pdAcct.dataPtr 0
                                                    upgradeAuth
                    ⟨m3, 0, CU_DEFAULT + sysCu⟩
              | _ => fail mem
      | _ => fail mem
  | _ => fail mem

/-! ## Dispatcher -/

/-- Single dispatch entry: returns `some` whenever the program-id matches,
    so unknown discriminants surface `r0=1` instead of falling through to
    the BPF registry. -/
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

/-! ## Boundedness — the loader leg of the `hnative` discharge
(`SVM/SBPF/BoundedCpi.lean`): every dispatch returns a u64 `r0` (always
`0`/`1`) and byte-bounded caller memory. In-file because the state
serializers (`writeU32`/`writeZeros`/`writeBufferState`/
`writeProgramDataState`), `commonCloseAccount`, and the System sub-call
(`invokeSystem`) are private. -/

private theorem writeU32_lt (mem : Mem) (addr v : Nat)
    (hm : ∀ a, mem a < 256) : ∀ a, writeU32 mem addr v a < 256 := by
  intro a
  apply SVM.SBPF.Mem.read_mk_lt
  intro x
  repeat first
    | apply SVM.SBPF.ite_lt
    | exact Nat.mod_lt _ (by decide)
    | exact hm _

private theorem writeZeros_lt (mem : Mem) (addr len : Nat)
    (hm : ∀ a, mem a < 256) : ∀ a, writeZeros mem addr len a < 256 := by
  intro a
  apply SVM.SBPF.Mem.read_mk_lt
  intro x
  apply SVM.SBPF.ite_lt
  · decide
  · exact hm _

private theorem writeBufferState_lt (mem : Mem) (dataPtr : Nat)
    (auth : Option ByteArray) (hm : ∀ a, mem a < 256) :
    ∀ a, writeBufferState mem dataPtr auth a < 256 := by
  unfold writeBufferState
  cases auth
  · exact writeZeros_lt _ _ _ (writeU32_lt _ _ _ (writeU32_lt _ _ _ hm))
  · refine SVM.SBPF.writeBytes_lt _ _ _ _ ?_
    intro x
    apply SVM.SBPF.Mem.read_mk_lt
    intro y
    apply SVM.SBPF.ite_lt
    · decide
    · exact writeU32_lt _ _ _ hm _

private theorem writeProgramDataState_lt (mem : Mem) (dataPtr slot : Nat)
    (auth : Option ByteArray) (hm : ∀ a, mem a < 256) :
    ∀ a, writeProgramDataState mem dataPtr slot auth a < 256 := by
  unfold writeProgramDataState
  cases auth
  · refine writeZeros_lt _ _ _ ?_
    intro x
    apply SVM.SBPF.Mem.read_mk_lt
    intro y
    apply SVM.SBPF.ite_lt
    · decide
    · exact SVM.SBPF.writeU64_lt _ _ _ (writeU32_lt _ _ _ hm) _
  · refine SVM.SBPF.writeBytes_lt _ _ _ _ ?_
    intro x
    apply SVM.SBPF.Mem.read_mk_lt
    intro y
    apply SVM.SBPF.ite_lt
    · decide
    · exact SVM.SBPF.writeU64_lt _ _ _ (writeU32_lt _ _ _ hm) _

private theorem invokeSystem_bounded {ixData : ByteArray}
    {subAccts : List AcctInput} {mem m' : Mem} {cu' : Nat}
    (h : invokeSystem ixData subAccts mem = some (m', cu'))
    (hm : ∀ a, mem a < 256) : ∀ a, m' a < 256 := by
  unfold invokeSystem at h
  cases hd : System.dispatch ixData subAccts mem with
  | none => rw [hd] at h; exact nomatch h
  | some r =>
    rw [hd] at h
    simp only [] at h
    split at h
    · injection h with h
      injection h with h1 h2
      exact h1 ▸ (System.dispatch_bounded hm hd).2
    · exact nomatch h

private theorem extendRentCpi_bounded {rest : List AcctInput}
    {pdAcct : AcctInput} {balanceRequired : Nat} {mem m' : Mem} {cu' : Nat}
    (h : extendRentCpi rest pdAcct balanceRequired mem = some (m', cu'))
    (hm : ∀ a, mem a < 256) : ∀ a, m' a < 256 := by
  unfold extendRentCpi at h
  split at h
  · split at h
    · exact invokeSystem_bounded h hm
    · exact nomatch h
  · injection h with h
    injection h with h1 h2
    exact h1 ▸ hm

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 65536 in
theorem dispatch_bounded {ixData : ByteArray} {accts : List AcctInput}
    {mem : Mem} {nr : NativeResult} (hm : ∀ a, mem a < 256)
    (h : dispatch ixData accts mem = some nr) :
    nr.r0 < SVM.SBPF.U64_MODULUS ∧ ∀ a, nr.mem a < 256 := by
  have hzero : (0 : Nat) < SVM.SBPF.U64_MODULUS := by decide
  have hone : (1 : Nat) < SVM.SBPF.U64_MODULUS := by decide
  unfold dispatch at h
  repeat' split at h
  all_goals (injection h with h; subst h)
  -- Per-exec control-flow case analysis via `fun_cases` — NOT `split`, whose
  -- internal branch simp max-steps on these zeta-inlined write-chain trees.
  -- `fun_cases` keeps leaf calls (`commonCloseAccount`, the serializers,
  -- `invokeSystem`) folded and names the CPI result equation, so the
  -- `invokeSystem_bounded (by assumption)` closer can consume it.
  all_goals
    first
      | exact ⟨hone, hm⟩
      | exact ⟨hzero, hm⟩
      | (first
          | fun_cases execInitializeBuffer
          | fun_cases execWrite
          | fun_cases execSetAuthority
          | fun_cases execSetAuthorityChecked
          | fun_cases execClose
          | fun_cases execDeployWithMaxDataLen
          | fun_cases execUpgrade
          | fun_cases execExtendProgram
         all_goals try fun_cases commonCloseAccount
         all_goals refine ⟨?_, ?_⟩
         all_goals
           first
             | exact hzero
             | exact hone
             | (intro a
                repeat first
                  | exact hm
                  | exact hm _
                  | (refine SVM.SBPF.writeU64_lt _ _ _ ?_)
                  | (refine SVM.SBPF.writeU64_lt _ _ _ ?_ _)
                  | (refine SVM.SBPF.writeBytes_lt _ _ _ _ ?_)
                  | (refine SVM.SBPF.writeBytes_lt _ _ _ _ ?_ _)
                  | (refine writeU32_lt _ _ _ ?_)
                  | (refine writeU32_lt _ _ _ ?_ _)
                  | (refine writeZeros_lt _ _ _ ?_)
                  | (refine writeZeros_lt _ _ _ ?_ _)
                  | (refine writeBufferState_lt _ _ _ ?_)
                  | (refine writeBufferState_lt _ _ _ ?_ _)
                  | (refine writeProgramDataState_lt _ _ _ _ ?_)
                  | (refine writeProgramDataState_lt _ _ _ _ ?_ _)
                  | (refine invokeSystem_bounded (by assumption) ?_)
                  | (refine invokeSystem_bounded (by assumption) ?_ _)
                  | (refine extendRentCpi_bounded (by assumption) ?_)
                  | (refine extendRentCpi_bounded (by assumption) ?_ _)
                  -- Serializer bodies iota-reduce on concrete `some` args
                  -- into raw `Mem` literals: open pointwise, keep peeling.
                  | (apply SVM.SBPF.Mem.read_mk_lt; intro _)
                  | apply SVM.SBPF.ite_lt
                  | exact Nat.mod_lt _ (by decide)
                  | omega
                  | intro _))

end SVM.Native.BpfLoaderUpgradeable
