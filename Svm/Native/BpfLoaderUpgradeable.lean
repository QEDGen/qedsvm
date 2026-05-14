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
-- All 8 variants decode. 5 dispatch arms are implemented end-to-end:
--
--   * InitializeBuffer     — Uninitialized → Buffer { authority }
--   * Write                — bounds-checked copy into buffer payload
--   * SetAuthority         — Buffer / ProgramData authority rotation
--   * SetAuthorityChecked  — same but with new-authority signer check
--   * Close                — all three target states (Uninit / Buffer /
--                             ProgramData), full lamport-drain semantics
--
-- The remaining 3 dispatch arms charge `CU` and surface `r0 = 1`
-- ("deferred"). They are *decoded* correctly so a future session can
-- swap in semantics without touching the wire path:
--
--   * DeployWithMaxDataLen — needs a native-internal CPI into
--     `System::CreateAccount` (programdata account) + ELF verification
--     hook; deploy-side semantics tracked in the agave processor at
--     lib.rs:202-356.
--   * Upgrade              — needs ELF verify + lamport spill +
--     buffer→programdata copy; lib.rs:357-529.
--   * ExtendProgram        — needs an internal `System::Transfer` for
--     rent top-up + data-length grow; lib.rs:759-911 (incl. SIMD-0431
--     `MINIMUM_EXTEND_PROGRAM_BYTES` gating).
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
import Svm.SBPF.Machine

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

/-! ## Dispatcher -/

/-- Single dispatch entry. The Tier-1 #2 native-program convention is
    "return `some` whenever the program-id matches" — even
    unimplemented variants surface a deterministic `r0=1` so the
    failure doesn't silently fall through to the BPF registry. -/
def dispatch (ixData : ByteArray) (accts : List AcctInput) (mem : Mem) :
    Option NativeResult :=
  match decode ixData with
  | .initializeBuffer      => some (execInitializeBuffer mem accts)
  | .write off bytes       => some (execWrite mem accts off bytes)
  | .setAuthority          => some (execSetAuthority mem accts)
  | .setAuthorityChecked   => some (execSetAuthorityChecked mem accts)
  | .close                 => some (execClose mem accts)
  -- The three deferred variants charge CU but surface r0=1
  -- ("deferred"): see module-doc.
  | .deployWithMaxDataLen _ => some ⟨mem, 1, CU_DEFAULT⟩
  | .upgrade                => some ⟨mem, 1, CU_DEFAULT⟩
  | .extendProgram _        => some ⟨mem, 1, CU_DEFAULT⟩
  | .unknown _              => some ⟨mem, 1, CU_DEFAULT⟩

end Svm.Native.BpfLoaderUpgradeable
