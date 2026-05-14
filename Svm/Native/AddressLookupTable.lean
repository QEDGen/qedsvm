-- The Solana AddressLookupTable program — native, not BPF.
--
-- Reference: agave's `solana-address-lookup-table-program-2.2.4`
-- (`processor.rs`) and the `solana-address-lookup-table-interface`
-- (`state.rs`, `instruction.rs`).
--
-- Five instructions: CreateLookupTable, FreezeLookupTable,
-- ExtendLookupTable, DeactivateLookupTable, CloseLookupTable.
-- All take the LUT account at `accts[0]` and an authority signer
-- at `accts[1]`. Create and Extend additionally need a payer at
-- `accts[2]` and the System program at `accts[3]`. Close needs a
-- recipient at `accts[2]`.
--
-- The LUT account's data layout (LOOKUP_TABLE_META_SIZE = 56 bytes
-- header, then a list of 32-byte addresses):
-- ```
-- bytes 0..4   u32 LE  ProgramState variant tag (=1 LookupTable)
-- bytes 4..12  u64 LE  deactivation_slot (= u64::MAX when active)
-- bytes 12..20 u64 LE  last_extended_slot
-- bytes 20..21 u8      last_extended_slot_start_index
-- bytes 21..22 u8      authority Option tag (1=Some, 0=None)
-- bytes 22..54 Pubkey  authority (zero-padded when None)
-- bytes 54..56 u16     padding (always 0)
-- bytes 56..N  list of 32-byte addresses
-- ```
--
-- Slot-related operations (Create/Extend/Deactivate/Close) read
-- the "current slot" from the Clock sysvar; formal-svm's Clock
-- stub returns 0, so cross-engine equality requires mollusk to
-- match. The SlotHashes-based cool-down for Close is approximated
-- by checking `deactivation_slot + DEACTIVATION_COOLDOWN ≤
-- current_slot` (where DEACTIVATION_COOLDOWN = MAX_ENTRIES = 512).

import Svm.Native.AcctInput
import Svm.SBPF.Machine
import Svm.SBPF.Sha256
import Svm.SBPF.Curve25519

namespace Svm.Native.AddressLookupTable

open Svm.SBPF.Memory
open Svm.SBPF (writeBytes)
open Svm.Native

/-- AddressLookupTable program-id
    (`AddressLookupTab1e1111111111111111111111111`) as a LE-encoded
    `Nat`. The raw bytes are
    `[2, 119, 166, 175, 151, 51, 155, 122, 200, 141, 24, 146, 201,
    4, 70, 245, 0, 2, 48, 146, 102, 246, 46, 83, 193, 24, 36, 73,
    130, 0, 0, 0]`. -/
def PROGRAM_ID : Nat :=
  0x00000082492418c1532ef66692300200f54604c992188dc87a9b3397afa67702

/-- `DEFAULT_COMPUTE_UNITS` from
    `solana-address-lookup-table-program/src/processor.rs`. Same flat
    charge for every variant. -/
def CU_DEFAULT : Nat := 750

/-- Max addresses a lookup table can hold (`LOOKUP_TABLE_MAX_ADDRESSES`). -/
def LOOKUP_TABLE_MAX_ADDRESSES : Nat := 256

/-- Serialized size of the meta header (`LOOKUP_TABLE_META_SIZE`). -/
def LOOKUP_TABLE_META_SIZE : Nat := 56

/-- `u64::MAX` — the "active" sentinel for `deactivation_slot`. -/
def U64_MAX : Nat := 0xFFFFFFFFFFFFFFFF

/-- Cool-down window after deactivation. Agave uses `SlotHashes`
    position; we approximate with `MAX_ENTRIES = 512` slots, matching
    `solana_slot_hashes::MAX_ENTRIES`. -/
def DEACTIVATION_COOLDOWN : Nat := 512

/-! ## Meta layout offsets -/

private def OFF_VARIANT_TAG       : Nat := 0
private def OFF_DEACTIVATION_SLOT : Nat := 4
private def OFF_LAST_EXTENDED     : Nat := 12
private def OFF_LAST_EXT_INDEX    : Nat := 20
private def OFF_AUTHORITY_TAG     : Nat := 21
private def OFF_AUTHORITY_PUBKEY  : Nat := 22
private def OFF_PADDING           : Nat := 54
private def OFF_ADDRESSES_START   : Nat := 56

/-- The ProgramState variant tag value for `LookupTable`. -/
private def STATE_TAG_LOOKUP_TABLE : Nat := 1

/-! ## Stubbed "current slot"

Agave reads the Clock sysvar's `slot` field via the invoke_context.
formal-svm models per-instruction, so there's no actual block
height — we use 0 as the canonical "current slot". Mollusk's
default Clock also defaults to slot=0, so this matches for
cross-engine tests. If a real fixture needs non-zero, plumb the
Clock state through and read here. -/
private def currentSlot : Nat := 0

/-! ## Instruction enum + decode -/

inductive AltIx
  /-- `CreateLookupTable { recent_slot, bump_seed }`. Discriminant 0. -/
  | createLookupTable (recentSlot bumpSeed : Nat)
  /-- `FreezeLookupTable`. Discriminant 1. -/
  | freezeLookupTable
  /-- `ExtendLookupTable { new_addresses }`. Discriminant 2. -/
  | extendLookupTable (newAddresses : List ByteArray)
  /-- `DeactivateLookupTable`. Discriminant 3. -/
  | deactivateLookupTable
  /-- `CloseLookupTable`. Discriminant 4. -/
  | closeLookupTable
  /-- Forward-compat. -/
  | unknown (discriminant : Nat)
  deriving Inhabited

/-- Read a u32 LE at offset `off`. -/
private def readU32LE (bs : ByteArray) (off : Nat) : Nat :=
  if off + 4 > bs.size then 0
  else
    (bs.get! off).toNat +
    (bs.get! (off + 1)).toNat * 0x100 +
    (bs.get! (off + 2)).toNat * 0x10000 +
    (bs.get! (off + 3)).toNat * 0x1000000

/-- Read a u64 LE at offset `off`. -/
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

/-- Read a 32-byte pubkey at offset `off`. -/
private def readPubkey (bs : ByteArray) (off : Nat) : ByteArray :=
  if off + 32 > bs.size then ByteArray.empty
  else bs.extract off (off + 32)

/-- Decode `ix.data`. The wire format is bincode with a u32 LE
    discriminant. ExtendLookupTable carries a `Vec<Pubkey>` with a
    u64 LE length followed by `len * 32` bytes. -/
def decode (ixData : ByteArray) : AltIx :=
  let disc := readU32LE ixData 0
  match disc with
  | 0 =>
    -- CreateLookupTable: recent_slot(u64) | bump_seed(u8)
    let slot := readU64LE ixData 4
    let bump := if ixData.size ≥ 13 then (ixData.get! 12).toNat else 0
    .createLookupTable slot bump
  | 1 => .freezeLookupTable
  | 2 =>
    -- ExtendLookupTable: new_addresses : Vec<Pubkey> (u64 len + len * 32 bytes)
    let len := readU64LE ixData 4
    let start := 12
    let addrs : List ByteArray :=
      (List.range len).map (fun i => readPubkey ixData (start + i * 32))
    .extendLookupTable addrs
  | 3 => .deactivateLookupTable
  | 4 => .closeLookupTable
  | d => .unknown d

/-! ## Meta read/write helpers

The LUT's account data starts at `acct.dataPtr` in caller memory.
Reading/writing the meta touches the first `LOOKUP_TABLE_META_SIZE`
bytes; the address list lives at `dataPtr + OFF_ADDRESSES_START`. -/

private def readVariantTag (mem : Mem) (dataPtr : Nat) : Nat :=
  let b0 := mem  dataPtr       % 256
  let b1 := mem (dataPtr + 1)  % 256
  let b2 := mem (dataPtr + 2)  % 256
  let b3 := mem (dataPtr + 3)  % 256
  b0 + b1 * 0x100 + b2 * 0x10000 + b3 * 0x1000000

private def readDeactivationSlot (mem : Mem) (dataPtr : Nat) : Nat :=
  readU64 mem (dataPtr + OFF_DEACTIVATION_SLOT)

private def readLastExtendedSlot (mem : Mem) (dataPtr : Nat) : Nat :=
  readU64 mem (dataPtr + OFF_LAST_EXTENDED)

private def readLastExtIndex (mem : Mem) (dataPtr : Nat) : Nat :=
  (mem (dataPtr + OFF_LAST_EXT_INDEX)) % 256

private def readAuthorityTag (mem : Mem) (dataPtr : Nat) : Nat :=
  (mem (dataPtr + OFF_AUTHORITY_TAG)) % 256

private def readAuthority (mem : Mem) (dataPtr : Nat) : ByteArray :=
  Svm.SBPF.readBytes mem (dataPtr + OFF_AUTHORITY_PUBKEY) 32

/-- Write a u32 LE at `addr`. -/
private def writeU32 (mem : Mem) (addr v : Nat) : Mem :=
  fun a =>
    if a = addr     then v % 0x100
    else if a = addr + 1 then v / 0x100 % 0x100
    else if a = addr + 2 then v / 0x10000 % 0x100
    else if a = addr + 3 then v / 0x1000000 % 0x100
    else mem a

/-- Write a single byte at `addr`. -/
private def writeU8 (mem : Mem) (addr v : Nat) : Mem :=
  fun a => if a = addr then v % 0x100 else mem a

/-- ByteArray-equality on 32-byte pubkeys. -/
private def pubkeyEq (a b : ByteArray) : Bool :=
  a.size = b.size && (List.range a.size).all (fun i => a.get! i = b.get! i)

/-- Is `b` the all-zero 32-byte pubkey? -/
private def isZeroPubkey (b : ByteArray) : Bool :=
  b.size = 32 && (List.range 32).all (fun i => b.get! i = 0)

/-- A 32-byte all-zero ByteArray. Used to scrub the authority slot
    when freezing a table. -/
private def zero32 : ByteArray :=
  (List.range 32).foldl (fun acc _ => acc.push 0) ByteArray.empty

/-! ## PDA derivation (internal)

`Pubkey::create_program_address(&[authority, recent_slot.to_le_bytes(),
&[bump_seed]], &alt_program_id)`. Same algorithm as the
`sol_create_program_address` syscall: hash all seeds + program_id +
the `"ProgramDerivedAddress"` suffix, fail if the result is on the
ed25519 curve. -/

/-- The 21-byte suffix agave appends in `create_program_address`. -/
private def PDA_MARKER : ByteArray :=
  ⟨"ProgramDerivedAddress".toUTF8.toList.toArray⟩

/-- Encode a u64 little-endian as 8 bytes. -/
private def u64LE (n : Nat) : ByteArray :=
  ⟨(List.range 8).map (fun i => ((n / 256^i) % 256).toUInt8) |>.toArray⟩

/-- The ALT program-id as a 32-byte ByteArray (the raw form expected
    by the PDA derivation). -/
private def PROGRAM_ID_BYTES : ByteArray := ⟨#[
  2, 119, 166, 175, 151, 51, 155, 122, 200, 141, 24, 146, 201, 4,
  70, 245, 0, 2, 48, 146, 102, 246, 46, 83, 193, 24, 36, 73, 130,
  0, 0, 0]⟩

/-- Derive the lookup-table address. Seeds: authority pubkey,
    `recent_slot` u64 LE, single-byte `bump_seed`. Returns the
    32-byte derived address, or `none` if the result is on-curve
    (i.e. not a valid PDA per agave's algorithm). -/
def deriveLookupTableAddress (authority : ByteArray) (recentSlot bumpSeed : Nat) :
    Option ByteArray :=
  let bumpBytes : ByteArray := ⟨#[bumpSeed.toUInt8]⟩
  let preimage := authority ++ u64LE recentSlot ++ bumpBytes
              ++ PROGRAM_ID_BYTES ++ PDA_MARKER
  let h := Svm.SBPF.Sha256.hash preimage
  -- Reject if the hash is a valid Edwards point (i.e. could be a
  -- real pubkey with a known private key).
  if Svm.SBPF.Curve25519.validateEdwards h then none else some h

/-! ## Executions -/

/-- Execute `FreezeLookupTable`. Sets authority to None. Required:
    LUT account owned by ALT, authority signs, table active (not
    deactivated), has at least one address.
    Accounts: [LUT, authority]. -/
def execFreezeLookupTable (mem : Mem) (accts : List AcctInput) :
    NativeResult :=
  match accts with
  | lut :: auth :: _ =>
    -- Owner must be ALT. lut.owner is 32 bytes; compare to PROGRAM_ID_BYTES.
    if !pubkeyEq lut.owner PROGRAM_ID_BYTES then ⟨mem, 1, CU_DEFAULT⟩
    else if !auth.isSigner then ⟨mem, 1, CU_DEFAULT⟩
    else if lut.dataLen < LOOKUP_TABLE_META_SIZE then ⟨mem, 1, CU_DEFAULT⟩
    else
      let variantTag := readVariantTag mem lut.dataPtr
      let authTag := readAuthorityTag mem lut.dataPtr
      if variantTag ≠ STATE_TAG_LOOKUP_TABLE then ⟨mem, 1, CU_DEFAULT⟩
      else if authTag = 0 then ⟨mem, 1, CU_DEFAULT⟩  -- already frozen
      else
        let curAuth := readAuthority mem lut.dataPtr
        if !pubkeyEq curAuth auth.key then ⟨mem, 1, CU_DEFAULT⟩
        else if readDeactivationSlot mem lut.dataPtr ≠ U64_MAX then
          ⟨mem, 1, CU_DEFAULT⟩  -- can't freeze deactivated tables
        else if lut.dataLen ≤ LOOKUP_TABLE_META_SIZE then
          ⟨mem, 1, CU_DEFAULT⟩  -- empty tables can't be frozen
        else
          -- Clear authority tag + zero the 32-byte pubkey slot.
          let m1 := writeU8 mem (lut.dataPtr + OFF_AUTHORITY_TAG) 0
          let m2 := writeBytes m1 (lut.dataPtr + OFF_AUTHORITY_PUBKEY) 32 zero32
          ⟨m2, 0, CU_DEFAULT⟩
  | _ => ⟨mem, 1, CU_DEFAULT⟩

/-- Execute `DeactivateLookupTable`. Sets `deactivation_slot` to the
    current slot. Required: ALT-owned, authority signs, table active.
    Accounts: [LUT, authority]. -/
def execDeactivateLookupTable (mem : Mem) (accts : List AcctInput) :
    NativeResult :=
  match accts with
  | lut :: auth :: _ =>
    if !pubkeyEq lut.owner PROGRAM_ID_BYTES then ⟨mem, 1, CU_DEFAULT⟩
    else if !auth.isSigner then ⟨mem, 1, CU_DEFAULT⟩
    else if lut.dataLen < LOOKUP_TABLE_META_SIZE then ⟨mem, 1, CU_DEFAULT⟩
    else
      let variantTag := readVariantTag mem lut.dataPtr
      let authTag := readAuthorityTag mem lut.dataPtr
      if variantTag ≠ STATE_TAG_LOOKUP_TABLE then ⟨mem, 1, CU_DEFAULT⟩
      else if authTag = 0 then ⟨mem, 1, CU_DEFAULT⟩  -- frozen
      else
        let curAuth := readAuthority mem lut.dataPtr
        if !pubkeyEq curAuth auth.key then ⟨mem, 1, CU_DEFAULT⟩
        else if readDeactivationSlot mem lut.dataPtr ≠ U64_MAX then
          ⟨mem, 1, CU_DEFAULT⟩  -- already deactivated
        else
          let m := writeU64 mem (lut.dataPtr + OFF_DEACTIVATION_SLOT) currentSlot
          ⟨m, 0, CU_DEFAULT⟩
  | _ => ⟨mem, 1, CU_DEFAULT⟩

/-- Execute `CloseLookupTable`. Transfer LUT lamports to recipient,
    then zero the LUT account.
    Accounts: [LUT, authority, recipient]. Requires deactivated
    (deactivation_slot + DEACTIVATION_COOLDOWN ≤ current_slot). -/
def execCloseLookupTable (mem : Mem) (accts : List AcctInput) :
    NativeResult :=
  match accts with
  | lut :: auth :: recipient :: _ =>
    if !pubkeyEq lut.owner PROGRAM_ID_BYTES then ⟨mem, 1, CU_DEFAULT⟩
    else if !auth.isSigner then ⟨mem, 1, CU_DEFAULT⟩
    else if pubkeyEq lut.key recipient.key then ⟨mem, 1, CU_DEFAULT⟩
    else if lut.dataLen < LOOKUP_TABLE_META_SIZE then ⟨mem, 1, CU_DEFAULT⟩
    else
      let variantTag := readVariantTag mem lut.dataPtr
      let authTag := readAuthorityTag mem lut.dataPtr
      if variantTag ≠ STATE_TAG_LOOKUP_TABLE then ⟨mem, 1, CU_DEFAULT⟩
      else if authTag = 0 then ⟨mem, 1, CU_DEFAULT⟩  -- frozen
      else
        let curAuth := readAuthority mem lut.dataPtr
        if !pubkeyEq curAuth auth.key then ⟨mem, 1, CU_DEFAULT⟩
        else
          let deact := readDeactivationSlot mem lut.dataPtr
          if deact = U64_MAX then ⟨mem, 1, CU_DEFAULT⟩
          else if deact + DEACTIVATION_COOLDOWN > currentSlot then
            ⟨mem, 1, CU_DEFAULT⟩  -- still cooling down
          else
            -- Transfer all LUT lamports to recipient; zero LUT.
            let lutLam := lut.lamports
            let newRec := recipient.lamports + lutLam
            let m1 := writeU64 mem lut.lamportsRefAddr 0
            let m2 := writeU64 m1 recipient.lamportsRefAddr newRec
            let m3 := writeU64 m2 lut.dataLenRefAddr 0
            let m4 := writeU64 m3 (lut.dataPtr - 8) 0
            ⟨m4, 0, CU_DEFAULT⟩
  | _ => ⟨mem, 1, CU_DEFAULT⟩

/-- Execute `ExtendLookupTable`. Append `newAddresses` to the LUT's
    address list, update meta's `last_extended_slot` /
    `last_extended_slot_start_index`, grow the data buffer.
    Accounts: [LUT, authority, payer?, system_program?].

    We don't model the rent top-up (would need a Rent sysvar + an
    internal System::transfer); we require the LUT account to
    already have enough lamports. -/
def execExtendLookupTable (mem : Mem) (accts : List AcctInput)
    (newAddresses : List ByteArray) : NativeResult :=
  match accts with
  | lut :: auth :: _ =>
    if !pubkeyEq lut.owner PROGRAM_ID_BYTES then ⟨mem, 1, CU_DEFAULT⟩
    else if !auth.isSigner then ⟨mem, 1, CU_DEFAULT⟩
    else if lut.dataLen < LOOKUP_TABLE_META_SIZE then ⟨mem, 1, CU_DEFAULT⟩
    else
      let variantTag := readVariantTag mem lut.dataPtr
      let authTag := readAuthorityTag mem lut.dataPtr
      if variantTag ≠ STATE_TAG_LOOKUP_TABLE then ⟨mem, 1, CU_DEFAULT⟩
      else if authTag = 0 then ⟨mem, 1, CU_DEFAULT⟩
      else
        let curAuth := readAuthority mem lut.dataPtr
        if !pubkeyEq curAuth auth.key then ⟨mem, 1, CU_DEFAULT⟩
        else if readDeactivationSlot mem lut.dataPtr ≠ U64_MAX then
          ⟨mem, 1, CU_DEFAULT⟩
        else if newAddresses.isEmpty then ⟨mem, 1, CU_DEFAULT⟩
        else
          let curAddrsBytes := lut.dataLen - LOOKUP_TABLE_META_SIZE
          let curAddrsLen   := curAddrsBytes / 32
          let newLen        := curAddrsLen + newAddresses.length
          if newLen > LOOKUP_TABLE_MAX_ADDRESSES then ⟨mem, 1, CU_DEFAULT⟩
          else
            -- Write each new address at the tail of the address list.
            let appendAt := lut.dataPtr + LOOKUP_TABLE_META_SIZE + curAddrsLen * 32
            let m1 := (newAddresses.zip (List.range newAddresses.length)).foldl
              (fun acc p => writeBytes acc (appendAt + p.2 * 32) 32 p.1) mem
            -- Update last_extended_slot + start_index if the slot is new.
            let lastExt := readLastExtendedSlot mem lut.dataPtr
            let m2 :=
              if lastExt = currentSlot then m1
              else
                let m' := writeU64 m1 (lut.dataPtr + OFF_LAST_EXTENDED) currentSlot
                writeU8 m' (lut.dataPtr + OFF_LAST_EXT_INDEX) curAddrsLen
            -- Grow the data buffer: new size = META + newLen * 32.
            let newDataLen := LOOKUP_TABLE_META_SIZE + newLen * 32
            let m3 := writeU64 m2 lut.dataLenRefAddr newDataLen
            let m4 := writeU64 m3 (lut.dataPtr - 8) newDataLen
            ⟨m4, 0, CU_DEFAULT⟩
  | _ => ⟨mem, 1, CU_DEFAULT⟩

/-- Execute `CreateLookupTable`. Verify the PDA derivation, allocate
    LOOKUP_TABLE_META_SIZE bytes for the LUT, assign it to the ALT
    program, and write the initial meta. Mirrors agave's
    `Processor::create_lookup_table` without the internal System
    CPIs (we inline the equivalent state mutations).

    Accounts: [LUT, authority, payer, system_program].
    Idempotent if the LUT account is already ALT-owned. -/
def execCreateLookupTable (mem : Mem) (accts : List AcctInput)
    (recentSlot bumpSeed : Nat) : NativeResult :=
  match accts with
  | lut :: auth :: payer :: _ =>
    if !payer.isSigner then ⟨mem, 1, CU_DEFAULT⟩
    else
      -- Skip the SlotHashes recency check — we'd need that sysvar
      -- plumbed. Mollusk's default Clock supplies slot=0 so any
      -- non-future slot passes its check; mirror that.
      match deriveLookupTableAddress auth.key recentSlot bumpSeed with
      | none => ⟨mem, 1, CU_DEFAULT⟩  -- PDA on curve (rejected)
      | some derived =>
        if !pubkeyEq lut.key derived then ⟨mem, 1, CU_DEFAULT⟩
        else if pubkeyEq lut.owner PROGRAM_ID_BYTES then
          -- Already initialized — agave returns Ok early.
          ⟨mem, 0, CU_DEFAULT⟩
        else
          -- Inline System::allocate(LOOKUP_TABLE_META_SIZE),
          -- System::assign(ALT), then init the meta. No rent
          -- top-up: we require the LUT account to already have
          -- enough lamports for rent-exempt minimum.
          let m1 := writeU64 mem lut.dataLenRefAddr LOOKUP_TABLE_META_SIZE
          let m2 := writeU64 m1 (lut.dataPtr - 8) LOOKUP_TABLE_META_SIZE
          let m3 := writeBytes m2 lut.ownerPtr 32 PROGRAM_ID_BYTES
          -- Initialize meta: tag=1, deactivation_slot=u64::MAX,
          -- last_extended_slot=0, start_index=0, authority=Some(auth).
          -- First zero the 56-byte header to drop any pre-existing
          -- bytes, then write each field.
          let m4 := (List.range LOOKUP_TABLE_META_SIZE).foldl
            (fun acc i => writeU8 acc (lut.dataPtr + i) 0) m3
          let m5 := writeU32 m4 (lut.dataPtr + OFF_VARIANT_TAG)
                                STATE_TAG_LOOKUP_TABLE
          let m6 := writeU64 m5 (lut.dataPtr + OFF_DEACTIVATION_SLOT) U64_MAX
          let m7 := writeU8  m6 (lut.dataPtr + OFF_AUTHORITY_TAG) 1
          let m8 := writeBytes m7 (lut.dataPtr + OFF_AUTHORITY_PUBKEY)
                                  32 auth.key
          ⟨m8, 0, CU_DEFAULT⟩
  | _ => ⟨mem, 1, CU_DEFAULT⟩

/-- Top-level ALT dispatcher. -/
def dispatch (ixData : ByteArray) (accts : List AcctInput) (mem : Mem) :
    Option NativeResult :=
  match decode ixData with
  | .createLookupTable slot bump =>
    some (execCreateLookupTable mem accts slot bump)
  | .freezeLookupTable     => some (execFreezeLookupTable mem accts)
  | .extendLookupTable as_ => some (execExtendLookupTable mem accts as_)
  | .deactivateLookupTable => some (execDeactivateLookupTable mem accts)
  | .closeLookupTable      => some (execCloseLookupTable mem accts)
  | .unknown _             => some ⟨mem, 1, CU_DEFAULT⟩

end Svm.Native.AddressLookupTable
