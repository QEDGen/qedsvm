-- Solana signature-verify precompiles.
--
-- Three "programs" with fixed program-ids that the runtime dispatches
-- to a Rust `verify()` closure instead of the BPF VM:
--
--   ed25519  (`Ed25519SigVerify1111…`)   — ed25519-dalek verify_strict
--   secp256k1 (`KeccakSecp256k11111…`)   — libsecp256k1 ECDSA recover
--   secp256r1 (`Secp256r1SigVerify1111…`) — openssl P-256 verify
--
-- Agave's `precompiles/src/{ed25519,secp256k1,secp256r1}.rs`. Each
-- precompile reads a header (`num_signatures` byte + optional padding)
-- followed by `num_signatures` packed `SignatureOffsets` structs, then
-- the actual signature / pubkey / message bytes packed at the
-- referenced offsets within the same `ix.data` (or — in a full
-- transaction — within another instruction's data, addressed by the
-- per-offset `instruction_index`).
--
-- ## Cross-instruction lookup (gap, documented)
--
-- agave's `verify()` takes `instruction_datas: &[&[u8]]` and lets each
-- offset entry pull bytes from any instruction in the transaction.
-- qedsvm processes one instruction at a time and has no access to
-- the surrounding transaction. We support exactly one shape:
--
--   - ed25519 / secp256r1: `instruction_index == u16::MAX (0xFFFF)`
--     means "use the current instruction's data". Any other index
--     fails with the equivalent of `PrecompileError::InvalidDataOffsets`
--     (r0 := 1).
--   - secp256k1: index is a u8, no sentinel. agave looks up
--     `instruction_datas[index]`; we only support `index == 0`
--     (treating it as the current instruction), and reject anything
--     else.
--
-- This matches the common construction where a single-instruction
-- precompile invocation packs sig + pubkey + msg inline. Multi-
-- instruction precompiles (sig in instruction[i], msg in
-- instruction[j]) are a runtime concern that qedsvm doesn't model.
--
-- ## CU charging
--
-- agave's cost-model charges per-signature
-- (`ED25519_VERIFY_STRICT_COST = 2400`, `SECP256K1_VERIFY_COST = 6690`,
-- `SECP256R1_VERIFY_COST = 4800`) at transaction-prep time, not at
-- runtime — precompiles never enter the program runtime's CU meter.
-- We charge the same per-signature cost here so the Native dispatch
-- result mirrors agave's accounting; transactions that route through
-- qedsvm see a single net CU figure that matches the on-chain
-- charge.

import Svm.Native.AcctInput
import Svm.SBPF.Machine
import Svm.SBPF.Sha256
import Svm.SBPF.Keccak256
import Svm.SBPF.Secp256k1

namespace Svm.Native.Precompiles

open Svm.SBPF.Memory
open Svm.Native

/-! ## FFI declarations -/

/-- Strict ed25519 signature verification via `ed25519-dalek = 2.2.0`.
    Returns 1 on success, 0 on any failure (invalid pubkey length,
    invalid signature length, malleable signature, mathematical
    verification failure). agave's precompile pins ed25519-dalek 1.0.1
    and calls `verify_strict` with equivalent semantics. -/
@[extern "lean_ed25519_verify_strict"]
opaque ed25519VerifyStrict
    (pubkey : @& ByteArray) (sig : @& ByteArray) (msg : @& ByteArray) :
    Bool

/-- NIST P-256 ECDSA verification with low-S enforcement via
    `p256 = 0.13`. Returns 1 on success, 0 otherwise. agave uses
    openssl + manual `s ≤ half_order` checks; we use `p256` +
    `normalize_s().is_some()` rejection for the same low-S contract. -/
@[extern "lean_secp256r1_verify"]
opaque secp256r1Verify
    (pubkey : @& ByteArray) (sig : @& ByteArray) (msg : @& ByteArray) :
    Bool

/-! ## Program-id constants -/

/-- `Ed25519SigVerify111111111111111111111111111` as a LE-encoded Nat.
    Raw bytes
    `[0x03, 0x7d, 0x46, 0xd6, 0x7c, 0x93, 0xfb, 0xbe, 0x12, 0xf9,
      0x42, 0x8f, 0x83, 0x8d, 0x40, 0xff, 0x05, 0x70, 0x74, 0x49,
      0x27, 0xf4, 0x8a, 0x64, 0xfc, 0xca, 0x70, 0x44, 0x80, 0x00,
      0x00, 0x00]`. -/
def ED25519_PROGRAM_ID : Nat :=
  0x000000804470cafc648af42749747005ff408d838f42f912befb937cd6467d03

/-- `KeccakSecp256k11111111111111111111111111111` as a LE-encoded Nat.
    Raw bytes
    `[0x04, 0xc6, 0xfc, 0x20, 0xf0, 0x50, 0xcc, 0xf0, 0x55, 0x84,
      0xd7, 0x21, 0x1c, 0x9f, 0x8c, 0xf5, 0x9e, 0xc1, 0x47, 0x85,
      0xbb, 0x16, 0x6a, 0x1e, 0x28, 0x30, 0xe8, 0x12, 0x20, 0x00,
      0x00, 0x00]`. -/
def SECP256K1_PROGRAM_ID : Nat :=
  0x0000002012e830281e6a16bb8547c19ef58c9f1c21d78455f0cc50f020fcc604

/-- `Secp256r1SigVerify1111111111111111111111111` as a LE-encoded Nat.
    Raw bytes
    `[0x06, 0x92, 0x0d, 0xec, 0x2f, 0xea, 0x71, 0xb5, 0xb7, 0x23,
      0x81, 0x4d, 0x74, 0x2d, 0xa9, 0x03, 0x1c, 0x83, 0xe7, 0x5f,
      0xdb, 0x79, 0x5d, 0x56, 0x8e, 0x75, 0x47, 0x80, 0x20, 0x00,
      0x00, 0x00]`. -/
def SECP256R1_PROGRAM_ID : Nat :=
  0x000000208047758e565d79db5fe7831c03a92d744d8123b7b571ea2fec0d9206

/-! ## CU costs (per signature)

Sourced from agave's `cost-model/src/block_cost_limits.rs`. Precompile
verification is paid by the cost-model layer pre-execution, not by
the program runtime, so these *are* the charges (no in-program base
cost on top). Multi-sig precompile instructions pay `num_signatures ×
per_sig_cost`. -/

def ED25519_VERIFY_STRICT_COST : Nat := 2400  -- 30 × 80
def SECP256K1_VERIFY_COST      : Nat := 6690  -- 30 × 223
def SECP256R1_VERIFY_COST      : Nat := 4800  -- 30 × 160

/-! ## Constants from the interface crates -/

private def SIGNATURE_OFFSETS_START : Nat := 2        -- ed25519 / secp256r1
private def SIGNATURE_OFFSETS_SERIALIZED_SIZE_LARGE : Nat := 14  -- ed25519 / secp256r1
private def SIGNATURE_OFFSETS_SERIALIZED_SIZE_SECP1 : Nat := 11
private def PUBKEY_SERIALIZED_SIZE_ED25519 : Nat := 32
private def PUBKEY_SERIALIZED_SIZE_SECP256R1 : Nat := 33
private def HASHED_PUBKEY_SERIALIZED_SIZE : Nat := 20
private def SIGNATURE_SERIALIZED_SIZE : Nat := 64

/-! ## Byte readers -/

/-- Read a u16 LE at offset `off`. Returns 0 past the end. -/
private def readU16LE (bs : ByteArray) (off : Nat) : Nat :=
  if off + 2 > bs.size then 0
  else (bs.get! off).toNat + (bs.get! (off + 1)).toNat * 0x100

/-- Read a u8 at offset `off`. Returns 0 past the end. -/
private def readU8 (bs : ByteArray) (off : Nat) : Nat :=
  if off ≥ bs.size then 0 else (bs.get! off).toNat

/-- Extract `len` bytes starting at `off`. Returns `none` if truncated. -/
private def sliceOpt (bs : ByteArray) (off len : Nat) : Option ByteArray :=
  if off + len > bs.size then none
  else some (bs.extract off (off + len))

/-! ## Ed25519 dispatcher -/

structure Ed25519Offsets where
  sigOffset      : Nat
  sigIxIndex     : Nat
  pubkeyOffset   : Nat
  pubkeyIxIndex  : Nat
  msgOffset      : Nat
  msgSize        : Nat
  msgIxIndex     : Nat
  deriving Inhabited

private def readEd25519Offsets (bs : ByteArray) (off : Nat) :
    Option Ed25519Offsets :=
  if off + SIGNATURE_OFFSETS_SERIALIZED_SIZE_LARGE > bs.size then none
  else some {
    sigOffset      := readU16LE bs (off + 0)
    sigIxIndex     := readU16LE bs (off + 2)
    pubkeyOffset   := readU16LE bs (off + 4)
    pubkeyIxIndex  := readU16LE bs (off + 6)
    msgOffset      := readU16LE bs (off + 8)
    msgSize        := readU16LE bs (off + 10)
    msgIxIndex     := readU16LE bs (off + 12)
  }

/-- Ed25519 sentinel: bytes can be pulled from the *current* instruction's
    data when the per-field `instruction_index = u16::MAX (0xFFFF)`. -/
private def U16_MAX : Nat := 0xFFFF

/-- Verify a single ed25519 signature entry. Returns `true` on success,
    `false` on any failure. Cross-instruction lookups (index ≠ 0xFFFF)
    are rejected per the documented gap. -/
private def verifyEd25519One (data : ByteArray) (o : Ed25519Offsets) : Bool :=
  if o.sigIxIndex ≠ U16_MAX ∨ o.pubkeyIxIndex ≠ U16_MAX ∨
     o.msgIxIndex ≠ U16_MAX then false
  else
    match sliceOpt data o.sigOffset SIGNATURE_SERIALIZED_SIZE with
    | none => false
    | some sig =>
      match sliceOpt data o.pubkeyOffset PUBKEY_SERIALIZED_SIZE_ED25519 with
      | none => false
      | some pk =>
        match sliceOpt data o.msgOffset o.msgSize with
        | none => false
        | some msg => ed25519VerifyStrict pk sig msg

/-- Walk N ed25519 signatures starting at byte 2. Returns success only if
    all verify. -/
private def verifyAllEd25519 (data : ByteArray) :
    (i : Nat) → (numSignatures : Nat) → Bool
  | _,     0     => true
  | i,     n + 1 =>
    let off := SIGNATURE_OFFSETS_START +
                 i * SIGNATURE_OFFSETS_SERIALIZED_SIZE_LARGE
    match readEd25519Offsets data off with
    | none => false
    | some o =>
      if !verifyEd25519One data o then false
      else verifyAllEd25519 data (i + 1) n

/-- Top-level ed25519 precompile dispatch. Charges
    `numSignatures × ED25519_VERIFY_STRICT_COST`. -/
def dispatchEd25519 (ixData : ByteArray) (_accts : List AcctInput)
    (mem : Mem) : NativeResult :=
  let n := readU8 ixData 0
  let expected := n * SIGNATURE_OFFSETS_SERIALIZED_SIZE_LARGE +
                    SIGNATURE_OFFSETS_START
  let cu := n * ED25519_VERIFY_STRICT_COST
  if ixData.size < SIGNATURE_OFFSETS_START then ⟨mem, 1, cu⟩
  else if n = 0 ∧ ixData.size > SIGNATURE_OFFSETS_START then
    -- agave rejects "0 sigs but oversized data" as InvalidInstructionDataSize.
    ⟨mem, 1, cu⟩
  else if ixData.size < expected then ⟨mem, 1, cu⟩
  else if verifyAllEd25519 ixData 0 n then ⟨mem, 0, cu⟩
  else ⟨mem, 1, cu⟩

/-! ## Secp256r1 dispatcher (same layout as ed25519, different sig math) -/

private def readSecp256r1Offsets (bs : ByteArray) (off : Nat) :
    Option Ed25519Offsets :=
  readEd25519Offsets bs off

private def verifySecp256r1One (data : ByteArray) (o : Ed25519Offsets) :
    Bool :=
  if o.sigIxIndex ≠ U16_MAX ∨ o.pubkeyIxIndex ≠ U16_MAX ∨
     o.msgIxIndex ≠ U16_MAX then false
  else
    match sliceOpt data o.sigOffset SIGNATURE_SERIALIZED_SIZE with
    | none => false
    | some sig =>
      match sliceOpt data o.pubkeyOffset PUBKEY_SERIALIZED_SIZE_SECP256R1 with
      | none => false
      | some pk =>
        match sliceOpt data o.msgOffset o.msgSize with
        | none => false
        | some msg => secp256r1Verify pk sig msg

private def verifyAllSecp256r1 (data : ByteArray) :
    (i : Nat) → (numSignatures : Nat) → Bool
  | _,     0     => true
  | i,     n + 1 =>
    let off := SIGNATURE_OFFSETS_START +
                 i * SIGNATURE_OFFSETS_SERIALIZED_SIZE_LARGE
    match readSecp256r1Offsets data off with
    | none => false
    | some o =>
      if !verifySecp256r1One data o then false
      else verifyAllSecp256r1 data (i + 1) n

/-- Top-level secp256r1 precompile dispatch. agave additionally caps
    `num_signatures ≤ 8`. -/
def dispatchSecp256r1 (ixData : ByteArray) (_accts : List AcctInput)
    (mem : Mem) : NativeResult :=
  let n := readU8 ixData 0
  let expected := n * SIGNATURE_OFFSETS_SERIALIZED_SIZE_LARGE +
                    SIGNATURE_OFFSETS_START
  let cu := n * SECP256R1_VERIFY_COST
  if ixData.size < SIGNATURE_OFFSETS_START then ⟨mem, 1, cu⟩
  else if n = 0 then ⟨mem, 1, cu⟩
  else if n > 8 then ⟨mem, 1, cu⟩
  else if ixData.size < expected then ⟨mem, 1, cu⟩
  else if verifyAllSecp256r1 ixData 0 n then ⟨mem, 0, cu⟩
  else ⟨mem, 1, cu⟩

/-! ## Secp256k1 dispatcher

agave's `secp256k1.rs` differs from the others:

  - Header is a single byte (no padding) — offsets start at byte 1.
  - `SecpSignatureOffsets` is 11 bytes (u16/u8/u16/u8/u16/u16/u8):
      sig_offset (u16) ‖ sig_ix_index (u8)
      eth_addr_offset (u16) ‖ eth_addr_ix_index (u8)
      msg_offset (u16) ‖ msg_size (u16) ‖ msg_ix_index (u8)
  - The signature blob is 65 bytes: 64-byte sig + 1-byte recovery_id.
  - Pubkey field is a 20-byte ETH address; we verify by running
    `secp256k1_recover(keccak256(msg), sig, recovery_id)` and
    matching `keccak256(recovered_pubkey)[12..32]`.
  - No `u8::MAX` sentinel — instruction_index is a direct lookup.
    We only support `index == 0` (treated as the current
    instruction's data). -/

structure SecpOffsets where
  sigOffset       : Nat
  sigIxIndex      : Nat
  ethAddrOffset   : Nat
  ethAddrIxIndex  : Nat
  msgOffset       : Nat
  msgSize         : Nat
  msgIxIndex      : Nat
  deriving Inhabited

private def readSecpOffsets (bs : ByteArray) (off : Nat) :
    Option SecpOffsets :=
  if off + SIGNATURE_OFFSETS_SERIALIZED_SIZE_SECP1 > bs.size then none
  else some {
    sigOffset      := readU16LE bs (off + 0)
    sigIxIndex     := readU8    bs (off + 2)
    ethAddrOffset  := readU16LE bs (off + 3)
    ethAddrIxIndex := readU8    bs (off + 5)
    msgOffset      := readU16LE bs (off + 6)
    msgSize        := readU16LE bs (off + 8)
    msgIxIndex     := readU8    bs (off + 10)
  }

/-- Compute the 20-byte Ethereum address from a 64-byte uncompressed
    secp256k1 public key (no 0x04 leading byte — the format
    `secp256k1_recover` returns). -/
private def ethAddressFromPubkey (pubkey : ByteArray) : ByteArray :=
  let h := Svm.SBPF.Keccak256.hash pubkey
  if h.size ≥ 32 then h.extract 12 32 else ByteArray.empty

/-- Byte-by-byte equality on N-byte arrays. -/
private def byteArrayEq (a b : ByteArray) : Bool :=
  a.size = b.size && (List.range a.size).all (fun i => a.get! i = b.get! i)

private def verifySecp256k1One (data : ByteArray) (o : SecpOffsets) : Bool :=
  if o.sigIxIndex ≠ 0 ∨ o.ethAddrIxIndex ≠ 0 ∨ o.msgIxIndex ≠ 0 then false
  else
    -- 64-byte sig + 1-byte recovery_id at sigOffset
    match sliceOpt data o.sigOffset SIGNATURE_SERIALIZED_SIZE with
    | none => false
    | some sig =>
      if o.sigOffset + SIGNATURE_SERIALIZED_SIZE ≥ data.size then false
      else
        let rid := (data.get! (o.sigOffset + SIGNATURE_SERIALIZED_SIZE)).toNat
        match sliceOpt data o.ethAddrOffset HASHED_PUBKEY_SERIALIZED_SIZE with
        | none => false
        | some ethAddr =>
          match sliceOpt data o.msgOffset o.msgSize with
          | none => false
          | some msg =>
            let msgHash := Svm.SBPF.Keccak256.hash msg
            match Svm.SBPF.Secp256k1.recover msgHash rid.toUInt8 sig with
            | .success pubkey =>
              byteArrayEq (ethAddressFromPubkey pubkey) ethAddr
            | _ => false

private def verifyAllSecp256k1 (data : ByteArray) :
    (i : Nat) → (numSignatures : Nat) → Bool
  | _,     0     => true
  | i,     n + 1 =>
    let off := 1 + i * SIGNATURE_OFFSETS_SERIALIZED_SIZE_SECP1
    match readSecpOffsets data off with
    | none => false
    | some o =>
      if !verifySecp256k1One data o then false
      else verifyAllSecp256k1 data (i + 1) n

/-- Top-level secp256k1 precompile dispatch. Header is a single
    `count` byte; offsets start at byte 1. -/
def dispatchSecp256k1 (ixData : ByteArray) (_accts : List AcctInput)
    (mem : Mem) : NativeResult :=
  if ixData.isEmpty then ⟨mem, 1, 0⟩
  else
    let n := readU8 ixData 0
    let expected := n * SIGNATURE_OFFSETS_SERIALIZED_SIZE_SECP1 + 1
    let cu := n * SECP256K1_VERIFY_COST
    if n = 0 ∧ ixData.size > 1 then ⟨mem, 1, cu⟩
    else if ixData.size < expected then ⟨mem, 1, cu⟩
    else if verifyAllSecp256k1 ixData 0 n then ⟨mem, 0, cu⟩
    else ⟨mem, 1, cu⟩

/-! ## Top-level dispatcher -/

/-- Returns `some result` if `pid` is one of the three sig-verify
    precompile program ids; `none` otherwise so `Native.dispatch` can
    fall through. -/
def dispatch (pid : Nat) (ixData : ByteArray) (accts : List AcctInput)
    (mem : Mem) : Option NativeResult :=
  if pid = ED25519_PROGRAM_ID then
    some (dispatchEd25519 ixData accts mem)
  else if pid = SECP256K1_PROGRAM_ID then
    some (dispatchSecp256k1 ixData accts mem)
  else if pid = SECP256R1_PROGRAM_ID then
    some (dispatchSecp256r1 ixData accts mem)
  else
    none

end Svm.Native.Precompiles
