-- The Solana Config program — native, not BPF.
--
-- Reference: agave's `solana-config-program-2.2.4`
-- (`src/config_processor.rs`) and `solana-config-interface-2.0.0`
-- (`src/state.rs`).
--
-- One instruction, no discriminant byte — the entire `ix.data` is a
-- bincode-serialized `ConfigKeys { keys: Vec<(Pubkey, bool)> }` (the
-- `keys` field uses `short_vec` length-prefix, not the default u64),
-- followed by the user's payload bytes. On success the program
-- overwrites `accts[0].data[..ix.data.len()]` with the full `ix.data`.
--
-- Config was migrated to Core BPF (see agave's
-- `fetch-core-bpf.sh`: `config 3.0.0 Config1111… BPFLoaderUpgradeab1e…`).
-- Mollusk's BUILTINS no longer registers it, so a diff-mollusk fixture
-- isn't feasible today; the Lean spec is the source of truth for the
-- legacy native semantics (the canonical pre-migration agave behavior).

import Svm.Native.AcctInput
import Svm.SBPF.Machine

namespace Svm.Native.Config

open Svm.SBPF.Memory
open Svm.SBPF (writeBytes readBytes)
open Svm.Native

/-- Config program-id (`Config1111111111111111111111111111111111111`)
    as a little-endian `Nat`. Raw bytes
    `[0x03, 0x06, 0x4a, 0xa3, 0x00, 0x2f, 0x74, 0xdc, 0xc8, 0x6e,
      0x43, 0x31, 0x0f, 0x0c, 0x05, 0x2a, 0xf8, 0xc5, 0xda, 0x27,
      0xf6, 0x10, 0x40, 0x19, 0xa3, 0x23, 0xef, 0xa0, 0x00, 0x00,
      0x00, 0x00]`. -/
def PROGRAM_ID : Nat :=
  0x00000000a0ef23a3194010f627dac5f82a050c0f31436ec8dc742f00a34a0603

/-- The 32-byte Config program-id, used as an owner-field comparison. -/
def PROGRAM_ID_BYTES : ByteArray :=
  ⟨#[0x03, 0x06, 0x4a, 0xa3, 0x00, 0x2f, 0x74, 0xdc,
     0xc8, 0x6e, 0x43, 0x31, 0x0f, 0x0c, 0x05, 0x2a,
     0xf8, 0xc5, 0xda, 0x27, 0xf6, 0x10, 0x40, 0x19,
     0xa3, 0x23, 0xef, 0xa0, 0x00, 0x00, 0x00, 0x00]⟩

/-- Agave's `DEFAULT_COMPUTE_UNITS` for Config
    (`config_processor.rs:10`). Flat per-invocation charge. -/
def CU_DEFAULT : Nat := 450

/-! ## Wire decode

The Config wire format is bincode with the `keys` field using
`#[serde(with = "short_vec")]`:

```
[ short_vec(count) ‖ (Pubkey ‖ u8(is_signer)) × count ‖ user_payload… ]
```

`short_vec` is Solana's compact-u16 encoding: 1–3 bytes, low 7 bits
per byte, high bit = continuation. We mirror agave's encoder by
rejecting overlong forms (continuation bit set when the value would
fit in fewer bytes). -/

/-- Decode a `short_vec` length prefix at `off`. Returns `(value,
    bytes_consumed)` or `none` on malformed input (truncated or
    overlong encoding). -/
private def decodeShortVec (bs : ByteArray) (off : Nat) :
    Option (Nat × Nat) :=
  if off ≥ bs.size then none
  else
    let b0 := (bs.get! off).toNat
    let v0 := b0 &&& 0x7f
    if b0 &&& 0x80 = 0 then some (v0, 1)
    else if off + 1 ≥ bs.size then none
    else
      let b1 := (bs.get! (off + 1)).toNat
      let v1 := b1 &&& 0x7f
      if v1 = 0 then none
      else if b1 &&& 0x80 = 0 then
        some (v0 ||| (v1 <<< 7), 2)
      else if off + 2 ≥ bs.size then none
      else
        let b2 := (bs.get! (off + 2)).toNat
        if b2 = 0 ∨ b2 ≥ 4 then none
        else some (v0 ||| (v1 <<< 7) ||| (b2 <<< 14), 3)

/-- Helper: decode `count` (pubkey, bool) entries starting at `cursor`.
    Returns the reversed accumulator + total bytes consumed
    (`cursor - start`), or `none` if truncated. -/
private def decodeEntries (bs : ByteArray) :
    (count cursor : Nat) → List (ByteArray × Bool) → Option (List (ByteArray × Bool) × Nat)
  | 0,           cursor, acc => some (acc.reverse, cursor)
  | count + 1,   cursor, acc =>
    if cursor + 33 > bs.size then none
    else
      let pk   := bs.extract cursor (cursor + 32)
      let flag := bs.get! (cursor + 32)
      decodeEntries bs count (cursor + 33) ((pk, flag ≠ 0) :: acc)

/-- Decode `ConfigKeys` at offset `off`. Returns `(entries,
    end_offset)` or `none` on malformed input. -/
private def decodeConfigKeys (bs : ByteArray) (off : Nat) :
    Option (List (ByteArray × Bool) × Nat) := do
  let (count, lenBytes) ← decodeShortVec bs off
  decodeEntries bs count (off + lenBytes) []

/-- Byte-by-byte equality on 32-byte pubkeys. -/
private def pubkeyEq (a b : ByteArray) : Bool :=
  a.size = b.size && (List.range a.size).all (fun i => a.get! i = b.get! i)

/-- Whether `acct.owner` equals the Config program-id. -/
private def isOwnerConfig (owner : ByteArray) : Bool :=
  pubkeyEq owner PROGRAM_ID_BYTES

/-- Look up `accts[i]`, returning `none` past the end. Manual recursion
    rather than `List.get?` (not in current Lean 4 stdlib). -/
private def getAcct : List AcctInput → Nat → Option AcctInput
  | [],       _     => none
  | x :: _,   0     => some x
  | _ :: xs,  n + 1 => getAcct xs n

/-- Does `curSigners` contain `pk`? Agave matches on pubkey alone (the
    `is_signer` flag on the *existing* entry is implicit since we
    pre-filtered to signers). -/
private def signerInCurrentSet (curSigners : List ByteArray)
    (pk : ByteArray) : Bool :=
  curSigners.any (fun s => pubkeyEq s pk)

/-- Detect a duplicate `(pubkey, bool)` pair in `entries`. Equivalent
    to agave's `BTreeSet<(Pubkey, bool)>` dedup check on
    `key_list.keys`. -/
private def hasDuplicate : List (ByteArray × Bool) → Bool
  | []              => false
  | (pk, b) :: rest =>
    if rest.any (fun (p2, b2) => b2 = b && pubkeyEq p2 pk) then true
    else hasDuplicate rest

/-- Filter the entries that have `is_signer = true`, returning their
    pubkeys. -/
private def signerPubkeys (entries : List (ByteArray × Bool)) :
    List ByteArray :=
  entries.filterMap (fun (pk, b) => if b then some pk else none)

/-- Walk the incoming signers, mirroring the loop in
    `config_processor.rs:54-99`. Returns the final counter (number of
    signers processed) on success, or `none` on any signature-validation
    failure.

    `counter` is 1-indexed by the time we look up `accts[counter]`:
    agave starts at 0, increments before use, then borrows
    `instruction_accounts[counter as IndexOfAccount]` where index 0 is
    the config account. -/
private def walkIncomingSigners
    (cfgKey : ByteArray) (cfgIsSigner : Bool)
    (curSigners : List ByteArray) (curInitialized : Bool)
    (accts : List AcctInput) :
    (incoming : List (ByteArray × Bool)) → (counter : Nat) → Option Nat
  | [],                       counter => some counter
  | (_, false) :: rest,       counter =>
    walkIncomingSigners cfgKey cfgIsSigner curSigners curInitialized
      accts rest counter
  | (pk, true) :: rest,       counter =>
    let counter' := counter + 1
    if pubkeyEq pk cfgKey then
      if cfgIsSigner then
        walkIncomingSigners cfgKey cfgIsSigner curSigners curInitialized
          accts rest counter'
      else none
    else
      match getAcct accts counter' with
      | none    => none
      | some sa =>
        if !sa.isSigner then none
        else if !pubkeyEq sa.key pk then none
        else if curInitialized ∧ !signerInCurrentSet curSigners pk then
          none
        else
          walkIncomingSigners cfgKey cfgIsSigner curSigners curInitialized
            accts rest counter'

/-- Read current config-account data (the full data buffer, sized
    `acct.dataLen`) into a `ByteArray`. -/
private def readCurrentData (mem : Mem) (acct : AcctInput) : ByteArray :=
  readBytes mem acct.dataPtr acct.dataLen

/-- Single-instruction dispatcher for the Config program.

    On any check failure → `r0 := 1`. On success → write `ixData` into
    `accts[0]`'s data buffer (via `writeBytes accts[0].dataPtr`) and
    `r0 := 0`. CU is the flat 450 either way.

    Failure modes (mirroring `InstructionError` values agave returns):
    - missing config account / no instruction accounts
    - account[0].owner ≠ Config PROGRAM_ID
    - ix_data does not parse as `ConfigKeys`
    - current account data does not parse as `ConfigKeys`
    - missing required signer (multiple sub-cases per agave)
    - duplicate `(pubkey, bool)` in incoming list
    - too-few signers (incoming signer count < existing signer count)
    - `ix_data.len() > current data buffer size`. -/
def dispatch (ixData : ByteArray) (accts : List AcctInput) (mem : Mem) :
    NativeResult :=
  let fail : NativeResult := ⟨mem, 1, CU_DEFAULT⟩
  match accts with
  | [] => fail
  | cfgAcct :: _ =>
    if !isOwnerConfig cfgAcct.owner then fail
    else
      match decodeConfigKeys ixData 0 with
      | none => fail
      | some (incoming, _) =>
        let curBytes := readCurrentData mem cfgAcct
        match decodeConfigKeys curBytes 0 with
        | none => fail
        | some (current, _) =>
          let curSigners := signerPubkeys current
          let curInitialized := !current.isEmpty
          let cfgIsSigner := cfgAcct.isSigner
          if curSigners.isEmpty ∧ !cfgIsSigner then fail
          else if hasDuplicate incoming then fail
          else
            match walkIncomingSigners cfgAcct.key cfgIsSigner curSigners
                    curInitialized accts incoming 0 with
            | none => fail
            | some counter =>
              if curSigners.length > counter then fail
              else if cfgAcct.dataLen < ixData.size then fail
              else
                let mem' := writeBytes mem cfgAcct.dataPtr ixData.size ixData
                ⟨mem', 0, CU_DEFAULT⟩

end Svm.Native.Config
