-- The Solana System program — native, not BPF.
--
-- Mirrors agave's `programs/system/src/system_processor.rs`: bincode-decode
-- `ix.data` and dispatch on the `SystemInstruction` u32 LE discriminant.
-- Program-id is the all-zero pubkey, so its LE Nat encoding is `0`;
-- Native.dispatch keys on this. All 13 variants are modeled per agave
-- semantics (not fixture coverage), see [[feedback-project-charter]].

import SVM.Native.AcctInput
import SVM.SBPF.Machine
import SVM.Syscalls.Sha256

namespace SVM.Native.System

open SVM.SBPF.Memory
open SVM.SBPF (writeBytes)
open SVM.Native

/-- The all-zero pubkey as a LE `Nat`; the CPI handler reads the program-id the same way. -/
def PROGRAM_ID : Nat := 0

/-- Per-instruction cost: agave's `solana_system_program_compute_cost = 150`
    for every System invocation. (Seed variants charge an extra sha256 cost
    in agave; we flatten to 150.) -/
def CU_DEFAULT : Nat := 150

/-! ## SystemInstruction discriminants

Mirrors agave's `solana_system_interface::SystemInstruction`, field-for-field. -/

inductive SystemIx
  /-- `CreateAccount { lamports, space, owner }`. Discriminant 0. -/
  | createAccount (lamports space : Nat) (owner : ByteArray)
  /-- `Assign { owner }`. Discriminant 1. -/
  | assign (owner : ByteArray)
  /-- `Transfer { lamports }`. Discriminant 2. -/
  | transfer (lamports : Nat)
  /-- `CreateAccountWithSeed { base, seed, lamports, space, owner }`.
      Discriminant 3. -/
  | createAccountWithSeed (base : ByteArray) (seed : ByteArray)
      (lamports space : Nat) (owner : ByteArray)
  /-- `AdvanceNonceAccount`. Discriminant 4. -/
  | advanceNonceAccount
  /-- `WithdrawNonceAccount(lamports)`. Discriminant 5. -/
  | withdrawNonceAccount (lamports : Nat)
  /-- `InitializeNonceAccount(authority)`. Discriminant 6. -/
  | initializeNonceAccount (authority : ByteArray)
  /-- `AuthorizeNonceAccount(new_authority)`. Discriminant 7. -/
  | authorizeNonceAccount (newAuthority : ByteArray)
  /-- `Allocate { space }`. Discriminant 8. -/
  | allocate (space : Nat)
  /-- `AllocateWithSeed { base, seed, space, owner }`. Discriminant 9. -/
  | allocateWithSeed (base : ByteArray) (seed : ByteArray)
      (space : Nat) (owner : ByteArray)
  /-- `AssignWithSeed { base, seed, owner }`. Discriminant 10. -/
  | assignWithSeed (base : ByteArray) (seed : ByteArray)
      (owner : ByteArray)
  /-- `TransferWithSeed { lamports, from_seed, from_owner }`.
      Discriminant 11. -/
  | transferWithSeed (lamports : Nat) (fromSeed : ByteArray)
      (fromOwner : ByteArray)
  /-- `UpgradeNonceAccount`. Discriminant 12. -/
  | upgradeNonceAccount
  /-- Any discriminant agave doesn't know — dispatch fails. -/
  | unknown (discriminant : Nat)
  deriving Inhabited

/-! ## Wire decode

`ix.data` is bincode: u32 LE discriminant + payload. Read directly from
the `ByteArray` (inputs are ≤80B, so explicit reads beat a serializer). -/

/-- Read a u32 LE at offset `off` in `bs`. Returns 0 past the end. -/
private def readU32LE (bs : ByteArray) (off : Nat) : Nat :=
  if off + 4 > bs.size then 0
  else
    (bs.get! off).toNat +
    (bs.get! (off + 1)).toNat * 0x100 +
    (bs.get! (off + 2)).toNat * 0x10000 +
    (bs.get! (off + 3)).toNat * 0x1000000

/-- Read a u64 LE at offset `off` in `bs`. Returns 0 past the end. -/
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

/-- Read a 32-byte pubkey at offset `off`. Returns an empty array if
    truncated. -/
private def readPubkey (bs : ByteArray) (off : Nat) : ByteArray :=
  if off + 32 > bs.size then ByteArray.empty
  else bs.extract off (off + 32)

/-- Read a bincode `String` at offset `off`: u64 LE length followed by
    that many UTF-8 bytes. Returns the bytes + next-cursor offset.
    On truncation returns empty bytes + same offset. -/
private def readString (bs : ByteArray) (off : Nat) : ByteArray × Nat :=
  let len := readU64LE bs off
  let start := off + 8
  if start + len > bs.size then (ByteArray.empty, off)
  else (bs.extract start (start + len), start + len)

/-- Decode the System instruction payload. The discriminant is the
    u32 LE at offset 0; payload starts at offset 4. -/
def decode (ixData : ByteArray) : SystemIx :=
  let disc := readU32LE ixData 0
  match disc with
  | 0 =>
    -- CreateAccount: lamports(u64) | space(u64) | owner(Pubkey)
    let lamports := readU64LE ixData 4
    let space    := readU64LE ixData 12
    let owner    := readPubkey ixData 20
    .createAccount lamports space owner
  | 1 =>
    -- Assign: owner(Pubkey)
    let owner := readPubkey ixData 4
    .assign owner
  | 2 =>
    -- Transfer: lamports(u64)
    let lamports := readU64LE ixData 4
    .transfer lamports
  | 3 =>
    -- CreateAccountWithSeed: base(Pubkey) | seed(String) | lamports(u64)
    --                         | space(u64) | owner(Pubkey)
    let base := readPubkey ixData 4
    let (seed, off) := readString ixData 36
    let lamports := readU64LE ixData off
    let space    := readU64LE ixData (off + 8)
    let owner    := readPubkey ixData (off + 16)
    .createAccountWithSeed base seed lamports space owner
  | 4 => .advanceNonceAccount
  | 5 =>
    -- WithdrawNonceAccount(u64)
    let lamports := readU64LE ixData 4
    .withdrawNonceAccount lamports
  | 6 =>
    -- InitializeNonceAccount(Pubkey)
    let authority := readPubkey ixData 4
    .initializeNonceAccount authority
  | 7 =>
    -- AuthorizeNonceAccount(Pubkey)
    let newAuthority := readPubkey ixData 4
    .authorizeNonceAccount newAuthority
  | 8 =>
    -- Allocate: space(u64)
    let space := readU64LE ixData 4
    .allocate space
  | 9 =>
    -- AllocateWithSeed: base(Pubkey) | seed(String) | space(u64) | owner(Pubkey)
    let base := readPubkey ixData 4
    let (seed, off) := readString ixData 36
    let space := readU64LE ixData off
    let owner := readPubkey ixData (off + 8)
    .allocateWithSeed base seed space owner
  | 10 =>
    -- AssignWithSeed: base(Pubkey) | seed(String) | owner(Pubkey)
    let base := readPubkey ixData 4
    let (seed, off) := readString ixData 36
    let owner := readPubkey ixData off
    .assignWithSeed base seed owner
  | 11 =>
    -- TransferWithSeed: lamports(u64) | from_seed(String) | from_owner(Pubkey)
    let lamports := readU64LE ixData 4
    let (fromSeed, off) := readString ixData 12
    let fromOwner := readPubkey ixData off
    .transferWithSeed lamports fromSeed fromOwner
  | 12 => .upgradeNonceAccount
  | d  => .unknown d

/-! ## Execution -/

/-- 64-bit modulus. Clamps post-transfer lamports against u64 overflow;
    agave returns `ResultWithNegativeLamports`, we return r0=1. -/
private def U64_MODULUS : Nat := 0x10000000000000000

/-- MAX_PERMITTED_DATA_LENGTH from agave: 10 MiB cap on create/grow. -/
private def MAX_PERMITTED_DATA_LENGTH : Nat := 10 * 1024 * 1024

/-- "owner = System" check (all-zero 32-byte pubkey) for the uninitialized-account gate. -/
private def isSystemOwner (b : ByteArray) : Bool :=
  b.size = 32 && (List.range 32).all (fun i => b.get! i = 0)

/-- Execute `Transfer { lamports }`. Two accounts required:
    `from` (signer, writable) and `to` (writable). Decrements
    `from.lamports` by `lamports`, increments `to.lamports`. -/
def execTransfer (mem : Mem) (accts : List AcctInput) (lamports : Nat) :
    NativeResult :=
  match accts with
  | fromAcct :: toAcct :: _ =>
    -- agave checks: from signer, both writable, from.owner = System,
    -- from.lamports ≥ lamports, no overflow on to. Any failure → r0 := 1.
    -- H9: the writable + owner gates were previously missing (agave rejects
    -- debiting a non-System-owned or read-only account). See SOUNDNESS_AUDIT_* (H9).
    if !fromAcct.isSigner then
      ⟨mem, 1, CU_DEFAULT⟩
    else if !fromAcct.isWritable || !toAcct.isWritable then
      ⟨mem, 1, CU_DEFAULT⟩
    else if !isSystemOwner fromAcct.owner then
      ⟨mem, 1, CU_DEFAULT⟩
    else if fromAcct.lamports < lamports then
      ⟨mem, 1, CU_DEFAULT⟩
    else if toAcct.lamports + lamports ≥ U64_MODULUS then
      ⟨mem, 1, CU_DEFAULT⟩
    else
      let newFrom := fromAcct.lamports - lamports
      let newTo   := toAcct.lamports + lamports
      let m1 := writeU64 mem fromAcct.lamportsRefAddr newFrom
      let m2 := writeU64 m1 toAcct.lamportsRefAddr newTo
      ⟨m2, 0, CU_DEFAULT⟩
  | _ => ⟨mem, 1, CU_DEFAULT⟩  -- not enough accounts

/-- Execute `CreateAccount { lamports, space, owner }`. Accounts: `from`
    (signer, funds), `to` (signer, must be uninitialized: empty data,
    0 lamports, system-owned). Checks `from.lamports ≥ lamports` and
    `space ≤ MAX_PERMITTED_DATA_LENGTH`; moves lamports, sets
    `to.dataLen := space` and `to.owner := newOwner`. -/
def execCreateAccount (mem : Mem) (accts : List AcctInput)
    (lamports space : Nat) (newOwner : ByteArray) : NativeResult :=
  match accts with
  | fromAcct :: toAcct :: _ =>
    if !fromAcct.isSigner then ⟨mem, 1, CU_DEFAULT⟩
    else if !toAcct.isSigner then ⟨mem, 1, CU_DEFAULT⟩
    else if toAcct.lamports ≠ 0 then ⟨mem, 1, CU_DEFAULT⟩
    else if toAcct.dataLen ≠ 0 then ⟨mem, 1, CU_DEFAULT⟩
    else if !isSystemOwner toAcct.owner then ⟨mem, 1, CU_DEFAULT⟩
    else if fromAcct.lamports < lamports then ⟨mem, 1, CU_DEFAULT⟩
    else if space > MAX_PERMITTED_DATA_LENGTH then ⟨mem, 1, CU_DEFAULT⟩
    else
      let newFrom := fromAcct.lamports - lamports
      let newTo   := lamports                       -- to was 0
      let m1 := writeU64 mem fromAcct.lamportsRefAddr newFrom
      let m2 := writeU64 m1 toAcct.lamportsRefAddr newTo
      -- Rc-chain length (in-program AccountInfo view).
      let m3 := writeU64 m2 toAcct.dataLenRefAddr space
      -- Serialized data_len slot (dataPtr-8); `deserialize_account_writes`
      -- reads this for the post-state, else the harness sees len 0.
      let m4 := writeU64 m3 (toAcct.dataPtr - 8) space
      let m5 := writeBytes m4 toAcct.ownerPtr 32 newOwner
      ⟨m5, 0, CU_DEFAULT⟩
  | _ => ⟨mem, 1, CU_DEFAULT⟩

/-- Execute `Allocate { space }`. One account (signer, uninitialized:
    empty data, system-owned). Sets `dataLen := space` in both the
    Rc-chain and input-buffer (dataPtr-8) slots; lamports/owner untouched. -/
def execAllocate (mem : Mem) (accts : List AcctInput) (space : Nat) :
    NativeResult :=
  match accts with
  | acct :: _ =>
    if !acct.isSigner then ⟨mem, 1, CU_DEFAULT⟩
    else if acct.dataLen ≠ 0 then ⟨mem, 1, CU_DEFAULT⟩
    else if !isSystemOwner acct.owner then ⟨mem, 1, CU_DEFAULT⟩
    else if space > MAX_PERMITTED_DATA_LENGTH then ⟨mem, 1, CU_DEFAULT⟩
    else
      let m1 := writeU64 mem acct.dataLenRefAddr space
      let m2 := writeU64 m1 (acct.dataPtr - 8) space
      ⟨m2, 0, CU_DEFAULT⟩
  | _ => ⟨mem, 1, CU_DEFAULT⟩

/-- Execute `Assign { owner }`. One account (writable signer, currently
    System-owned). Overwrites `acct.owner` via `ownerPtr`; lamports/data untouched. -/
def execAssign (mem : Mem) (accts : List AcctInput) (newOwner : ByteArray) :
    NativeResult :=
  match accts with
  | acct :: _ =>
    -- H9: agave's `Assign` requires a writable signer currently owned by
    -- System; the owner gate was previously missing. See SOUNDNESS_AUDIT_* (H9/M4-account).
    if !acct.isSigner then ⟨mem, 1, CU_DEFAULT⟩
    else if !acct.isWritable then ⟨mem, 1, CU_DEFAULT⟩
    else if !isSystemOwner acct.owner then ⟨mem, 1, CU_DEFAULT⟩
    else
      let m1 := writeBytes mem acct.ownerPtr 32 newOwner
      ⟨m1, 0, CU_DEFAULT⟩
  | _ => ⟨mem, 1, CU_DEFAULT⟩

/-! ## With-seed variants

`create_with_seed(base, seed, owner) = SHA256(base ‖ seed ‖ owner)`. Like
PDA derivation but without the bump search / on-curve check (the base
account signs). agave checks `seed.len() ≤ 32` + address equality. -/

/-- Compose `base ‖ seed ‖ owner` and SHA-256 it. -/
private def deriveWithSeed (base seed owner : ByteArray) : ByteArray :=
  SVM.SBPF.Sha256.hash (base ++ seed ++ owner)

/-- ByteArray equality on 32-byte pubkeys, byte-by-byte. -/
private def pubkeyEq (a b : ByteArray) : Bool :=
  a.size = b.size && (List.range a.size).all (fun i => a.get! i = b.get! i)

/-- The agave seed-length limit. `create_with_seed` returns
    `MaxSeedLengthExceeded` for `seed.len() > 32`. -/
private def MAX_SEED_LEN : Nat := 32

/-- Execute `CreateAccountWithSeed`. The new account (`accts[1]`) isn't a
    signer; its address must equal `SHA256(base ‖ seed ‖ owner)`, and the
    base (`accts[2]`) is the signer authorizing it. `accts[0]` funds it. -/
def execCreateAccountWithSeed (mem : Mem) (accts : List AcctInput)
    (base seed : ByteArray) (lamports space : Nat) (newOwner : ByteArray) :
    NativeResult :=
  if seed.size > MAX_SEED_LEN then ⟨mem, 1, CU_DEFAULT⟩
  else
    match accts with
    | fromAcct :: toAcct :: baseAcct :: _ =>
      let expected := deriveWithSeed base seed newOwner
      if !pubkeyEq toAcct.key expected then ⟨mem, 1, CU_DEFAULT⟩
      else if !pubkeyEq baseAcct.key base then ⟨mem, 1, CU_DEFAULT⟩
      else if !fromAcct.isSigner then ⟨mem, 1, CU_DEFAULT⟩
      else if !baseAcct.isSigner then ⟨mem, 1, CU_DEFAULT⟩
      else if toAcct.lamports ≠ 0 then ⟨mem, 1, CU_DEFAULT⟩
      else if toAcct.dataLen ≠ 0 then ⟨mem, 1, CU_DEFAULT⟩
      else if !isSystemOwner toAcct.owner then ⟨mem, 1, CU_DEFAULT⟩
      else if fromAcct.lamports < lamports then ⟨mem, 1, CU_DEFAULT⟩
      else if space > MAX_PERMITTED_DATA_LENGTH then ⟨mem, 1, CU_DEFAULT⟩
      else
        let newFrom := fromAcct.lamports - lamports
        let m1 := writeU64 mem fromAcct.lamportsRefAddr newFrom
        let m2 := writeU64 m1 toAcct.lamportsRefAddr lamports
        let m3 := writeU64 m2 toAcct.dataLenRefAddr space
        let m4 := writeU64 m3 (toAcct.dataPtr - 8) space
        let m5 := writeBytes m4 toAcct.ownerPtr 32 newOwner
        ⟨m5, 0, CU_DEFAULT⟩
    | _ => ⟨mem, 1, CU_DEFAULT⟩

/-- Execute `AllocateWithSeed`. Accounts: derived address (`accts[0]`, not
    signer), base (`accts[1]`, signer). Allocates `space` AND reassigns the
    owner (agave's allocate_with_seed does both). -/
def execAllocateWithSeed (mem : Mem) (accts : List AcctInput)
    (base seed : ByteArray) (space : Nat) (newOwner : ByteArray) :
    NativeResult :=
  if seed.size > MAX_SEED_LEN then ⟨mem, 1, CU_DEFAULT⟩
  else
    match accts with
    | acct :: baseAcct :: _ =>
      let expected := deriveWithSeed base seed newOwner
      if !pubkeyEq acct.key expected then ⟨mem, 1, CU_DEFAULT⟩
      else if !pubkeyEq baseAcct.key base then ⟨mem, 1, CU_DEFAULT⟩
      else if !baseAcct.isSigner then ⟨mem, 1, CU_DEFAULT⟩
      else if acct.dataLen ≠ 0 then ⟨mem, 1, CU_DEFAULT⟩
      else if !isSystemOwner acct.owner then ⟨mem, 1, CU_DEFAULT⟩
      else if space > MAX_PERMITTED_DATA_LENGTH then ⟨mem, 1, CU_DEFAULT⟩
      else
        let m1 := writeU64 mem acct.dataLenRefAddr space
        let m2 := writeU64 m1 (acct.dataPtr - 8) space
        let m3 := writeBytes m2 acct.ownerPtr 32 newOwner
        ⟨m3, 0, CU_DEFAULT⟩
    | _ => ⟨mem, 1, CU_DEFAULT⟩

/-- Execute `AssignWithSeed`. Two accounts: address + base. -/
def execAssignWithSeed (mem : Mem) (accts : List AcctInput)
    (base seed : ByteArray) (newOwner : ByteArray) : NativeResult :=
  if seed.size > MAX_SEED_LEN then ⟨mem, 1, CU_DEFAULT⟩
  else
    match accts with
    | acct :: baseAcct :: _ =>
      let expected := deriveWithSeed base seed newOwner
      if !pubkeyEq acct.key expected then ⟨mem, 1, CU_DEFAULT⟩
      else if !pubkeyEq baseAcct.key base then ⟨mem, 1, CU_DEFAULT⟩
      else if !baseAcct.isSigner then ⟨mem, 1, CU_DEFAULT⟩
      else
        let m := writeBytes mem acct.ownerPtr 32 newOwner
        ⟨m, 0, CU_DEFAULT⟩
    | _ => ⟨mem, 1, CU_DEFAULT⟩

/-- Execute `TransferWithSeed`. Accounts: `from` (must derive from
    base+seed+from_owner), `base` (signer), `to`. Lamports move from `from` to `to`. -/
def execTransferWithSeed (mem : Mem) (accts : List AcctInput)
    (lamports : Nat) (fromSeed fromOwner : ByteArray) : NativeResult :=
  if fromSeed.size > MAX_SEED_LEN then ⟨mem, 1, CU_DEFAULT⟩
  else
    match accts with
    | fromAcct :: baseAcct :: toAcct :: _ =>
      let expected := deriveWithSeed baseAcct.key fromSeed fromOwner
      if !pubkeyEq fromAcct.key expected then ⟨mem, 1, CU_DEFAULT⟩
      else if !baseAcct.isSigner then ⟨mem, 1, CU_DEFAULT⟩
      else if fromAcct.lamports < lamports then ⟨mem, 1, CU_DEFAULT⟩
      else if toAcct.lamports + lamports ≥ U64_MODULUS then ⟨mem, 1, CU_DEFAULT⟩
      else
        let newFrom := fromAcct.lamports - lamports
        let newTo   := toAcct.lamports + lamports
        let m1 := writeU64 mem fromAcct.lamportsRefAddr newFrom
        let m2 := writeU64 m1 toAcct.lamportsRefAddr newTo
        ⟨m2, 0, CU_DEFAULT⟩
    | _ => ⟨mem, 1, CU_DEFAULT⟩

/-! ## Nonce-account variants

Durable-nonce machinery. The on-chain account stores a versioned
`NonceState`:

```
struct NonceVersions {
  version: u32 = 1,
  state:   NonceState,    -- Uninitialized | Initialized
}

struct Initialized {
  authority:      Pubkey,   -- 32 B
  durable_nonce:  Hash,     -- 32 B
  fee_calculator: FeeCalculator { lamports_per_signature: u64 },  -- 8 B
}
```

Serialized size: 4 + 4 + 32 + 32 + 8 = 80 bytes.

State machine: Init via `InitializeNonceAccount`; once Initialized,
`AdvanceNonceAccount` rotates `durable_nonce`, `AuthorizeNonceAccount`
rotates `authority`, `WithdrawNonceAccount` moves lamports out.
`UpgradeNonceAccount` (v0→v1) is a no-op since we only model v1.

The "current blockhash" (agave reads the `RecentBlockhashes` sysvar) is
modeled as a fixed `RECENT_BLOCKHASH_STUB`; mollusk's default matches it,
so cross-engine equality holds. -/

/-- Per-account nonce-data offsets within the account's `data` buffer
    (which lives at `acct.dataPtr` in caller memory). -/
private def NONCE_VERSION_OFFSET     : Nat := 0    -- 4 B u32
private def NONCE_STATE_TAG_OFFSET   : Nat := 4    -- 4 B u32: 0=Uninit, 1=Init
private def NONCE_AUTHORITY_OFFSET   : Nat := 8    -- 32 B
private def NONCE_DURABLE_OFFSET     : Nat := 40   -- 32 B
private def NONCE_FEE_OFFSET         : Nat := 72   -- 8 B u64
private def NONCE_TOTAL_SIZE         : Nat := 80

private def NONCE_VERSION_V1     : Nat := 1
private def NONCE_STATE_INIT     : Nat := 1

/-- Fixed stub blockhash (we don't track block boundaries; agave reads the sysvar). -/
private def RECENT_BLOCKHASH_STUB : ByteArray :=
  ⟨((List.range 32).map (fun _ => (0 : UInt8))).toArray⟩

/-- Stub fee-calculator: lamports_per_signature = 5000 (mainnet's
    historical default). -/
private def DEFAULT_LAMPORTS_PER_SIGNATURE : Nat := 5000

/-- Read the 4-byte version tag from the account's data buffer. -/
private def readNonceVersion (mem : Mem) (dataPtr : Nat) : Nat :=
  let b0 := mem  dataPtr             % 256
  let b1 := mem (dataPtr + 1)        % 256
  let b2 := mem (dataPtr + 2)        % 256
  let b3 := mem (dataPtr + 3)        % 256
  b0 + b1 * 0x100 + b2 * 0x10000 + b3 * 0x1000000

/-- Read the 4-byte state-variant tag. -/
private def readNonceStateTag (mem : Mem) (dataPtr : Nat) : Nat :=
  let off := dataPtr + NONCE_STATE_TAG_OFFSET
  let b0 := mem  off             % 256
  let b1 := mem (off + 1)        % 256
  let b2 := mem (off + 2)        % 256
  let b3 := mem (off + 3)        % 256
  b0 + b1 * 0x100 + b2 * 0x10000 + b3 * 0x1000000

/-- Read the 32-byte authority pubkey. -/
private def readNonceAuthority (mem : Mem) (dataPtr : Nat) : ByteArray :=
  SVM.SBPF.readBytes mem (dataPtr + NONCE_AUTHORITY_OFFSET) 32

/-- Write a u32 LE at `addr`. -/
private def writeU32 (mem : Mem) (addr v : Nat) : Mem :=
  fun a =>
    if a = addr     then v % 0x100
    else if a = addr + 1 then v / 0x100 % 0x100
    else if a = addr + 2 then v / 0x10000 % 0x100
    else if a = addr + 3 then v / 0x1000000 % 0x100
    else mem a

/-- Execute `AuthorizeNonceAccount(new_authority)`. The current
    authority must sign; we then overwrite `state.authority`. -/
def execAuthorizeNonceAccount (mem : Mem) (accts : List AcctInput)
    (newAuthority : ByteArray) : NativeResult :=
  match accts with
  | acct :: _ =>
    if acct.dataLen < NONCE_TOTAL_SIZE then ⟨mem, 1, CU_DEFAULT⟩
    else
      let version := readNonceVersion mem acct.dataPtr
      let stateTag := readNonceStateTag mem acct.dataPtr
      if version ≠ NONCE_VERSION_V1 ∨ stateTag ≠ NONCE_STATE_INIT then
        ⟨mem, 1, CU_DEFAULT⟩
      else
        let curAuth := readNonceAuthority mem acct.dataPtr
        -- agave requires the current authority to sign. We approximate as
        -- `acct.isSigner ∧ acct.key == curAuth` (self-authorized nonce).
        if !acct.isSigner then ⟨mem, 1, CU_DEFAULT⟩
        else if !pubkeyEq acct.key curAuth then ⟨mem, 1, CU_DEFAULT⟩
        else
          let m := writeBytes mem (acct.dataPtr + NONCE_AUTHORITY_OFFSET)
                              32 newAuthority
          ⟨m, 0, CU_DEFAULT⟩
  | _ => ⟨mem, 1, CU_DEFAULT⟩

/-- Execute `InitializeNonceAccount(authority)`. The account must be
    uninitialized (state tag = 0). After: version = 1, state =
    Initialized { authority, durable_nonce = RECENT_BLOCKHASH_STUB,
    fee_calculator = DEFAULT }. -/
def execInitializeNonceAccount (mem : Mem) (accts : List AcctInput)
    (authority : ByteArray) : NativeResult :=
  match accts with
  | acct :: _ =>
    if acct.dataLen < NONCE_TOTAL_SIZE then ⟨mem, 1, CU_DEFAULT⟩
    else
      let stateTag := readNonceStateTag mem acct.dataPtr
      if stateTag ≠ 0 then ⟨mem, 1, CU_DEFAULT⟩  -- not Uninitialized
      else
        -- Write: version=1 | state=Init(1) | authority | nonce | fee.
        let m1 := writeU32  mem (acct.dataPtr + NONCE_VERSION_OFFSET)     1
        let m2 := writeU32  m1  (acct.dataPtr + NONCE_STATE_TAG_OFFSET)   1
        let m3 := writeBytes m2 (acct.dataPtr + NONCE_AUTHORITY_OFFSET)   32 authority
        let m4 := writeBytes m3 (acct.dataPtr + NONCE_DURABLE_OFFSET)     32 RECENT_BLOCKHASH_STUB
        let m5 := writeU64  m4  (acct.dataPtr + NONCE_FEE_OFFSET) DEFAULT_LAMPORTS_PER_SIGNATURE
        ⟨m5, 0, CU_DEFAULT⟩
  | _ => ⟨mem, 1, CU_DEFAULT⟩

/-- Execute `AdvanceNonceAccount`. Rotates `state.durable_nonce` to
    the current blockhash. Authority must sign. -/
def execAdvanceNonceAccount (mem : Mem) (accts : List AcctInput) :
    NativeResult :=
  match accts with
  | acct :: _ =>
    if acct.dataLen < NONCE_TOTAL_SIZE then ⟨mem, 1, CU_DEFAULT⟩
    else
      let stateTag := readNonceStateTag mem acct.dataPtr
      if stateTag ≠ NONCE_STATE_INIT then ⟨mem, 1, CU_DEFAULT⟩
      else
        let curAuth := readNonceAuthority mem acct.dataPtr
        if !acct.isSigner then ⟨mem, 1, CU_DEFAULT⟩
        else if !pubkeyEq acct.key curAuth then ⟨mem, 1, CU_DEFAULT⟩
        else
          let m := writeBytes mem (acct.dataPtr + NONCE_DURABLE_OFFSET)
                              32 RECENT_BLOCKHASH_STUB
          ⟨m, 0, CU_DEFAULT⟩
  | _ => ⟨mem, 1, CU_DEFAULT⟩

/-- Execute `WithdrawNonceAccount(lamports)`. Accounts: nonce (signs),
    recipient. Moves lamports out; full drain wipes the account back to
    Uninitialized. We don't model Rent (agave's rent-exempt-minimum check). -/
def execWithdrawNonceAccount (mem : Mem) (accts : List AcctInput)
    (lamports : Nat) : NativeResult :=
  match accts with
  | nonceAcct :: toAcct :: _ =>
    if nonceAcct.lamports < lamports then ⟨mem, 1, CU_DEFAULT⟩
    else if toAcct.lamports + lamports ≥ U64_MODULUS then ⟨mem, 1, CU_DEFAULT⟩
    else if !nonceAcct.isSigner then ⟨mem, 1, CU_DEFAULT⟩
    else
      let newNonce := nonceAcct.lamports - lamports
      let newTo    := toAcct.lamports + lamports
      let m1 := writeU64 mem nonceAcct.lamportsRefAddr newNonce
      let m2 := writeU64 m1 toAcct.lamportsRefAddr newTo
      -- Full drain → reset state to Uninitialized.
      let m3 := if newNonce = 0 then
        writeU32 m2 (nonceAcct.dataPtr + NONCE_STATE_TAG_OFFSET) 0
      else m2
      ⟨m3, 0, CU_DEFAULT⟩
  | _ => ⟨mem, 1, CU_DEFAULT⟩

/-- Execute `UpgradeNonceAccount`. We only model v1: no-op if already v1,
    fail for legacy v0. -/
def execUpgradeNonceAccount (mem : Mem) (accts : List AcctInput) :
    NativeResult :=
  match accts with
  | acct :: _ =>
    if acct.dataLen < NONCE_TOTAL_SIZE then ⟨mem, 1, CU_DEFAULT⟩
    else
      let version := readNonceVersion mem acct.dataPtr
      if version = NONCE_VERSION_V1 then ⟨mem, 0, CU_DEFAULT⟩  -- already v1
      else ⟨mem, 1, CU_DEFAULT⟩
  | _ => ⟨mem, 1, CU_DEFAULT⟩

/-- Top-level System dispatcher. Always returns `some` (so native dispatch
    consumes the call); unknown variants return `r0=1` instead of falling
    through to the BPF registry. -/
def dispatch (ixData : ByteArray) (accts : List AcctInput) (mem : Mem) :
    Option NativeResult :=
  match decode ixData with
  | .createAccount lamports space owner =>
    some (execCreateAccount mem accts lamports space owner)
  | .assign owner                       => some (execAssign mem accts owner)
  | .transfer lamports                  => some (execTransfer mem accts lamports)
  | .createAccountWithSeed base seed lamports space owner =>
    some (execCreateAccountWithSeed mem accts base seed lamports space owner)
  | .advanceNonceAccount                => some (execAdvanceNonceAccount mem accts)
  | .withdrawNonceAccount lamports      => some (execWithdrawNonceAccount mem accts lamports)
  | .initializeNonceAccount authority   => some (execInitializeNonceAccount mem accts authority)
  | .authorizeNonceAccount newAuth      => some (execAuthorizeNonceAccount mem accts newAuth)
  | .allocate space                     => some (execAllocate mem accts space)
  | .allocateWithSeed base seed space owner =>
    some (execAllocateWithSeed mem accts base seed space owner)
  | .assignWithSeed base seed owner     => some (execAssignWithSeed mem accts base seed owner)
  | .transferWithSeed lamports fromSeed fromOwner =>
    some (execTransferWithSeed mem accts lamports fromSeed fromOwner)
  | .upgradeNonceAccount                => some (execUpgradeNonceAccount mem accts)
  | .unknown _ =>
    -- Unknown discriminant: deterministic failure, no fall-through.
    some ⟨mem, 1, CU_DEFAULT⟩

/-! ## Boundedness — the System leg of the `hnative` discharge
(`SVM/SBPF/BoundedCpi.lean`): every dispatch returns a u64 `r0` (always
`0`/`1`) and byte-bounded caller memory (all writes go through
`writeU64`/`writeBytes`/`writeU32`). In-file because the nonce arms write
through the private `writeU32`. -/

private theorem writeU32_lt (mem : Mem) (addr v : Nat)
    (hm : ∀ a, mem a < 256) : ∀ a, writeU32 mem addr v a < 256 := by
  intro a
  apply SVM.SBPF.Mem.read_mk_lt
  intro x
  repeat first
    | apply SVM.SBPF.ite_lt
    | exact Nat.mod_lt _ (by decide)
    | exact hm _

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 65536 in
set_option linter.unusedSimpArgs false in
theorem dispatch_bounded {ixData : ByteArray} {accts : List AcctInput}
    {mem : Mem} {nr : NativeResult} (hm : ∀ a, mem a < 256)
    (h : dispatch ixData accts mem = some nr) :
    nr.r0 < SVM.SBPF.U64_MODULUS ∧ ∀ a, nr.mem a < 256 := by
  have hzero : (0 : Nat) < SVM.SBPF.U64_MODULUS := by decide
  have hone : (1 : Nat) < SVM.SBPF.U64_MODULUS := by decide
  unfold dispatch at h
  repeat' split at h
  all_goals (injection h with h; subst h)
  all_goals
    first
      | exact ⟨hone, hm⟩
      | exact ⟨hzero, hm⟩
      | (simp only [execTransfer, execCreateAccount, execAllocate, execAssign,
           execCreateAccountWithSeed, execAllocateWithSeed, execAssignWithSeed,
           execTransferWithSeed, execAuthorizeNonceAccount,
           execInitializeNonceAccount, execAdvanceNonceAccount,
           execWithdrawNonceAccount, execUpgradeNonceAccount]
         refine ⟨?_, ?_⟩
         · repeat' split
           all_goals first | exact hzero | exact hone
         · intro a
           repeat' split
           all_goals
             repeat first
               | exact hm
               | exact hm _
               | (refine SVM.SBPF.writeU64_lt _ _ _ ?_)
               | (refine SVM.SBPF.writeU64_lt _ _ _ ?_ _)
               | (refine SVM.SBPF.writeBytes_lt _ _ _ _ ?_)
               | (refine SVM.SBPF.writeBytes_lt _ _ _ _ ?_ _)
               | (refine writeU32_lt _ _ _ ?_)
               | (refine writeU32_lt _ _ _ ?_ _))

end SVM.Native.System
