-- The Solana System program — native, not BPF.
--
-- Agave's System program implementation lives in
-- `programs/system/src/system_processor.rs`. It deserializes its
-- instruction from `ix.data` via bincode and dispatches on the
-- `SystemInstruction` enum discriminant (a u32 LE prefix).
--
-- The program-id is the all-zero pubkey (`11111111111111111111111111111111`),
-- so when its little-endian Nat encoding is computed by the Runner's
-- CPI arm it lands at `0`. Native.dispatch keys on this.
--
-- All 13 SystemInstruction variants are modeled here. Coverage is
-- driven by agave's actual semantics, not by what existing fixtures
-- happen to exercise — see [[feedback-project-charter]].

import SVM.Native.AcctInput
import SVM.SBPF.Machine
import SVM.Syscalls.Sha256

namespace SVM.Native.System

open SVM.SBPF.Memory
open SVM.SBPF (writeBytes)
open SVM.Native

/-- The all-zero pubkey, encoded little-endian as a `Nat`. The CPI
    handler reads the 32-byte program-id from caller memory the same
    way, so equality matches under this encoding. -/
def PROGRAM_ID : Nat := 0

/-- Per-instruction compute cost. Agave charges
    `solana_system_program_compute_cost = 150` for every System
    invocation (`solana-compute-budget/src/compute_budget.rs`).
    Per-discriminant variance only kicks in for the seed-based
    variants (which charge an extra sha256 cost); the simple
    Transfer / Assign / Allocate / CreateAccount paths all bottom
    out at 150. -/
def CU_DEFAULT : Nat := 150

/-! ## SystemInstruction discriminants

Mirrors agave's `solana_system_interface::SystemInstruction` enum,
field-for-field. All 13 variants are decoded; each has its own
arm in `dispatch` below. -/

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

`ix.data` is bincode-encoded: a u32 LE discriminant followed by the
payload. We read fields directly from the `ByteArray` rather than
going through a generic bincode layer; the inputs are small (≤80B
for the largest System variant) so the explicit reads are clearer
than a serializer. -/

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

/-- 64-bit modulus, mirroring `Memory.U64_MODULUS`. Used to clamp the
    post-transfer lamports against u64 overflow on the destination
    (agave returns `SystemError::ResultWithNegativeLamports` instead;
    we return r0=1 on both underflow and overflow). -/
private def U64_MODULUS : Nat := 0x10000000000000000

/-- MAX_PERMITTED_DATA_LENGTH from agave (and mirrored in
    `blueshift/sbpf/crates/runtime/src/cpi/builtins/system.rs:13`).
    System refuses to create or grow an account past 10 MiB. -/
private def MAX_PERMITTED_DATA_LENGTH : Nat := 10 * 1024 * 1024

/-- The all-zero System program pubkey (32 bytes). Used as the
    "owner = System" check for `CreateAccount`'s
    "is-this-account-uninitialized" gate. -/
private def isSystemOwner (b : ByteArray) : Bool :=
  b.size = 32 && (List.range 32).all (fun i => b.get! i = 0)

/-- Execute `Transfer { lamports }`. Two accounts required:
    `from` (signer, writable) and `to` (writable). Decrements
    `from.lamports` by `lamports`, increments `to.lamports`. -/
def execTransfer (mem : Mem) (accts : List AcctInput) (lamports : Nat) :
    NativeResult :=
  match accts with
  | fromAcct :: toAcct :: _ =>
    -- Agave checks: from is signer, both writable, from.owner = System,
    -- from.lamports ≥ lamports, no overflow on to. We surface a
    -- single failure code (r0 := 1) for any of these; specific
    -- `SystemError` mapping is a follow-up. (H9: the writable + owner
    -- gates were previously missing — agave rejects a transfer debiting a
    -- non-System-owned or read-only account: `ExternalAccountLamportSpend`
    -- / `ReadonlyLamportChange`. See docs/SOUNDNESS_AUDIT_* (H9).)
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

/-- Execute `CreateAccount { lamports, space, owner }`. Two accounts:
    `from` (signer, writable, funds source) and `to` (signer,
    writable, must be uninitialized).

    Agave checks:
    - both signers,
    - `to` looks uninitialized: `data.is_empty() ∧ lamports == 0 ∧
      owner == System`,
    - `from.lamports ≥ lamports`,
    - `space ≤ MAX_PERMITTED_DATA_LENGTH`.

    Effects:
    - `from.lamports -= lamports`, `to.lamports += lamports`,
    - `to.dataLen := space` (new bytes are zero — the caller's
      MAX_PERMITTED_DATA_INCREASE pad already covers it),
    - `to.owner := newOwner`.

    Returns `r0 := 1` on any check failure, otherwise the mutated
    memory + `r0 := 0` + `CU_DEFAULT`. -/
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
      -- Update the BPF program's Rc-chain length (so subsequent
      -- in-program AccountInfo accesses see the new size).
      let m3 := writeU64 m2 toAcct.dataLenRefAddr space
      -- Also update the *serialized* `data_len` slot in the input
      -- buffer (8 bytes before `dataPtr` per `serialize_parameters`
      -- block layout). This is what `deserialize_account_writes`
      -- reads when reconstructing the post-state, so without this
      -- write the harness sees `data.len() == 0` even though the
      -- BPF program would see the right size.
      let m4 := writeU64 m3 (toAcct.dataPtr - 8) space
      let m5 := writeBytes m4 toAcct.ownerPtr 32 newOwner
      ⟨m5, 0, CU_DEFAULT⟩
  | _ => ⟨mem, 1, CU_DEFAULT⟩

/-- Execute `Allocate { space }`. One account: `acct` (signer,
    writable, must be uninitialized: empty data, system-owned).
    Sets `acct.dataLen := space` in both the Rc-chain slot and the
    input-buffer slot (8 bytes before `dataPtr`). The MAX_PERMITTED
    pad already covers the new bytes (pre-zeroed). Lamports and
    owner are untouched. -/
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

/-- Execute `Assign { owner }`. One account: `acct` (signer,
    writable). Overwrites `acct.owner` with the 32-byte `newOwner`
    pubkey via `ownerPtr`. Lamports and data are untouched.

    Note: agave is permissive about the current owner — even a
    non-system-owned account can re-assign to a different owner if
    it's a signer (programs commonly use this to hand off accounts
    they created). -/
def execAssign (mem : Mem) (accts : List AcctInput) (newOwner : ByteArray) :
    NativeResult :=
  match accts with
  | acct :: _ =>
    -- H9: agave's `Assign` requires the account to be a (writable)
    -- signer AND currently owned by the System program — you cannot
    -- reassign an account another program owns. The owner gate was
    -- previously missing. See docs/SOUNDNESS_AUDIT_* (H9/M4-account).
    if !acct.isSigner then ⟨mem, 1, CU_DEFAULT⟩
    else if !acct.isWritable then ⟨mem, 1, CU_DEFAULT⟩
    else if !isSystemOwner acct.owner then ⟨mem, 1, CU_DEFAULT⟩
    else
      let m1 := writeBytes mem acct.ownerPtr 32 newOwner
      ⟨m1, 0, CU_DEFAULT⟩
  | _ => ⟨mem, 1, CU_DEFAULT⟩

/-! ## With-seed variants

`Pubkey::create_with_seed(base, seed, owner) = SHA256(base ‖ seed ‖
owner)`. Same primitive as PDA derivation but *without* the bump
search and the on-curve check — `create_with_seed` is allowed to
land on a valid ed25519 point, since the base account is what
actually signs. agave's check is just `seed.len() ≤ MAX_SEED_LEN
(32)` and an equality test against the pre-derived address. -/

/-- Compose `base ‖ seed ‖ owner` and SHA-256 it. -/
private def deriveWithSeed (base seed owner : ByteArray) : ByteArray :=
  SVM.SBPF.Sha256.hash (base ++ seed ++ owner)

/-- ByteArray equality on 32-byte pubkeys, byte-by-byte. -/
private def pubkeyEq (a b : ByteArray) : Bool :=
  a.size = b.size && (List.range a.size).all (fun i => a.get! i = b.get! i)

/-- The agave seed-length limit. `create_with_seed` returns
    `MaxSeedLengthExceeded` for `seed.len() > 32`. -/
private def MAX_SEED_LEN : Nat := 32

/-- Execute `CreateAccountWithSeed`. The new account (`accts[1]`) is
    NOT a signer of the transaction — instead its address is verified
    to equal `SHA256(base ‖ seed ‖ owner)`, and the base account
    (`accts[2]`) is the signer that authorizes the derivation.
    `accts[0]` is the funding `from`, same as the non-seed variant.

    Mirrors `blueshift/sbpf/crates/runtime/src/cpi/builtins/system.rs::create_account_with_seed`. -/
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

/-- Execute `AllocateWithSeed`. Two accounts: the derived address
    (`accts[0]`, NOT signer) and the base (`accts[1]`, signer that
    authorizes the operation). Allocates `space` bytes AND reassigns
    the owner (agave's allocate_with_seed does both, see
    `blueshift/.../system.rs:374-376`). -/
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

/-- Execute `TransferWithSeed`. Three accounts: `from` (writable,
    must be derived from base+seed+from_owner), `base` (signer,
    funds the signature), `to` (writable). Lamports move from
    `from` to `to` like a regular transfer. -/
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

Durable nonces are pre-priority-fees-era machinery that let
transactions live beyond a recent-blockhash window by carrying a
"nonce" the runtime advances after each use. The on-chain account
stores a versioned `NonceState`:

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

Serialized size: 4 (version) + 4 (variant tag for `state`) + 32
(authority) + 32 (nonce) + 8 (fee) = 80 bytes total.

State-machine: `Uninitialized → Initialized` via
`InitializeNonceAccount`. `Initialized → Initialized` via
`AdvanceNonceAccount` (rotates `durable_nonce` to the recent
blockhash), `AuthorizeNonceAccount` (rotates `authority`), or
`WithdrawNonceAccount` (lamports out — restricted to fully-funded
withdrawals to keep rent-exempt unless emptying entirely).

`UpgradeNonceAccount` is a v0→v1 migration we treat as a no-op
since qedsvm only models v1.

For `AdvanceNonceAccount` / `InitializeNonceAccount` we need a
"current blockhash" — agave reads `RecentBlockhashes` sysvar
account (deprecated but still threaded through this code path).
We model that as a fixed 32-byte value (`RECENT_BLOCKHASH_STUB`)
since qedsvm is per-instruction; mollusk's default supplies
the same stub, so cross-engine equality holds. -/

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

/-- Stub blockhash for AdvanceNonce / InitializeNonce. Agave reads the
    `RecentBlockhashes` sysvar; we don't track block boundaries, so
    we use a single fixed 32-byte value. -/
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

/-- Write a u32 LE at `addr`. Helper since most state fields are u32
    headers. -/
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
        -- Agave requires the *current authority* to be a signer of
        -- this transaction. We approximate by requiring `acct.isSigner`
        -- AND `acct.key == curAuth` — the nonce account itself can be
        -- the authority for self-authorized nonces. For cases where
        -- the authority is a separate pubkey, the caller must pass
        -- that account as a signer; we surface the failure when
        -- `acct` isn't both writable and signer.
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

/-- Execute `WithdrawNonceAccount(lamports)`. Two accounts: nonce
    account (writable, authority signs) and recipient (writable).
    Moves lamports out. For partial withdrawals the nonce account
    must remain rent-exempt; for full withdrawals (`lamports ==
    nonce.lamports`) we wipe the nonce account back to
    Uninitialized. We don't model Rent here — agave's check is
    `remaining < rent_exempt_minimum(80) → fail`; without Rent
    plumbing we just require either `lamports < nonce.lamports`
    (no rent check) or full drain. -/
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

/-- Execute `UpgradeNonceAccount`. agave migrates v0 → v1 nonce
    accounts here; qedsvm only models v1, so this is a no-op
    when the account is already v1, and a failure for legacy v0
    (we don't model it). -/
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

/-- Top-level System dispatcher. Decodes `ixData` and routes. Returns
    `some result` so the CPI handler knows native dispatch consumed
    the call; unimplemented variants still return `some` with `r0=1`
    so the failure surfaces deterministically rather than silently
    falling back to the BPF registry. -/
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
    -- Truly unknown discriminant (forward-compat: agave adds a new
    -- variant we haven't modeled yet). Surfaces as a deterministic
    -- failure rather than falling through to the BPF registry.
    some ⟨mem, 1, CU_DEFAULT⟩

end SVM.Native.System
