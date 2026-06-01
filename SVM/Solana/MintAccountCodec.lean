/-
  Byte-level SL codec for the SPL Token *mint* account, plus the
  record-keyed view bridging it to the abstract `Mint` record
  (`SVM/Solana/Abstract/State.lean`). Sibling of `TokenAccount.lean` +
  `TokenAccountCodec.lean`, for the MintTo / Burn intrinsics.

  Only `supply` is mutated by MintTo/Burn; it sits at byte offset 36,
  after the 36-byte `COption<Pubkey>` mint_authority, so it can't be a
  single trailing field. The mint_authority (`preAuth`) and the
  decimals/is_initialized/freeze_authority tail (`rest`) are carried as
  opaque byte-arrays that flow through unchanged.
-/

import SVM.SBPF.PubkeySL
import SVM.Solana.Abstract.State

namespace SVM.Solana

open SVM.SBPF
open SVM.Solana.Abstract

/-! ## Field offsets (SPL Token v4 Mint Pack layout) -/

/-- Byte offset of the `mint_authority` COption<Pubkey> (36 bytes). -/
def MINT_AUTH_OFF : Nat := 0

/-- Byte offset of the `supply` field (8-byte little-endian u64). -/
def SUPPLY_OFF : Nat := 36

/-- Byte offset of the opaque tail (decimals / is_initialized /
    freeze_authority). -/
def MINT_REST_OFF : Nat := 44

/-- Total serialized size of an SPL Token mint account. -/
def MINT_ACCOUNT_SIZE : Nat := 82

/-! ## SL predicate -/

/-- An SPL Token mint account at byte address `base` with the given
    supply. `preAuth` (36 bytes: the `COption<Pubkey>` mint_authority)
    and `rest` (38 bytes: decimals / is_initialized / freeze_authority)
    are opaque flow-through byte-arrays; well-formed callers require
    `preAuth.size = 36` and `rest.size = 38`.

    The post-state of a MintTo/Burn rebinds only the `supply` argument
    (`supply ± amount`); `preAuth` and `rest` flow through unchanged. -/
def mintAcctSupply
    (base : Nat) (preAuth : ByteArray) (supply : Nat) (rest : ByteArray) :
    Assertion :=
  ((base + MINT_AUTH_OFF) ↦Bytes preAuth) **
  ((base + SUPPLY_OFF)    ↦U64   supply)  **
  ((base + MINT_REST_OFF) ↦Bytes rest)

/-! ## Record-keyed view -/

/-- Record-keyed view of `mintAcctSupply`: the SL atom for a full mint
    account at byte address `base`, with contents matching abstract `m`. -/
def mintSupplyOf (base : Nat) (m : Abstract.Mint) : Assertion :=
  mintAcctSupply base m.preAuth m.supply m.rest

/-- Definitional unfold for `simp` chains. -/
@[simp] theorem mintSupplyOf_eq (base : Nat) (m : Abstract.Mint) :
    mintSupplyOf base m = mintAcctSupply base m.preAuth m.supply m.rest := rfl

/-- A `withSupply` shift on the abstract record rewrites the SL atom to
    one with the new supply, preAuth/rest unchanged. The load-bearing
    lemma the MintTo/Burn refinement applies to convert the abstract
    post-state to the asm-side predicate. -/
@[simp] theorem mintSupplyOf_withSupply
    (base : Nat) (m : Abstract.Mint) (s : Nat) :
    mintSupplyOf base (m.withSupply s) =
      mintAcctSupply base m.preAuth s m.rest := by
  unfold mintSupplyOf Abstract.Mint.withSupply
  rfl

end SVM.Solana
