/-
  Byte-level SL codec for the SPL Token *mint* account + record-keyed view
  onto the abstract `Mint`. For the MintTo / Burn intrinsics.

  Only `supply` is mutated; it sits mid-struct at offset 36 (after the
  36-byte `COption<Pubkey>` mint_authority), so not a trailing field.
  mint_authority (`preAuth`) and the decimals/is_init/freeze tail (`rest`)
  are opaque flow-through byte-arrays.
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

/-- Byte offset of the opaque tail (decimals / is_initialized / freeze_authority). -/
def MINT_REST_OFF : Nat := 44

/-- Total serialized size of an SPL Token mint account. -/
def MINT_ACCOUNT_SIZE : Nat := 82

/-! ## SL predicate -/

/-- An SPL Token mint account at byte address `base` with the given supply.
    `preAuth` (36-byte mint_authority) and `rest` (38-byte decimals/is_init/freeze
    tail) are opaque flow-through; well-formed callers require sizes 36 / 38.
    A MintTo/Burn post-state rebinds only `supply` (`supply ± amount`). -/
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

/-- Load-bearing: a `withSupply` shift rewrites the SL atom to the new supply
    (preAuth/rest unchanged); the MintTo/Burn refinement applies it to convert
    the abstract post-state to the asm-side predicate. -/
@[simp] theorem mintSupplyOf_withSupply
    (base : Nat) (m : Abstract.Mint) (s : Nat) :
    mintSupplyOf base (m.withSupply s) =
      mintAcctSupply base m.preAuth s m.rest := by
  unfold mintSupplyOf Abstract.Mint.withSupply
  rfl

end SVM.Solana
