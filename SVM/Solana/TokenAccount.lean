-- High-level SL predicate for an SPL Token v4 account.
--
-- The byte layout matches `spl_token::state::Account` serialized via Pack:
--
--   offset  size  field
--   0       32    mint              (Pubkey)
--   32      32    owner             (Pubkey)
--   64      8     amount            (u64, little-endian)
--   72      36    delegate          (COption<Pubkey>: 4-byte disc + 32-byte pk)
--   108     1     state             (AccountState: 0=Uninit, 1=Init, 2=Frozen)
--   109     12    is_native         (COption<u64>: 4-byte disc + 8-byte value)
--   121     8     delegated_amount  (u64)
--   129     36    close_authority   (COption<Pubkey>)
--   ----   ----
--   total = 165 bytes
--
-- `tokenAcctBalance`: a bundled SL atom over the mint / owner / amount triple
-- (the load-bearing fields for Transfer-class proofs) with the remaining 93
-- bytes as an opaque `rest : ByteArray` frame. Refinement proofs unfold it to
-- align with the per-instruction `↦U64` / `↦Pubkey` atoms.

import SVM.SBPF.PubkeySL

namespace SVM.Solana

open SVM.SBPF
open SVM.Pubkey

/-! ## Field offsets (SPL Token v4 Pack layout) -/

/-- Byte offset of the `mint` field within an SPL Token account. -/
def MINT_OFF : Nat := 0

/-- Byte offset of the `owner` field. -/
def OWNER_OFF : Nat := 32

/-- Byte offset of the `amount` field (8-byte little-endian u64). -/
def AMOUNT_OFF : Nat := 64

/-- Byte offset of the opaque tail (delegate / state / is_native / delegated_amount / close_authority). -/
def REST_OFF : Nat := 72

/-- Total serialized size of an SPL Token account. -/
def TOKEN_ACCOUNT_SIZE : Nat := 165

/-- Size of the opaque tail (`TOKEN_ACCOUNT_SIZE - REST_OFF`). -/
def REST_SIZE : Nat := 93

/-! ## SL predicate -/

/-- An SPL Token account at byte address `ata` with the given mint, owner, and
    balance. The remaining 93 bytes (delegate / state / is_native /
    delegated_amount / close_authority) are an opaque `rest` byte-array;
    well-formed callers require `rest.size = REST_SIZE`.

    A balance-preserving Transfer post-state rebinds only `amount` (`preA - x` /
    `preB + x`); `mint`, `owner`, `rest` flow through unchanged. -/
def tokenAcctBalance
    (ata : Nat) (mint owner : Pubkey) (amount : Nat) (rest : ByteArray) :
    Assertion :=
  ((ata + MINT_OFF)   ↦Pubkey mint)  **
  ((ata + OWNER_OFF)  ↦Pubkey owner) **
  ((ata + AMOUNT_OFF) ↦U64    amount) **
  ((ata + REST_OFF)   ↦Bytes  rest)

end SVM.Solana
