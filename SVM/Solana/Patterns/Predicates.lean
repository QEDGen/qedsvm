-- Solana Pattern Proof Library, Layer 1: predicates.
--
-- Reusable, security-meaningful state predicates for the low-level checks that
-- real Solana programs perform (and that exploits skip): signer, owner, key,
-- balance, discriminator, PDA. These are the spec vocabulary; Layer 2
-- (Recognizers) proves bytecode idioms refine them, Layer 3 (Guards) proves a
-- check dominates an effect on all paths. See docs/SOLANA_PATTERNS_LIBRARY.md.
--
-- SOUNDNESS DISCIPLINE: every predicate is defined over the grounded state
-- (real serialized offsets / SL atoms), never a convenient abstraction, so the
-- names cannot over-promise (the trap the solanalib Finance layer fell into).
-- Everything here is concrete byte/Nat work, so the library stays Mathlib-free.
--
-- TWO ADDRESS-SPACE VIEWS (do not conflate):
--   * Input-region account block: the SBF aligned-v1 serialized account, holding
--     runtime privilege/identity (signer/writable/key/owner-program/lamports).
--     Offsets mirror qedsvm-rs/src/serialize.rs and Runner.parseInputPrivileges.
--   * Account-data view: the bytes inside the account's `data` region
--     (discriminator/state byte, SPL token mint/owner/amount).
-- The two `owner`s differ: input-block owner@40 is the owning PROGRAM; the
-- token-data owner@32 (SVM.Solana.OWNER_OFF) is the token HOLDER.

import SVM.SBPF.PubkeySL
import SVM.SBPF.Memory
import SVM.Solana.Pda
import SVM.Solana.TokenAccount

namespace SVM.Solana.Patterns

open SVM.SBPF
open SVM.Pubkey

/-! ## Input-region serialized account block offsets (aligned-v1 loader)

Offsets are relative to a per-account block base `b`. The first block sits at
`INPUT_START + 8` (after the `u64 num_accounts` header); later blocks stride by
`nonDupBlockSize` (a multi-account locator is an open item). -/

/-- Non-dup marker byte (`0xFF`). -/
def DUP_MARKER_OFF : Nat := 0
/-- `is_signer` flag byte. -/
def SIGNER_OFF : Nat := 1
/-- `is_writable` flag byte. -/
def WRITABLE_OFF : Nat := 2
/-- `executable` flag byte. -/
def EXEC_OFF : Nat := 3
/-- Account key (Pubkey, 32 bytes). -/
def KEY_OFF : Nat := 8
/-- Owning program (Pubkey, 32 bytes). Distinct from the token-data owner. -/
def OWNER_PROG_OFF : Nat := 40
/-- Lamport balance (u64, little-endian). -/
def LAMPORTS_OFF : Nat := 72
/-- Account data length (u64, little-endian). -/
def DATA_LEN_OFF : Nat := 80
/-- Start of the account `data` bytes. -/
def DATA_OFF : Nat := 88

/-- Base of the first serialized account block in the input region. -/
def firstAcctBlock : Nat := Memory.INPUT_START + 8

/-! ## Privilege / identity predicates (input-region view)

Flag predicates pin the exact byte (`memByteIs` stores raw, and the serializer
writes exactly `0`/`1`), so they carry the value constraint by construction. -/

/-- The account at input block `b` is marked a signer. -/
def isSigner (b : Nat) : Assertion := (b + SIGNER_OFF) ↦ₘ 1

/-- The account at input block `b` is NOT a signer (the negative the bug-finders
    care about; pairs with Layer-3 domination). -/
def notSigner (b : Nat) : Assertion := (b + SIGNER_OFF) ↦ₘ 0

/-- The account at input block `b` is marked writable. -/
def isWritable (b : Nat) : Assertion := (b + WRITABLE_OFF) ↦ₘ 1

/-- The account at input block `b` is marked executable. -/
def isExecutable (b : Nat) : Assertion := (b + EXEC_OFF) ↦ₘ 1

/-- The account key at input block `b` equals `k`. -/
def keyIs (b : Nat) (k : Pubkey) : Assertion := (b + KEY_OFF) ↦Pubkey k

/-- The account at input block `b` is owned by program `prog`. This is the
    canonical owner check (the most-skipped check in real exploits). -/
def ownedByProgram (b : Nat) (prog : Pubkey) : Assertion :=
  (b + OWNER_PROG_OFF) ↦Pubkey prog

/-- Exact lamport balance of the account at input block `b`. -/
def lamportsIs (b v : Nat) : Assertion := (b + LAMPORTS_OFF) ↦U64 v

/-- The account at input block `b` holds at least `n` lamports. A genuine lower
    bound (existential over the cell value with a `≤`), not a degenerate one. -/
def lamportsAtLeast (b n : Nat) : Assertion :=
  fun ps => ∃ v, n ≤ v ∧ lamportsIs b v ps

/-- The account data length at input block `b` equals `n`. -/
def dataLenIs (b n : Nat) : Assertion := (b + DATA_LEN_OFF) ↦U64 n

/-! ## Pubkey equality

The on-chain key/owner check compiles to a 32-byte comparison; at the spec level
it is just decidable `Pubkey` equality. Layer 2 proves a `memcmp`/unrolled-loop
idiom refines this. -/

/-- Two pubkeys are equal. `Pubkey` has `DecidableEq`, so this is computable. -/
abbrev pubkeyEq (a b : Pubkey) : Prop := a = b

/-! ## Discriminator / account-type (account-data view)

`dataBase` is the start of an account's `data` (e.g. `b + DATA_OFF` for an input
account). A missing discriminator check is the type-confusion bug class. -/

/-- One-byte discriminator / state tag at `dataBase` equals `disc` (SPL token
    uses 1-byte tags). `disc < 256` is implied by the raw-byte cell. -/
def hasDiscriminator8 (dataBase disc : Nat) : Assertion := dataBase ↦ₘ disc

/-- Multi-byte discriminator at `dataBase` equals `tag` (Anchor uses 8 bytes). -/
def hasDiscriminator (dataBase : Nat) (tag : ByteArray) : Assertion :=
  dataBase ↦Bytes tag

/-! ## Token balance (account-data view)

Read consistently with `tokenAcctBalance`: the balance lives at
`ata + AMOUNT_OFF` (= 64) as a `↦U64`. -/

/-- The SPL token account at data address `ata` holds at least `n` tokens. -/
def balanceAtLeast (ata n : Nat) : Assertion :=
  fun ps => ∃ v, n ≤ v ∧ ((ata + SVM.Solana.AMOUNT_OFF) ↦U64 v) ps

/-! ## PDA

Reuse the existing derivation predicates (raw `ByteArray` form). Off-curve is
opaque FFI, discharged as a hypothesis by consumers (see
`call_sol_create_program_address_spec`). A `Pubkey`-typed `isPdaPubkey` awaits
the `Pubkey ↔ ByteArray` bridge (open item). -/

/-- `ata` is the canonical PDA of `seeds` under `program`. -/
abbrev isPda := SVM.Solana.isPda

/-- `ata` is the PDA of `seeds` under `program` for the specific `bump`. -/
abbrev isPdaWithBump := SVM.Solana.isPdaWithBump

/-! ## Layer 2 / Layer 3 (separate files, not here)

A Layer-2 recognizer has the shape (illustrative, proven SEMANTICALLY via the
account_agg / codecCoarse_eq_fine / cuTripleWithinMem machinery, never by
byte-matching):

    theorem recognize_owner_check (cr : CodeReq) (entry exit b : Nat)
        (prog : Pubkey) ... :
      cuTripleWithinMem nSteps nCu entry exit cr
        (ownedByProgram b prog ** P) (ownedByProgram b prog ** P) rr

A Layer-3 guard states "effect E is dominated by check C on all paths," built on
the dispatch/CFG substrate (`dispatch_routing_complete`). That is the
missing-check detector for qedgen. -/

end SVM.Solana.Patterns
