-- PDA derivation predicates.
--
-- A Program Derived Address (PDA) is a Pubkey deterministically derived
-- from a list of seeds and a program ID, such that the resulting address
-- lies off the ed25519 curve (so it cannot be a real keypair's public
-- key, and only the owning program can sign for it). See the agave
-- documentation for `Pubkey::find_program_address` /
-- `create_program_address`.
--
-- This module provides two Prop-level predicates over the existing PDA
-- syscall machinery in `SVM.Syscalls.Pda`:
--
--   * `isPda ata program seeds` — `ata` is the canonical PDA of `seeds`
--     under `program` (the off-curve hash for the highest valid bump).
--     Existentially quantifies the bump; matches what
--     `find_program_address` returns.
--
--   * `isPdaWithBump ata program seeds bump` — `ata` is the PDA for the
--     specific `bump`. Cheaper to verify than `isPda` (no existential)
--     and matches what programs do when re-deriving with a known bump
--     (`create_program_address` instead of `find_program_address`).
--
-- These are the canonical refinement target for a PDA-deriving step
-- (`Stmt::Pda { bind, seeds, program }`): the derivation obligation is
-- exactly `isPda bind program seeds`.
--
-- Both predicates operate over raw `ByteArray` (the form returned by
-- the syscall API in `SVM.SBPF.Pda`). A Pubkey-typed wrapper
-- (`isPdaPubkey ata program seeds` taking `Pubkey` rather than
-- `ByteArray`) waits on `Pubkey ↔ ByteArray` conversion utilities
-- landing in `SVM.Pubkey`; see the open task referenced in the
-- mir-direction-a project memory.

import SVM.Syscalls.Pda

namespace SVM.Solana

/-- `ata` is the canonical PDA of `seeds` under program `program`.
    Asserts the existence of a bump value such that
    `find_program_address(seeds, program) = (ata, bump)`. -/
def isPda (ata program : ByteArray) (seeds : List ByteArray) : Prop :=
  ∃ bump : UInt8,
    SVM.SBPF.Pda.tryFindProgramAddress seeds program = some (ata, bump)

/-- `ata` is the PDA for the specific `bump` under program `program`.
    Equivalent to `create_program_address(seeds ++ [bump], program) = ata`.

    Used at sites where the program carries `bump` as a known constant
    (typical for PDAs whose canonical-bump was computed off-chain and
    is now passed as instruction data or stored in account state). -/
def isPdaWithBump (ata program : ByteArray) (seeds : List ByteArray)
    (bump : UInt8) : Prop :=
  SVM.SBPF.Pda.createProgramAddress (seeds ++ [⟨#[bump]⟩]) program
    = some ata

/-- The canonical-bump form implies the existence form: if a specific
    bump derives `ata`, then *some* bump derives it (namely `bump`,
    though the canonical `find_program_address` may discover a larger
    one first). The converse — extracting `bump` from `isPda` — is the
    canonical-bump-equals-witnessed-bump statement, which holds when
    the witness is the largest valid bump (true for any PDA produced
    by `tryFindProgramAddress`; not provable here without unfolding
    the search loop). -/
theorem isPdaWithBump_implies_create
    {ata program : ByteArray} {seeds : List ByteArray} {bump : UInt8}
    (h : isPdaWithBump ata program seeds bump) :
    SVM.SBPF.Pda.createProgramAddress (seeds ++ [⟨#[bump]⟩]) program
      = some ata := h

end SVM.Solana
