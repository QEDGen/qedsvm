-- PDA derivation predicates over the `SVM.Syscalls.Pda` machinery.
--
-- A PDA is a Pubkey derived from seeds + program ID landing off the ed25519
-- curve (so no keypair can sign; only the owning program can). Mirrors agave
-- `Pubkey::find_program_address` / `create_program_address`.
--
--   * `isPda` — canonical PDA (off-curve hash for the highest valid bump);
--     existential over bump, matching `find_program_address`.
--   * `isPdaWithBump` — PDA for a specific bump; no existential, matching a
--     program re-deriving with a known bump (`create_program_address`).
--
-- Canonical refinement target for `Stmt::Pda { bind, seeds, program }`:
-- the obligation is exactly `isPda bind program seeds`.
--
-- Both take raw `ByteArray` (the syscall API form). A `Pubkey`-typed wrapper
-- `isPdaPubkey` waits on `Pubkey ↔ ByteArray` utils (mir-direction-a memory).

import SVM.Syscalls.Pda

namespace SVM.Solana

/-- `ata` is the canonical PDA of `seeds` under program `program`.
    Asserts the existence of a bump value such that
    `find_program_address(seeds, program) = (ata, bump)`. -/
def isPda (ata program : ByteArray) (seeds : List ByteArray) : Prop :=
  ∃ bump : UInt8,
    SVM.SBPF.Pda.tryFindProgramAddress seeds program = some (ata, bump)

/-- `ata` is the PDA for the specific `bump`: `create_program_address(seeds ++
    [bump], program) = ata`. Used where the program carries `bump` as a known
    constant (canonical-bump computed off-chain, passed in / stored in state). -/
def isPdaWithBump (ata program : ByteArray) (seeds : List ByteArray)
    (bump : UInt8) : Prop :=
  SVM.SBPF.Pda.createProgramAddress (seeds ++ [⟨#[bump]⟩]) program
    = some ata

/-- Canonical-bump form implies the existence form. The converse (extracting
    `bump` from `isPda`) holds only when the witness is the largest valid bump,
    not provable here without unfolding the search loop. -/
theorem isPdaWithBump_implies_create
    {ata program : ByteArray} {seeds : List ByteArray} {bump : UInt8}
    (h : isPdaWithBump ata program seeds bump) :
    SVM.SBPF.Pda.createProgramAddress (seeds ++ [⟨#[bump]⟩]) program
      = some ata := h

end SVM.Solana
