-- Separation-logic atom for `Pubkey`.
--
-- `SVM/SBPF/Pubkey.lean` defines `pubkeyAt mem base pk` over the flat `Mem`
-- model. This module adds the SL-level companion `pubkeyIs base pk`: an
-- `Assertion` over partial states, composable with the other `↦`-atoms in
-- `SepLogic.lean` via separating conjunction `**`.
--
-- Shape: four chained `↦U64` atoms at offsets 0, 8, 16, 24 — matching the
-- in-memory representation that compiled sBPF code reads via four `ldxdw`
-- chunk-loads (see `SVM.Pubkey.Pubkey` doc-comment).

import SVM.SBPF.Pubkey
import SVM.SBPF.SepLogic

namespace SVM.SBPF

open SVM.Pubkey

/-- SL assertion: a `Pubkey` lives at `base..base+32` as four little-endian
    U64 chunks. The SL-level companion to `pubkeyAt`. -/
def pubkeyIs (base : Nat) (pk : Pubkey) : Assertion :=
  (base          ↦U64 pk.c0) **
  ((base + 8)    ↦U64 pk.c1) **
  ((base + 16)   ↦U64 pk.c2) **
  ((base + 24)   ↦U64 pk.c3)

@[inherit_doc] notation:50 a " ↦Pubkey " pk => pubkeyIs a pk

end SVM.SBPF
