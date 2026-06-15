-- Separation-logic atom for `Pubkey`: the SL companion `pubkeyIs base pk` to
-- `Pubkey.lean`'s flat-`Mem` `pubkeyAt`, composable with other `↦`-atoms via
-- `**`. Shape: four chained `↦U64` at offsets 0/8/16/24, matching the four
-- `ldxdw` chunk-loads compiled sBPF code uses.

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
