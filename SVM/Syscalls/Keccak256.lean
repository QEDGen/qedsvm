/-
  Keccak-256 (original Keccak, not FIPS-202 SHA-3).

  Solana uses original Keccak with 0x01 padding (vs SHA-3's 0x06).
  Backed by `lean-bridge` calling the `sha3 = 0.10.8` crate's
  `Keccak256` digest — exactly what agave's `solana-keccak-hasher`
  wraps. The `opaque` Lean side treats the hash as a black box at
  proof time; `native_decide` reduces it via `ofReduceBool` (same
  axiom already in use elsewhere).

  We deliberately do **not** ship a pure-Lean spec here. Verification
  of Keccak's algebraic properties is downstream work — its own
  project — and shouldn't gate the runner.

  Wired to the `.sol_keccak256` syscall via `Keccak256.exec` below.
-/

import SVM.SBPF.Machine

namespace SVM.SBPF
namespace Keccak256

/-- Keccak-256 of `data`, returning the 32-byte digest.

    Implemented in Rust (`lean-bridge`) calling
    `sha3::Keccak256`. Solana variant — uses 0x01 padding, NOT SHA-3's
    0x06 padding. -/
@[extern "lean_keccak256"]
opaque hash (data : @& ByteArray) : ByteArray

/-! ## `sol_keccak256` syscall

Same `SliceDesc`-list ABI and base cost as `sol_sha256`. -/

@[simp] def cu (s : State) : Nat := 85 + hashSliceCost s.mem s.regs.r1 s.regs.r2

/-- H6 (stage 3a): route the fixed 32-byte output `[r3, r3+32)` through
    `guardWrite` (agave's `translate_slice_mut`, checked before hashing). -/
@[simp] def exec (s : State) : State :=
  let digest := hash (readSlices s.mem s.regs.r1 s.regs.r2)
  s.guardWrite s.regs.r3 32 fun s =>
    { s with regs := s.regs.set .r0 0
             mem  := writeBytes s.mem s.regs.r3 32 digest }

end Keccak256
end SVM.SBPF
