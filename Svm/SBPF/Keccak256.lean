/-
  Keccak-256 (original Keccak, not FIPS-202 SHA-3).

  Solana uses original Keccak with 0x01 padding (vs SHA-3's 0x06).
  Backed by `rust-bridge` calling the `sha3 = 0.10.8` crate's
  `Keccak256` digest — exactly what agave's `solana-keccak-hasher`
  wraps. The `opaque` Lean side treats the hash as a black box at
  proof time; `native_decide` reduces it via `ofReduceBool` (same
  axiom already in use elsewhere).

  We deliberately do **not** ship a pure-Lean spec here. Verification
  of Keccak's algebraic properties is downstream work — its own
  project — and shouldn't gate the runner.

  Wired to the `.sol_keccak256` syscall via `Keccak256.exec` below.
-/

import Svm.SBPF.Machine

namespace Svm.SBPF
namespace Keccak256

/-- Keccak-256 of `data`, returning the 32-byte digest.

    Implemented in Rust (`rust-bridge`) calling
    `sha3::Keccak256`. Solana variant — uses 0x01 padding, NOT SHA-3's
    0x06 padding. -/
@[extern "lean_keccak256"]
opaque hash (data : @& ByteArray) : ByteArray

/-! ## `sol_keccak256` syscall

Same `SliceDesc`-list ABI and base cost as `sol_sha256`. -/

def cu : Nat := 85

@[simp] def exec (s : State) : State :=
  let digest := hash (readSlices s.mem s.regs.r1 s.regs.r2)
  { s with regs := s.regs.set .r0 0
           mem  := writeBytes s.mem s.regs.r3 32 digest }

end Keccak256
end Svm.SBPF
