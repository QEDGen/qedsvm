/-
  SHA-512 (FIPS-180-4, 64-byte output).

  Backed by `rust-bridge` calling `sha2 = 0.10.8` — the same crate
  agave's `solana-sha512-hasher` wraps with the `sha2` feature.
  The `opaque` Lean side treats the hash as a black box at proof
  time; `native_decide` reduces it via `ofReduceBool`.

  Wired to the `.sol_sha512` syscall via `Sha512.exec` below.
-/

import Svm.SBPF.Machine

namespace Svm.SBPF
namespace Sha512

/-- SHA-512 of `data`, returning the 64-byte digest.

    Implemented in Rust (`rust-bridge`) calling `sha2::Sha512::digest`. -/
@[extern "lean_sha512"]
opaque hash (data : @& ByteArray) : ByteArray

/-! ## `sol_sha512` syscall

Same `SliceDesc`-list ABI as `sol_sha256` / `sol_keccak256`, only the
output is 64 bytes. Cost mirrors agave's `sha256_base_cost` (the same
table entry covers all four hash families). -/

/-- Same per-byte CU as sha256 (one row in agave's cost table covers
    sha256/sha512/keccak256/blake3): `base (85) + bytes`. -/
@[simp] def cu (s : State) : Nat := 85 + sumSliceLens s.mem s.regs.r1 s.regs.r2

@[simp] def exec (s : State) : State :=
  let digest := hash (readSlices s.mem s.regs.r1 s.regs.r2)
  { s with regs := s.regs.set .r0 0
           mem  := writeBytes s.mem s.regs.r3 64 digest }

end Sha512
end Svm.SBPF
