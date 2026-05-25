/-
  SHA-512 (FIPS-180-4, 64-byte output).

  Backed by `lean-bridge` calling `sha2 = 0.10.8` — the same crate
  agave's `solana-sha512-hasher` wraps with the `sha2` feature.
  The `opaque` Lean side treats the hash as a black box at proof
  time; `native_decide` reduces it via `ofReduceBool`.

  Wired to the `.sol_sha512` syscall via `Sha512.exec` below.
-/

import SVM.SBPF.Machine

namespace SVM.SBPF
namespace Sha512

/-- SHA-512 of `data`, returning the 64-byte digest.

    Implemented in Rust (`lean-bridge`) calling `sha2::Sha512::digest`. -/
@[extern "lean_sha512"]
opaque hash (data : @& ByteArray) : ByteArray

/-! ## `sol_sha512` syscall

Same `SliceDesc`-list ABI as `sol_sha256` / `sol_keccak256`, only the
output is 64 bytes. Cost mirrors agave's `sha256_base_cost` (the same
table entry covers all four hash families). -/

/-- Same per-slice CU as sha256: `base (85)` + sum over slices of
    `max(10, len/2)`. See `Sha256.cu` for the agave reference. -/
@[simp] def cu (s : State) : Nat := 85 + hashSliceCost s.mem s.regs.r1 s.regs.r2

@[simp] def exec (s : State) : State :=
  let digest := hash (readSlices s.mem s.regs.r1 s.regs.r2)
  { s with regs := s.regs.set .r0 0
           mem  := writeBytes s.mem s.regs.r3 64 digest }

end Sha512
end SVM.SBPF
