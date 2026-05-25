/-
  BLAKE3 (default hashing mode, 32-byte output).

  Backed by `lean-bridge` calling the `blake3 = 1.8.5` crate — agave's
  master pin. The `opaque` Lean side treats the hash as a black box at
  proof time; `native_decide` reduces it via `ofReduceBool` (same
  axiom already in use elsewhere).

  We deliberately do **not** ship a pure-Lean spec here. Verification
  of BLAKE3's tree / compression structure is downstream work — its
  own project.

  Wired to the `.sol_blake3` syscall via `Blake3.exec` below.
-/

import SVM.SBPF.Machine

namespace SVM.SBPF
namespace Blake3

/-- BLAKE3 of `data`, returning the 32-byte digest.

    Implemented in Rust (`lean-bridge`) calling `blake3::hash`. -/
@[extern "lean_blake3"]
opaque hash (data : @& ByteArray) : ByteArray

/-! ## `sol_blake3` syscall

Same `SliceDesc`-list ABI and base cost as `sol_sha256`. -/

@[simp] def cu (s : State) : Nat := 85 + hashSliceCost s.mem s.regs.r1 s.regs.r2

@[simp] def exec (s : State) : State :=
  let digest := hash (readSlices s.mem s.regs.r1 s.regs.r2)
  { s with regs := s.regs.set .r0 0
           mem  := writeBytes s.mem s.regs.r3 32 digest }

end Blake3
end SVM.SBPF
