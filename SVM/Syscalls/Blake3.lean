/-
  BLAKE3 (default hashing mode, 32-byte output).

  Backed by `lean-bridge` calling `blake3 = 1.8.5` (agave's master pin).
  The hash is opaque at proof time; `native_decide` reduces it via
  `ofReduceBool`. No pure-Lean spec: verifying BLAKE3's structure is
  downstream work. Wired to `.sol_blake3`.
-/

import SVM.SBPF.Machine

namespace SVM.SBPF
namespace Blake3

/-- BLAKE3 of `data`, returning the 32-byte digest (Rust `blake3::hash`). -/
@[extern "lean_blake3"]
opaque hash (data : @& ByteArray) : ByteArray

/-! ## `sol_blake3` syscall

Same `SliceDesc`-list ABI and base cost as `sol_sha256`. -/

@[simp] def cu (s : State) : Nat := 85 + hashSliceCost s.mem s.regs.r1 s.regs.r2

/-- H6: region envelope via `State.hashWrite` — output `[r3, r3+32)` checked
    first, then the `r1` descriptor array (`r2` × 16 bytes) and each slice. -/
@[simp] def exec (s : State) : State :=
  s.hashWrite s.regs.r3 32 s.regs.r1 s.regs.r2
    (hash (readSlices s.mem s.regs.r1 s.regs.r2))

end Blake3
end SVM.SBPF
