/-
  Keccak-256 (original Keccak with 0x01 padding, not FIPS-202 SHA-3's 0x06).

  Backed by `lean-bridge` calling `sha3 = 0.10.8`'s `Keccak256` (what
  agave's `solana-keccak-hasher` wraps). Opaque at proof time;
  `native_decide` reduces it via `ofReduceBool`. No pure-Lean spec:
  Keccak's properties are downstream work. Wired to `.sol_keccak256`.
-/

import SVM.SBPF.Machine

namespace SVM.SBPF
namespace Keccak256

/-- Keccak-256 of `data`, returning the 32-byte digest (Rust
    `sha3::Keccak256`, Solana variant: 0x01 padding, not SHA-3's 0x06). -/
@[extern "lean_keccak256"]
opaque hash (data : @& ByteArray) : ByteArray

/-! ## `sol_keccak256` syscall

Same `SliceDesc`-list ABI and base cost as `sol_sha256`. -/

@[simp] def cu (s : State) : Nat := 85 + hashSliceCost s.mem s.regs.r1 s.regs.r2

/-- H6: region envelope via `State.hashWrite` — output `[r3, r3+32)` checked
    first, then the `r1` descriptor array (`r2` × 16 bytes) and each slice. -/
@[simp] def exec (s : State) : State :=
  s.hashWrite s.regs.r3 32 s.regs.r1 s.regs.r2
    (hash (readSlices s.mem s.regs.r1 s.regs.r2))

end Keccak256
end SVM.SBPF
