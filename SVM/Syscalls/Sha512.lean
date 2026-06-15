/-
  SHA-512 (64-byte output): backed by `lean-bridge` calling `sha2 = 0.10.8`, the
  same crate agave's `solana-sha512-hasher` wraps. Opaque at proof time;
  `native_decide` reduces it. Wired to `.sol_sha512` via `Sha512.exec`.
-/

import SVM.SBPF.Machine

namespace SVM.SBPF
namespace Sha512

/-- SHA-512 of `data` (64-byte digest). Rust `sha2::Sha512::digest` via lean-bridge. -/
@[extern "lean_sha512"]
opaque hash (data : @& ByteArray) : ByteArray

/-! ## `sol_sha512` syscall

Same `SliceDesc`-list ABI as `sol_sha256`, output 64 bytes; same cost table entry. -/

/-- Same per-slice CU as sha256: `85 + Σ max(10, len/2)`. See `Sha256.cu`. -/
@[simp] def cu (s : State) : Nat := 85 + hashSliceCost s.mem s.regs.r1 s.regs.r2

/-- H6: full region envelope via `hashWrite` — output `[r3,64)` first, then the
    `r1` descriptor array (`r2` × 16) and each input slice. -/
@[simp] def exec (s : State) : State :=
  s.hashWrite s.regs.r3 64 s.regs.r1 s.regs.r2
    (hash (readSlices s.mem s.regs.r1 s.regs.r2))

end Sha512
end SVM.SBPF
