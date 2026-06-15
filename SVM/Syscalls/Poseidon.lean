/-
  Poseidon hash (BN254, x^5 S-box). Backed by `lean-bridge` calling
  `light-poseidon = 0.4.0` + `ark-bn254 = 0.5.0` — the exact crates agave's
  `solana-poseidon` 4.0 uses. Wired to `.sol_poseidon` via `Poseidon.exec`.
-/

import SVM.SBPF.Machine

namespace SVM.SBPF
namespace Poseidon

/-- Solana ABI parameter selector. Only Bn254X5 is currently defined. -/
def BN254_X5 : Nat := 0

/-- Solana ABI endianness selector. -/
def BIG_ENDIAN    : Nat := 0
def LITTLE_ENDIAN : Nat := 1

/-- Poseidon hash of `n` 32-byte field elements concatenated in `inputs`.
    `parameters` = curve (0 = Bn254X5), `endianness` = 0 BE / 1 LE.
    `some <32-byte digest>` on success, `none` on: n=0 or n>12, parameters≠0,
    endianness>1, `inputs.size ≠ 32*n`, or any input ≥ BN254 modulus.
    Implemented in Rust (`lean-bridge`). -/
@[extern "lean_poseidon"]
opaque hash (parameters endianness : UInt8) (inputs : @& ByteArray) (n : UInt64)
    : Option ByteArray

/-! ## `sol_poseidon` syscall

ABI: r1 = parameters, r2 = endianness, r3 = `*const [VmSlice; n]`,
r4 = n (1..=12), r5 = `*mut [u8; 32]`. r0 = 0 success / 1 failure. -/

/-- Agave's quadratic poseidon cost `(61*n + 542) * n`, n = slice count (r4,
    1..=12). Source: `blueshift/sbpf/crates/runtime/src/config.rs:120-121`. -/
@[simp] def cu (s : State) : Nat :=
  let n := s.regs.r4
  (61 * n + 542) * n

/-- H6: full region envelope via `guardedCommit` — output `[r5,32)` first, then
    the `r3` descriptor array (`r4` × 16) and each input slice; `commitOptional`
    handles poseidon's some/none (r0:=0 write / r0:=1). -/
@[simp] def exec (s : State) : State :=
  s.guardedCommit s.regs.r5 32 s.regs.r3 s.regs.r4
    (hash s.regs.r1.toUInt8 s.regs.r2.toUInt8
          (readSlices s.mem s.regs.r3 s.regs.r4)
          s.regs.r4.toUInt64)

end Poseidon
end SVM.SBPF
