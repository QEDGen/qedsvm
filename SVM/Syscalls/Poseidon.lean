/-
  Poseidon hash (BN254 curve, x^5 S-box).

  Backed by `lean-bridge` calling `light-poseidon = 0.4.0` with
  `ark-bn254 = 0.5.0` — the exact crates agave's `solana-poseidon`
  4.0 uses internally. Used by zk-friendly applications on Solana
  (privacy-preserving programs, ZK proof verification).

  Wired to `.sol_poseidon` via `Poseidon.exec` below.
-/

import SVM.SBPF.Machine

namespace SVM.SBPF
namespace Poseidon

/-- Solana ABI parameter selector. Only Bn254X5 is currently defined. -/
def BN254_X5 : Nat := 0

/-- Solana ABI endianness selector. -/
def BIG_ENDIAN    : Nat := 0
def LITTLE_ENDIAN : Nat := 1

/-- Compute the Poseidon hash of `n` 32-byte field-element inputs
    concatenated in `inputs`. `parameters` selects the curve (must be
    0 = Bn254X5), `endianness` selects byte order (0 = BE, 1 = LE) for
    both input interpretation and output bytes.

    Returns `some <32-byte digest>` on success or `none` on:
    - n = 0 or n > 12 (agave's `InvalidLength`)
    - `parameters` ≠ 0
    - `endianness` > 1
    - `inputs.size ≠ 32 * n` (input padding violation)
    - any input is not a canonical field element (≥ BN254 modulus)

    Implemented in Rust (`lean-bridge`). -/
@[extern "lean_poseidon"]
opaque hash (parameters endianness : UInt8) (inputs : @& ByteArray) (n : UInt64)
    : Option ByteArray

/-! ## `sol_poseidon` syscall

ABI: r1 = parameters, r2 = endianness, r3 = `*const [VmSlice; n]`,
r4 = n (1..=12), r5 = `*mut [u8; 32]`. r0 = 0 success / 1 failure. -/

/-- Agave's poseidon cost is input-count-quadratic:
    `(coefficient_a (61) * n + coefficient_c (542)) * n` where `n` is
    the input slice count (`r4`, in 1..=12). For n=1 this evaluates to
    603. Source: `blueshift/sbpf/crates/runtime/src/config.rs:120-121`. -/
@[simp] def cu (s : State) : Nat :=
  let n := s.regs.r4
  (61 * n + 542) * n

/-- H6 (stage 3a): route the fixed 32-byte output `[r5, r5+32)` through
    `guardWrite` (agave's `translate_slice_mut`, checked before hashing) —
    a non-writable / out-of-region output traps even on the failure path,
    since agave translates the output buffer before computing. The inner
    `commitOptional` still handles the some/none (r0:=0 write / r0:=1). -/
@[simp] def exec (s : State) : State :=
  let result := hash s.regs.r1.toUInt8 s.regs.r2.toUInt8
                     (readSlices s.mem s.regs.r3 s.regs.r4)
                     s.regs.r4.toUInt64
  s.guardWrite s.regs.r5 32 fun s =>
    commitOptional s s.regs.r5 32 result

end Poseidon
end SVM.SBPF
