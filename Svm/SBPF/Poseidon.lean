/-
  Poseidon hash (BN254 curve, x^5 S-box).

  Backed by `rust-bridge` calling `light-poseidon = 0.4.0` with
  `ark-bn254 = 0.5.0` — the exact crates agave's `solana-poseidon`
  4.0 uses internally. Used by zk-friendly applications on Solana
  (privacy-preserving programs, ZK proof verification).

  Wired to `.sol_poseidon` in `Execute.lean`.
-/

namespace Svm.SBPF
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

    Implemented in Rust (`rust-bridge`). -/
@[extern "lean_poseidon"]
opaque hash (parameters endianness : UInt8) (inputs : @& ByteArray) (n : UInt64)
    : Option ByteArray

end Poseidon
end Svm.SBPF
