/-
  alt_bn128 (BN254) elliptic-curve operations.

  Backed by `rust-bridge` calling `solana-bn254 = 3.2.1` — agave's
  master pin. Used for Ethereum-precompile parity (BN254 group ops
  and pairing live at Ethereum precompiles 0x06–0x08 since EIP-196 /
  EIP-197) and for ZK verifiers that target the BN254 curve.

  Operations are identified by a u64 `op_id` that encodes both the
  operation (ADD/MUL/PAIRING × G1/G2) and the endianness (high bit
  `0x80` = little-endian). See `LE_FLAG`.

  Wired to `.sol_alt_bn128_group_op` and `.sol_alt_bn128_compression`
  in `Execute.lean`.
-/

namespace Svm.SBPF
namespace AltBn128

/-! ## Endianness flag

`op_id | LE_FLAG` selects little-endian; bare `op_id` selects
big-endian. -/
def LE_FLAG : Nat := 0x80

/-! ## Group operations (`sol_alt_bn128_group_op`) -/
def ALT_BN128_G1_ADD_BE   : Nat := 0
def ALT_BN128_G1_ADD_LE   : Nat := 0 ||| LE_FLAG
def ALT_BN128_G1_MUL_BE   : Nat := 2
def ALT_BN128_G1_MUL_LE   : Nat := 2 ||| LE_FLAG
def ALT_BN128_PAIRING_BE  : Nat := 3
def ALT_BN128_PAIRING_LE  : Nat := 3 ||| LE_FLAG
def ALT_BN128_G2_ADD_BE   : Nat := 4
def ALT_BN128_G2_ADD_LE   : Nat := 4 ||| LE_FLAG
def ALT_BN128_G2_MUL_BE   : Nat := 6
def ALT_BN128_G2_MUL_LE   : Nat := 6 ||| LE_FLAG

/-! ## Compression operations (`sol_alt_bn128_compression`) -/
def ALT_BN128_G1_COMPRESS_BE   : Nat := 0
def ALT_BN128_G1_COMPRESS_LE   : Nat := 0 ||| LE_FLAG
def ALT_BN128_G1_DECOMPRESS_BE : Nat := 1
def ALT_BN128_G1_DECOMPRESS_LE : Nat := 1 ||| LE_FLAG
def ALT_BN128_G2_COMPRESS_BE   : Nat := 2
def ALT_BN128_G2_COMPRESS_LE   : Nat := 2 ||| LE_FLAG
def ALT_BN128_G2_DECOMPRESS_BE : Nat := 3
def ALT_BN128_G2_DECOMPRESS_LE : Nat := 3 ||| LE_FLAG

/-- Perform a BN254 group operation. The `opId` byte selects both the
    operation (ADD/MUL/PAIRING on G1 or G2) and the endianness.
    Input size depends on the op:
    - G1 ADD: 128 bytes  (two 64-byte G1 points)
    - G1 MUL: 96 bytes   (64-byte G1 point + 32-byte scalar)
    - G2 ADD: 256 bytes  (two 128-byte G2 points)
    - G2 MUL: 160 bytes  (128-byte G2 point + 32-byte scalar)
    - PAIRING: 192n bytes (n × (G1, G2) pair, n ≥ 1)

    Output size:
    - G1 ops: 64 bytes
    - G2 ops: 128 bytes
    - PAIRING: 32 bytes (1 = pairing identity, 0 otherwise)

    Returns `none` on invalid op_id, malformed input, off-curve point,
    or any internal error. -/
@[extern "lean_alt_bn128_group_op"]
opaque groupOp (opId : UInt64) (input : @& ByteArray) : Option ByteArray

/-- Perform a BN254 compression/decompression operation.
    Input sizes:
    - G1 COMPRESS:   64 bytes  → 32 bytes
    - G1 DECOMPRESS: 32 bytes  → 64 bytes
    - G2 COMPRESS:   128 bytes → 64 bytes
    - G2 DECOMPRESS: 64 bytes  → 128 bytes

    Returns `none` on invalid op_id, malformed input, or any error. -/
@[extern "lean_alt_bn128_compression"]
opaque compression (opId : UInt64) (input : @& ByteArray) : Option ByteArray

end AltBn128
end Svm.SBPF
