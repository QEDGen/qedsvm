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
  via `AltBn128.execGroupOp` and `AltBn128.execCompression` below.
-/

import Svm.SBPF.Machine

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

/-! ## Syscall bindings -/

/-- `sol_alt_bn128_group_op` CU charge. Mirrors agave's
    `bn128_g1_addition` baseline; real cost varies per op. -/
def cuGroupOp     : Nat := 334
/-- `sol_alt_bn128_compression` CU charge (g1_compress baseline). -/
def cuCompression : Nat := 30

/-- Output buffer size for a given group-op `op_id`. -/
@[simp] def groupOpOutSize (opId : Nat) : Nat :=
  if opId = ALT_BN128_PAIRING_BE ∨ opId = ALT_BN128_PAIRING_LE then 32
  else if opId = ALT_BN128_G2_ADD_BE ∨ opId = ALT_BN128_G2_ADD_LE
       ∨ opId = ALT_BN128_G2_MUL_BE ∨ opId = ALT_BN128_G2_MUL_LE then 128
  else if opId = ALT_BN128_G1_ADD_BE ∨ opId = ALT_BN128_G1_ADD_LE
       ∨ opId = ALT_BN128_G1_MUL_BE ∨ opId = ALT_BN128_G1_MUL_LE then 64
  else 0

/-- Output buffer size for a given compression `op_id`. -/
@[simp] def compressionOutSize (opId : Nat) : Nat :=
  if opId = ALT_BN128_G1_COMPRESS_BE ∨ opId = ALT_BN128_G1_COMPRESS_LE then 32
  else if opId = ALT_BN128_G1_DECOMPRESS_BE ∨ opId = ALT_BN128_G1_DECOMPRESS_LE then 64
  else if opId = ALT_BN128_G2_COMPRESS_BE ∨ opId = ALT_BN128_G2_COMPRESS_LE then 64
  else if opId = ALT_BN128_G2_DECOMPRESS_BE ∨ opId = ALT_BN128_G2_DECOMPRESS_LE then 128
  else 0

/-- Execute `sol_alt_bn128_group_op`.
    ABI: r1 = op_id, r2 = input, r3 = input_size, r4 = out. r0 = 0/1. -/
@[simp] def execGroupOp (s : State) : State :=
  let opId   := s.regs.r1
  let inputB := readBytes s.mem s.regs.r2 s.regs.r3
  let result := groupOp opId.toUInt64 inputB
  commitOptional s s.regs.r4 (groupOpOutSize opId) result

/-- Execute `sol_alt_bn128_compression`. Same ABI shape as `execGroupOp`. -/
@[simp] def execCompression (s : State) : State :=
  let opId   := s.regs.r1
  let inputB := readBytes s.mem s.regs.r2 s.regs.r3
  let result := compression opId.toUInt64 inputB
  commitOptional s s.regs.r4 (compressionOutSize opId) result

end AltBn128
end Svm.SBPF
