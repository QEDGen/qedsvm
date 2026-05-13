/-
  BLS12-381 elliptic-curve operations.

  Backed by `rust-bridge` calling the `solana-bls12-381-syscall = 0.1.0`
  crate — the same crate agave's `SyscallCurveDecompress` and
  `SyscallCurvePairingMap` arms use. Pinned to agave's master.

  Used by zk-rollup bridges, Ethereum-style ZK verifiers, and any
  Solana program that needs BLS pairings (e.g., aggregate signature
  verification).

  Wired to `.sol_curve_decompress` and `.sol_curve_pairing_map` in
  `Execute.lean`. Note: these two syscalls are dispatched on `curve_id`
  in the BLS12-381 ID space (`4..=6 | 0x80`), distinct from the
  curve25519 IDs (`0..1`). Earlier sessions discovered that despite
  the `sol_curve_*` naming these syscalls are BLS12-381 only.
-/

namespace Svm.SBPF
namespace Bls12_381

/-! ## Curve identifiers (Solana ABI, from `agave/syscalls`'s
    `bls12_381_curve_id` module). The high bit (`0x80`) selects BE;
    clearing it selects LE. -/

def BLS12_381_LE    : Nat := 4
def BLS12_381_BE    : Nat := 4 ||| 0x80   -- 0x84
def BLS12_381_G1_LE : Nat := 5
def BLS12_381_G1_BE : Nat := 5 ||| 0x80   -- 0x85
def BLS12_381_G2_LE : Nat := 6
def BLS12_381_G2_BE : Nat := 6 ||| 0x80   -- 0x86

/-! ## Endianness flag passed to the bridge: `0` = BE, `1` = LE. -/

/-- Decompress a 48-byte G1 compressed point to a 96-byte
    uncompressed (`x || y`) representation. Returns `none` on
    malformed input, point not on G1, or bad endianness byte. -/
@[extern "lean_bls12_381_g1_decompress"]
opaque g1Decompress (input : @& ByteArray) (endianness : UInt8) : Option ByteArray

/-- Decompress a 96-byte G2 compressed point to a 192-byte
    uncompressed representation. Same error semantics as G1. -/
@[extern "lean_bls12_381_g2_decompress"]
opaque g2Decompress (input : @& ByteArray) (endianness : UInt8) : Option ByteArray

/-- Batch pairing: given `n` G1 points (concatenated, 96n bytes) and
    `n` G2 points (concatenated, 192n bytes), compute the product of
    pairings `e(P_1, Q_1) · e(P_2, Q_2) · … · e(P_n, Q_n)` in the
    target group, returning the 576-byte Gt element.

    Returns `none` on n = 0, n > 8 (agave's `MAX_PAIRING_LENGTH`),
    mismatched buffer sizes, any malformed point, or bad endianness. -/
@[extern "lean_bls12_381_pairing_map"]
opaque pairingMap (g1Points g2Points : @& ByteArray) (n : UInt64) (endianness : UInt8)
    : Option ByteArray

end Bls12_381
end Svm.SBPF
