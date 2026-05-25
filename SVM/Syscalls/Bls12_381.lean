/-
  BLS12-381 elliptic-curve operations.

  Backed by `lean-bridge` calling the `solana-bls12-381-syscall = 0.1.0`
  crate — the same crate agave's `SyscallCurveDecompress` and
  `SyscallCurvePairingMap` arms use. Pinned to agave's master.

  Used by zk-rollup bridges, Ethereum-style ZK verifiers, and any
  Solana program that needs BLS pairings (e.g., aggregate signature
  verification).

  Wired to `.sol_curve_decompress` and `.sol_curve_pairing_map` via
  `Bls12_381.execDecompress` and `Bls12_381.execPairing` below. Note:
  these two syscalls are dispatched on `curve_id` in the BLS12-381 ID
  space (`4..=6 | 0x80`), distinct from the curve25519 IDs (`0..1`).
  Earlier sessions discovered that despite the `sol_curve_*` naming
  these syscalls are BLS12-381 only.
-/

import SVM.SBPF.Machine

namespace SVM.SBPF
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

/-! ## Syscall bindings -/

/-- `sol_curve_decompress` CU charge. Mirrors agave's BLS12-381
    `g1_decompress` cost. -/
def cuDecompress : Nat := 2_100
/-- `sol_curve_pairing_map` CU charge. Mirrors agave's
    `bls12_381_one_pair`; real cost scales with `n`. -/
def cuPairing    : Nat := 25_445

/-- Execute `sol_curve_decompress`. BLS12-381 only.
    ABI: r1 = curve_id (G1_LE/G1_BE/G2_LE/G2_BE), r2 = compressed in,
    r3 = uncompressed out. r0 = 0/1 (incl. unsupported curve_id). -/
@[simp] def execDecompress (s : State) : State :=
  let curveId := s.regs.r1
  let result : Option ByteArray :=
    if curveId = BLS12_381_G1_LE then g1Decompress (readBytes s.mem s.regs.r2 48) 1
    else if curveId = BLS12_381_G1_BE then g1Decompress (readBytes s.mem s.regs.r2 48) 0
    else if curveId = BLS12_381_G2_LE then g2Decompress (readBytes s.mem s.regs.r2 96) 1
    else if curveId = BLS12_381_G2_BE then g2Decompress (readBytes s.mem s.regs.r2 96) 0
    else none
  let outputSize : Nat :=
    if curveId = BLS12_381_G1_LE ∨ curveId = BLS12_381_G1_BE then 96
    else if curveId = BLS12_381_G2_LE ∨ curveId = BLS12_381_G2_BE then 192
    else 0
  commitOptional s s.regs.r3 outputSize result

/-- Execute `sol_curve_pairing_map`. BLS12-381 only.
    ABI: r1 = curve_id (BLS12_381_LE/BE), r2 = n (1..=8), r3 = G1 ptr,
    r4 = G2 ptr, r5 = `*mut PodGtElement` (576 bytes). r0 = 0/1. -/
@[simp] def execPairing (s : State) : State :=
  let curveId := s.regs.r1
  let nPairs  := s.regs.r2
  let g1B := readBytes s.mem s.regs.r3 (96 * nPairs)
  let g2B := readBytes s.mem s.regs.r4 (192 * nPairs)
  let result : Option ByteArray :=
    if curveId = BLS12_381_LE then pairingMap g1B g2B nPairs.toUInt64 1
    else if curveId = BLS12_381_BE then pairingMap g1B g2B nPairs.toUInt64 0
    else none
  commitOptional s s.regs.r5 576 result

end Bls12_381
end SVM.SBPF
