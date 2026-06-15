/-
  BLS12-381 elliptic-curve operations.

  Backed by `lean-bridge` calling `solana-bls12-381-syscall = 0.1.0` (the
  crate agave's `SyscallCurveDecompress`/`SyscallCurvePairingMap` use).
  Wired to `.sol_curve_decompress`/`.sol_curve_pairing_map`. NOTE: despite
  the `sol_curve_*` naming these dispatch on BLS12-381 curve_ids
  (`4..=6 | 0x80`), distinct from curve25519 (`0..1`) — BLS12-381 only.
-/

import SVM.SBPF.Machine

namespace SVM.SBPF
namespace Bls12_381

/-! ## Curve identifiers (Solana ABI, `bls12_381_curve_id`). High bit
    `0x80` = BE; cleared = LE. -/

def BLS12_381_LE    : Nat := 4
def BLS12_381_BE    : Nat := 4 ||| 0x80   -- 0x84
def BLS12_381_G1_LE : Nat := 5
def BLS12_381_G1_BE : Nat := 5 ||| 0x80   -- 0x85
def BLS12_381_G2_LE : Nat := 6
def BLS12_381_G2_BE : Nat := 6 ||| 0x80   -- 0x86

/-! ## Endianness flag passed to the bridge: `0` = BE, `1` = LE. -/

/-- Decompress a 48-byte G1 compressed point to 96-byte uncompressed
    (`x || y`). Returns `none` on malformed input, off-G1, or bad
    endianness byte. -/
@[extern "lean_bls12_381_g1_decompress"]
opaque g1Decompress (input : @& ByteArray) (endianness : UInt8) : Option ByteArray

/-- Decompress a 96-byte G2 compressed point to 192-byte uncompressed.
    Same error semantics as G1. -/
@[extern "lean_bls12_381_g2_decompress"]
opaque g2Decompress (input : @& ByteArray) (endianness : UInt8) : Option ByteArray

/-- Batch pairing: from `n` G1 points (96n bytes) and `n` G2 points
    (192n bytes), compute `∏ e(P_i, Q_i)`, returning the 576-byte Gt
    element. Returns `none` on n = 0, n > 8 (agave's `MAX_PAIRING_LENGTH`),
    mismatched buffer sizes, malformed point, or bad endianness. -/
@[extern "lean_bls12_381_pairing_map"]
opaque pairingMap (g1Points g2Points : @& ByteArray) (n : UInt64) (endianness : UInt8)
    : Option ByteArray

/-! ## Syscall bindings -/

/-- `sol_curve_decompress` CU; agave's `g1_decompress`. -/
def cuDecompress : Nat := 2_100
/-- `sol_curve_pairing_map` CU; agave's `bls12_381_one_pair` (real cost
    scales with `n`). -/
def cuPairing    : Nat := 25_445

/-- Execute `sol_curve_decompress`. BLS12-381 only.
    ABI: r1 = curve_id (G1_LE/G1_BE/G2_LE/G2_BE), r2 = compressed in,
    r3 = uncompressed out. r0 = 0/1 (incl. unsupported curve_id). -/
@[simp] def execDecompress (s : State) : State :=
  let curveId := s.regs.r1
  -- H6: compressed input (48 G1 / 96 G2, Load) then uncompressed output
  -- (96 / 192, Store). Unsupported curve_id → both sizes 0 (guards pass,
  -- zero-length never checked) and `commitOptional none` sets r0:=1.
  let inputSize : Nat :=
    if curveId = BLS12_381_G1_LE ∨ curveId = BLS12_381_G1_BE then 48
    else if curveId = BLS12_381_G2_LE ∨ curveId = BLS12_381_G2_BE then 96
    else 0
  let outputSize : Nat :=
    if curveId = BLS12_381_G1_LE ∨ curveId = BLS12_381_G1_BE then 96
    else if curveId = BLS12_381_G2_LE ∨ curveId = BLS12_381_G2_BE then 192
    else 0
  s.guardRead s.regs.r2 inputSize fun s =>
  s.guardWrite s.regs.r3 outputSize fun s =>
    let result : Option ByteArray :=
      if curveId = BLS12_381_G1_LE then g1Decompress (readBytes s.mem s.regs.r2 48) 1
      else if curveId = BLS12_381_G1_BE then g1Decompress (readBytes s.mem s.regs.r2 48) 0
      else if curveId = BLS12_381_G2_LE then g2Decompress (readBytes s.mem s.regs.r2 96) 1
      else if curveId = BLS12_381_G2_BE then g2Decompress (readBytes s.mem s.regs.r2 96) 0
      else none
    commitOptional s s.regs.r3 outputSize result

/-- Execute `sol_curve_pairing_map`. BLS12-381 only.
    ABI: r1 = curve_id (BLS12_381_LE/BE), r2 = n (1..=8), r3 = G1 ptr,
    r4 = G2 ptr, r5 = `*mut PodGtElement` (576 bytes). r0 = 0/1. -/
@[simp] def execPairing (s : State) : State :=
  let curveId := s.regs.r1
  let nPairs  := s.regs.r2
  -- H6: G1 `[r3, 96·n)` and G2 `[r4, 192·n)` (Load) then 576-byte Gt
  -- output `[r5,576)` (Store).
  s.guardRead s.regs.r3 (96 * nPairs) fun s =>
  s.guardRead s.regs.r4 (192 * nPairs) fun s =>
  s.guardWrite s.regs.r5 576 fun s =>
    let g1B := readBytes s.mem s.regs.r3 (96 * nPairs)
    let g2B := readBytes s.mem s.regs.r4 (192 * nPairs)
    let result : Option ByteArray :=
      if curveId = BLS12_381_LE then pairingMap g1B g2B nPairs.toUInt64 1
      else if curveId = BLS12_381_BE then pairingMap g1B g2B nPairs.toUInt64 0
      else none
    commitOptional s s.regs.r5 576 result

/-- H6: on a supported curve_id (G1_LE ⇒ 48-byte input), an out-of-region
    compressed input `[r2,48)` traps. -/
theorem execDecompress_faults_oob (s : State)
    (hcurve : s.regs.r1 = BLS12_381_G1_LE)
    (hoob : s.regions.containsRange s.regs.r2 48 = false) :
    (execDecompress s).vmError = some .accessViolation := by
  simp [execDecompress, hcurve, State.guardRead, hoob]

/-- H6: for an empty pairing (`n = 0`, input guards pass), an out-of-region
    576-byte Gt output `[r5,576)` traps. -/
theorem execPairing_faults_oob (s : State)
    (hn : s.regs.r2 = 0)
    (hoob : s.regions.containsWritable s.regs.r5 576 = false) :
    (execPairing s).vmError = some .accessViolation := by
  simp [execPairing, hn, State.guardRead, State.guardWrite, hoob]

end Bls12_381
end SVM.SBPF
