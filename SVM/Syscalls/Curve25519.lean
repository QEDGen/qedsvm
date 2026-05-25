/-
  curve25519 — point validation (Edwards / Ristretto).

  Calls into `lean-bridge` which uses `curve25519-dalek = "4.1.3"`
  (agave's master pin), via the same logic
  `solana-curve25519::{edwards,ristretto}::validate_*` uses:
  `CompressedX::from_slice(b).decompress().is_some()`.

  This is the first slice of the five-syscall curve25519 family. The
  remaining four (`sol_curve_group_op`, `sol_curve_multiscalar_mul`,
  `sol_curve_decompress`, `sol_curve_pairing_map`) follow the same
  bridge pattern.

  We deliberately do **not** ship a pure-Lean curve25519 spec.
  Verification of the field/group arithmetic is downstream work.

  Wired to `.sol_curve_validate_point`, `.sol_curve_group_op`, and
  `.sol_curve_multiscalar_mul` via the three `exec*` functions below.
-/

import SVM.SBPF.Machine

namespace SVM.SBPF
namespace Curve25519

/-- Solana ABI curve identifiers, copied from
    `solana-curve25519::curve_syscall_traits`. -/
def CURVE25519_EDWARDS   : Nat := 0
def CURVE25519_RISTRETTO : Nat := 1

/-- Solana ABI group-operation identifiers for `sol_curve_group_op`. -/
def OP_ADD : Nat := 0
def OP_SUB : Nat := 1
def OP_MUL : Nat := 2

/-- True iff `point` (32 bytes) is a valid compressed Edwards point on
    the ed25519 curve.

    Returns `false` for length ≠ 32, decompression failures (bad
    encoding, point not on curve), or any internal error.

    Implemented in Rust (`lean-bridge`) →
    `curve25519-dalek::edwards::CompressedEdwardsY`. Treated as
    opaque to the kernel; `native_decide` reduces it via
    `ofReduceBool`. -/
@[extern "lean_curve_validate_edwards"]
opaque validateEdwards (point : @& ByteArray) : Bool

/-- True iff `point` (32 bytes) is a valid compressed Ristretto point.

    Ristretto encoding rules are a strict subset of the Edwards
    encoding — many valid Edwards points are *not* valid Ristretto
    points, so the two validators do not agree on arbitrary inputs.

    Implemented in Rust (`lean-bridge`) →
    `curve25519-dalek::ristretto::CompressedRistretto`. -/
@[extern "lean_curve_validate_ristretto"]
opaque validateRistretto (point : @& ByteArray) : Bool

/-! ## Group operations (`sol_curve_group_op`)

Each takes two 32-byte ByteArrays and returns `some <32-byte
compressed point>` on success or `none` on any decode/decompression
failure (or non-canonical scalar for `MUL`). The operations exactly
mirror `solana-curve25519`'s `add_*` / `subtract_*` / `multiply_*`
free functions, which in turn delegate to `curve25519-dalek`'s
operator overloads.

For `MUL`: the first argument is a canonical scalar (32 bytes LE,
strictly < the curve25519 subgroup order `ℓ`); the second is a
compressed point on the curve. `Scalar::from_canonical_bytes`
rejects scalars ≥ `ℓ`, matching `PodScalar -> Scalar`. -/

@[extern "lean_curve_edwards_add"]
opaque edwardsAdd (left right : @& ByteArray) : Option ByteArray
@[extern "lean_curve_edwards_sub"]
opaque edwardsSub (left right : @& ByteArray) : Option ByteArray
@[extern "lean_curve_edwards_mul"]
opaque edwardsMul (scalar point : @& ByteArray) : Option ByteArray

@[extern "lean_curve_ristretto_add"]
opaque ristrettoAdd (left right : @& ByteArray) : Option ByteArray
@[extern "lean_curve_ristretto_sub"]
opaque ristrettoSub (left right : @& ByteArray) : Option ByteArray
@[extern "lean_curve_ristretto_mul"]
opaque ristrettoMul (scalar point : @& ByteArray) : Option ByteArray

/-! ## Multiscalar multiplication (`sol_curve_multiscalar_mul`)

Variable-length input: scalars (32n bytes) and points (32n bytes) are
each a concatenated `n`-element buffer. The Lean caller is responsible
for pre-concatenating them; this maps naturally to
`readBytes mem ptr (32 * n)`.

Returns `some <32-byte compressed result>` on success, `none` if any
scalar is non-canonical, any point fails decompression, or `n = 0`.
Agave caps `n ≤ 512` at the syscall boundary; we enforce that in the
`.sol_curve_multiscalar_mul` arm rather than here. -/

@[extern "lean_curve_edwards_msm"]
opaque edwardsMSM   (scalars points : @& ByteArray) : Option ByteArray
@[extern "lean_curve_ristretto_msm"]
opaque ristrettoMSM (scalars points : @& ByteArray) : Option ByteArray

/-! ## Syscall bindings -/

/-! ## CU charges (per agave's `SVMTransactionExecutionCost::default()`,
mirrored at `blueshift/sbpf/crates/runtime/src/config.rs:96-107`).

Each cost depends on the curve_id in `r1` (and for `group_op` also the
op_id in `r2`); unknown variants charge the cheapest path so the
caller still pays *something*. -/

/-- `sol_curve_validate_point`: 159 (edwards) / 169 (ristretto). -/
@[simp] def cuValidatePoint (s : State) : Nat :=
  if s.regs.r1 = CURVE25519_EDWARDS then 159
  else if s.regs.r1 = CURVE25519_RISTRETTO then 169
  else 159

/-- `sol_curve_group_op`. Per-curve × per-op: edwards add=473/sub=475/mul=2177,
    ristretto add=521/sub=519/mul=2208. -/
@[simp] def cuGroupOp (s : State) : Nat :=
  if s.regs.r1 = CURVE25519_EDWARDS then
    if s.regs.r2 = OP_ADD then 473
    else if s.regs.r2 = OP_SUB then 475
    else if s.regs.r2 = OP_MUL then 2_177
    else 473
  else if s.regs.r1 = CURVE25519_RISTRETTO then
    if s.regs.r2 = OP_ADD then 521
    else if s.regs.r2 = OP_SUB then 519
    else if s.regs.r2 = OP_MUL then 2_208
    else 521
  else 473

/-- `sol_curve_multiscalar_mul`. Base + n × incremental:
    edwards = 2273 + n·758, ristretto = 2303 + n·788. `n` is the
    point count in `r4`. -/
@[simp] def cuMSM (s : State) : Nat :=
  let n := s.regs.r4
  if s.regs.r1 = CURVE25519_EDWARDS then 2_273 + n * 758
  else if s.regs.r1 = CURVE25519_RISTRETTO then 2_303 + n * 788
  else 2_273

/-- Execute `sol_curve_validate_point`.
    ABI: r1 = curve_id, r2 = `*const [u8; 32]` point.
    r0 = 0 valid / 1 invalid / 2 unsupported curve_id. -/
@[simp] def execValidate (s : State) : State :=
  let curveId  := s.regs.r1
  let pointA   := s.regs.r2
  let pointB   := readBytes s.mem pointA 32
  let errCode  : Nat :=
    if curveId = CURVE25519_EDWARDS then
      if validateEdwards pointB then 0 else 1
    else if curveId = CURVE25519_RISTRETTO then
      if validateRistretto pointB then 0 else 1
    else 2
  { s with regs := s.regs.set .r0 errCode }

/-- Execute `sol_curve_group_op`.
    ABI: r1 = curve_id, r2 = op_id (0=ADD/1=SUB/2=MUL),
    r3 = left ptr, r4 = right ptr, r5 = out. r0 = 0/1. -/
@[simp] def execGroupOp (s : State) : State :=
  let curveId := s.regs.r1
  let opId    := s.regs.r2
  let leftB   := readBytes s.mem s.regs.r3 32
  let rightB  := readBytes s.mem s.regs.r4 32
  let result : Option ByteArray :=
    if curveId = CURVE25519_EDWARDS then
      if opId = OP_ADD then edwardsAdd leftB rightB
      else if opId = OP_SUB then edwardsSub leftB rightB
      else if opId = OP_MUL then edwardsMul leftB rightB
      else none
    else if curveId = CURVE25519_RISTRETTO then
      if opId = OP_ADD then ristrettoAdd leftB rightB
      else if opId = OP_SUB then ristrettoSub leftB rightB
      else if opId = OP_MUL then ristrettoMul leftB rightB
      else none
    else none
  commitOptional s s.regs.r5 32 result

/-- Execute `sol_curve_multiscalar_mul`.
    ABI: r1 = curve_id, r2 = `*const PodScalar*`,
    r3 = `*const PodPoint*`, r4 = n (≤ 512), r5 = out. r0 = 0/1. -/
@[simp] def execMSM (s : State) : State :=
  let curveId   := s.regs.r1
  let pointsLen := s.regs.r4
  let scalarsB  := readBytes s.mem s.regs.r2 (32 * pointsLen)
  let pointsB   := readBytes s.mem s.regs.r3 (32 * pointsLen)
  let result : Option ByteArray :=
    if pointsLen = 0 ∨ pointsLen > 512 then none
    else if curveId = CURVE25519_EDWARDS then edwardsMSM scalarsB pointsB
    else if curveId = CURVE25519_RISTRETTO then ristrettoMSM scalarsB pointsB
    else none
  commitOptional s s.regs.r5 32 result

end Curve25519
end SVM.SBPF
