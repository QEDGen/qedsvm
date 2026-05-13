/-
  curve25519 — point validation (Edwards / Ristretto).

  Calls into `rust-bridge` which uses `curve25519-dalek = "4.1.3"`
  (agave's master pin), via the same logic
  `solana-curve25519::{edwards,ristretto}::validate_*` uses:
  `CompressedX::from_slice(b).decompress().is_some()`.

  This is the first slice of the five-syscall curve25519 family. The
  remaining four (`sol_curve_group_op`, `sol_curve_multiscalar_mul`,
  `sol_curve_decompress`, `sol_curve_pairing_map`) follow the same
  bridge pattern.

  We deliberately do **not** ship a pure-Lean curve25519 spec.
  Verification of the field/group arithmetic is downstream work.

  Wired to `.sol_curve_validate_point` in `Execute.lean`.
-/

namespace Svm.SBPF
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

    Implemented in Rust (`rust-bridge`) →
    `curve25519-dalek::edwards::CompressedEdwardsY`. Treated as
    opaque to the kernel; `native_decide` reduces it via
    `ofReduceBool`. -/
@[extern "lean_curve_validate_edwards"]
opaque validateEdwards (point : @& ByteArray) : Bool

/-- True iff `point` (32 bytes) is a valid compressed Ristretto point.

    Ristretto encoding rules are a strict subset of the Edwards
    encoding — many valid Edwards points are *not* valid Ristretto
    points, so the two validators do not agree on arbitrary inputs.

    Implemented in Rust (`rust-bridge`) →
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

end Curve25519
end Svm.SBPF
