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

end Curve25519
end Svm.SBPF
