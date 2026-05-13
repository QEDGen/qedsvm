/-
  Big-integer modular exponentiation: `base^exponent mod modulus`.

  Backed by `rust-bridge` calling `solana-big-mod-exp = 3.0.0`
  (agave's master pin). Internally uses `num-bigint`'s `modpow`.

  Inputs and output are big-endian byte strings. Output is padded
  with leading zeros to exactly `modulus.size` bytes.

  Wired to `.sol_big_mod_exp` in `Execute.lean`.
-/

namespace Svm.SBPF
namespace BigModExp

/-- Agave-enforced per-argument byte-length cap. -/
def MAX_INPUT_LEN : Nat := 512

/-- Compute `base^exponent mod modulus` over big-endian byte strings.
    The result is left-padded with zeros to `modulus.size` bytes.

    Edge cases (matching `num-bigint::BigUint::modpow`):
    - `modulus = 0` or `modulus = 1` → result is all zeros of size
      `modulus.size`.
    - `exponent = 0` → result is 1 (left-padded), unless modulus ≤ 1.

    Total allocation: `O(modulus.size)`. This function does NOT
    enforce the `MAX_INPUT_LEN` cap — the caller (the syscall arm)
    does. -/
@[extern "lean_big_mod_exp"]
opaque modpow (base exponent modulus : @& ByteArray) : ByteArray

end BigModExp
end Svm.SBPF
