/-
  Big-integer modular exponentiation: `base^exponent mod modulus`.

  Backed by `rust-bridge` calling `solana-big-mod-exp = 3.0.0`
  (agave's master pin). Internally uses `num-bigint`'s `modpow`.

  Inputs and output are big-endian byte strings. Output is padded
  with leading zeros to exactly `modulus.size` bytes.

  Wired to `.sol_big_mod_exp` via `BigModExp.exec` below.
-/

import Svm.SBPF.Machine

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

/-! ## `sol_big_mod_exp` syscall

ABI: r1 = `*const BigModExpParams` (48 bytes — 6 × u64 LE:
`{ base, base_len, exponent, exponent_len, modulus, modulus_len }`),
r2 = `*mut [u8; modulus_len]` output. r0 = 0/1 (1 iff any len > 512). -/

/-- `big_modular_exponentiation_cost` from agave's
    `SVMTransactionExecutionCost::default()` (mirrored at
    `blueshift/sbpf/crates/runtime/src/config.rs:119`). Agave actually
    consumes a more complex `cost.saturating_mul(n)` per modulus byte
    inside the syscall; this flat value is a soft approximation until
    a fixture forces the input-scaled form. -/
def cu : Nat := 33

@[simp] def exec (s : State) : State :=
  let paramsA := s.regs.r1
  let basePtr := Memory.readU64 s.mem  paramsA
  let baseLen := Memory.readU64 s.mem (paramsA + 8)
  let expPtr  := Memory.readU64 s.mem (paramsA + 16)
  let expLen  := Memory.readU64 s.mem (paramsA + 24)
  let modPtr  := Memory.readU64 s.mem (paramsA + 32)
  let modLen  := Memory.readU64 s.mem (paramsA + 40)
  let valid := baseLen ≤ MAX_INPUT_LEN ∧ expLen ≤ MAX_INPUT_LEN
            ∧ modLen ≤ MAX_INPUT_LEN
  let result : Option ByteArray :=
    if valid then
      some (modpow (readBytes s.mem basePtr baseLen)
                   (readBytes s.mem expPtr  expLen)
                   (readBytes s.mem modPtr  modLen))
    else none
  commitOptional s s.regs.r2 modLen result

end BigModExp
end Svm.SBPF
