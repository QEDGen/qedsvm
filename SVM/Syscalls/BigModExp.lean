/-
  Big-integer modular exponentiation: `base^exponent mod modulus`.

  Backed by `lean-bridge` calling `solana-big-mod-exp = 3.0.0`
  (agave's master pin). Internally uses `num-bigint`'s `modpow`.

  Inputs and output are big-endian byte strings. Output is padded
  with leading zeros to exactly `modulus.size` bytes.

  Wired to `.sol_big_mod_exp` via `BigModExp.exec` below.
-/

import SVM.SBPF.Machine

namespace SVM.SBPF
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

/-- `sol_big_mod_exp` CU, exact per agave-syscalls 4.0.0-rc.0
    (`src/lib.rs:2280-2295`): `syscall_base_cost +
    (input_len² / big_modular_exponentiation_cost_divisor +
    big_modular_exponentiation_base_cost)`, with
    `input_len = max(base_len, exponent_len, modulus_len)` and the
    `SVMTransactionExecutionCost::default()` constants (100, divisor 2,
    base 190 — `solana-program-runtime/src/execution_budget.rs:236,257,
    258`), i.e. `100 + (input_len² / 2 + 190)`. The `/2` is Nat-floored,
    matching agave's `checked_div`. Audit M9: the pre-fix flat `33` was a
    soft approximation; this is the input-scaled form. -/
def cu (s : State) : Nat :=
  let paramsA := s.regs.r1
  let baseLen := Memory.readU64 s.mem (paramsA + 8)
  let expLen  := Memory.readU64 s.mem (paramsA + 24)
  let modLen  := Memory.readU64 s.mem (paramsA + 40)
  let inputLen := max baseLen (max expLen modLen)
  100 + (inputLen * inputLen / 2 + 190)

@[simp] def exec (s : State) : State :=
  let paramsA := s.regs.r1
  let basePtr := Memory.readU64 s.mem  paramsA
  let baseLen := Memory.readU64 s.mem (paramsA + 8)
  let expPtr  := Memory.readU64 s.mem (paramsA + 16)
  let expLen  := Memory.readU64 s.mem (paramsA + 24)
  let modPtr  := Memory.readU64 s.mem (paramsA + 32)
  let modLen  := Memory.readU64 s.mem (paramsA + 40)
  -- Agave rejects any operand longer than 512 bytes with
  -- `SyscallError::InvalidLength` (an instruction abort), NOT an in-band
  -- error return. Fail closed. See docs/SOUNDNESS_AUDIT_* (M9).
  if baseLen ≤ MAX_INPUT_LEN ∧ expLen ≤ MAX_INPUT_LEN ∧ modLen ≤ MAX_INPUT_LEN then
    let result := modpow (readBytes s.mem basePtr baseLen)
                         (readBytes s.mem expPtr  expLen)
                         (readBytes s.mem modPtr  modLen)
    commitOptional s s.regs.r2 modLen (some result)
  else
    { s with exitCode := some ERR_INVALID_LENGTH, vmError := some .invalidLength }

end BigModExp
end SVM.SBPF
