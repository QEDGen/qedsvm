/-
  Big-integer modular exponentiation: `base^exponent mod modulus`.

  Backed by `lean-bridge` calling `solana-big-mod-exp = 3.0.0` (agave's
  master pin, `num-bigint::modpow`). Inputs/output are big-endian byte
  strings, output left-padded with zeros to `modulus.size`. Wired to
  `.sol_big_mod_exp`.
-/

import SVM.SBPF.Machine

namespace SVM.SBPF
namespace BigModExp

/-- Agave-enforced per-argument byte-length cap. -/
def MAX_INPUT_LEN : Nat := 512

/-- Compute `base^exponent mod modulus` over big-endian byte strings,
    left-padded with zeros to `modulus.size` bytes.

    Edge cases (matching `num-bigint::BigUint::modpow`):
    - `modulus = 0` or `1` → all zeros of size `modulus.size`.
    - `exponent = 0` → 1 (left-padded), unless modulus ≤ 1.

    Does NOT enforce the `MAX_INPUT_LEN` cap — the syscall arm does. -/
@[extern "lean_big_mod_exp"]
opaque modpow (base exponent modulus : @& ByteArray) : ByteArray

/-! ## `sol_big_mod_exp` syscall

ABI: r1 = `*const BigModExpParams` (48 bytes — 6 × u64 LE:
`{ base, base_len, exponent, exponent_len, modulus, modulus_len }`),
r2 = `*mut [u8; modulus_len]` output. r0 = 0/1 (1 iff any len > 512). -/

/-- `sol_big_mod_exp` CU, exact per agave-syscalls 4.0.0-rc.0
    (`src/lib.rs:2280-2295`): `100 + (input_len² / 2 + 190)` with
    `input_len = max(base_len, exponent_len, modulus_len)`; constants from
    `execution_budget.rs:236,257,258`. `/2` Nat-floored, matching agave's
    `checked_div`. Audit M9: replaces the pre-fix flat `33`. -/
def cu (s : State) : Nat :=
  let paramsA := s.regs.r1
  let baseLen := Memory.readU64 s.mem (paramsA + 8)
  let expLen  := Memory.readU64 s.mem (paramsA + 24)
  let modLen  := Memory.readU64 s.mem (paramsA + 40)
  let inputLen := max baseLen (max expLen modLen)
  100 + (inputLen * inputLen / 2 + 190)

@[simp] def exec (s : State) : State :=
  let paramsA := s.regs.r1
  -- H6: translate the 48-byte `BigModExpParams` struct `[r1,48)` (Load) for
  -- the operand ptrs/lens, then (after the length check) each operand slice
  -- (base/exp/mod, Load) and the `modLen`-byte output (Store). Any
  -- out-of-region slice traps.
  s.guardRead paramsA 48 fun s =>
  let basePtr := Memory.readU64 s.mem  paramsA
  let baseLen := Memory.readU64 s.mem (paramsA + 8)
  let expPtr  := Memory.readU64 s.mem (paramsA + 16)
  let expLen  := Memory.readU64 s.mem (paramsA + 24)
  let modPtr  := Memory.readU64 s.mem (paramsA + 32)
  let modLen  := Memory.readU64 s.mem (paramsA + 40)
  -- Agave aborts (not in-band error) on any operand > 512 bytes with
  -- `SyscallError::InvalidLength`. Fail closed. See docs/SOUNDNESS_AUDIT_* (M9).
  if baseLen ≤ MAX_INPUT_LEN ∧ expLen ≤ MAX_INPUT_LEN ∧ modLen ≤ MAX_INPUT_LEN then
    s.guardRead basePtr baseLen fun s =>
    s.guardRead expPtr  expLen  fun s =>
    s.guardRead modPtr  modLen  fun s =>
    s.guardWrite s.regs.r2 modLen fun s =>
      let result := modpow (readBytes s.mem basePtr baseLen)
                           (readBytes s.mem expPtr  expLen)
                           (readBytes s.mem modPtr  modLen)
      commitOptional s s.regs.r2 modLen (some result)
  else
    { s with exitCode := some ERR_INVALID_LENGTH, vmError := some .invalidLength }

/-- H6: an out-of-region 48-byte `BigModExpParams` struct `[r1,48)` traps
    (first guarded slice, before the operands and output). -/
theorem exec_faults_oob (s : State)
    (hoob : s.regions.containsRange s.regs.r1 48 = false) :
    (exec s).vmError = some .accessViolation := by
  simp only [exec, State.guardRead]
  rw [if_neg (by
    rintro (h | h)
    · exact absurd h (by decide)
    · rw [hoob] at h; exact absurd h (by decide))]
  rfl

end BigModExp
end SVM.SBPF
