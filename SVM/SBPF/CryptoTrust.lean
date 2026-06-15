/-
  Trust statements for the FFI-bridged crypto syscalls.

  ## Trust model

  Of the 12 crypto-family syscalls, 10 bridge to Rust crates via
  `qedsvm-rs/lean-bridge/` (`@[extern] opaque` on the Lean side). The opaque
  is a black box at proof time, so any Hoare triple bottoms out in an axiom
  asserting what it returns — the trust statement: "the FFI bridge returns
  exactly what agave's runtime returns, because they call the same crate at
  the same version". This file collects those axioms (one per syscall, with
  crate pin + agave-equivalence rationale); `InstructionSpecs.lean`'s
  bookkeeping triples cite them.

  The two pure-Lean syscalls (`sol_sha256`, `Murmur3`) are NOT covered — they
  are real verifications, no axiom needed.

  ## Crate pins (all from agave master, queried 2026-05-13)

  | Syscall                          | Rust crate (pin)                        |
  |----------------------------------|-----------------------------------------|
  | `sol_sha512`                     | `sha2 = 0.10.8`                         |
  | `sol_keccak256`                  | `sha3 = 0.10.8`                         |
  | `sol_blake3`                     | `blake3 = 1.8.5`                        |
  | `sol_secp256k1_recover`          | `libsecp256k1 = 0.7.2` (paritytech)     |
  | `sol_curve_validate_point` (×2)  | `curve25519-dalek = 4.1.3`              |
  | `sol_curve_group_op` (×6)        | `curve25519-dalek = 4.1.3`              |
  | `sol_curve_multiscalar_mul` (×2) | `curve25519-dalek = 4.1.3`              |
  | `sol_curve_decompress`           | `solana-bls12-381-syscall = 0.1.0`      |
  | `sol_curve_pairing_map`          | `solana-bls12-381-syscall = 0.1.0`      |
  | `sol_alt_bn128_group_op`         | `solana-bn254 = 3.2.1` (uses ark-bn254) |
  | `sol_alt_bn128_compression`      | `solana-bn254 = 3.2.1`                  |
  | `sol_big_mod_exp`                | `solana-big-mod-exp = 3.0.0`            |
  | `sol_poseidon`                   | `light-poseidon 0.4.0` + `ark-bn254`    |

  When agave bumps a pin, the matching `qedsvm-rs/lean-bridge/Cargo.toml` line
  must move in lockstep and the axiom block here record the new version.

  ## Axiom shape

  Each axiom asserts a *property* (output size, Option shape, boolean-only
  validator) — the facts the SL Hoare triples need to commute their byte-write
  obligations through the writeBytes layer. We deliberately do *not*
  axiomatize the algebraic semantics (collision-resistance, group laws) —
  those are downstream verification projects, not gating items here.
-/

import SVM.Syscalls.Sha512
import SVM.Syscalls.Keccak256
import SVM.Syscalls.Blake3
import SVM.Syscalls.Secp256k1
import SVM.Syscalls.Curve25519
import SVM.Syscalls.Bls12_381
import SVM.Syscalls.AltBn128
import SVM.Syscalls.BigModExp
import SVM.Syscalls.Poseidon

namespace SVM.SBPF
namespace CryptoTrust

/-! ## `sol_sha512`  (trusts `sha2 = 0.10.8`)

`Sha512.hash` bridges to `sha2::Sha512::digest`; agave's
`solana-sha512-hasher` wraps the same crate/version. Trust: the digest is
exactly 64 bytes — without it the byte-write obligation cannot be tied to the
size-64 `↦Bytes` SL atom. -/
axiom sha512_hash_size (data : ByteArray) : (Sha512.hash data).size = 64

/-! ## `sol_keccak256`  (trusts `sha3 = 0.10.8`)

`Keccak256.hash` is the Solana original-Keccak variant (0x01 padding, *not*
FIPS-202 SHA-3) bridging to `sha3::Keccak256`; agave's `solana-keccak-hasher`
wraps the same crate/version. Trust: 32-byte digest. -/
axiom keccak256_hash_size (data : ByteArray) : (Keccak256.hash data).size = 32

/-! ## `sol_blake3`  (trusts `blake3 = 1.8.5`)

`Blake3.hash` calls `blake3::hash` (default non-keyed mode); agave pins the
same crate/version. Trust: 32-byte digest. -/
axiom blake3_hash_size (data : ByteArray) : (Blake3.hash data).size = 32

/-! ## `sol_secp256k1_recover`  (trusts `libsecp256k1 = 0.7.2`, paritytech)

`Secp256k1.recover` bridges to paritytech's pure-Rust `libsecp256k1::recover`,
*not* Bitcoin Core's C library — load-bearing: paritytech rejects high-S
signatures, Bitcoin Core accepts them. Agave uses the same crate/version, so
mainnet conformance holds. Trust: the recovered pubkey is exactly 64 bytes
(`x || y`, no `0x04` prefix) on the success arm. -/
axiom secp256k1_recover_success_size (hash : ByteArray) (recId : UInt8) (sig : ByteArray) :
    ∀ pubkey, Secp256k1.recover hash recId sig = .success pubkey → pubkey.size = 64

/-! ## `sol_curve_validate_point`  (trusts `curve25519-dalek = 4.1.3`)

Boolean validators only — no byte output. `validateEdwards` /
`validateRistretto` return `Bool` (valid compressed point on the curve);
Ristretto-validity is a strict subset of Edwards-validity. Unlike the size
axioms below these are THEOREMS, not trusted axioms: a `Bool` is always
true/false regardless of what the bridge returns. Kept as named lemmas only so
call sites read uniformly. -/
theorem curve_validate_edwards_total (point : ByteArray) :
    Curve25519.validateEdwards point = true ∨ Curve25519.validateEdwards point = false := by
  cases h : Curve25519.validateEdwards point <;> simp [h]

theorem curve_validate_ristretto_total (point : ByteArray) :
    Curve25519.validateRistretto point = true ∨ Curve25519.validateRistretto point = false := by
  cases h : Curve25519.validateRistretto point <;> simp [h]

/-! ## `sol_curve_group_op`  (trusts `curve25519-dalek = 4.1.3`)

Six opaque functions: {Edwards, Ristretto} × {add, sub, mul}. Each takes two
32-byte inputs, returns `Option ByteArray`. Trust: every `some` payload is
exactly 32 bytes. -/
axiom curve_edwards_add_size (l r : ByteArray) :
    ∀ bs, Curve25519.edwardsAdd l r = some bs → bs.size = 32
axiom curve_edwards_sub_size (l r : ByteArray) :
    ∀ bs, Curve25519.edwardsSub l r = some bs → bs.size = 32
axiom curve_edwards_mul_size (s p : ByteArray) :
    ∀ bs, Curve25519.edwardsMul s p = some bs → bs.size = 32
axiom curve_ristretto_add_size (l r : ByteArray) :
    ∀ bs, Curve25519.ristrettoAdd l r = some bs → bs.size = 32
axiom curve_ristretto_sub_size (l r : ByteArray) :
    ∀ bs, Curve25519.ristrettoSub l r = some bs → bs.size = 32
axiom curve_ristretto_mul_size (s p : ByteArray) :
    ∀ bs, Curve25519.ristrettoMul s p = some bs → bs.size = 32

/-! ## `sol_curve_multiscalar_mul`  (trusts `curve25519-dalek = 4.1.3`)

Variable-length input (n scalars + n points), returns `Option ByteArray`.
Trust: the success payload is exactly 32 bytes. -/
axiom curve_edwards_msm_size (scalars points : ByteArray) :
    ∀ bs, Curve25519.edwardsMSM scalars points = some bs → bs.size = 32
axiom curve_ristretto_msm_size (scalars points : ByteArray) :
    ∀ bs, Curve25519.ristrettoMSM scalars points = some bs → bs.size = 32

/-! ## `sol_curve_decompress`  (trusts `solana-bls12-381-syscall = 0.1.0`)

Despite the shared name, these are *BLS12-381 only* — the curve_id dispatch
lives in the BLS ID space (`4..=6 | 0x80`), distinct from curve25519's `0..1`.
Trust: G1/G2 decompression payloads are 96 / 192 bytes. -/
axiom bls12_381_g1_decompress_size (input : ByteArray) (endianness : UInt8) :
    ∀ bs, Bls12_381.g1Decompress input endianness = some bs → bs.size = 96
axiom bls12_381_g2_decompress_size (input : ByteArray) (endianness : UInt8) :
    ∀ bs, Bls12_381.g2Decompress input endianness = some bs → bs.size = 192

/-! ## `sol_curve_pairing_map`  (trusts `solana-bls12-381-syscall = 0.1.0`)

Batch pairing of n (G1, G2) pairs, n ∈ 1..=8 (agave's `MAX_PAIRING_LENGTH`).
Trust: the success payload is a 576-byte Gt element. -/
axiom bls12_381_pairing_map_size (g1Points g2Points : ByteArray)
    (n : UInt64) (endianness : UInt8) :
    ∀ bs, Bls12_381.pairingMap g1Points g2Points n endianness = some bs → bs.size = 576

/-! ## `sol_alt_bn128_group_op`  (trusts `solana-bn254 = 3.2.1`)

BN254 group ops (G1/G2 ADD/MUL, PAIRING); output size is op-dependent. Trust:
the success payload matches `AltBn128.groupOpOutSize` for the op_id. -/
axiom alt_bn128_group_op_size (opId : UInt64) (input : ByteArray) :
    ∀ bs, AltBn128.groupOp opId input = some bs →
      bs.size = AltBn128.groupOpOutSize opId.toNat

/-! ## `sol_alt_bn128_compression`  (trusts `solana-bn254 = 3.2.1`)

BN254 G1/G2 compress/decompress; output size per op captured by
`AltBn128.compressionOutSize`. -/
axiom alt_bn128_compression_size (opId : UInt64) (input : ByteArray) :
    ∀ bs, AltBn128.compression opId input = some bs →
      bs.size = AltBn128.compressionOutSize opId.toNat

/-! ## `sol_big_mod_exp`  (trusts `solana-big-mod-exp = 3.0.0`)

`BigModExp.modpow` computes `base^exponent mod modulus` via
`num-bigint::BigUint::modpow` (agave pins the same crate). Trust: the output
is *always* `modulus.size` bytes, even for zero/unity moduli (all zeros). -/
axiom big_mod_exp_size (base exponent modulus : ByteArray) :
    (BigModExp.modpow base exponent modulus).size = modulus.size

/-! ## `sol_poseidon`  (trusts `light-poseidon 0.4.0` + `ark-bn254 0.5.0`)

`Poseidon.hash` over n ∈ 1..=12 inputs of 32 bytes each on BN254 with the x^5
S-box. Trust: the success payload is exactly 32 bytes. -/
axiom poseidon_hash_size (parameters endianness : UInt8) (inputs : ByteArray) (n : UInt64) :
    ∀ bs, Poseidon.hash parameters endianness inputs n = some bs → bs.size = 32

/-! ## Consumer-facing Hoare-triple status

The 10 axioms above are the *trust artifact* — the only soundness foothold the
SL proofs have; `InstructionSpecs.lean`'s triples are bookkeeping on top.

**H6 update.** The four short-circuit bookkeeping triples for the no-FFI error
paths (recovery_id > 3, msm n = 0, BLS unsupported curve_id ⇒ `r0 := errCode,
mem untouched`) are RETIRED: under H6 every crypto syscall routes its slices
through the region guards, so the unconditional "mem untouched" claim no longer
holds for an out-of-region buffer (agave traps there too). Being unconsumed,
they are replaced by model-side `*_faults_oob` lemmas (out-of-region ⇒ typed
`accessViolation`), cross-engine-pinned by the `oob_*` diff fixtures. The
generic `cuTripleWithin_syscall_writes_r0_only_pinned` helper is kept. The
**success paths** (FFI called, digest written) remain deferred — they need the
~400-line PDA n=0 proof template parameterized by the spec `digest` function, a
size axiom (Tier 1) or real lemma (Tier 2), and per-ABI input SL atoms. The 10
axioms land independently. -/

end CryptoTrust
end SVM.SBPF
