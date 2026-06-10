/-
  Trust statements for the FFI-bridged crypto syscalls.

  ## Trust model

  Of the 12 crypto-family syscalls qedsvm models, 10 bridge to Rust
  crates via `qedsvm-rs/lean-bridge/` (declared as `@[extern] opaque` on the Lean
  side). For each such opaque function, the executor body (in
  `SVM/Syscalls/*.lean`) embeds an `opaque` call inside `writeBytes` /
  `commitOptional`. The opaque is a black box at proof time, so any
  Hoare triple involving the syscall has to bottom out in an axiom that
  asserts what the opaque "should" return — and that axiom is the
  trust statement: it says "the FFI bridge returns exactly what
  agave's runtime returns, because they call the same crate at the
  same version".

  This file collects those trust statements, one per syscall, with the
  Rust crate name + pinned version + agave-equivalence rationale. The
  bookkeeping Hoare triples in `InstructionSpecs.lean` cite these
  axioms; consumers reasoning about programs that call these syscalls
  inherit the trust.

  See `docs/deferred-arch-lifts.md` §5 ("Crypto family — explicit
  trust-statement docs + bookkeeping triples") for the design sketch
  and the ROADMAP "Phase H — Crypto syscalls" entry for the
  production-status framing. The two pure-Lean syscalls
  (`sol_sha256`, and `Murmur3` used by the decoder) are NOT covered
  here — they are real verifications, no axiom needed; see the
  corresponding `SVM/Syscalls/Sha256.lean` and `SVM/SBPF/Murmur3.lean`
  files.

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
  must move in lockstep, and the axiom block here should record the
  new version in the trust statement.

  ## Axiom shape

  Each axiom asserts a *property* the opaque function satisfies — the
  size of the output digest, the bounded shape of an Option return,
  or the boolean-only nature of a validator. These are exactly the
  facts the SL-level Hoare triples need to commute their byte-write
  obligations through the writeBytes layer. We deliberately do *not*
  axiomatize the algebraic semantics (e.g. "sha512 is collision-
  resistant", "curve25519 group law respects associativity") — those
  are downstream pure-Lean verification projects, not gating items
  for the reference interpreter.
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

`Sha512.hash` is `@[extern "lean_sha512"] opaque`, defined in
`SVM/Syscalls/Sha512.lean`, and implemented in `lean-bridge` by a
call to `sha2::Sha512::digest`. We trust that for every input
`data : ByteArray`, the digest returned is exactly 64 bytes long and
equals what agave's `solana-sha512-hasher` (which wraps the same
`sha2` crate at the same pinned version) returns.

Without this size axiom, the byte-write obligation
`writeBytes s.mem outAddr 64 (Sha512.hash data)` cannot be tied to
the SL atom `outAddr ↦Bytes <digest>` of size 64. -/
axiom sha512_hash_size (data : ByteArray) : (Sha512.hash data).size = 64

/-! ## `sol_keccak256`  (trusts `sha3 = 0.10.8`)

`Keccak256.hash` (the Solana original-Keccak variant with 0x01
padding, *not* FIPS-202 SHA-3 with 0x06) bridges to `sha3::Keccak256`
via `lean-bridge`. Agave's `solana-keccak-hasher` wraps the same
crate, same version. We trust the digest is exactly 32 bytes. -/
axiom keccak256_hash_size (data : ByteArray) : (Keccak256.hash data).size = 32

/-! ## `sol_blake3`  (trusts `blake3 = 1.8.5`)

`Blake3.hash` calls `blake3::hash` in the default (non-keyed) hashing
mode. Agave's master pins the same crate at the same version. We
trust the digest is exactly 32 bytes. -/
axiom blake3_hash_size (data : ByteArray) : (Blake3.hash data).size = 32

/-! ## `sol_secp256k1_recover`  (trusts `libsecp256k1 = 0.7.2`, paritytech)

`Secp256k1.recover` bridges to paritytech's pure-Rust
`libsecp256k1::recover` — *not* Bitcoin Core's C library. The choice
is load-bearing: paritytech's `Signature::parse_standard_slice`
rejects high-S signatures, while Bitcoin Core's accepts them. Agave's
`SyscallSecp256k1Recover` uses the same crate at the same version,
so byte-for-byte conformance with mainnet is preserved.

On success the recovered public key is exactly 64 bytes (the
`x || y` coordinates, no `0x04` uncompressed prefix). Failures
(invalidHash / invalidRecoveryId / invalidSignature) carry no
payload. We trust this size invariant on the success arm. -/
axiom secp256k1_recover_success_size (hash : ByteArray) (recId : UInt8) (sig : ByteArray) :
    ∀ pubkey, Secp256k1.recover hash recId sig = .success pubkey → pubkey.size = 64

/-! ## `sol_curve_validate_point`  (trusts `curve25519-dalek = 4.1.3`)

Boolean validators only — no byte output. `Curve25519.validateEdwards`
and `Curve25519.validateRistretto` return `Bool` (true iff the
32-byte input is a valid compressed point on the respective curve).
Both bridge to `curve25519-dalek` via `lean-bridge`, exactly as
agave's `solana-curve25519::{edwards,ristretto}::validate_*` do.

Ristretto-validity is a strict subset of Edwards-validity (many
valid Edwards points are not valid Ristretto points); the two
validators do not agree on arbitrary inputs.

These are trivial *shape* statements — included for parity with the
other curve syscalls. There is no payload size to assert because the
return type is `Bool`, so unlike the size statements below they are
THEOREMS (provable by `Bool` case analysis), not trusted axioms: a
`Bool` is always `true` or `false` regardless of what the bridge
returns. Kept as named lemmas only so call sites read uniformly. -/
theorem curve_validate_edwards_total (point : ByteArray) :
    Curve25519.validateEdwards point = true ∨ Curve25519.validateEdwards point = false := by
  cases h : Curve25519.validateEdwards point <;> simp [h]

theorem curve_validate_ristretto_total (point : ByteArray) :
    Curve25519.validateRistretto point = true ∨ Curve25519.validateRistretto point = false := by
  cases h : Curve25519.validateRistretto point <;> simp [h]

/-! ## `sol_curve_group_op`  (trusts `curve25519-dalek = 4.1.3`)

Six opaque functions — two curves (Edwards / Ristretto) × three ops
(add / sub / mul). Each takes two 32-byte inputs and returns
`Option ByteArray`: `some <32-byte compressed point>` on success,
`none` on decode/decompression failure (or non-canonical scalar for
MUL). We trust that every `some` payload is exactly 32 bytes. -/
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

Variable-length input (n scalars + n points, each 32n bytes), returns
`Option ByteArray`: `some <32-byte compressed result>` on success, or
`none` on n=0, non-canonical scalar, or any decompression failure.
We trust the success payload is exactly 32 bytes. -/
axiom curve_edwards_msm_size (scalars points : ByteArray) :
    ∀ bs, Curve25519.edwardsMSM scalars points = some bs → bs.size = 32
axiom curve_ristretto_msm_size (scalars points : ByteArray) :
    ∀ bs, Curve25519.ristrettoMSM scalars points = some bs → bs.size = 32

/-! ## `sol_curve_decompress`  (trusts `solana-bls12-381-syscall = 0.1.0`)

Despite the name being shared with the curve25519 family, these two
syscalls are *BLS12-381 only* — the curve_id dispatch in
`Bls12_381.execDecompress` lives in the BLS12-381 ID space
(`4..=6 | 0x80`), distinct from curve25519's `0..1`. We trust the
G1/G2 decompression payloads are exactly 96 / 192 bytes
respectively. -/
axiom bls12_381_g1_decompress_size (input : ByteArray) (endianness : UInt8) :
    ∀ bs, Bls12_381.g1Decompress input endianness = some bs → bs.size = 96
axiom bls12_381_g2_decompress_size (input : ByteArray) (endianness : UInt8) :
    ∀ bs, Bls12_381.g2Decompress input endianness = some bs → bs.size = 192

/-! ## `sol_curve_pairing_map`  (trusts `solana-bls12-381-syscall = 0.1.0`)

Batch pairing of n (G1, G2) pairs; n ∈ 1..=8 (agave's
`MAX_PAIRING_LENGTH`). Returns `Option ByteArray`: `some
<576-byte Gt element>` on success, `none` on n=0, n>8, mismatched
buffer sizes, malformed points, or bad endianness. -/
axiom bls12_381_pairing_map_size (g1Points g2Points : ByteArray)
    (n : UInt64) (endianness : UInt8) :
    ∀ bs, Bls12_381.pairingMap g1Points g2Points n endianness = some bs → bs.size = 576

/-! ## `sol_alt_bn128_group_op`  (trusts `solana-bn254 = 3.2.1`)

BN254 group operations: G1/G2 ADD, G1/G2 MUL, PAIRING. Output size
depends on the operation (64 bytes for G1 ops, 128 for G2, 32 for
PAIRING). The axiom asserts the success payload matches
`AltBn128.groupOpOutSize` for the requested op_id. -/
axiom alt_bn128_group_op_size (opId : UInt64) (input : ByteArray) :
    ∀ bs, AltBn128.groupOp opId input = some bs →
      bs.size = AltBn128.groupOpOutSize opId.toNat

/-! ## `sol_alt_bn128_compression`  (trusts `solana-bn254 = 3.2.1`)

BN254 compress/decompress for G1 and G2. Output size per op:
G1 COMPRESS → 32, G1 DECOMPRESS → 64, G2 COMPRESS → 64,
G2 DECOMPRESS → 128. Captured by `AltBn128.compressionOutSize`. -/
axiom alt_bn128_compression_size (opId : UInt64) (input : ByteArray) :
    ∀ bs, AltBn128.compression opId input = some bs →
      bs.size = AltBn128.compressionOutSize opId.toNat

/-! ## `sol_big_mod_exp`  (trusts `solana-big-mod-exp = 3.0.0`)

`BigModExp.modpow` computes `base^exponent mod modulus` over big-
endian byte strings, returning a `ByteArray` left-padded to exactly
`modulus.size` bytes. Internally calls `num-bigint::BigUint::modpow`;
agave master pins the same crate. The size invariant is the key
property: the output is *always* `modulus.size` bytes, even for
zero / unity moduli (returning all zeros at that size). -/
axiom big_mod_exp_size (base exponent modulus : ByteArray) :
    (BigModExp.modpow base exponent modulus).size = modulus.size

/-! ## `sol_poseidon`  (trusts `light-poseidon 0.4.0` + `ark-bn254 0.5.0`)

`Poseidon.hash` computes the Poseidon hash over n ∈ 1..=12 inputs of
32 bytes each on the BN254 curve with the x^5 S-box. Returns
`Option ByteArray`: `some <32-byte digest>` on success, `none` on
out-of-range n, bad parameters/endianness, mismatched input length,
or non-canonical field element. We trust the success payload is
exactly 32 bytes. -/
axiom poseidon_hash_size (parameters endianness : UInt8) (inputs : ByteArray) (n : UInt64) :
    ∀ bs, Poseidon.hash parameters endianness inputs n = some bs → bs.size = 32

/-! ## Consumer-facing Hoare-triple status

The 10 axioms above are the *trust artifact* — they pin down what the
FFI is trusted to do, and they are the only soundness foothold the SL
proofs can use. The matching consumer-facing Hoare triples in
`InstructionSpecs.lean` are bookkeeping on top of these axioms.

**Shipped this lift** (6 triples, all using a new helper
`cuTripleWithin_syscall_writes_r0_only_pinned` — a generalization of
`writes_r0_only` that pins one extra register and makes the regs/mem
post-state conditional on that pinning):

- (`sol_curve_validate_point` unsupported curve_id now FAILS CLOSED
  with `ERR_INVALID_ATTRIBUTE` — matches agave under
  `abort_on_invalid_curve` — so the old "r0 := 2" triple was removed; see
  `InstructionSpecs/Crypto.lean` and SOUNDNESS_AUDIT M7)
- `call_sol_secp256k1_recover_invalid_recid_spec` (recovery_id > 3
  ⇒ r0 := 2, mem untouched, no FFI call)
- (`sol_curve_group_op` unsupported curve_id now FAILS CLOSED with
  `ERR_INVALID_ATTRIBUTE` too; the old "r0 := 1" triple was removed — M7)
- `call_sol_curve_multiscalar_mul_zero_n_spec` (n = 0 ⇒ r0 := 1,
  mem untouched)
- `call_sol_curve_decompress_unsupported_spec` (unsupported BLS
  curve_id ⇒ r0 := 1, mem untouched)
- `call_sol_curve_pairing_map_unsupported_spec` (unsupported BLS
  curve_id ⇒ r0 := 1, mem untouched)

These triples cover the syscalls' **error / shortcircuit paths** where
no FFI call happens, so they need no axiom support from this file.
They establish the pattern; the corresponding **success paths** —
where the FFI is called and writes a digest at the output address —
are deferred to a follow-on SL session because they require the
~400-line PDA n=0 proof template (`call_create_program_address_n0_spec`)
parameterized by:

- the spec function `digest : State → ByteArray` (Sha256.hash for
  Tier 2; the opaque FFI function for Tier 1),
- a size axiom from above (Tier 1) or a real
  `(Sha256.hash _).size = 32` lemma (Tier 2),
- the input-byte SL atoms (variable per syscall ABI).

The 10 axioms above land independently of the success-path triples —
they tighten the TCB documentation and are referenced by the ROADMAP
"Phase H" entry. -/

end CryptoTrust
end SVM.SBPF
