//! Rust bridge for qedsvm's crypto syscalls.
//!
//! Every export here is the direct target of a Lean `@[extern "name"]`
//! declaration in `Svm/SBPF/*.lean`. Functions take/return Lean's
//! `lean_object` ABI directly (no intermediary C shim layer) — that's
//! why `csrc/` no longer exists. The minimal Rust ↔ Lean ABI surface
//! lives in `lean_ffi.rs`.
//!
//! Crate pins are kept in lockstep with agave's `master/Cargo.toml`
//! (queried 2026-05-13):
//!   - `libsecp256k1 = 0.7.2` (no-default-features, `+std`,
//!     `+static-context`) — agave's `solana-syscalls` runtime dep
//!   - `sha2 = 0.10.8` (no-default-features) — via
//!     `solana-sha256-hasher`
//!   - `sha3 = 0.10.8` — via `solana-keccak-hasher`
//!   - `blake3 = 1.8.5` — agave master pin
//!   - `curve25519-dalek = 4.1.3` (`+digest`, `+rand_core`) — via
//!     `solana-curve25519`
//!
//! When agave bumps a version, bump here in lockstep — that is the
//! whole point of this crate.

#![deny(unsafe_op_in_unsafe_fn)]

mod lean_ffi;
use lean_ffi::{
    alloc_bytearray, b_lean_obj_arg, lean_alloc_ctor, lean_box, lean_ctor_set, lean_obj_arg,
    lean_obj_res, sarray_as_slice,
};
use sha2::Digest as _;

// ───────────────────────────────────────────────────────────────────
// SHA-256 (`sha2 = 0.10.8`) — agave-conformance audit hook for the
// pure-Lean Sha256.hash impl. The production path is the pure-Lean
// version; this exists so `Sha256.hash x = Sha256.hashAgave x` can be
// proved by native_decide across a sweep of inputs.
// ───────────────────────────────────────────────────────────────────

#[no_mangle]
pub extern "C" fn lean_sha256_agave(input: b_lean_obj_arg) -> lean_obj_res {
    let bytes = unsafe { sarray_as_slice(input) };
    let digest = sha2::Sha256::digest(bytes);
    alloc_bytearray(&digest)
}

// ───────────────────────────────────────────────────────────────────
// SHA-512 (`sha2 = 0.10.8`). Output is 64 bytes — same crate /
// underlying impl agave's `solana-sha512-hasher` wraps with the
// `sha2` feature. Production path for `SVM.SBPF.Sha512.hash`.
// ───────────────────────────────────────────────────────────────────

#[no_mangle]
pub extern "C" fn lean_sha512(input: b_lean_obj_arg) -> lean_obj_res {
    let bytes = unsafe { sarray_as_slice(input) };
    let digest = sha2::Sha512::digest(bytes);
    alloc_bytearray(&digest)
}

// ───────────────────────────────────────────────────────────────────
// Keccak-256 (`sha3::Keccak256`, original Keccak with 0x01 padding —
// Solana's variant, NOT FIPS-202 SHA-3 which uses 0x06).
// Production path for `Keccak256.hash`.
// ───────────────────────────────────────────────────────────────────

#[no_mangle]
pub extern "C" fn lean_keccak256(input: b_lean_obj_arg) -> lean_obj_res {
    let bytes = unsafe { sarray_as_slice(input) };
    let digest = sha3::Keccak256::digest(bytes);
    alloc_bytearray(&digest)
}

// ───────────────────────────────────────────────────────────────────
// BLAKE3 (`blake3 = 1.8.5`, default hashing mode, 32-byte output).
// Production path for `Blake3.hash`.
// ───────────────────────────────────────────────────────────────────

#[no_mangle]
pub extern "C" fn lean_blake3(input: b_lean_obj_arg) -> lean_obj_res {
    let bytes = unsafe { sarray_as_slice(input) };
    let digest = blake3::hash(bytes);
    alloc_bytearray(digest.as_bytes())
}

// ───────────────────────────────────────────────────────────────────
// secp256k1 ECDSA recovery (`libsecp256k1 = 0.7.2`, paritytech).
//
// Matches agave's `SyscallSecp256k1Recover` body byte-for-byte:
//   Message::parse_slice(hash) → InvalidHash
//   RecoveryId::parse(rid)     → InvalidRecoveryId
//   Signature::parse_standard_slice(sig) → InvalidSignature
//   libsecp256k1::recover(...) → InvalidSignature on Err
//   serialize() trims leading 0x04 → Solana's 64-byte format.
//
// Returns the Lean inductive `Secp256k1.RecoverResult` directly:
//   tag 0 (`success`, 1 obj field = 64-byte ByteArray)
//   tag 1 (`invalidHash`, nullary → lean_box(1))
//   tag 2 (`invalidRecoveryId`, nullary → lean_box(2))
//   tag 3 (`invalidSignature`, nullary → lean_box(3))
// Inductive tags must stay in lockstep with Svm/SBPF/Secp256k1.lean.
// ───────────────────────────────────────────────────────────────────

#[no_mangle]
pub extern "C" fn lean_secp256k1_recover(
    hash: b_lean_obj_arg,
    recovery_id: u8,
    sig: b_lean_obj_arg,
) -> lean_obj_res {
    let hash_bytes = unsafe { sarray_as_slice(hash) };
    let sig_bytes = unsafe { sarray_as_slice(sig) };

    if hash_bytes.len() != 32 {
        return unsafe { lean_box(1) };
    }
    if sig_bytes.len() != 64 {
        return unsafe { lean_box(3) };
    }
    if recovery_id > 3 {
        return unsafe { lean_box(2) };
    }

    let Ok(message) = libsecp256k1::Message::parse_slice(hash_bytes) else {
        return unsafe { lean_box(1) };
    };
    let Ok(rid) = libsecp256k1::RecoveryId::parse(recovery_id) else {
        return unsafe { lean_box(2) };
    };
    let Ok(signature) = libsecp256k1::Signature::parse_standard_slice(sig_bytes) else {
        return unsafe { lean_box(3) };
    };
    let pubkey = match libsecp256k1::recover(&message, &signature, &rid) {
        Ok(pk) => pk,
        Err(_) => return unsafe { lean_box(3) },
    };
    let serialized = pubkey.serialize(); // 65 bytes, leading 0x04
    let bytes_obj = alloc_bytearray(&serialized[1..65]);

    // .success bytes_obj  →  ctor tag 0, 1 obj field, 0 scalar bytes
    let ctor = unsafe { lean_alloc_ctor(0, 1, 0) };
    unsafe { lean_ctor_set(ctor as lean_obj_arg, 0, bytes_obj as lean_obj_arg) };
    ctor
}

// ───────────────────────────────────────────────────────────────────
// curve25519 — point validation (`curve25519-dalek = 4.1.3`).
//
// Matches `solana_curve25519::{edwards,ristretto}::validate_*`
// byte-for-byte: both reduce to
// `CompressedX::from_slice(b).decompress().is_some()`.
//
// Lean's `Bool` ABI is a primitive `uint8_t` (0 = false, 1 = true),
// NOT a heap object — these functions do not allocate.
// ───────────────────────────────────────────────────────────────────

#[no_mangle]
pub extern "C" fn lean_curve_validate_edwards(point: b_lean_obj_arg) -> u8 {
    let bytes = unsafe { sarray_as_slice(point) };
    if bytes.len() != 32 {
        return 0;
    }
    match curve25519_dalek::edwards::CompressedEdwardsY::from_slice(bytes) {
        Ok(c) if c.decompress().is_some() => 1,
        _ => 0,
    }
}

#[no_mangle]
pub extern "C" fn lean_curve_validate_ristretto(point: b_lean_obj_arg) -> u8 {
    let bytes = unsafe { sarray_as_slice(point) };
    if bytes.len() != 32 {
        return 0;
    }
    match curve25519_dalek::ristretto::CompressedRistretto::from_slice(bytes) {
        Ok(c) if c.decompress().is_some() => 1,
        _ => 0,
    }
}

// ───────────────────────────────────────────────────────────────────
// curve25519 group operations — ADD/SUB/MUL on Edwards + Ristretto.
//
// Each function takes two 32-byte ByteArrays and returns
// `Option ByteArray` (Lean side: `some <32-byte compressed point>` on
// success, `none` on any decode/decompression failure or non-canonical
// scalar).
//
// For ADD / SUB: both inputs are compressed points on the relevant
// curve. For MUL: `left` is a canonical 32-byte scalar (little-endian,
// must be < ell where ell is the curve25519 subgroup order); `right`
// is a compressed point.
//
// Exactly mirrors agave's `PodEdwardsPoint::{add,subtract,multiply}`
// and `PodRistrettoPoint::{add,subtract,multiply}`, which delegate to
// curve25519-dalek's `+`, `-`, scalar `*` operators.
// ───────────────────────────────────────────────────────────────────

use curve25519_dalek::{
    edwards::{CompressedEdwardsY, EdwardsPoint},
    ristretto::{CompressedRistretto, RistrettoPoint},
    scalar::Scalar,
};

/// Returns `Some(point)` if the 32 bytes decode and decompress to a
/// valid Edwards point; otherwise `None`.
fn decompress_edwards(bytes: &[u8]) -> Option<EdwardsPoint> {
    if bytes.len() != 32 {
        return None;
    }
    CompressedEdwardsY::from_slice(bytes).ok()?.decompress()
}

fn decompress_ristretto(bytes: &[u8]) -> Option<RistrettoPoint> {
    if bytes.len() != 32 {
        return None;
    }
    CompressedRistretto::from_slice(bytes).ok()?.decompress()
}

/// Returns `Some(scalar)` if the 32 bytes are a canonical scalar
/// (i.e. strictly less than the subgroup order `ell`); otherwise
/// `None`. Matches `PodScalar -> Scalar` via
/// `Scalar::from_canonical_bytes` in solana-curve25519.
fn parse_canonical_scalar(bytes: &[u8]) -> Option<Scalar> {
    if bytes.len() != 32 {
        return None;
    }
    let array: [u8; 32] = bytes.try_into().ok()?;
    Scalar::from_canonical_bytes(array).into()
}

/// Wrap a 32-byte point as Lean's `Option ByteArray = .some bytes`.
fn some_bytearray(bytes: &[u8; 32]) -> lean_obj_res {
    let arr = alloc_bytearray(bytes);
    let some = unsafe { lean_alloc_ctor(1, 1, 0) };
    unsafe { lean_ctor_set(some as lean_obj_arg, 0, arr as lean_obj_arg) };
    some
}

#[inline]
fn none_obj() -> lean_obj_res {
    unsafe { lean_box(0) }
}

#[no_mangle]
pub extern "C" fn lean_curve_edwards_add(
    left: b_lean_obj_arg, right: b_lean_obj_arg,
) -> lean_obj_res {
    let l = unsafe { sarray_as_slice(left) };
    let r = unsafe { sarray_as_slice(right) };
    let (Some(lp), Some(rp)) = (decompress_edwards(l), decompress_edwards(r)) else {
        return none_obj();
    };
    let result = (lp + rp).compress().to_bytes();
    some_bytearray(&result)
}

#[no_mangle]
pub extern "C" fn lean_curve_edwards_sub(
    left: b_lean_obj_arg, right: b_lean_obj_arg,
) -> lean_obj_res {
    let l = unsafe { sarray_as_slice(left) };
    let r = unsafe { sarray_as_slice(right) };
    let (Some(lp), Some(rp)) = (decompress_edwards(l), decompress_edwards(r)) else {
        return none_obj();
    };
    let result = (lp - rp).compress().to_bytes();
    some_bytearray(&result)
}

#[no_mangle]
pub extern "C" fn lean_curve_edwards_mul(
    scalar: b_lean_obj_arg, point: b_lean_obj_arg,
) -> lean_obj_res {
    let s = unsafe { sarray_as_slice(scalar) };
    let p = unsafe { sarray_as_slice(point) };
    let (Some(sc), Some(pt)) = (parse_canonical_scalar(s), decompress_edwards(p)) else {
        return none_obj();
    };
    let result = (sc * pt).compress().to_bytes();
    some_bytearray(&result)
}

#[no_mangle]
pub extern "C" fn lean_curve_ristretto_add(
    left: b_lean_obj_arg, right: b_lean_obj_arg,
) -> lean_obj_res {
    let l = unsafe { sarray_as_slice(left) };
    let r = unsafe { sarray_as_slice(right) };
    let (Some(lp), Some(rp)) = (decompress_ristretto(l), decompress_ristretto(r)) else {
        return none_obj();
    };
    let result = (lp + rp).compress().to_bytes();
    some_bytearray(&result)
}

#[no_mangle]
pub extern "C" fn lean_curve_ristretto_sub(
    left: b_lean_obj_arg, right: b_lean_obj_arg,
) -> lean_obj_res {
    let l = unsafe { sarray_as_slice(left) };
    let r = unsafe { sarray_as_slice(right) };
    let (Some(lp), Some(rp)) = (decompress_ristretto(l), decompress_ristretto(r)) else {
        return none_obj();
    };
    let result = (lp - rp).compress().to_bytes();
    some_bytearray(&result)
}

#[no_mangle]
pub extern "C" fn lean_curve_ristretto_mul(
    scalar: b_lean_obj_arg, point: b_lean_obj_arg,
) -> lean_obj_res {
    let s = unsafe { sarray_as_slice(scalar) };
    let p = unsafe { sarray_as_slice(point) };
    let (Some(sc), Some(pt)) = (parse_canonical_scalar(s), decompress_ristretto(p)) else {
        return none_obj();
    };
    let result = (sc * pt).compress().to_bytes();
    some_bytearray(&result)
}

// ───────────────────────────────────────────────────────────────────
// curve25519 multiscalar multiplication.
//
// Inputs: concatenated 32-byte scalars (32n bytes) and concatenated
// 32-byte points (32n bytes). N is derived from the lengths. Mirrors
// agave's `multiscalar_multiply_{edwards,ristretto}` via
// `EdwardsPoint::vartime_multiscalar_mul` / its ristretto analogue.
//
// Returns `Some(32-byte result)` or `None` if any input is malformed
// (non-canonical scalar, undecompressable point, mismatched lengths,
// zero N, or non-multiple-of-32 lengths). Agave's syscall arm caps
// `points_len` at 512; we do not enforce that here — it's the
// syscall arm's job (matches Solana's per-callsite policy).
// ───────────────────────────────────────────────────────────────────

use curve25519_dalek::traits::VartimeMultiscalarMul;

fn msm_decode_scalars_points<F, P>(
    scalars: &[u8], points: &[u8], decompress: F,
) -> Option<(Vec<Scalar>, Vec<P>)>
where
    F: Fn(&[u8]) -> Option<P>,
{
    if scalars.is_empty() || scalars.len() != points.len() {
        return None;
    }
    if scalars.len() % 32 != 0 {
        return None;
    }
    let n = scalars.len() / 32;
    let mut sc = Vec::with_capacity(n);
    let mut pt = Vec::with_capacity(n);
    for i in 0..n {
        sc.push(parse_canonical_scalar(&scalars[i * 32..(i + 1) * 32])?);
        pt.push(decompress(&points[i * 32..(i + 1) * 32])?);
    }
    Some((sc, pt))
}

#[no_mangle]
pub extern "C" fn lean_curve_edwards_msm(
    scalars: b_lean_obj_arg, points: b_lean_obj_arg,
) -> lean_obj_res {
    let s = unsafe { sarray_as_slice(scalars) };
    let p = unsafe { sarray_as_slice(points) };
    let Some((sc, pt)) = msm_decode_scalars_points(s, p, decompress_edwards) else {
        return none_obj();
    };
    let result = EdwardsPoint::vartime_multiscalar_mul(sc, pt)
        .compress()
        .to_bytes();
    some_bytearray(&result)
}

#[no_mangle]
pub extern "C" fn lean_curve_ristretto_msm(
    scalars: b_lean_obj_arg, points: b_lean_obj_arg,
) -> lean_obj_res {
    let s = unsafe { sarray_as_slice(scalars) };
    let p = unsafe { sarray_as_slice(points) };
    let Some((sc, pt)) = msm_decode_scalars_points(s, p, decompress_ristretto) else {
        return none_obj();
    };
    let result = RistrettoPoint::vartime_multiscalar_mul(sc, pt)
        .compress()
        .to_bytes();
    some_bytearray(&result)
}

// ───────────────────────────────────────────────────────────────────
// Poseidon (BN254 curve, x^5 S-box).
//
// Matches agave's `SyscallPoseidon` byte-for-byte: uses
// `light-poseidon = 0.4.0` with `ark-bn254 = 0.5.0` (agave's master
// pins). The `parameters` byte selects the curve config (only `0` =
// `Bn254X5` is currently defined). `endianness`: `0` = BigEndian,
// `1` = LittleEndian — controls both how input bytes are interpreted
// as field elements and the byte order of the output hash.
//
// Inputs are passed as a single concatenated buffer; the syscall arm
// is responsible for reading per-input slices via VmSlice descriptors
// and joining them. n must satisfy `1 ≤ n ≤ 12` (agave's
// `vals_len > 12 ⇒ InvalidLength`). For modern agave with
// `poseidon_enforce_padding`, each input must be exactly 32 bytes;
// we encode that constraint by treating the input buffer as `32n`
// bytes split into `n` 32-byte chunks.
// ───────────────────────────────────────────────────────────────────

// ───────────────────────────────────────────────────────────────────
// BLS12-381 decompress + pairing_map.
//
// Backed by `solana-bls12-381-syscall = 0.1.0` (agave's master pin) —
// the same crate agave's `SyscallCurveDecompress` /
// `SyscallCurvePairingMap` arms use.
//
// Sizes (from solana_bls12_381_syscall::encoding):
//   G1_COMPRESSED   = 48 bytes (FQ_SIZE)
//   G1_UNCOMPRESSED = 96 bytes (2 × FQ)
//   G2_COMPRESSED   = 96 bytes (FQ2_SIZE)
//   G2_UNCOMPRESSED = 192 bytes (2 × FQ2)
//   GT              = 576 bytes (12 × FQ)
//   MAX_PAIRING_LENGTH = 8
//
// Endianness: `0` = BE (canonical Zcash/IETF), `1` = LE (per-FQ-chunk
// byte reversal). Bytes beyond 1 are rejected.
// ───────────────────────────────────────────────────────────────────

#[no_mangle]
pub extern "C" fn lean_bls12_381_g1_decompress(
    input: b_lean_obj_arg,
    endianness: u8,
) -> lean_obj_res {
    use solana_bls12_381_syscall::{
        bls12_381_g1_decompress, Endianness, PodG1Compressed, Version,
    };
    let bytes = unsafe { sarray_as_slice(input) };
    if bytes.len() != 48 {
        return none_obj();
    }
    let mut arr = [0u8; 48];
    arr.copy_from_slice(bytes);
    let endian = match endianness {
        0 => Endianness::BE,
        1 => Endianness::LE,
        _ => return none_obj(),
    };
    match bls12_381_g1_decompress(Version::V0, &PodG1Compressed(arr), endian) {
        Some(p) => some_bytearray_slice(&p.0),
        None => none_obj(),
    }
}

#[no_mangle]
pub extern "C" fn lean_bls12_381_g2_decompress(
    input: b_lean_obj_arg,
    endianness: u8,
) -> lean_obj_res {
    use solana_bls12_381_syscall::{
        bls12_381_g2_decompress, Endianness, PodG2Compressed, Version,
    };
    let bytes = unsafe { sarray_as_slice(input) };
    if bytes.len() != 96 {
        return none_obj();
    }
    let mut arr = [0u8; 96];
    arr.copy_from_slice(bytes);
    let endian = match endianness {
        0 => Endianness::BE,
        1 => Endianness::LE,
        _ => return none_obj(),
    };
    match bls12_381_g2_decompress(Version::V0, &PodG2Compressed(arr), endian) {
        Some(p) => some_bytearray_slice(&p.0),
        None => none_obj(),
    }
}

#[no_mangle]
pub extern "C" fn lean_bls12_381_pairing_map(
    g1_points: b_lean_obj_arg,
    g2_points: b_lean_obj_arg,
    n: u64,
    endianness: u8,
) -> lean_obj_res {
    use solana_bls12_381_syscall::{
        bls12_381_pairing_map, Endianness, PodG1Point, PodG2Point, Version,
    };
    if n == 0 || n > 8 {
        return none_obj();
    }
    let g1_bytes = unsafe { sarray_as_slice(g1_points) };
    let g2_bytes = unsafe { sarray_as_slice(g2_points) };
    if g1_bytes.len() != (n as usize) * 96 || g2_bytes.len() != (n as usize) * 192 {
        return none_obj();
    }
    let endian = match endianness {
        0 => Endianness::BE,
        1 => Endianness::LE,
        _ => return none_obj(),
    };

    let g1_vec: Vec<PodG1Point> = g1_bytes
        .chunks_exact(96)
        .map(|c| {
            let mut a = [0u8; 96];
            a.copy_from_slice(c);
            PodG1Point(a)
        })
        .collect();
    let g2_vec: Vec<PodG2Point> = g2_bytes
        .chunks_exact(192)
        .map(|c| {
            let mut a = [0u8; 192];
            a.copy_from_slice(c);
            PodG2Point(a)
        })
        .collect();

    match bls12_381_pairing_map(Version::V0, &g1_vec, &g2_vec, endian) {
        Some(gt) => some_bytearray_slice(&gt.0),
        None => none_obj(),
    }
}

/// Variant of `some_bytearray` for arbitrary-length payloads.
fn some_bytearray_slice(bytes: &[u8]) -> lean_obj_res {
    let arr = alloc_bytearray(bytes);
    let some = unsafe { lean_alloc_ctor(1, 1, 0) };
    unsafe { lean_ctor_set(some as lean_obj_arg, 0, arr as lean_obj_arg) };
    some
}

// ───────────────────────────────────────────────────────────────────
// alt_bn128 (BN254) — Ethereum precompile parity.
//
// Backed by `solana-bn254 = 3.2.1` (agave's master pin). The op_id
// space carries both the operation and the endianness (high bit
// 0x80 = LE). Op_ids match `solana_bn254::*` constants:
//   group_op:
//     G1_ADD_BE=0, G1_ADD_LE=0x80, G1_MUL_BE=2, G1_MUL_LE=0x82,
//     PAIRING_BE=3, PAIRING_LE=0x83, G2_ADD_BE=4, G2_ADD_LE=0x84,
//     G2_MUL_BE=6, G2_MUL_LE=0x86
//   compression:
//     G1_COMPRESS_BE=0, G1_COMPRESS_LE=0x80, G1_DECOMPRESS_BE=1,
//     G1_DECOMPRESS_LE=0x81, G2_COMPRESS_BE=2, G2_COMPRESS_LE=0x82,
//     G2_DECOMPRESS_BE=3, G2_DECOMPRESS_LE=0x83
//
// Per-version choices match agave's call sites (addition: V0,
// multiplication: V1, pairing: V1).
// ───────────────────────────────────────────────────────────────────

#[no_mangle]
pub extern "C" fn lean_alt_bn128_group_op(
    op_id: u64,
    input: b_lean_obj_arg,
) -> lean_obj_res {
    use solana_bn254::versioned::{
        alt_bn128_versioned_g1_addition, alt_bn128_versioned_g1_multiplication,
        alt_bn128_versioned_g2_addition, alt_bn128_versioned_g2_multiplication,
        alt_bn128_versioned_pairing, Endianness, VersionedG1Addition,
        VersionedG1Multiplication, VersionedG2Addition, VersionedG2Multiplication,
        VersionedPairing, ALT_BN128_G1_ADD_BE, ALT_BN128_G1_ADD_LE, ALT_BN128_G1_MUL_BE,
        ALT_BN128_G1_MUL_LE, ALT_BN128_G2_ADD_BE, ALT_BN128_G2_ADD_LE,
        ALT_BN128_G2_MUL_BE, ALT_BN128_G2_MUL_LE, ALT_BN128_PAIRING_BE,
        ALT_BN128_PAIRING_LE,
    };
    let bytes = unsafe { sarray_as_slice(input) };
    let result = match op_id {
        ALT_BN128_G1_ADD_BE =>
            alt_bn128_versioned_g1_addition(VersionedG1Addition::V0, bytes, Endianness::BE),
        ALT_BN128_G1_ADD_LE =>
            alt_bn128_versioned_g1_addition(VersionedG1Addition::V0, bytes, Endianness::LE),
        ALT_BN128_G2_ADD_BE =>
            alt_bn128_versioned_g2_addition(VersionedG2Addition::V0, bytes, Endianness::BE),
        ALT_BN128_G2_ADD_LE =>
            alt_bn128_versioned_g2_addition(VersionedG2Addition::V0, bytes, Endianness::LE),
        ALT_BN128_G1_MUL_BE =>
            alt_bn128_versioned_g1_multiplication(VersionedG1Multiplication::V1, bytes, Endianness::BE),
        ALT_BN128_G1_MUL_LE =>
            alt_bn128_versioned_g1_multiplication(VersionedG1Multiplication::V1, bytes, Endianness::LE),
        ALT_BN128_G2_MUL_BE =>
            alt_bn128_versioned_g2_multiplication(VersionedG2Multiplication::V0, bytes, Endianness::BE),
        ALT_BN128_G2_MUL_LE =>
            alt_bn128_versioned_g2_multiplication(VersionedG2Multiplication::V0, bytes, Endianness::LE),
        ALT_BN128_PAIRING_BE =>
            alt_bn128_versioned_pairing(VersionedPairing::V1, bytes, Endianness::BE),
        ALT_BN128_PAIRING_LE =>
            alt_bn128_versioned_pairing(VersionedPairing::V1, bytes, Endianness::LE),
        _ => return none_obj(),
    };
    match result {
        Ok(out) => some_bytearray_slice(&out),
        Err(_) => none_obj(),
    }
}

// ───────────────────────────────────────────────────────────────────
// Big-integer modular exponentiation (`solana-big-mod-exp = 3.0.0`).
//
// Inputs: BE-encoded `base`, `exponent`, `modulus`. Returns the BE
// result padded with leading zeros to `modulus.len()` bytes. Matches
// agave's `SyscallBigModExp` minus the per-arg-length 512-byte cap
// (the syscall arm in `Execute.lean` enforces that bound).
// ───────────────────────────────────────────────────────────────────

#[no_mangle]
pub extern "C" fn lean_big_mod_exp(
    base: b_lean_obj_arg,
    exponent: b_lean_obj_arg,
    modulus: b_lean_obj_arg,
) -> lean_obj_res {
    let base_b = unsafe { sarray_as_slice(base) };
    let exp_b  = unsafe { sarray_as_slice(exponent) };
    let mod_b  = unsafe { sarray_as_slice(modulus) };
    let out = solana_big_mod_exp::big_mod_exp(base_b, exp_b, mod_b);
    alloc_bytearray(&out)
}

#[no_mangle]
pub extern "C" fn lean_alt_bn128_compression(
    op_id: u64,
    input: b_lean_obj_arg,
) -> lean_obj_res {
    use solana_bn254::compression::prelude::{
        alt_bn128_g1_compress_be, alt_bn128_g1_compress_le, alt_bn128_g1_decompress_be,
        alt_bn128_g1_decompress_le, alt_bn128_g2_compress_be, alt_bn128_g2_compress_le,
        alt_bn128_g2_decompress_be, alt_bn128_g2_decompress_le, ALT_BN128_G1_COMPRESS_BE,
        ALT_BN128_G1_COMPRESS_LE, ALT_BN128_G1_DECOMPRESS_BE, ALT_BN128_G1_DECOMPRESS_LE,
        ALT_BN128_G2_COMPRESS_BE, ALT_BN128_G2_COMPRESS_LE, ALT_BN128_G2_DECOMPRESS_BE,
        ALT_BN128_G2_DECOMPRESS_LE,
    };
    let bytes = unsafe { sarray_as_slice(input) };
    match op_id {
        ALT_BN128_G1_COMPRESS_BE => match alt_bn128_g1_compress_be(bytes) {
            Ok(o) => some_bytearray_slice(&o),
            Err(_) => none_obj(),
        },
        ALT_BN128_G1_COMPRESS_LE => match alt_bn128_g1_compress_le(bytes) {
            Ok(o) => some_bytearray_slice(&o),
            Err(_) => none_obj(),
        },
        ALT_BN128_G1_DECOMPRESS_BE => match alt_bn128_g1_decompress_be(bytes) {
            Ok(o) => some_bytearray_slice(&o),
            Err(_) => none_obj(),
        },
        ALT_BN128_G1_DECOMPRESS_LE => match alt_bn128_g1_decompress_le(bytes) {
            Ok(o) => some_bytearray_slice(&o),
            Err(_) => none_obj(),
        },
        ALT_BN128_G2_COMPRESS_BE => match alt_bn128_g2_compress_be(bytes) {
            Ok(o) => some_bytearray_slice(&o),
            Err(_) => none_obj(),
        },
        ALT_BN128_G2_COMPRESS_LE => match alt_bn128_g2_compress_le(bytes) {
            Ok(o) => some_bytearray_slice(&o),
            Err(_) => none_obj(),
        },
        ALT_BN128_G2_DECOMPRESS_BE => match alt_bn128_g2_decompress_be(bytes) {
            Ok(o) => some_bytearray_slice(&o),
            Err(_) => none_obj(),
        },
        ALT_BN128_G2_DECOMPRESS_LE => match alt_bn128_g2_decompress_le(bytes) {
            Ok(o) => some_bytearray_slice(&o),
            Err(_) => none_obj(),
        },
        _ => none_obj(),
    }
}

#[no_mangle]
pub extern "C" fn lean_poseidon(
    parameters: u8,
    endianness: u8,
    inputs_concat: b_lean_obj_arg,
    n: u64,
) -> lean_obj_res {
    use ark_bn254::Fr;
    use light_poseidon::{Poseidon, PoseidonBytesHasher};

    if n == 0 || n > 12 {
        return none_obj();
    }
    if parameters != 0 {
        return none_obj();
    }
    if endianness > 1 {
        return none_obj();
    }
    let bytes = unsafe { sarray_as_slice(inputs_concat) };
    let expected = (n as usize) * 32;
    if bytes.len() != expected {
        return none_obj();
    }
    let chunks: Vec<&[u8]> = bytes.chunks_exact(32).collect();
    let Ok(mut hasher) = Poseidon::<Fr>::new_circom(n as usize) else {
        return none_obj();
    };
    let result = match endianness {
        0 => hasher.hash_bytes_be(&chunks),
        _ => hasher.hash_bytes_le(&chunks),
    };
    let Ok(hash) = result else {
        return none_obj();
    };
    some_bytearray(&hash)
}

// ───────────────────────────────────────────────────────────────────
// ed25519 strict signature verification (`ed25519-dalek = 2.2.0`).
//
// Used by the ed25519 precompile (`Ed25519SigVerify1111…`). Agave's
// workspace pins ed25519-dalek 1.0.1 and the precompile calls
// `PublicKey::from_bytes(...).verify_strict(msg, &sig)`; the 2.x
// `VerifyingKey::verify_strict` has equivalent semantics for any
// signature/pubkey/message accepted by 1.0.1, so we use 2.x here.
//
// Returns 1 on success, 0 on any failure (invalid pubkey, invalid
// signature length, mathematical verification failure). The Lean side
// surfaces this as a single `r0 := 0 | 1` outcome — the precompile
// doesn't distinguish between failure categories.
// ───────────────────────────────────────────────────────────────────

#[no_mangle]
pub extern "C" fn lean_ed25519_verify_strict(
    pubkey: b_lean_obj_arg,
    sig: b_lean_obj_arg,
    msg: b_lean_obj_arg,
) -> u8 {
    let pubkey_bytes = unsafe { sarray_as_slice(pubkey) };
    let sig_bytes = unsafe { sarray_as_slice(sig) };
    let msg_bytes = unsafe { sarray_as_slice(msg) };

    let Ok(pubkey_arr): Result<[u8; 32], _> = pubkey_bytes.try_into() else {
        return 0;
    };
    let Ok(sig_arr): Result<[u8; 64], _> = sig_bytes.try_into() else {
        return 0;
    };

    let Ok(vk) = ed25519_dalek::VerifyingKey::from_bytes(&pubkey_arr) else {
        return 0;
    };
    let signature = ed25519_dalek::Signature::from_bytes(&sig_arr);

    match vk.verify_strict(msg_bytes, &signature) {
        Ok(()) => 1,
        Err(_) => 0,
    }
}

// ───────────────────────────────────────────────────────────────────
// secp256r1 (NIST P-256) ECDSA verification with low-S enforcement
// (`p256 = 0.13`).
//
// Agave's secp256r1 precompile uses openssl directly + manual range
// checks against the curve order's half (low-S non-malleability). We
// use the pure-Rust `p256` crate and apply the same low-S rule.
//
// Inputs:
//   pubkey: 33-byte compressed point (SEC1 format).
//   sig:    64-byte r || s big-endian integers (P-256 field size = 32).
//   msg:    arbitrary bytes; the verifier internally SHA-256s it.
//
// Returns 1 on success, 0 on any failure: bad input lengths,
// uncompressible pubkey, r/s out of range, signature mismatch, or
// `s > n/2` (rejected per agave).
// ───────────────────────────────────────────────────────────────────

#[no_mangle]
pub extern "C" fn lean_secp256r1_verify(
    pubkey: b_lean_obj_arg,
    sig: b_lean_obj_arg,
    msg: b_lean_obj_arg,
) -> u8 {
    use p256::ecdsa::signature::Verifier;

    let pubkey_bytes = unsafe { sarray_as_slice(pubkey) };
    let sig_bytes = unsafe { sarray_as_slice(sig) };
    let msg_bytes = unsafe { sarray_as_slice(msg) };

    if pubkey_bytes.len() != 33 || sig_bytes.len() != 64 {
        return 0;
    }

    // Parse the signature: P-256 uses 32-byte big-endian r and s.
    let Ok(signature) = p256::ecdsa::Signature::try_from(sig_bytes) else {
        return 0;
    };

    // Reject high-S to mirror agave's manual `s ≤ half_order` check.
    // `normalize_s` returns `Some` when s is in the upper half and
    // would have been rewritten to its low counterpart; we reject
    // outright rather than normalising.
    if signature.normalize_s().is_some() {
        return 0;
    }

    // Parse compressed pubkey + build a verifying key.
    let Ok(vk) = p256::ecdsa::VerifyingKey::from_sec1_bytes(pubkey_bytes) else {
        return 0;
    };

    match vk.verify(msg_bytes, &signature) {
        Ok(()) => 1,
        Err(_) => 0,
    }
}

// ───────────────────────────────────────────────────────────────────
// PC trace hook — target of `SVM/SBPF/Runner.lean`'s `traceStep`
// (`@[extern "lean_qedsvm_trace_step"]`). When `QEDSVM_TRACE_OUT` is
// set, every interpreter step appends one decimal logical PC per line
// to that file (truncated at first use, so each run yields a fresh
// trace). Unset: a single cached-None check, effectively free. This
// is the automated producer of the `.pcs` files `qedlift --trace` and
// `qedrecover --trace` consume; see `scripts/capture_trace.sh`.
// ───────────────────────────────────────────────────────────────────

fn trace_out() -> &'static Option<std::sync::Mutex<std::fs::File>> {
    static TRACE_OUT: std::sync::OnceLock<Option<std::sync::Mutex<std::fs::File>>> =
        std::sync::OnceLock::new();
    TRACE_OUT.get_or_init(|| {
        let path = std::env::var_os("QEDSVM_TRACE_OUT")?;
        match std::fs::File::create(&path) {
            Ok(f) => Some(std::sync::Mutex::new(f)),
            Err(e) => {
                eprintln!(
                    "qedsvm: QEDSVM_TRACE_OUT={}: {} (tracing disabled)",
                    path.to_string_lossy(),
                    e
                );
                None
            }
        }
    })
}

#[no_mangle]
pub extern "C" fn lean_qedsvm_trace_step(pc: usize, f: lean_obj_arg) -> lean_obj_res {
    if let Some(file) = trace_out() {
        use std::io::Write as _;
        if let Ok(mut g) = file.lock() {
            let _ = writeln!(g, "{}", pc);
        }
    }
    unsafe { lean_ffi::lean_apply_unit(f) }
}
