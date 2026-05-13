//! Rust bridge for formal-svm's crypto syscalls.
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
// `sha2` feature. Production path for `Svm.SBPF.Sha512.hash`.
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
