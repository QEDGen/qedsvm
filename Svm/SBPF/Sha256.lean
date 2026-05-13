/-
  SHA-256 (FIPS-180-4).

  Pure-Lean, kernel-reducible 32-byte hash. Used by the `sol_sha256`
  syscall, and (indirectly) by PDA derivation via
  `sol_create_program_address` / `sol_try_find_program_address`.

  The shape mirrors `Svm/SBPF/Murmur3.lean`: a handful of 32-bit
  arithmetic helpers, the round constants, a per-block compression
  function, and a top-level `hash : ByteArray → ByteArray` that returns
  the 32-byte big-endian digest.

  Test vectors at the bottom of the file are checked by `native_decide`.

  References:
  - FIPS-180-4 (NIST), §5 (padding), §6.2.2 (SHA-256 round).
  - Firedancer `src/ballet/sha256/fd_sha256.c`.
  - Agave: `solana-bpf-loader-program/src/syscalls/mod.rs` (`SyscallSha256`).
-/

namespace Svm.SBPF
namespace Sha256

/-! ## Constants -/

def U32 : Nat := 2 ^ 32

/-! ## 32-bit arithmetic helpers -/

@[inline] def wadd (a b : Nat) : Nat := (a + b) % U32

@[inline] def rotr (x r : Nat) : Nat :=
  ((x >>> r) ||| (x <<< (32 - r))) % U32

@[inline] def not32 (x : Nat) : Nat := (U32 - 1) ^^^ x

/-- Initial hash values H₀ (FIPS-180-4 §5.3.3). -/
def H0 : Array Nat := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19 ]

/-- Round constants K[0..63] (FIPS-180-4 §4.2.2). -/
def K : Array Nat := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
  0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
  0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
  0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
  0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
  0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
  0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
  0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
  0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2 ]

/-! ## Byte-array readers -/

@[inline] def byteAt (b : ByteArray) (i : Nat) : Nat := (b.get! i).toNat

/-- Read a 4-byte big-endian U32 from `b` at offset `off`. -/
@[inline] def readU32BE (b : ByteArray) (off : Nat) : Nat :=
  byteAt b off * 0x1000000
  + byteAt b (off + 1) * 0x10000
  + byteAt b (off + 2) * 0x100
  + byteAt b (off + 3)

/-! ## Padding (FIPS-180-4 §5.1.1) -/

/-- Append a single zero byte. -/
@[inline] def pushZero (b : ByteArray) : ByteArray := b.push 0

/-- Encode a Nat in 8-byte big-endian. Only the low 64 bits are emitted. -/
def u64BE (x : Nat) : ByteArray := ⟨#[
  ((x >>> 56) % 256).toUInt8,
  ((x >>> 48) % 256).toUInt8,
  ((x >>> 40) % 256).toUInt8,
  ((x >>> 32) % 256).toUInt8,
  ((x >>> 24) % 256).toUInt8,
  ((x >>> 16) % 256).toUInt8,
  ((x >>> 8) % 256).toUInt8,
  (x % 256).toUInt8 ]⟩

/-- Pad `msg` to a multiple of 64 bytes: append `0x80`, zero-fill, then
    append the original bit-length as an 8-byte big-endian value. -/
def padMessage (msg : ByteArray) : ByteArray :=
  let n := msg.size
  let bits := n * 8
  let zeroPad : Nat := (64 - (n + 9) % 64) % 64
  let withMark : ByteArray := msg.push 0x80
  let withZeros : ByteArray :=
    (List.range zeroPad).foldl (fun acc _ => pushZero acc) withMark
  withZeros ++ u64BE bits

/-! ## Message schedule and compression -/

/-- Compute the 64-word message schedule W for one 64-byte block. -/
def messageSchedule (msg : ByteArray) (blockOff : Nat) : Array Nat :=
  let w0 : Array Nat :=
    (List.range 16).foldl
      (fun a i => a.push (readU32BE msg (blockOff + i * 4))) #[]
  (List.range 48).foldl (fun w i =>
    let t := i + 16
    let w15 := w[t - 15]!
    let w2  := w[t - 2]!
    let s0 := (rotr w15 7) ^^^ (rotr w15 18) ^^^ (w15 >>> 3)
    let s1 := (rotr w2 17) ^^^ (rotr w2 19) ^^^ (w2 >>> 10)
    let new := wadd (wadd (wadd s1 w[t - 7]!) s0) w[t - 16]!
    w.push new) w0

/-- One SHA-256 compression: update hash state `H` from the 64-byte block
    starting at `blockOff` in `msg`. -/
def processBlock (H : Array Nat) (msg : ByteArray) (blockOff : Nat) : Array Nat :=
  let W := messageSchedule msg blockOff
  let a := H[0]!
  let b := H[1]!
  let c := H[2]!
  let d := H[3]!
  let e := H[4]!
  let f := H[5]!
  let g := H[6]!
  let h := H[7]!
  let final := (List.range 64).foldl
    (fun (st : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat) t =>
      let (a, b, c, d, e, f, g, h) := st
      let S1 := (rotr e 6) ^^^ (rotr e 11) ^^^ (rotr e 25)
      let ch := (e &&& f) ^^^ ((not32 e) &&& g)
      let temp1 := wadd (wadd (wadd (wadd h S1) ch) K[t]!) W[t]!
      let S0 := (rotr a 2) ^^^ (rotr a 13) ^^^ (rotr a 22)
      let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
      let temp2 := wadd S0 maj
      (wadd temp1 temp2, a, b, c, wadd d temp1, e, f, g))
    (a, b, c, d, e, f, g, h)
  let (a', b', c', d', e', f', g', h') := final
  #[ wadd H[0]! a',
     wadd H[1]! b',
     wadd H[2]! c',
     wadd H[3]! d',
     wadd H[4]! e',
     wadd H[5]! f',
     wadd H[6]! g',
     wadd H[7]! h' ]

/-- Compress every 64-byte block of the padded message. -/
def processAllBlocks (H : Array Nat) (padded : ByteArray) : Array Nat :=
  let nBlocks := padded.size / 64
  (List.range nBlocks).foldl
    (fun H i => processBlock H padded (i * 64)) H

/-- Encode a u32 in big-endian as 4 bytes. -/
def u32BE (x : Nat) : ByteArray := ⟨#[
  ((x >>> 24) % 256).toUInt8,
  ((x >>> 16) % 256).toUInt8,
  ((x >>> 8) % 256).toUInt8,
  (x % 256).toUInt8 ]⟩

/-- Top-level SHA-256: return the 32-byte big-endian digest of `msg`. -/
def hash (msg : ByteArray) : ByteArray :=
  let padded := padMessage msg
  let H := processAllBlocks H0 padded
  (List.range 8).foldl (fun acc i => acc ++ u32BE H[i]!) ByteArray.empty

/-! ## Test vectors (FIPS-180-4 Appendix B) -/

/-- `sha256("") = e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` -/
example : Sha256.hash ByteArray.empty = ⟨#[
  0xe3, 0xb0, 0xc4, 0x42, 0x98, 0xfc, 0x1c, 0x14,
  0x9a, 0xfb, 0xf4, 0xc8, 0x99, 0x6f, 0xb9, 0x24,
  0x27, 0xae, 0x41, 0xe4, 0x64, 0x9b, 0x93, 0x4c,
  0xa4, 0x95, 0x99, 0x1b, 0x78, 0x52, 0xb8, 0x55 ]⟩ := by native_decide

/-- `sha256("abc") = ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad` -/
example : Sha256.hash ⟨#[0x61, 0x62, 0x63]⟩ = ⟨#[
  0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea,
  0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22, 0x23,
  0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c,
  0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad ]⟩ := by native_decide

/-! ## Agave-conformance audit hook

`hashAgave` calls the same `sha2 = 0.10.8` crate agave's runtime uses
(via `rust-bridge`). Byte-equivalence between `hash` (pure-Lean
FIPS-180-4) and `hashAgave` is verified on a sweep of inputs by Demo
28 in `RunnerDemo.lean`. The production path remains `hash`; this is
a safety net to catch any future divergence. -/
@[extern "lean_sha256_agave"]
opaque hashAgave (data : @& ByteArray) : ByteArray

end Sha256
end Svm.SBPF
