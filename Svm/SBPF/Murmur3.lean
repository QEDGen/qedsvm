/-
  Murmur3-32 hash function (Austin Appleby, standard variant).

  Solana uses the standard 32-bit Murmur3 with seed 0 to derive syscall
  identifiers from their names: the 32-bit immediate of a `call`
  instruction is `Murmur3::hash32(b"sol_log_", 0)` (for example).

  This implementation is a pure Lean function — kernel-reducible, so
  `native_decide` evaluates it during proof checking. Each hash is
  precomputed once and stored as a `def` so the decoder doesn't pay
  the hash cost per `call` it sees.
-/

namespace Svm.SBPF
namespace Murmur3

/-! ## Constants -/

def U32 : Nat := 2 ^ 32
def C1 : Nat := 0xcc9e2d51
def C2 : Nat := 0x1b873593

/-! ## 32-bit arithmetic helpers -/

@[inline] def wmul (a b : Nat) : Nat := (a * b) % U32

@[inline] def rol (x r : Nat) : Nat :=
  ((x <<< r) ||| (x >>> (32 - r))) % U32

/-! ## Mixing functions -/

/-- Mix one 32-bit chunk into the running hash. -/
def mixChunk (h k : Nat) : Nat :=
  let k1 := wmul k C1
  let k2 := rol k1 15
  let k3 := wmul k2 C2
  let h1 := h ^^^ k3
  let h2 := rol h1 13
  (wmul h2 5 + 0xe6546b64) % U32

/-- Mix the trailing 1–3 bytes (packed as a partial U32). -/
def mixTail (h k : Nat) : Nat :=
  let k1 := wmul k C1
  let k2 := rol k1 15
  let k3 := wmul k2 C2
  h ^^^ k3

/-- The Murmur3 finalization mix. -/
def finalize (h len : Nat) : Nat :=
  let h0 := h ^^^ len
  let h1 := h0 ^^^ (h0 >>> 16)
  let h2 := wmul h1 0x85ebca6b
  let h3 := h2 ^^^ (h2 >>> 13)
  let h4 := wmul h3 0xc2b2ae35
  h4 ^^^ (h4 >>> 16)

/-! ## Byte-array readers -/

@[inline] def byteAt (bytes : ByteArray) (off : Nat) : Nat :=
  (bytes.get! off).toNat

/-- Read a 4-byte little-endian U32. -/
@[inline] def readU32LE (bytes : ByteArray) (off : Nat) : Nat :=
  byteAt bytes off
  + byteAt bytes (off + 1) * 0x100
  + byteAt bytes (off + 2) * 0x10000
  + byteAt bytes (off + 3) * 0x1000000

/-! ## Body + tail processing -/

/-- Process the 4-byte body chunks of the input. -/
def processBody (bytes : ByteArray) (seed : Nat) : Nat :=
  (List.range (bytes.size / 4)).foldl
    (fun h i => mixChunk h (readU32LE bytes (i * 4)))
    seed

/-- Pack the trailing 0–3 bytes into a partial U32 and mix into the hash. -/
def processTail (bytes : ByteArray) (h : Nat) : Nat :=
  let bodyLen := (bytes.size / 4) * 4
  let tailLen := bytes.size - bodyLen
  match tailLen with
  | 0 => h
  | 1 => mixTail h (byteAt bytes bodyLen)
  | 2 =>
    let k := byteAt bytes bodyLen
            + byteAt bytes (bodyLen + 1) * 0x100
    mixTail h k
  | _ =>
    let k := byteAt bytes bodyLen
            + byteAt bytes (bodyLen + 1) * 0x100
            + byteAt bytes (bodyLen + 2) * 0x10000
    mixTail h k

/-! ## Top-level hash -/

/-- 32-bit Murmur3 hash of `bytes` with the given seed (default 0). -/
def hash (bytes : ByteArray) (seed : Nat := 0) : Nat :=
  let h0 := seed
  let h1 := processBody bytes h0
  let h2 := processTail bytes h1
  finalize h2 bytes.size

/-- Hash a `String` (encoded as UTF-8). -/
@[inline] def hashString (s : String) (seed : Nat := 0) : Nat :=
  hash s.toUTF8 seed

end Murmur3
end Svm.SBPF
