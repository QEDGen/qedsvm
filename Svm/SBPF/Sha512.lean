/-
  SHA-512 (FIPS-180-4, 64-byte output).

  Backed by `rust-bridge` calling `sha2 = 0.10.8` — the same crate
  agave's `solana-sha512-hasher` wraps with the `sha2` feature.
  The `opaque` Lean side treats the hash as a black box at proof
  time; `native_decide` reduces it via `ofReduceBool`.

  Wired to the `.sol_sha512` syscall in `Execute.lean`.
-/

namespace Svm.SBPF
namespace Sha512

/-- SHA-512 of `data`, returning the 64-byte digest.

    Implemented in Rust (`rust-bridge`) calling `sha2::Sha512::digest`. -/
@[extern "lean_sha512"]
opaque hash (data : @& ByteArray) : ByteArray

end Sha512
end Svm.SBPF
