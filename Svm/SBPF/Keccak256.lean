/-
  Keccak-256 (original Keccak, not FIPS-202 SHA-3).

  Solana uses original Keccak with 0x01 padding (vs SHA-3's 0x06). The
  implementation lives in C at `csrc/keccak256.c` and is called via
  `@[extern]`. The `opaque` Lean side means proof-time reasoning treats
  the hash as a black box; runtime (compiled + `native_decide`) uses the
  C implementation.

  We deliberately do **not** ship a pure-Lean spec here. Verification of
  Keccak's algebraic properties is downstream work — likely its own
  project — and shouldn't gate the runner.

  Wired to the `.sol_keccak256` syscall in `Execute.lean`.
-/

namespace Svm.SBPF
namespace Keccak256

/-- Keccak-256 of `data`, returning a 32-byte big-endian-of-state digest.

    Implemented in C (`csrc/keccak256.c`). Treated as opaque to the kernel:
    `decide` cannot reduce it, but `native_decide` will (via `ofReduceBool`,
    the same axiom already in use elsewhere). -/
@[extern "lean_keccak256"]
opaque hash (data : @& ByteArray) : ByteArray

/-- Agave-conformance audit hook. Calls `sha3::Keccak256` from the
    `sha3 = 0.10.8` crate (the same crate agave's
    `solana-keccak-hasher` wraps) via `rust-bridge`. Byte-equivalence
    with `hash` is verified by Demo 28 in `RunnerDemo.lean`. -/
@[extern "lean_keccak256_agave"]
opaque hashAgave (data : @& ByteArray) : ByteArray

end Keccak256
end Svm.SBPF
