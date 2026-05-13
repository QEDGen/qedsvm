/-
  BLAKE3 (sequential reference, default hashing mode, 32-byte output).

  The implementation lives in C at `csrc/blake3.c` and is called via
  `@[extern]`. The `opaque` Lean side means proof-time reasoning treats
  the hash as a black box; runtime (compiled + `native_decide`) uses the
  C implementation.

  We deliberately do **not** ship a pure-Lean spec here. Verification of
  BLAKE3's tree / compression structure is downstream work — likely its
  own project — and shouldn't gate the runner.

  Wired to the `.sol_blake3` syscall in `Execute.lean`.
-/

namespace Svm.SBPF
namespace Blake3

/-- BLAKE3 of `data`, returning a 32-byte digest.

    Implemented in C (`csrc/blake3.c`). Treated as opaque to the kernel:
    `decide` cannot reduce it, but `native_decide` will (via `ofReduceBool`,
    the same axiom already in use elsewhere). -/
@[extern "lean_blake3"]
opaque hash (data : @& ByteArray) : ByteArray

end Blake3
end Svm.SBPF
