/-
Regression pin for V0 internal-call resolution (soundness-audit H2).

After `R_BPF_64_32` relocation, an internal `call`'s 32-bit immediate is
the Murmur3 hash agave looks up in the function registry
(`Elf.buildFnRegistry`). `Decode.decodeInsn` must:

  1. resolve a registered key to `.call_local <logical PC>` (through the
     slot map), and
  2. FAIL CLOSED on an unknown key — decode to `.call (.unknown _)`,
     whose execution aborts (`Misc.execUnknown`, agave's runtime
     `UnsupportedInstruction`) — rather than the pre-H2 behavior of
     fabricating `.call_local 0` from a bogus slot offset.

These pins lock both directions down at the decode level, plus the
agave-convention hash constants (`pcHash` of a slot = Murmur3 of its 8
LE bytes; `entrypointHash` = Murmur3 of the name "entrypoint"), so a
refactor of `decodeInsn` / `buildFnRegistry` / `Murmur3` that broke
fail-closed resolution fails the `Examples` build immediately.
-/
import SVM.SBPF.Decode
import SVM.SBPF.Elf

namespace Examples.H2Pin
open SVM.SBPF

/-- One `0x85` call instruction whose imm (bytes 4..7, little-endian) is
    `imm`. `dst`/`src`/`off` are zero. -/
def callInsnBytes (imm : Nat) : ByteArray :=
  ⟨#[0x85, 0x00, 0x00, 0x00,
     UInt8.ofNat (imm % 256),
     UInt8.ofNat (imm / 0x100 % 256),
     UInt8.ofNat (imm / 0x10000 % 256),
     UInt8.ofNat (imm / 0x1000000 % 256)]⟩

/-- A value that is neither a syscall hash nor a registry key. (Real
    murmur3 keys are large; `0x55` collides with nothing.) -/
def unknownKey : Nat := 0x55

/-! ## Fail-closed on an unknown key (the core H2 guarantee) -/

/-- An internal call with no matching registry entry decodes to the
    fail-closed `.call (.unknown _)`, NOT a fabricated `.call_local`. -/
theorem unknown_call_fails_closed :
    Decode.decodeInsn (callInsnBytes unknownKey) #[0] 0 [] =
      some (.call (.unknown unknownKey), 8) := by
  native_decide

/-- Even with a NON-MATCHING registry, an unknown key still fails closed
    (the lookup misses, no spurious `.call_local`). -/
theorem unknown_call_fails_closed_with_other_entries :
    Decode.decodeInsn (callInsnBytes unknownKey) #[0] 0 [(999, 0), (1234, 0)] =
      some (.call (.unknown unknownKey), 8) := by
  native_decide

/-! ## Resolution of a registered key -/

/-- A registered key resolves to `.call_local <slotMap[slot]>`. Here the
    registry maps `unknownKey → slot 0`, and `slotMap[0] = 0`. -/
theorem registered_call_resolves :
    Decode.decodeInsn (callInsnBytes unknownKey) #[0, 1, 2] 0 [(unknownKey, 2)] =
      some (.call_local 2, 8) := by
  native_decide

/-- A registered key whose target slot is past the slot map fails the
    decode (the loader guarantees in-text targets, so this is malformed
    input — fail closed, not a fabricated PC). -/
theorem registered_call_out_of_range_fails_decode :
    Decode.decodeInsn (callInsnBytes unknownKey) #[0] 0 [(unknownKey, 9)] = none := by
  native_decide

/-! ## agave hash-convention constants -/

/-- The bpf-to-bpf key is Murmur3-32 of the target slot's 8 LE bytes
    (`register_function_hashed_legacy`, the V0 path). Cross-checked
    against `solana_sbpf::ebpf::hash_symbol_name(&slot.to_le_bytes())`. -/
theorem pcHash_slot0 : Elf.pcHash 0 = 1669671676 := by native_decide
theorem pcHash_slot4 : Elf.pcHash 4 = 3491892518 := by native_decide

/-- The entrypoint keys by the hash of the literal name, not its PC.
    (In `counter_with_helper` this is the key for the entry slot 4.) -/
theorem entrypointHash_pin : Elf.entrypointHash = 1910755201 := by native_decide

end Examples.H2Pin
