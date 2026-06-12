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

/-! ## End-to-end loader pin: `Elf.buildFnRegistry` on a real `.so`

The pins above exercise `decodeInsn` against a *hand-built* registry and
pin the hash constants. They do NOT exercise `Elf.buildFnRegistry` (the
runtime-loader path used by `runElf`/`run`/CPI) on a real ELF — the
shipped lifts decode with the qedlift-EMITTED (solana-sbpf ground-truth)
registry, leaving `buildFnRegistry`'s own assembly unanchored. These two
pins close that: they run the WHOLE Lean loader on the real
`counter_with_helper.so` and check both the registry it builds and that
the pipeline resolves the internal `call` to the right `.call_local`. -/

/-- The full `counter_with_helper.so` (1144 bytes). Its `.text` carries one
    bpf-to-bpf `call -1` resolved by an `R_BPF_64_32` relocation against the
    defined function `increment_by` (slot 0); the entrypoint is slot 4. So
    this fixture exercises both `buildFnRegistry` registry-producing paths:
    the entrypoint derivation and `rel32KeyEntry` for a defined function. -/
def counterWithHelperSo : ByteArray := Decode.bytesOfHex
  "7f454c46020101000000000000000000030007010100000040010000000000004000000000000000b80200000000000000000000400038000300400007000600010000000500000020010000000000002001000000000000200100000000000048000000000000004800000000000000001000000000000001000000040000000802000000000000080200000000000008020000000000007800000000000000780000000000000000100000000000000200000006000000680100000000000068010000000000006801000000000000a000000000000000a0000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000079130000000000000f230000000000007b3100000000000095000000000000007912000000000000070100000800000085100000ffffffffb70000000000000095000000000000001e000000000000000400000000000000110000000000000070020000000000001200000000000000100000000000000013000000000000001000000000000000060000000000000008020000000000000b000000000000001800000000000000050000000000000050020000000000000a00000000000000190000000000000016000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000012000100400100000000000028000000000000000c000000120001002001000000000000200000000000000000656e747279706f696e7400696e6372656d656e745f6279000000000000000050010000000000000a00000002000000002e74657874002e64796e737472002e72656c2e64796e002e64796e73796d002e64796e616d6963002e736873747274616200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000100000006000000000000002001000000000000200100000000000048000000000000000000000000000000080000000000000000000000000000002000000006000000030000000000000068010000000000006801000000000000a000000000000000040000000000000008000000000000001000000000000000180000000b0000000200000000000000080200000000000008020000000000004800000000000000040000000100000008000000000000001800000000000000070000000300000002000000000000005002000000000000500200000000000019000000000000000000000000000000010000000000000000000000000000000f00000009000000020000000000000070020000000000007002000000000000100000000000000003000000000000000800000000000000100000000000000029000000030000000000000000000000000000000000000080020000000000003300000000000000000000000000000001000000000000000000000000000000"

/-- The decoded `.text` of `counter_with_helper.so` (inlined from the lift,
    kept independent of regeneration). The `.call_local 0` is the internal
    call resolved through the registry. -/
def counterWithHelperInsns : Array Insn := #[
  .ldx .dword .r3 .r1 0,
  .add64 .r3 (.reg .r2),
  .stx .dword .r1 0 .r3,
  .exit,
  .ldx .dword .r2 .r1 0,
  .add64 .r1 (.imm (8)),
  .call_local 0,
  .mov64 .r0 (.imm (0)),
  .exit]

/-- `Elf.buildFnRegistry` run on the real `.so` produces the (key → slot)
    mapping solana-sbpf builds: the entrypoint (`entrypointHash → 4`,
    registered FIRST for first-match precedence) and the rel32 defined
    function `increment_by` (`pcHash 0 → 0`). This is the qedlift-emitted
    `CounterWithHelperFnRegistry = [(1669671676, 0), (1910755201, 4)]`
    reordered (entrypoint-first; the keys are distinct so first-match
    lookup is order-independent). -/
theorem buildFnRegistry_on_real_so :
    (do
      let h ← Elf.parseHeader counterWithHelperSo
      let ts ← Elf.findSection counterWithHelperSo h Elf.textName
      let raw := Elf.extractSection counterWithHelperSo ts
      pure (Elf.buildFnRegistry counterWithHelperSo h ts.addr raw))
      = some [(1910755201, 4), (1669671676, 0)] := by native_decide

/-- The whole Lean loader pipeline (parseHeader → applyRelocations →
    buildFnRegistry → decodeProgram) run on the real `.so` resolves the
    internal `call` to `.call_local 0` — the SAME instruction array the
    qedlift lift pins with the solana-sbpf-emitted registry
    (`CounterWithHelper_decodes`). So `Elf.buildFnRegistry` is now anchored
    to ground truth, not merely code-reviewed. -/
theorem loader_pipeline_resolves_internal_call :
    (do
      let h ← Elf.parseHeader counterWithHelperSo
      let ts ← Elf.findSection counterWithHelperSo h Elf.textName
      let raw := Elf.extractSection counterWithHelperSo ts
      let text := Elf.applyRelocations counterWithHelperSo h ts.addr raw
      let reg := Elf.buildFnRegistry counterWithHelperSo h ts.addr raw
      Decode.decodeProgram text reg)
      = some counterWithHelperInsns := by native_decide

end Examples.H2Pin
