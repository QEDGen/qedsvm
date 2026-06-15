/-
Regression pins for soundness-audit H2: V0 internal-call resolution.

`Decode.decodeInsn` must (1) resolve a registered Murmur3 key to `.call_local <PC>` and
(2) FAIL CLOSED on unknown keys → `.call (.unknown _)` (aborts via `Misc.execUnknown`),
not the pre-H2 fabricated `.call_local 0`. Pins also lock the agave-convention hash
constants so any drift in Murmur3/buildFnRegistry fails the Examples build immediately.
-/
import SVM.SBPF.Decode
import SVM.SBPF.Elf

namespace Examples.H2Pin
open SVM.SBPF

/-- Single `0x85` call insn with `imm` in bytes 4..7 LE; dst/src/off = 0. -/
def callInsnBytes (imm : Nat) : ByteArray :=
  ⟨#[0x85, 0x00, 0x00, 0x00,
     UInt8.ofNat (imm % 256),
     UInt8.ofNat (imm / 0x100 % 256),
     UInt8.ofNat (imm / 0x10000 % 256),
     UInt8.ofNat (imm / 0x1000000 % 256)]⟩

/-- A value that is neither a syscall hash nor a real registry key. -/
def unknownKey : Nat := 0x55

/-! ## Fail-closed on an unknown key (the core H2 guarantee) -/

/-- Unknown key → fail-closed `.call (.unknown _)`, not a fabricated `.call_local`. -/
theorem unknown_call_fails_closed :
    Decode.decodeInsn (callInsnBytes unknownKey) #[0] 0 [] =
      some (.call (.unknown unknownKey), 8) := by
  native_decide

/-- Non-matching registry: lookup misses → still fail-closed. -/
theorem unknown_call_fails_closed_with_other_entries :
    Decode.decodeInsn (callInsnBytes unknownKey) #[0] 0 [(999, 0), (1234, 0)] =
      some (.call (.unknown unknownKey), 8) := by
  native_decide

/-! ## Resolution of a registered key -/

/-- Registered key resolves to `.call_local <slotMap[slot]>`. -/
theorem registered_call_resolves :
    Decode.decodeInsn (callInsnBytes unknownKey) #[0, 1, 2] 0 [(unknownKey, 2)] =
      some (.call_local 2, 8) := by
  native_decide

/-- Key targeting an out-of-range slot: decode fails (malformed input; fail-closed). -/
theorem registered_call_out_of_range_fails_decode :
    Decode.decodeInsn (callInsnBytes unknownKey) #[0] 0 [(unknownKey, 9)] = none := by
  native_decide

/-! ## agave hash-convention constants -/

/-- bpf-to-bpf key = Murmur3-32 of slot's 8 LE bytes (V0 path). Cross-checked
    against `solana_sbpf::ebpf::hash_symbol_name`. -/
theorem pcHash_slot0 : Elf.pcHash 0 = 1669671676 := by native_decide
theorem pcHash_slot4 : Elf.pcHash 4 = 3491892518 := by native_decide

/-- Entrypoint keys by hash of the literal name "entrypoint", not its PC. -/
theorem entrypointHash_pin : Elf.entrypointHash = 1910755201 := by native_decide

/-! ## End-to-end loader pin: `Elf.buildFnRegistry` on a real `.so`

Prior pins only exercised `decodeInsn` with a hand-built registry; `buildFnRegistry`'s
own logic was unanchored. These pins run the whole Lean loader on `counter_with_helper.so`
and verify both the built registry and that the call resolves to the right `.call_local`. -/

/-- `counter_with_helper.so` (1144 bytes): one bpf-to-bpf `call -1` resolved by
    `R_BPF_64_32` against `increment_by` (slot 0); entrypoint at slot 4.
    Exercises both `buildFnRegistry` paths: entrypoint derivation + `rel32KeyEntry`. -/
def counterWithHelperSo : ByteArray := Decode.bytesOfHex
  "7f454c46020101000000000000000000030007010100000040010000000000004000000000000000b80200000000000000000000400038000300400007000600010000000500000020010000000000002001000000000000200100000000000048000000000000004800000000000000001000000000000001000000040000000802000000000000080200000000000008020000000000007800000000000000780000000000000000100000000000000200000006000000680100000000000068010000000000006801000000000000a000000000000000a0000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000079130000000000000f230000000000007b3100000000000095000000000000007912000000000000070100000800000085100000ffffffffb70000000000000095000000000000001e000000000000000400000000000000110000000000000070020000000000001200000000000000100000000000000013000000000000001000000000000000060000000000000008020000000000000b000000000000001800000000000000050000000000000050020000000000000a00000000000000190000000000000016000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000012000100400100000000000028000000000000000c000000120001002001000000000000200000000000000000656e747279706f696e7400696e6372656d656e745f6279000000000000000050010000000000000a00000002000000002e74657874002e64796e737472002e72656c2e64796e002e64796e73796d002e64796e616d6963002e736873747274616200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000100000006000000000000002001000000000000200100000000000048000000000000000000000000000000080000000000000000000000000000002000000006000000030000000000000068010000000000006801000000000000a000000000000000040000000000000008000000000000001000000000000000180000000b0000000200000000000000080200000000000008020000000000004800000000000000040000000100000008000000000000001800000000000000070000000300000002000000000000005002000000000000500200000000000019000000000000000000000000000000010000000000000000000000000000000f00000009000000020000000000000070020000000000007002000000000000100000000000000003000000000000000800000000000000100000000000000029000000030000000000000000000000000000000000000080020000000000003300000000000000000000000000000001000000000000000000000000000000"

/-- Decoded `.text` of `counter_with_helper.so` (inlined, independent of regeneration). -/
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

/-- `buildFnRegistry` on the real `.so` gives entrypoint-first (first-match precedence)
    + `increment_by`; matches qedlift-emitted registry modulo ordering. -/
theorem buildFnRegistry_on_real_so :
    (do
      let h ← Elf.parseHeader counterWithHelperSo
      let ts ← Elf.findSection counterWithHelperSo h Elf.textName
      let raw := Elf.extractSection counterWithHelperSo ts
      pure (Elf.buildFnRegistry counterWithHelperSo h ts.addr raw))
      = some [(1910755201, 4), (1669671676, 0)] := by native_decide

/-- Full loader pipeline on the real `.so` resolves the internal call to `.call_local 0`,
    matching the qedlift-pinned array. `Elf.buildFnRegistry` anchored to ground truth. -/
theorem loader_pipeline_resolves_internal_call :
    (do
      let h ← Elf.parseHeader counterWithHelperSo
      let ts ← Elf.findSection counterWithHelperSo h Elf.textName
      let raw := Elf.extractSection counterWithHelperSo ts
      let text := Elf.applyRelocations counterWithHelperSo h ts.addr raw
      let reg := Elf.buildFnRegistry counterWithHelperSo h ts.addr raw
      Decode.decodeProgram text reg)
      = some counterWithHelperInsns := by native_decide

/-! ## Registry collision gate (H2 residual)

`registryCollisionFree` mirrors agave's `SymbolHashCollision` rejection. Real collisions
need murmur3 preimages, so pins test the predicate directly + the real binary's registry. -/

/-- Same key, different targets: collision detected. -/
theorem collision_detected :
    Elf.registryCollisionFree [(5, 1), (5, 2)] = false := by native_decide

/-- Exact duplicate pairs are not collisions (same key+target registered multiple times). -/
theorem duplicate_pair_ok :
    Elf.registryCollisionFree [(5, 1), (5, 1), (7, 2)] = true := by native_decide

/-- `entrypointHash` exempt: agave re-registers from `e_entry` (elf.rs:637-643),
    so a mismatch resolves by e_entry precedence, not a collision. -/
theorem entrypoint_key_exempt :
    Elf.registryCollisionFree [(Elf.entrypointHash, 4), (Elf.entrypointHash, 0)]
      = true := by native_decide

/-- Collision behind the entrypoint pair is still detected. -/
theorem collision_behind_entrypoint_detected :
    Elf.registryCollisionFree [(Elf.entrypointHash, 4), (5, 1), (5, 2)]
      = false := by native_decide

/-- The real binary's registry is collision-free (`runElf` accepts it). -/
theorem real_registry_collision_free :
    (do
      let h ← Elf.parseHeader counterWithHelperSo
      let ts ← Elf.findSection counterWithHelperSo h Elf.textName
      let raw := Elf.extractSection counterWithHelperSo ts
      pure (Elf.registryCollisionFree
        (Elf.buildFnRegistry counterWithHelperSo h ts.addr raw)))
      = some true := by native_decide

end Examples.H2Pin
