/-
  Worked example: hand-encoded byte_increment program → Lean spec on
  `Runner.run` output. The first end-to-end "raw bytecode satisfies Q"
  theorem in the repo.

  The program reads one byte from r1's memory address, increments it,
  writes it back, and exits. Encoded directly as sBPF bytes so the
  proof chain is:

      byteIncrementBytes  →  Decode.decodeProgram (= some [4 insns])
                          →  byte_increment_macro_spec
                          →  run_reaches_spec
                          →  Q.holdsFor (executeFn .. k)

  The witness state at pc=3 has the post-condition Q from the macro
  spec; this is the assertion that the byte at the input address has
  been incremented modulo 256.
-/

import Svm.SBPF.RunnerBridge
import Svm.SBPF.MacroDemo

namespace Svm.SBPF.Demo

open Svm.SBPF
open Svm.SBPF.Runner
open Memory

/-- Hand-encoded sBPF bytecode for byte_increment. Four 8-byte slots:

    `pc=0  ldx .byte .r2 .r1 0`   → `71 12 00 00 00 00 00 00`
    `pc=1  add64 .r2 (.imm 1)`    → `07 02 00 00 01 00 00 00`
    `pc=2  stx .byte .r1 0 .r2`   → `73 21 00 00 00 00 00 00`
    `pc=3  exit`                  → `95 00 00 00 00 00 00 00`

    Encoding follows `Svm.SBPF.Decode.decodeInsn`:
    `opcode | (src<<4 | dst) | off16 LE | imm32 LE`. -/
def byteIncrementBytes : ByteArray :=
  ⟨#[ 0x71, 0x12, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x07, 0x02, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00,
      0x73, 0x21, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x95, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 ]⟩

/-- The four decoded instructions. -/
def byteIncrementInsns : Array Insn :=
  #[ .ldx .byte .r2 .r1 0,
     .add64 .r2 (.imm 1),
     .stx .byte .r1 0 .r2,
     .exit ]

/-- Decoding the bytes yields exactly the expected instruction array. -/
theorem byteIncrement_decodes :
    Decode.decodeProgram byteIncrementBytes = some byteIncrementInsns := by
  native_decide

/-- The program contains no CPI-call instructions, so the spec-level
    `executeFn` agrees with `Runner.run`'s `executeFnCpi` (via
    `executeFnCpi_eq_executeFn_of_no_cpi_array`). -/
theorem byteIncrement_noCpi :
    ∀ i, i ∈ byteIncrementInsns → Insn.isCpiCall i = false := by
  intro i hi
  rcases Array.mem_iff_getElem.mp hi with ⟨j, hj, hjeq⟩
  have hj4 : j < 4 := by simp [byteIncrementInsns] at hj; exact hj
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;>
    (simp [byteIncrementInsns] at hjeq; subst hjeq; rfl)

/-- The macro-spec's CodeReq is satisfied by `fetchFromArray byteIncrementInsns`. -/
theorem byteIncrement_cr_satisfied :
    (((CodeReq.singleton 0 (.ldx .byte .r2 .r1 0)).union
      (CodeReq.singleton 1 (.add64 .r2 (.imm 1)))).union
     (CodeReq.singleton 2 (.stx .byte .r1 0 .r2))).SatisfiedBy
       (fetchFromArray byteIncrementInsns) := by
  intro a i hpin
  match a with
  | 0 =>
    simp [CodeReq.union, CodeReq.singleton] at hpin
    subst hpin
    unfold fetchFromArray; simp [byteIncrementInsns]
  | 1 =>
    simp [CodeReq.union, CodeReq.singleton] at hpin
    subst hpin
    unfold fetchFromArray; simp [byteIncrementInsns]
  | 2 =>
    simp [CodeReq.union, CodeReq.singleton] at hpin
    subst hpin
    unfold fetchFromArray; simp [byteIncrementInsns]
  | _ + 3 =>
    simp [CodeReq.union, CodeReq.singleton] at hpin

/-! ## End-to-end lift

Two theorems compose the bridge:

1. `byteIncrement_run_is_executeFn` — the structural fact that
   `Runner.run` on this bytecode equals `executeFn` over its decoded
   form. Doesn't reference any spec.

2. `byteIncrement_macro_witness` — the spec fact: in the pure
   `executeFn` trace from `Runner.initialState cfg`, a k ≤ 3 witness
   state satisfies `byte_increment_macro_spec`'s post-condition.

Composed, these say: bytecode `byteIncrementBytes` executed by
`Runner.run` agrees, on its first ≤ 3 instructions, with the Lean spec
for byte_increment. This is the first end-to-end "raw bytes → Lean
spec" theorem in the repo. -/

/-- Structural bridge: `Runner.run byteIncrementBytes cfg` is the
    decoded `byteIncrementInsns` array executed under the pure
    `executeFn` stepper. No spec involved. -/
theorem byteIncrement_run_is_executeFn (cfg : RunConfig) :
    Runner.run byteIncrementBytes cfg = some
      (executeFn (fetchFromArray byteIncrementInsns)
                 (Runner.initialState cfg) cfg.cuBudget) := by
  unfold Runner.run
  rw [byteIncrement_decodes]
  -- Goal: Option.bind (some byteIncrementInsns) (fun insns => some (executeFnCpi ...)) = some (executeFn ...)
  -- Lean kernel reduces `Option.bind (some _) _` via iota; then we need
  -- executeFnCpi = executeFn under noCpi.
  exact congrArg some
    (executeFnCpi_eq_executeFn_of_no_cpi_array
      cfg.programRegistry byteIncrementInsns
      (Runner.initialState cfg) cfg.cuBudget byteIncrement_noCpi)

/-- Spec witness: applying `byte_increment_macro_spec` (via the
    standard `cuTripleWithinMem.toExec` bridge) to the executeFn trace
    from `Runner.initialState cfg`. Given a state that satisfies the
    pre-condition (r2 = vR2Old, r1 = baseAddr, mem[baseAddr] = oldByte)
    and the region requirements, produces a k ≤ 3 witness where the
    post-condition holds.

    The pre-condition `hP` and region condition `hregions` are passed
    in by the caller because they depend on `cfg.input` and the
    specific `baseAddr` the caller chooses. -/
theorem byteIncrement_macro_witness
    (cfg : RunConfig) (baseAddr vR2Old oldByte : Nat)
    (hP : ((.r2 ↦ᵣ vR2Old) ** (.r1 ↦ᵣ baseAddr) **
            (effectiveAddr baseAddr 0 ↦ₘ oldByte)).holdsFor
            (Runner.initialState cfg))
    (hregions :
        (Runner.initialState cfg).regions.containsRange
          (effectiveAddr baseAddr 0) 1 = true ∧
        (Runner.initialState cfg).regions.containsWritable
          (effectiveAddr baseAddr 0) 1 = true) :
    ∃ k, k ≤ 3 ∧
      let sk := executeFn (fetchFromArray byteIncrementInsns)
                          (Runner.initialState cfg) k
      sk.pc = 3 ∧
      sk.exitCode = none ∧
      ((.r2 ↦ᵣ wrapAdd (oldByte % 256) (toU64 1)) ** (.r1 ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr 0 ↦ₘ
          (wrapAdd (oldByte % 256) (toU64 1) % 256))).holdsFor sk := by
  exact (byte_increment_macro_spec baseAddr vR2Old oldByte).toExec
    byteIncrement_cr_satisfied hP
    (Runner.initialState_pc cfg)
    (Runner.initialState_exitCode cfg)
    hregions

/-! ## Session 3b: LLVM-compiled .so demo

The byte sequence below is the `.text` section content of
`formal-svm-rs/tests/fixtures/byte_increment.so`, produced by
`cargo-build-sbf` from `byte_increment_src/`. LLVM emits 5
instructions: the same 3-instruction byte_increment macro, plus
`mov r0, 0` (set return value) and `exit`.

This demonstrates the same theorem chain as Session 3a, but the
bytes are LLVM output rather than hand-encoded — i.e. it works on
*compiled* output of a real Rust program. The first 3 instructions
exactly match `byteIncrementInsns[0..3]`, so the macro spec applies
unchanged.

The Rust source is:
```rust
#[no_mangle]
pub extern "C" fn entrypoint(input: *mut u8) -> u64 {
    unsafe {
        let b = core::ptr::read(input);
        core::ptr::write(input, b.wrapping_add(1));
    }
    0
}
```

To verify this byte sequence stays in sync with `byte_increment.so`:
```sh
cd formal-svm-rs/tests/fixtures/byte_increment_src && cargo-build-sbf
xxd -s 0x120 -l 40 ../byte_increment.so
``` -/

/-- LLVM-emitted `.text` from `byte_increment.so`. Five 8-byte slots. -/
def byteIncrementSoText : ByteArray :=
  ⟨#[ 0x71, 0x12, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- ldx byte r2, r1, 0
      0x07, 0x02, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00,   -- add64 r2, 1
      0x73, 0x21, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- stx byte r1, 0, r2
      0xb7, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- mov64 r0, 0
      0x95, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 ]⟩ -- exit

/-- Decoded form of `byteIncrementSoText`: the 3 macro insns + return + exit. -/
def byteIncrementSoInsns : Array Insn :=
  #[ .ldx .byte .r2 .r1 0,
     .add64 .r2 (.imm 1),
     .stx .byte .r1 0 .r2,
     .mov64 .r0 (.imm 0),
     .exit ]

theorem byteIncrementSo_decodes :
    Decode.decodeProgram byteIncrementSoText = some byteIncrementSoInsns := by
  native_decide

theorem byteIncrementSo_noCpi :
    ∀ i, i ∈ byteIncrementSoInsns → Insn.isCpiCall i = false := by
  intro i hi
  rcases Array.mem_iff_getElem.mp hi with ⟨j, hj, hjeq⟩
  have hj5 : j < 5 := by simp [byteIncrementSoInsns] at hj; exact hj
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;>
    (simp [byteIncrementSoInsns] at hjeq; subst hjeq; rfl)

/-- The macro-spec's 3-singleton CodeReq is satisfied by
    `fetchFromArray byteIncrementSoInsns`. Same shape as
    `byteIncrement_cr_satisfied` for Session 3a — the .text just has
    two additional instructions after the macro range, which the cr
    doesn't pin. -/
theorem byteIncrementSo_cr_satisfied :
    (((CodeReq.singleton 0 (.ldx .byte .r2 .r1 0)).union
      (CodeReq.singleton 1 (.add64 .r2 (.imm 1)))).union
     (CodeReq.singleton 2 (.stx .byte .r1 0 .r2))).SatisfiedBy
       (fetchFromArray byteIncrementSoInsns) := by
  intro a i hpin
  match a with
  | 0 =>
    simp [CodeReq.union, CodeReq.singleton] at hpin
    subst hpin; unfold fetchFromArray; simp [byteIncrementSoInsns]
  | 1 =>
    simp [CodeReq.union, CodeReq.singleton] at hpin
    subst hpin; unfold fetchFromArray; simp [byteIncrementSoInsns]
  | 2 =>
    simp [CodeReq.union, CodeReq.singleton] at hpin
    subst hpin; unfold fetchFromArray; simp [byteIncrementSoInsns]
  | _ + 3 =>
    simp [CodeReq.union, CodeReq.singleton] at hpin

/-- Structural bridge for the LLVM-compiled .text: `Runner.run` on
    `byteIncrementSoText` agrees with the pure `executeFn` of the
    decoded array. Identical proof shape to
    `byteIncrement_run_is_executeFn` — only the bytes and the insn
    array change. -/
theorem byteIncrementSo_run_is_executeFn (cfg : RunConfig) :
    Runner.run byteIncrementSoText cfg = some
      (executeFn (fetchFromArray byteIncrementSoInsns)
                 (Runner.initialState cfg) cfg.cuBudget) := by
  unfold Runner.run
  rw [byteIncrementSo_decodes]
  exact congrArg some
    (executeFnCpi_eq_executeFn_of_no_cpi_array
      cfg.programRegistry byteIncrementSoInsns
      (Runner.initialState cfg) cfg.cuBudget byteIncrementSo_noCpi)

/-- Spec witness for the LLVM-compiled program: the macro spec
    produces a k ≤ 3 witness inside the executeFn trace. The 4th
    instruction (`mov r0, 0`) is beyond pc=3 and not exercised by
    this theorem; closing through `exit` would require Form B of
    `run_terminates_with_spec`. -/
theorem byteIncrementSo_macro_witness
    (cfg : RunConfig) (baseAddr vR2Old oldByte : Nat)
    (hP : ((.r2 ↦ᵣ vR2Old) ** (.r1 ↦ᵣ baseAddr) **
            (effectiveAddr baseAddr 0 ↦ₘ oldByte)).holdsFor
            (Runner.initialState cfg))
    (hregions :
        (Runner.initialState cfg).regions.containsRange
          (effectiveAddr baseAddr 0) 1 = true ∧
        (Runner.initialState cfg).regions.containsWritable
          (effectiveAddr baseAddr 0) 1 = true) :
    ∃ k, k ≤ 3 ∧
      let sk := executeFn (fetchFromArray byteIncrementSoInsns)
                          (Runner.initialState cfg) k
      sk.pc = 3 ∧
      sk.exitCode = none ∧
      ((.r2 ↦ᵣ wrapAdd (oldByte % 256) (toU64 1)) ** (.r1 ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr 0 ↦ₘ
          (wrapAdd (oldByte % 256) (toU64 1) % 256))).holdsFor sk := by
  exact (byte_increment_macro_spec baseAddr vR2Old oldByte).toExec
    byteIncrementSo_cr_satisfied hP
    (Runner.initialState_pc cfg)
    (Runner.initialState_exitCode cfg)
    hregions

end Svm.SBPF.Demo
