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

import SVM.SBPF.RunnerBridge
import SVM.SBPF.Macros

namespace Examples.ByteIncrement

open SVM.SBPF
open SVM.SBPF.Runner
open Memory

/-- Hand-encoded sBPF bytecode for byte_increment. Four 8-byte slots:

    `pc=0  ldx .byte .r2 .r1 0`   → `71 12 00 00 00 00 00 00`
    `pc=1  add64 .r2 (.imm 1)`    → `07 02 00 00 01 00 00 00`
    `pc=2  stx .byte .r1 0 .r2`   → `73 21 00 00 00 00 00 00`
    `pc=3  exit`                  → `95 00 00 00 00 00 00 00`

    Encoding follows `SVM.SBPF.Decode.decodeInsn`:
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
          (effectiveAddr baseAddr 0) 1 = true)
    (hbudget : 3 ≤ cfg.cuBudget) :
    ∃ k, k ≤ 3 ∧
      let sk := executeFn (fetchFromArray byteIncrementInsns)
                          (Runner.initialState cfg) k
      sk.pc = 3 ∧
      sk.exitCode = none ∧
      ((.r2 ↦ᵣ wrapAdd (oldByte % 256) (toU64 1)) ** (.r1 ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr 0 ↦ₘ
          (wrapAdd (oldByte % 256) (toU64 1) % 256))).holdsFor sk := by
  obtain ⟨k, hk, hpc', hex', _, hQ⟩ :=
    (byte_increment_macro_spec baseAddr vR2Old oldByte).toExec
      byteIncrement_cr_satisfied hP
      (Runner.initialState_pc cfg)
      (Runner.initialState_exitCode cfg)
      (by simp only [Runner.initialState_cuConsumed,
                     Runner.initialState_cuBudget]; omega)
      hregions
  exact ⟨k, hk, hpc', hex', hQ⟩

/-- No `.call_local` in the 4-instruction program; required for Form B. -/
theorem byteIncrement_noCallLocal :
    ∀ i, i ∈ byteIncrementInsns → Insn.isCallLocal i = false := by
  intro i hi
  rcases Array.mem_iff_getElem.mp hi with ⟨j, hj, hjeq⟩
  have hj4 : j < 4 := by simp [byteIncrementInsns] at hj; exact hj
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;>
    (simp [byteIncrementInsns] at hjeq; subst hjeq; rfl)

/-- The hand-encoded byte_increment program's `.exit` is at slot 3. -/
theorem byteIncrement_exit_at_3 :
    fetchFromArray byteIncrementInsns 3 = some Insn.exit := by
  unfold fetchFromArray
  simp [byteIncrementInsns]

/-- **End-to-end terminated run** for the hand-encoded byte_increment:
    `Runner.run` produces a halted state, Q holds at the pre-exit
    witness, and the run's exit code is the witness's `r0`. -/
theorem byteIncrement_run_terminates
    (cfg : RunConfig) (baseAddr vR2Old oldByte : Nat)
    (hP : ((.r2 ↦ᵣ vR2Old) ** (.r1 ↦ᵣ baseAddr) **
            (effectiveAddr baseAddr 0 ↦ₘ oldByte)).holdsFor
            (Runner.initialState cfg))
    (hregions :
        (Runner.initialState cfg).regions.containsRange
          (effectiveAddr baseAddr 0) 1 = true ∧
        (Runner.initialState cfg).regions.containsWritable
          (effectiveAddr baseAddr 0) 1 = true)
    (hbudget : 4 ≤ cfg.cuBudget) :
    ∃ k, k ≤ 3 ∧
      let s_witness := executeFn (fetchFromArray byteIncrementInsns)
                                 (Runner.initialState cfg) k
      s_witness.pc = 3 ∧
      s_witness.exitCode = none ∧
      ((.r2 ↦ᵣ wrapAdd (oldByte % 256) (toU64 1)) ** (.r1 ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr 0 ↦ₘ
          (wrapAdd (oldByte % 256) (toU64 1) % 256))).holdsFor s_witness ∧
      Runner.run byteIncrementBytes cfg =
        some (chargeCu (step Insn.exit s_witness)) ∧
      (step Insn.exit s_witness).exitCode = some s_witness.regs.r0 :=
  run_terminates_with_spec_mem
    byteIncrement_decodes byteIncrement_cr_satisfied byteIncrement_exit_at_3
    byteIncrement_noCpi byteIncrement_noCallLocal
    (byte_increment_macro_spec baseAddr vR2Old oldByte) hP hregions hbudget

/-! ## Session 3b: LLVM-compiled .so demo

The byte sequence below is the `.text` section content of
`qedsvm-rs/tests/fixtures/byte_increment.so`, produced by
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
cd qedsvm-rs/tests/fixtures/byte_increment_src && cargo-build-sbf
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
          (effectiveAddr baseAddr 0) 1 = true)
    (hbudget : 3 ≤ cfg.cuBudget) :
    ∃ k, k ≤ 3 ∧
      let sk := executeFn (fetchFromArray byteIncrementSoInsns)
                          (Runner.initialState cfg) k
      sk.pc = 3 ∧
      sk.exitCode = none ∧
      ((.r2 ↦ᵣ wrapAdd (oldByte % 256) (toU64 1)) ** (.r1 ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr 0 ↦ₘ
          (wrapAdd (oldByte % 256) (toU64 1) % 256))).holdsFor sk := by
  obtain ⟨k, hk, hpc', hex', _, hQ⟩ :=
    (byte_increment_macro_spec baseAddr vR2Old oldByte).toExec
      byteIncrementSo_cr_satisfied hP
      (Runner.initialState_pc cfg)
      (Runner.initialState_exitCode cfg)
      (by simp only [Runner.initialState_cuConsumed,
                     Runner.initialState_cuBudget]; omega)
      hregions
  exact ⟨k, hk, hpc', hex', hQ⟩

/-- Helper: `step mov` (CU-charged) then `step .exit` from a
    `callStack`-empty state halts with `exitCode = some 0`. Factored out
    to avoid simp's elaboration of the giant `executeFn` term in the
    demo proof. -/
private theorem step_exit_after_mov_r0_zero (s : State) (h : s.callStack = []) :
    (step Insn.exit (chargeCu (step (.mov64 .r0 (.imm 0)) s))).exitCode = some 0 := by
  simp [step, h, RegFile.set, RegFile.get, toU64]

/-! ### Session 3b's terminated-run theorem

Unlike 3a (whose `.exit` is at slot 3 directly after the macro), 3b's
`.exit` sits at slot 4 after LLVM's emitted `mov r0, 0` at slot 3.
The macro spec only covers slots 0-2; to reach the halt, we manually
step through the `mov` instruction after the macro witness state and
then apply the Form-B style composition (witness → step .exit → run).

A cleaner version would compose `byte_increment_macro_spec` with
`mov64_imm_spec` via `cuTripleWithinMem_seq` to obtain a 4-step
cuTriple, then apply `run_terminates_with_spec_mem` directly. That
needs additional framing infrastructure (the macro is about r2/r1/mem,
mov is about r0) which is non-trivial; for now we ship the bespoke
version. -/

theorem byteIncrementSo_noCallLocal :
    ∀ i, i ∈ byteIncrementSoInsns → Insn.isCallLocal i = false := by
  intro i hi
  rcases Array.mem_iff_getElem.mp hi with ⟨j, hj, hjeq⟩
  have hj5 : j < 5 := by simp [byteIncrementSoInsns] at hj; exact hj
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;>
    (simp [byteIncrementSoInsns] at hjeq; subst hjeq; rfl)

theorem byteIncrementSo_exit_at_4 :
    fetchFromArray byteIncrementSoInsns 4 = some Insn.exit := by
  unfold fetchFromArray
  simp [byteIncrementSoInsns]

theorem byteIncrementSo_mov_at_3 :
    fetchFromArray byteIncrementSoInsns 3 = some (.mov64 .r0 (.imm 0)) := by
  unfold fetchFromArray
  simp [byteIncrementSoInsns]

/-- **End-to-end terminated run** for the LLVM-compiled byte_increment:
    `Runner.run` produces a halted state with `exitCode = some 0`
    (the value LLVM's `mov r0, 0` puts in r0 before `.exit`), and Q
    holds at the pre-exit witness state.

    The witness state is at pc=3 (right after the macro, before
    `mov r0, 0`); Q is the macro post-condition. The halted state is
    `step .exit (step (.mov64 .r0 (.imm 0)) s_witness)`. -/
theorem byteIncrementSo_run_terminates
    (cfg : RunConfig) (baseAddr vR2Old oldByte : Nat)
    (hP : ((.r2 ↦ᵣ vR2Old) ** (.r1 ↦ᵣ baseAddr) **
            (effectiveAddr baseAddr 0 ↦ₘ oldByte)).holdsFor
            (Runner.initialState cfg))
    (hregions :
        (Runner.initialState cfg).regions.containsRange
          (effectiveAddr baseAddr 0) 1 = true ∧
        (Runner.initialState cfg).regions.containsWritable
          (effectiveAddr baseAddr 0) 1 = true)
    (hbudget : 5 ≤ cfg.cuBudget) :
    ∃ k, k ≤ 3 ∧
      let s_witness := executeFn (fetchFromArray byteIncrementSoInsns)
                                 (Runner.initialState cfg) k
      let s_mov := chargeCu (step (.mov64 .r0 (.imm 0)) s_witness)
      s_witness.pc = 3 ∧
      ((.r2 ↦ᵣ wrapAdd (oldByte % 256) (toU64 1)) ** (.r1 ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr 0 ↦ₘ
          (wrapAdd (oldByte % 256) (toU64 1) % 256))).holdsFor s_witness ∧
      Runner.run byteIncrementSoText cfg =
        some (chargeCu (step Insn.exit s_mov)) ∧
      (step Insn.exit s_mov).exitCode = some 0 := by
  -- Step 1: macro witness at pc=3.
  obtain ⟨k, hk, hpc, hex, hQ, hcuW⟩ :=
    run_reaches_spec_mem byteIncrementSoInsns cfg byteIncrementSo_cr_satisfied
      (byte_increment_macro_spec baseAddr vR2Old oldByte) hP hregions
      (by omega)
  -- callStack invariant along the trace.
  have hcs_witness : (executeFn (fetchFromArray byteIncrementSoInsns)
                  (Runner.initialState cfg) k).callStack = [] :=
    executeFn_callStack_empty (fetchFromArray byteIncrementSoInsns)
      (Runner.initialState cfg) k (Runner.initialState_callStack cfg)
      (fetchFromArray_property_of_mem byteIncrementSo_noCallLocal)
  -- Witness state stays within budget (needed for per-step unfolds).
  have h_wbud : (executeFn (fetchFromArray byteIncrementSoInsns)
        (Runner.initialState cfg) k).cuConsumed ≤
      (executeFn (fetchFromArray byteIncrementSoInsns)
        (Runner.initialState cfg) k).cuBudget := by
    rw [executeFn_preserves_cuBudget]
    simp only [Runner.initialState_cuBudget]
    omega
  refine ⟨k, hk, hpc, hQ, ?_, ?_⟩
  · -- Runner.run byteIncrementSoText cfg
    --   = some (chargeCu (step .exit (chargeCu (step mov s_witness))))
    -- Chain:
    --   executeFn fetch s_witness 1            = chargeCu (step mov s_witness)         (mov at pc=3)
    --   executeFn fetch (chargeCu (step mov s_witness)) 1
    --                                          = chargeCu (step .exit (chargeCu ...))  (exit at pc=4)
    --   executeFn fetch (initialState) (k+2)   = chargeCu (step .exit ...)             (compose)
    --   executeFn fetch (initialState) cfg.cuBudget = chargeCu (step .exit ...)        (halted)
    --   executeFnCpi = executeFn                (bridge via noCpi)
    --   Runner.run = some (executeFnCpi ... cuBudget) (unfold)
    have h_step_mov : executeFn (fetchFromArray byteIncrementSoInsns) (executeFn (fetchFromArray byteIncrementSoInsns) (Runner.initialState cfg) k) 1 =
                     chargeCu (step (.mov64 .r0 (.imm 0)) (executeFn (fetchFromArray byteIncrementSoInsns) (Runner.initialState cfg) k)) := by
      have hf : (fetchFromArray byteIncrementSoInsns) (executeFn (fetchFromArray byteIncrementSoInsns) (Runner.initialState cfg) k).pc =
                some (.mov64 .r0 (.imm 0)) := by
        rw [hpc]; exact byteIncrementSo_mov_at_3
      rw [executeFn_step (fetchFromArray byteIncrementSoInsns) (executeFn (fetchFromArray byteIncrementSoInsns) (Runner.initialState cfg) k) 0
            (.mov64 .r0 (.imm 0)) hex h_wbud hf]
      simp [executeFn]
    -- step mov (CU-charged) increments pc to 4 and preserves exitCode = none.
    have hpc_smov : (chargeCu (step (.mov64 .r0 (.imm 0)) (executeFn (fetchFromArray byteIncrementSoInsns) (Runner.initialState cfg) k))).pc = 4 := by
      simp only [chargeCu, step, hpc]
    have hex_smov : (chargeCu (step (.mov64 .r0 (.imm 0)) (executeFn (fetchFromArray byteIncrementSoInsns) (Runner.initialState cfg) k))).exitCode = none := by
      simp only [chargeCu, step, hex]
    -- The charged mov state is still within budget (one baseline CU on
    -- top of the witness's ≤ 3, against budget ≥ 5).
    have h_bud_smov : (chargeCu (step (.mov64 .r0 (.imm 0)) (executeFn (fetchFromArray byteIncrementSoInsns) (Runner.initialState cfg) k))).cuConsumed ≤
        (chargeCu (step (.mov64 .r0 (.imm 0)) (executeFn (fetchFromArray byteIncrementSoInsns) (Runner.initialState cfg) k))).cuBudget := by
      show (executeFn (fetchFromArray byteIncrementSoInsns) (Runner.initialState cfg) k).cuConsumed + 1 ≤
        (executeFn (fetchFromArray byteIncrementSoInsns) (Runner.initialState cfg) k).cuBudget
      rw [executeFn_preserves_cuBudget]
      simp only [Runner.initialState_cuBudget]
      omega
    have h_step_exit : executeFn (fetchFromArray byteIncrementSoInsns)
        (chargeCu (step (.mov64 .r0 (.imm 0)) (executeFn (fetchFromArray byteIncrementSoInsns) (Runner.initialState cfg) k))) 1 =
        chargeCu (step Insn.exit (chargeCu (step (.mov64 .r0 (.imm 0)) (executeFn (fetchFromArray byteIncrementSoInsns) (Runner.initialState cfg) k)))) := by
      have hf : (fetchFromArray byteIncrementSoInsns)
                (chargeCu (step (.mov64 .r0 (.imm 0)) (executeFn (fetchFromArray byteIncrementSoInsns) (Runner.initialState cfg) k))).pc = some Insn.exit := by
        rw [hpc_smov]; exact byteIncrementSo_exit_at_4
      rw [executeFn_step (fetchFromArray byteIncrementSoInsns)
            (chargeCu (step (.mov64 .r0 (.imm 0)) (executeFn (fetchFromArray byteIncrementSoInsns) (Runner.initialState cfg) k))) 0 Insn.exit hex_smov h_bud_smov hf]
      simp [executeFn]
    -- step .exit halts (callStack = []).
    have h_exit_halted : (step Insn.exit (chargeCu (step (.mov64 .r0 (.imm 0)) (executeFn (fetchFromArray byteIncrementSoInsns) (Runner.initialState cfg) k)))).exitCode =
        some ((chargeCu (step (.mov64 .r0 (.imm 0)) (executeFn (fetchFromArray byteIncrementSoInsns) (Runner.initialState cfg) k))).regs.get Reg.r0) := by
      simp only [chargeCu, step, hcs_witness]
    -- Compose: executeFn fetch (initialState) (k+2) = chargeCu (step .exit (chargeCu (step mov s_witness))).
    have h_kp2 : executeFn (fetchFromArray byteIncrementSoInsns)
                  (Runner.initialState cfg) (k + 2) =
                  chargeCu (step Insn.exit (chargeCu (step (.mov64 .r0 (.imm 0)) (executeFn (fetchFromArray byteIncrementSoInsns) (Runner.initialState cfg) k)))) := by
      have h_k1 : executeFn (fetchFromArray byteIncrementSoInsns)
                    (Runner.initialState cfg) (k + 1) =
                    chargeCu (step (.mov64 .r0 (.imm 0)) (executeFn (fetchFromArray byteIncrementSoInsns) (Runner.initialState cfg) k)) := by
        rw [executeFn_compose, h_step_mov]
      have : k + 2 = (k + 1) + 1 := by omega
      rw [this, executeFn_compose, h_k1, h_step_exit]
    -- Past the halt, additional fuel is a no-op.
    have h_halted_after_kp2 : ∀ m,
        executeFn (fetchFromArray byteIncrementSoInsns)
          (chargeCu (step Insn.exit (chargeCu (step (.mov64 .r0 (.imm 0)) (executeFn (fetchFromArray byteIncrementSoInsns) (Runner.initialState cfg) k))))) m =
          chargeCu (step Insn.exit (chargeCu (step (.mov64 .r0 (.imm 0)) (executeFn (fetchFromArray byteIncrementSoInsns) (Runner.initialState cfg) k)))) := by
      intro m
      exact executeFn_halted (fetchFromArray byteIncrementSoInsns) _ m _ h_exit_halted
    have h_kp2_le : k + 2 ≤ cfg.cuBudget := by omega
    have h_full : executeFn (fetchFromArray byteIncrementSoInsns)
                    (Runner.initialState cfg) cfg.cuBudget =
                  chargeCu (step Insn.exit (chargeCu (step (.mov64 .r0 (.imm 0)) (executeFn (fetchFromArray byteIncrementSoInsns) (Runner.initialState cfg) k)))) := by
      have h_eq : cfg.cuBudget = (k + 2) + (cfg.cuBudget - (k + 2)) :=
        (Nat.add_sub_cancel' h_kp2_le).symm
      rw [h_eq, executeFn_compose (fetchFromArray byteIncrementSoInsns)
            (Runner.initialState cfg) (k + 2) (cfg.cuBudget - (k + 2)),
          h_kp2, h_halted_after_kp2]
    -- Bridge executeFnCpi → executeFn.
    have h_bridge : executeFnCpi cfg.programRegistry
                      (fetchFromArray byteIncrementSoInsns)
                      (Runner.initialState cfg) cfg.cuBudget =
                    executeFn (fetchFromArray byteIncrementSoInsns)
                      (Runner.initialState cfg) cfg.cuBudget :=
      executeFnCpi_eq_executeFn_of_no_cpi_array cfg.programRegistry
        byteIncrementSoInsns (Runner.initialState cfg) cfg.cuBudget
        byteIncrementSo_noCpi
    unfold Runner.run
    rw [byteIncrementSo_decodes]
    show some _ = some _
    congr 1
    rw [h_bridge, h_full]
  · -- Goal: (step .exit (chargeCu (step mov X))).exitCode = some 0.
    -- Discharge via the helper lemma using hcs_witness.
    exact step_exit_after_mov_r0_zero
      (executeFn (fetchFromArray byteIncrementSoInsns) (Runner.initialState cfg) k)
      hcs_witness

end Examples.ByteIncrement
