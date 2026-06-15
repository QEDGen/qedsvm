/-
  End-to-end "raw bytecode → Lean spec" worked example: hand-encoded byte_increment.
  Chain: bytes → decode → macro spec → run_reaches_spec → Q.holdsFor (executeFn k).
  Witness at pc=3: byte at input address incremented mod 256.
-/

import SVM.SBPF.RunnerBridge
import SVM.SBPF.Macros

namespace Examples.ByteIncrement

open SVM.SBPF
open SVM.SBPF.Runner
open Memory

/-- Hand-encoded sBPF bytecode: ldx byte, add64, stx byte, exit.
    Encoding: `opcode | (src<<4 | dst) | off16 LE | imm32 LE`. -/
def byteIncrementBytes : ByteArray :=
  ⟨#[ 0x71, 0x12, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x07, 0x02, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00,
      0x73, 0x21, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x95, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 ]⟩

/-- Decoded instruction array for byteIncrementBytes. -/
def byteIncrementInsns : Array Insn :=
  #[ .ldx .byte .r2 .r1 0,
     .add64 .r2 (.imm 1),
     .stx .byte .r1 0 .r2,
     .exit ]

/-- Decode pin. Registry arg matches `Runner.run` convention (H2); no internal calls
    so the result is registry-independent. -/
theorem byteIncrement_decodes :
    Decode.decodeProgram byteIncrementBytes [(Elf.entrypointHash, 0)] =
      some byteIncrementInsns := by
  native_decide

/-- No CPI calls: `executeFnCpi` = `executeFn` via `executeFnCpi_eq_executeFn_of_no_cpi_array`. -/
theorem byteIncrement_noCpi :
    ∀ i, i ∈ byteIncrementInsns → Insn.isCpiCall i = false := by
  intro i hi
  rcases Array.mem_iff_getElem.mp hi with ⟨j, hj, hjeq⟩
  have hj4 : j < 4 := by simp [byteIncrementInsns] at hj; exact hj
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;>
    (simp [byteIncrementInsns] at hjeq; subst hjeq; rfl)

/-- The macro CodeReq is satisfied by `fetchFromArray byteIncrementInsns`. -/
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

`byteIncrement_run_is_executeFn` (structural) + `byteIncrement_macro_witness` (spec)
compose to: raw bytes → Lean spec, first end-to-end theorem in the repo. -/

/-- Structural bridge: `Runner.run` on raw bytes = `executeFn` on decoded array. -/
theorem byteIncrement_run_is_executeFn (cfg : RunConfig) :
    Runner.run byteIncrementBytes cfg = some
      (executeFn (fetchFromArray byteIncrementInsns)
                 (Runner.initialState cfg) cfg.cuBudget) := by
  unfold Runner.run
  rw [byteIncrement_decodes]
  -- Bridge executeFnCpi → executeFn via noCpi.
  exact congrArg some
    (executeFnCpi_eq_executeFn_of_no_cpi_array
      cfg.programRegistry byteIncrementInsns
      (Runner.initialState cfg) cfg.cuBudget byteIncrement_noCpi)

/-- Spec witness: `byte_increment_macro_spec.toExec` yields k ≤ 3 satisfying post-Q.
    Pre/region conditions are caller-supplied (depend on `cfg.input` and `baseAddr`). -/
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

/-- No `.call_local` in the program; required for Form B. -/
theorem byteIncrement_noCallLocal :
    ∀ i, i ∈ byteIncrementInsns → Insn.isCallLocal i = false := by
  intro i hi
  rcases Array.mem_iff_getElem.mp hi with ⟨j, hj, hjeq⟩
  have hj4 : j < 4 := by simp [byteIncrementInsns] at hj; exact hj
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;>
    (simp [byteIncrementInsns] at hjeq; subst hjeq; rfl)

/-- `.exit` is at slot 3. -/
theorem byteIncrement_exit_at_3 :
    fetchFromArray byteIncrementInsns 3 = some Insn.exit := by
  unfold fetchFromArray
  simp [byteIncrementInsns]

/-- End-to-end terminated run: `Runner.run` halts, Q holds at witness, exitCode = r0. -/
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

Same theorem chain but bytes are LLVM output (`cargo-build-sbf`) from
`byte_increment_src/`. LLVM emits 5 insns: the same 3-insn macro + `mov r0, 0` + `exit`.
First 3 insns match `byteIncrementInsns[0..3]` so the macro spec is unchanged.

To sync-check: `cd qedsvm-rs/tests/fixtures/byte_increment_src && cargo-build-sbf && xxd -s 0x120 -l 40 ../byte_increment.so` -/

/-- LLVM-emitted `.text` from `byte_increment.so` (5 insns). -/
def byteIncrementSoText : ByteArray :=
  ⟨#[ 0x71, 0x12, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- ldx byte r2, r1, 0
      0x07, 0x02, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00,   -- add64 r2, 1
      0x73, 0x21, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- stx byte r1, 0, r2
      0xb7, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,   -- mov64 r0, 0
      0x95, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 ]⟩ -- exit

/-- Decoded: 3 macro insns + `mov r0, 0` + exit. -/
def byteIncrementSoInsns : Array Insn :=
  #[ .ldx .byte .r2 .r1 0,
     .add64 .r2 (.imm 1),
     .stx .byte .r1 0 .r2,
     .mov64 .r0 (.imm 0),
     .exit ]

theorem byteIncrementSo_decodes :
    Decode.decodeProgram byteIncrementSoText [(Elf.entrypointHash, 0)] =
      some byteIncrementSoInsns := by
  native_decide

theorem byteIncrementSo_noCpi :
    ∀ i, i ∈ byteIncrementSoInsns → Insn.isCpiCall i = false := by
  intro i hi
  rcases Array.mem_iff_getElem.mp hi with ⟨j, hj, hjeq⟩
  have hj5 : j < 5 := by simp [byteIncrementSoInsns] at hj; exact hj
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;>
    (simp [byteIncrementSoInsns] at hjeq; subst hjeq; rfl)

/-- Same 3-singleton CodeReq shape as 3a; the 2 post-macro insns are not pinned. -/
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

/-- Structural bridge for LLVM .text; identical shape to `byteIncrement_run_is_executeFn`. -/
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

/-- Spec witness for LLVM program: k ≤ 3 satisfying macro post-Q. The `mov r0, 0`
    at pc=3 is not exercised; closing through exit requires Form B. -/
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

/-- `step mov; step exit` from empty callStack gives exitCode=0.
    Factored to avoid simp elaborating the giant `executeFn` term. -/
private theorem step_exit_after_mov_r0_zero (s : State) (h : s.callStack = []) :
    (step Insn.exit (chargeCu (step (.mov64 .r0 (.imm 0)) s))).exitCode = some 0 := by
  simp [step, h, RegFile.set, RegFile.get, toU64]

/-! ### Session 3b terminated-run theorem

3b's `.exit` is at slot 4 (after `mov r0, 0` at slot 3); macro covers only 0-2.
Manual step through `mov` then Form-B composition. A cleaner path would compose
via `cuTripleWithinMem_seq` but needs extra framing (macro is r2/r1/mem, mov is r0). -/

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

/-- End-to-end terminated run for LLVM byte_increment: exitCode=0, Q at witness (pc=3).
    Halted state = `step .exit (step (.mov64 .r0 (.imm 0)) s_witness)`. -/
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
  -- Macro witness at pc=3.
  obtain ⟨k, hk, hpc, hex, hQ, hcuW⟩ :=
    run_reaches_spec_mem byteIncrementSoInsns cfg byteIncrementSo_cr_satisfied
      (byte_increment_macro_spec baseAddr vR2Old oldByte) hP hregions
      (by omega)
  -- callStack is empty along the trace (no call_local insns).
  have hcs_witness : (executeFn (fetchFromArray byteIncrementSoInsns)
                  (Runner.initialState cfg) k).callStack = [] :=
    executeFn_callStack_empty (fetchFromArray byteIncrementSoInsns)
      (Runner.initialState cfg) k (Runner.initialState_callStack cfg)
      (fetchFromArray_property_of_mem byteIncrementSo_noCallLocal)
  -- Witness stays within budget (needed for per-step unfolds).
  have h_wbud : (executeFn (fetchFromArray byteIncrementSoInsns)
        (Runner.initialState cfg) k).cuConsumed ≤
      (executeFn (fetchFromArray byteIncrementSoInsns)
        (Runner.initialState cfg) k).cuBudget := by
    rw [executeFn_preserves_cuBudget]
    simp only [Runner.initialState_cuBudget]
    omega
  refine ⟨k, hk, hpc, hQ, ?_, ?_⟩
  · -- Chain: step mov (pc=3) → step exit (pc=4) → compose to k+2 → extend to budget → bridge.
    have h_step_mov : executeFn (fetchFromArray byteIncrementSoInsns) (executeFn (fetchFromArray byteIncrementSoInsns) (Runner.initialState cfg) k) 1 =
                     chargeCu (step (.mov64 .r0 (.imm 0)) (executeFn (fetchFromArray byteIncrementSoInsns) (Runner.initialState cfg) k)) := by
      have hf : (fetchFromArray byteIncrementSoInsns) (executeFn (fetchFromArray byteIncrementSoInsns) (Runner.initialState cfg) k).pc =
                some (.mov64 .r0 (.imm 0)) := by
        rw [hpc]; exact byteIncrementSo_mov_at_3
      rw [executeFn_step (fetchFromArray byteIncrementSoInsns) (executeFn (fetchFromArray byteIncrementSoInsns) (Runner.initialState cfg) k) 0
            (.mov64 .r0 (.imm 0)) hex h_wbud hf]
      simp [executeFn]
    have hpc_smov : (chargeCu (step (.mov64 .r0 (.imm 0)) (executeFn (fetchFromArray byteIncrementSoInsns) (Runner.initialState cfg) k))).pc = 4 := by
      simp only [chargeCu, step, hpc]
    have hex_smov : (chargeCu (step (.mov64 .r0 (.imm 0)) (executeFn (fetchFromArray byteIncrementSoInsns) (Runner.initialState cfg) k))).exitCode = none := by
      simp only [chargeCu, step, hex]
    -- Charged mov still within budget (1 CU on top of witness ≤ 3, budget ≥ 5).
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
    have h_exit_halted : (step Insn.exit (chargeCu (step (.mov64 .r0 (.imm 0)) (executeFn (fetchFromArray byteIncrementSoInsns) (Runner.initialState cfg) k)))).exitCode =
        some ((chargeCu (step (.mov64 .r0 (.imm 0)) (executeFn (fetchFromArray byteIncrementSoInsns) (Runner.initialState cfg) k))).regs.get Reg.r0) := by
      simp only [chargeCu, step, hcs_witness]
    have h_kp2 : executeFn (fetchFromArray byteIncrementSoInsns)
                  (Runner.initialState cfg) (k + 2) =
                  chargeCu (step Insn.exit (chargeCu (step (.mov64 .r0 (.imm 0)) (executeFn (fetchFromArray byteIncrementSoInsns) (Runner.initialState cfg) k)))) := by
      have h_k1 : executeFn (fetchFromArray byteIncrementSoInsns)
                    (Runner.initialState cfg) (k + 1) =
                    chargeCu (step (.mov64 .r0 (.imm 0)) (executeFn (fetchFromArray byteIncrementSoInsns) (Runner.initialState cfg) k)) := by
        rw [executeFn_compose, h_step_mov]
      have : k + 2 = (k + 1) + 1 := by omega
      rw [this, executeFn_compose, h_k1, h_step_exit]
    -- Past halt, additional fuel is a no-op.
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
  · exact step_exit_after_mov_r0_zero
      (executeFn (fetchFromArray byteIncrementSoInsns) (Runner.initialState cfg) k)
      hcs_witness

end Examples.ByteIncrement
