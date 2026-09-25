# sBPF v3 Proof and Default Workflow Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make V3 the default new-program path and emit checked selected-path proofs for every non-syscall V3 ISA form and modeled syscall effects.

**Architecture:** Consume Stage 1's versioned ELF and complete V3 execution. Extend `qedlift`'s symbolic walk, generated Lean instruction specs, and byte pins by opcode family. Keep deprecated V0 artifacts working through explicit compatibility entrypoints. CPI path proofs cross a call only through PR #63's callee-contract relation.

**Tech Stack:** Lean 4, Rust, `qedlift`, `qedrecover`, `qed-analysis`, Lake, Mollusk, cargo-build-sbf 4.3.0/platform-tools 1.57.

**Spec:** `docs/superpowers/specs/2026-09-25-sbpfv3-default-migration-design.md`

**Prerequisite:** `docs/superpowers/plans/2026-09-25-sbpfv3-runtime.md` has passed its Stage 1 gate. Its V3 opcode matrix and loaded-program interface are the input to this plan.

## Global Constraints

- New builds, fixtures, raw-byte API defaults, quick starts, and CI smoke tests target V3.
- Preserve existing V0 regression proofs, but add no V0/V1/V2 feature coverage.
- A generated theorem pins the complete V3 ELF, version, loaded text, and every walked decode.
- No fabricated branch, call, syscall, CPI, memory, or compute effect may enter a proof.
- Every non-syscall V3 opcode form gets a selected-path proof test. Only modeled syscall effects are in scope.
- PR #63's `CalleeSemantics`, `Transitions`, and `applyResult` define CPI composition.

## Review Focus

- A JMP32 register-source signed comparison with high bits set takes the correct path and yields an honest guard hypothesis.
- A traced `callx` path pins both target register value and mapped target PC; a contradictory trace fails.
- A V3 shared-text batch binds its proof to the same complete ELF and loaded text as a single-path lift.
- A V3 CPI caller without a callee contract cannot emit a cross-CPI proof; a supplied contract proves success and rollback.
- Deprecated V0 generated proofs still compile after unqualified raw-byte APIs default to V3.

## File map

- `qedsvm-rs/qedlift/src/exec/control.rs`, `exec/step.rs`, `exec/walk.rs`: V3 symbolic branch, call, and instruction effects.
- `qedsvm-rs/qedlift/src/isa.rs`, `spec_call.rs`, `lift.rs`, `render.rs`: instruction rendering, Lean spec selection, proof pins, and diagnostics.
- `SVM/SBPF/InstructionSpecs/Jump.lean`, `CallReturn.lean`, `Alu.lean`, `SpecGen.lean`: one-step and composition proofs.
- `SVM/SBPF/Decode.lean`, `SVM/SBPF/Runner.lean`, existing generated V0 modules: explicit compatibility entrypoints.
- `qedsvm-rs/qedlift/tests/public_api.rs`, `qedsvm-rs/tests/fixtures/`, `examples/lean/Generated/`: source-built V3 path cases and sorry-free theorems.
- `qedsvm-rs/qedlift/README.md`, `docs/PIPELINE.md`, `docs/COVERAGE.md`, `.github/workflows/build.yml`: V3-first workflow and release gates.

---

### Task 1: Make V3 the public raw-byte default with explicit legacy access

**Files:** Modify `SVM/SBPF/Decode.lean`, `SVM/SBPF/Runner.lean`, `SVM/SBPF/RunnerTests.lean`, legacy examples that call `Decode.decodeProgram`, and `qedsvm-rs/qedlift/README.md`.

**Interfaces:** ELF-based APIs always use `e_flags`. Unqualified raw-byte `Decode.decodeProgram` and runner calls use V3. A clearly named `decodeProgramV0`/`runV0` or explicit `.v0` parameter preserves existing generated V0 proofs.

- [ ] **Step 1: Add a red default-version test** using V3-only `JEQ32_IMM` bytes. Assert the unqualified decoder accepts it while an explicit V0 decoder rejects it:

  ```lean
  example : (Decode.decodeProgram (Decode.bytesOfHex
      "16000000010000009500000000000000")).isSome = true := by native_decide
  example : (Decode.decodeProgramV0 (Decode.bytesOfHex
      "16000000010000009500000000000000")).isNone = true := by native_decide
  ```

- [ ] **Step 2: Run `lake build SVM.SBPF.RunnerTests` and confirm the new default test fails.**
- [ ] **Step 3: Change only unqualified raw-byte entrypoints to V3.** Route ELF APIs by `Elf.readVersion` as before; add V0 compatibility wrappers and change V0 examples/generated artifacts to call them explicitly. Preserve their theorem statements apart from the decoder function name.
- [ ] **Step 4: Run `lake build Examples` and the V0 runner tests; commit** with `git commit -m "feat(sbpfv3): default raw byte APIs to V3"`.

### Task 2: Lift every V3 JMP32 form and complete non-syscall opcode parity

**Files:** Modify `qedsvm-rs/qedlift/src/lift.rs`, `exec/control.rs`, `exec/step.rs`, `isa.rs`, `spec_call.rs`, `SVM/SBPF/InstructionSpecs/Jump.lean`, `SVM/SBPF/SpecGen.lean`, and `qedsvm-rs/qedlift/tests/public_api.rs`.

**Interfaces:** The symbolic walk uses V3's low-32-bit branch relation for all 11 conditions in immediate and register modes. `spec_call` selects `jmp32_imm_spec` or `jmp32_reg_spec` with the actual condition and branch decision. Other non-syscall V3 forms use the exact Stage 1 opcode matrix.

- [ ] **Step 1: Add red lift tests** for taken and untaken `JEQ32`, `JNE32`, unsigned and signed order comparisons, `JSET32`, both source modes, and high-bit counterexamples. For each test, invoke `Lifter` on a valid V3 ELF and assert the generated Lean text names the correct `jmp32_*_spec` and guard.
- [ ] **Step 2: Run `cargo test -p qedlift --test public_api` and confirm the current `V3 JMP32 opcode ... has no symbolic path spec` gate is hit.**
- [ ] **Step 3: Remove the blanket V3 JMP32 rejection in `lift.rs` only after** `exec/control.rs`, `exec/step.rs`, `isa.rs`, and `spec_call.rs` handle every condition/source combination. Bind each proof's taken or untaken guard to the symbolic low-32-bit comparison; a trace determines which guard to prove, not its truth.
- [ ] **Step 4: Work through every remaining non-syscall row in `docs/SBPFV3_ISA_MATRIX.md`.** Add a Rust symbolic-walk case and Lean one-step spec for any row lacking proof coverage. Keep division-by-zero, invalid memory, and invalid target paths as typed fault proofs, not successful arithmetic paths.
- [ ] **Step 5: Generate one Lean module per condition family and run `lake build Examples`.** Run `cargo test -p qedlift` and commit with `git commit -m "feat(sbpfv3): prove all V3 jump and ALU path forms"`.

### Task 3: Prove traced V3 callx and return paths

**Files:** Modify `qedsvm-rs/qedlift/src/exec/walk.rs`, `exec/step.rs`, `isa.rs`, `spec_call.rs`, `SVM/SBPF/InstructionSpecs/CallReturn.lean`, `SVM/SBPF/SpecGen.lean`, and V3 source fixture/tests.

**Interfaces:** For a V3 `callx`, the proof precondition owns the destination register's program virtual address. The instruction spec maps that address through Stage 1's slot map, pushes the call frame, and returns to the next PC; call depth and invalid targets remain explicit fault cases.

- [ ] **Step 1: Add a red source-built V3 callx fixture** with one valid indirect callee and a captured path trace. Add a second trace with an incorrect callee PC and assert `qedlift` returns a typed path-mismatch diagnostic.
- [ ] **Step 2: Run the focused Rust lift test and `lake build` for the generated Lean fixture; record the missing callx spec.**
- [ ] **Step 3: Add a Lean `callx_v3_spec` in `CallReturn.lean`** whose precondition states the destination register's address, its validated logical target PC, frame capacity, and saved registers. Connect its postcondition to the same call-stack shape as `call_local_spec`.
- [ ] **Step 4: Make Rust symbolic execution and `spec_call.rs` emit that address/target hypothesis and apply `callx_v3_spec`.** Remove V3 `CALL_REG` from the blanket rejection only after a generated proof builds. Add invalid target and call-depth typed-fault tests.
- [ ] **Step 5: Run `cargo test -p qedlift`, `lake build Examples`, and the callx Mollusk differential case; commit** with `git commit -m "feat(sbpfv3): prove indirect call paths"`.

### Task 4: Preserve full V3 byte pins in shared-text mode

**Files:** Modify `qedsvm-rs/qedlift/src/lift.rs`, `render.rs`, `qedsvm-rs/qedlift/tests/public_api.rs`, and generated shared-text V3 example modules.

**Interfaces:** A shared V3 module contains the complete ELF and strict-loader text theorem once. Every per-path module imports that module and pins its walked V3 decodes to the shared text. The shared module's version is V3.

- [ ] **Step 1: Add a red public API test** lifting two paths from `sbpfv3_compiled_account.so` with `shared_text: Some("Sbpfv3Shared")`; assert a shared module is returned, both paths import it, and it contains `Elf.loadV3`, the complete ELF bytes, and `.v3` decode pins.
- [ ] **Step 2: Run `cargo test -p qedlift --test public_api` and observe the current `V3 shared-text mode is not yet supported` error.**
- [ ] **Step 3: Move `render::v3_elf_pin` into the shared module path when shared text is requested.** Keep the complete ELF pin in single-path mode. Never let a V3 shared module reuse a V0 function registry or a V0 decode claim.
- [ ] **Step 4: Build both generated Lean path modules and run the public API tests; commit** with `git commit -m "feat(sbpfv3): share pinned V3 text across paths"`.

### Task 5: Connect V3 CPI path proofs to PR #63 contracts

**Files:** Modify `qedsvm-rs/qedlift/src/exec/syscall_registry.rs`, `exec/walk.rs`, `lift.rs`, `spec_call.rs`, `SVM/SBPF/InstructionSpecs/CallReturn.lean` or a focused new `CpiContract.lean`, and V3 CPI generated examples.

**Interfaces:** A V3 lift receives an explicit `CalleeSemantics` contract and a theorem relating the callee's result to its selected input. The emitted path proof uses `Cpi.Transitions` and `Cpi.applyResult`; without a contract the lift returns a typed unsupported-CPI diagnostic and emits no cross-CPI theorem.

- [ ] **Step 1: Add red tests** for a V3 caller invoking a V3 callee: no contract, success contract, and nonzero-result rollback contract. Assert absence of a cross-CPI proof for no contract and exact caller memory/return-data/compute results for both supplied contracts.
- [ ] **Step 2: Run `cargo test -p qedlift` and `lake build ExamplesCpi` to confirm the current proof walk ends at the CPI terminal.**
- [ ] **Step 3: Add an explicit callee-contract input to `LiftOptions`** and validate its theorem/module identifier before emitting Lean. Render a `Cpi.Transitions` application rather than treating the CPI as an effect-free syscall. Keep existing V0 terminal artifacts unchanged.
- [ ] **Step 4: Build the generated V3 CPI caller proofs and run the Stage 1 V3 CPI differential test.** The success proof commits proposed memory; the failure proof keeps caller memory and propagates result fields through `Cpi.applyResult`.
- [ ] **Step 5: Commit** with `git commit -m "feat(sbpfv3): compose CPI path proofs with callee contracts"`.

### Task 6: Make V3-first coverage and CI the release gate

**Files:** Modify `qedsvm-rs/qedlift/README.md`, `docs/PIPELINE.md`, `docs/COVERAGE.md`, `qedsvm-rs/tests/fixtures/README.md`, `.github/workflows/build.yml`, and V3 example modules.

**Interfaces:** The documented first lift uses a source-built V3 ELF. CI verifies V3 version, full opcode matrix, generated path proofs, Mollusk conformance, and deprecated V0 regression examples.

- [ ] **Step 1: Replace the V0 `byte_increment.so` quick start** with the source-built `sbpfv3_compiled_account.so`, its captured trace, and the checked generated Lean module. Document `cargo-build-sbf --arch v3` and the required platform-tools version.
- [ ] **Step 2: Add CI commands for `lake build Examples`, `cargo test --features diff-mollusk`, opcode-matrix checks, and strict Clippy.** Ensure the V3 source fixture's `e_flags` and recorded SHA-256 are checked, not inferred from filename.
- [ ] **Step 3: Run the final release gates:**

  ```text
  lake build
  lake build Examples
  cargo test --workspace --quiet
  cargo test --features diff-mollusk --quiet
  cargo clippy --workspace --all-targets --all-features -- -D warnings
  cargo fmt --all -- --check
  git diff --check
  ```

  Run cargo commands from `qedsvm-rs/`. Confirm the full V3 matrix has proof and execution evidence, all generated V3 theorems are sorry-free, and existing V0 examples remain green.
- [ ] **Step 4: Check the Agave 4.4 release alignment.** Record the exact Agave-compatible sbpf and Mollusk versions in `docs/SBPFV3_ISA_MATRIX.md`, compare their V3 verifier and interpreter to the pinned Stage 1 versions, and rerun the differential suite on any changed semantics. If compatible releases are not yet available, label the final Agave 4.4 conformance gate pending; do not claim full migration complete.
- [ ] **Step 5: Update `docs/COVERAGE.md`** to distinguish full V3 ISA coverage from limited syscall/CPI/refinement coverage. Mark V0/V1/V2 deprecated and state that no legacy coverage was added.
- [ ] **Step 6: Commit** with `git commit -m "docs: make V3 the default verification workflow"`.

## Completion handoff

The migration is complete only after this plan and the Stage 1 plan pass their gates against the recorded V3 runtime/toolchain matrix. The final report must name the remaining syscall, CPI-contract, and whole-program proof boundaries without calling them ISA gaps.
