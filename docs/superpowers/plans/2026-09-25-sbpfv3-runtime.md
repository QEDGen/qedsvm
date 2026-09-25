# sBPF v3 Runtime Completion Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Load, decode, and execute every valid sBPF V3 ISA form with behavior checked against the pinned Solana runtime.

**Architecture:** Keep the existing V0 compatibility route. Route V3 ELF and CPI callees through one strict-header loader, then carry the V3 interpretation into decode and execution. Use a checked opcode matrix and differential fixtures as the release gate.

**Tech Stack:** Lean 4, Rust, `solana-sbpf 0.14.4`, Mollusk `0.12.1-agave-4.0`, Lake, cargo-build-sbf 4.3.0, platform-tools 1.57.

**Spec:** `docs/superpowers/specs/2026-09-25-sbpfv3-default-migration-design.md`

## Global Constraints

- V3 is the target for new fixtures; use `--arch v3` and platform-tools 1.56 or newer.
- Do not add V0/V1/V2 ISA or proof coverage. Preserve existing V0 regression behavior.
- Read the ELF version from `e_flags`; reject V1, V2, and V4 in the Lean proof path.
- PR #63's `Cpi.applyResult` success/rollback boundary remains authoritative.
- Malformed V3 ELF, unknown opcodes, and invalid targets fail closed.
- Pin the tested sbpf, Mollusk/Agave, build-tool, and platform-tools versions.

## Review Focus

- A sectionless V3 ELF with a valid executable segment loads; the same bytes with an invalid header fail.
- A V3 `callx` reads `dst`, interprets its value as a program virtual address, pushes a frame, and returns to the next PC.
- JMP32 compares low 32 bits for all signed/unsigned conditions and both source modes.
- A V3 ELF registered as a CPI callee is loaded as V3; it cannot fall through to raw V0 text.
- A V0 ELF and the existing CPI success/rollback tests retain their results.

## File map

- `docs/SBPFV3_ISA_MATRIX.md`: pinned runtime/toolchain versions and one row per V3 opcode form, with test links.
- `SVM/SBPF/Elf.lean`, `SVM/SBPF/Runner.lean`: strict V3 program image and shared top-level/CPI loading.
- `SVM/SBPF/Decode.lean`, `SVM/SBPF/ISA.lean`: V3 opcode and operand interpretation.
- `SVM/SBPF/Machine.lean`, `SVM/SBPF/Execute.lean`: callx target mapping, frames, and instruction effects.
- `SVM/SBPF/ElfTests.lean`, `SVM/SBPF/RunnerTests.lean`, `SVM/SBPF/V3DecodeTests.lean`: Lean acceptance and rejection pins.
- `qedsvm-rs/tests/diff_mollusk.rs`, `qedsvm-rs/tests/fixtures/`: execution corpus and fixture provenance.

---

### Task 1: Pin the V3 ISA and conformance target

**Files:** Create `docs/SBPFV3_ISA_MATRIX.md`; modify `qedsvm-rs/tests/fixtures/README.md`; create `SVM/SBPF/V3DecodeTests.lean`.

**Interfaces:** Produce a checked list of V3-accepted opcode forms, their operand constraints, and corresponding Lean decode/execution tests. Later tasks close each missing row.

- [ ] **Step 1: Record the existing version pins.** Read `qedsvm-rs/Cargo.lock`, `qedsvm-rs/Cargo.toml`, and the checked-in source fixture. Record `solana-sbpf 0.14.4`, Mollusk `0.12.1-agave-4.0`, cargo-build-sbf 4.3.0, platform-tools 1.57, and the compiled fixture SHA-256 in the matrix.
- [ ] **Step 2: Enumerate valid V3 forms from the pinned verifier.** Use the V3 guards in `solana-sbpf-0.14.4/src/verifier.rs`. Include `lddw`; byte/half/word/dword loads and stores; ALU32/ALU64 immediate and register forms; `le`/`be`; all 11 JMP32 conditions in immediate and register modes; all JMP64 forms; `call`, `callx`, and `exit`. Exclude V2-only PQR opcodes. Mark immediate zero divisors, shift bounds, register 10 writes, `lddw` continuation, and branch bounds as verifier rejects.
- [ ] **Step 3: Add a green baseline decode pin.** V3 `callx` reads its register from `dst`:

  ```lean
  example : Decode.decodeInsn (Decode.bytesOfHex "8d01000000000000") #[0] 0 [] .v3 =
      some (.callx .r1, 8) := by
    native_decide
  ```

- [ ] **Step 4: Run `lake build SVM.SBPF.V3DecodeTests`.** Add a row in the matrix for each verifier-accepted opcode and each rejection rule. Mark only the currently tested rows complete; Task 3 adds red tests and closes the remaining rows.
- [ ] **Step 5: Commit the matrix and green baseline test** with `git commit -m "test(sbpfv3): pin verifier opcode inventory"`.

### Task 2: Complete strict V3 ELF routing, including CPI

**Files:** Modify `SVM/SBPF/Elf.lean`, `SVM/SBPF/Runner.lean`, `SVM/SBPF/ElfTests.lean`, `SVM/SBPF/RunnerTests.lean`, and `SVM/SBPF/BoundedCpi.lean` only as required by the new loader route.

**Interfaces:** `Elf.loadV3` remains the strict parser. A single runner helper returns decoded instructions, mapped code/read-only memory, entry PC, and version for both top-level execution and `buildCalleeVM`.

- [ ] **Step 1: Add failing ELF tests** for no section headers, invalid `e_flags`, wrong program-header flags/address/offset, truncated segment, invalid entry point, and a valid two-segment V3 image. Reuse `v3Minimal` and `v3WithRodata` in `ElfTests.lean`; mutate one header field per test using `set!` as the existing tests do.
- [ ] **Step 2: Add a failing CPI regression** in `RunnerTests.lean`: register `v3HelloElf` as a V3 ELF callee, invoke it, and assert its exit/account state is reached. Add a nonzero-result case that checks rollback through the existing `Cpi.applyResult` boundary.
- [ ] **Step 3: Route the CPI loader by `Elf.readVersion`.** In `Runner.buildCalleeVM`, replace the V0-only `tryElf` branch with a V3 branch that invokes `Elf.loadV3`, `Decode.decodeProgram text [] .v3`, maps `textAddr` and read-only bytes, and uses `entrySlot`. Keep the current V0 branch for V0 and the raw-text branch only for input that is not ELF. Reject a malformed or unsupported-version ELF without raw-text fallback.
- [ ] **Step 4: Run `lake build SVM.SBPF.ElfTests SVM.SBPF.RunnerTests SVM.SBPF.BoundedCpi` and `lake build ExamplesCpi`.** Confirm the new V3 CPI case and all existing CPI rollback cases pass.
- [ ] **Step 5: Commit** with `git commit -m "feat(sbpfv3): route CPI callees through strict V3 loader"`.

### Task 3: Close V3 decoder and verifier-rule gaps

**Files:** Modify `SVM/SBPF/Decode.lean`, `SVM/SBPF/ISA.lean`, `SVM/SBPF/ElfTests.lean`, and `SVM/SBPF/V3DecodeTests.lean`.

**Interfaces:** `Decode.decodeInsn ... .v3` and `Decode.decodeProgram ... .v3` accept exactly the supported V3 instruction forms and enforce the pinned verifier's operand restrictions. Existing `.v0` calls retain their meaning.

- [ ] **Step 1: Add one red test per missing matrix row.** For each opcode, encode a valid 8-byte instruction (16 bytes for `lddw`), provide a slot map large enough for a branch or call target, and assert the exact `Insn` constructor. Pair `callx`, `lddw`, shifts, division, endian conversion, and JMP32 with invalid operand tests.
- [ ] **Step 2: Run `lake build SVM.SBPF.V3DecodeTests` and group failures by missing opcode, wrong operand, or missing verifier guard.** Keep that classification in the matrix so implementation does not mistake a rejected input for an unmodeled valid instruction.
- [ ] **Step 3: Implement only the missing V3 constructors and decode cases.** Preserve the current V0 result for the same bytes where its ISA differs. Apply V3 register, immediate, jump-target, and `callx dst < r10` constraints before returning a decoded instruction.
- [ ] **Step 4: Run the Lean decode/ELF tests and the V0 decode pins:**

  ```text
  lake build SVM.SBPF.V3DecodeTests SVM.SBPF.ElfTests
  lake build Examples
  ```

- [ ] **Step 5: Commit** with `git commit -m "feat(sbpfv3): complete versioned ISA decoding"`.

### Task 4: Execute V3 callx, calls, and all opcode effects

**Files:** Modify `SVM/SBPF/Machine.lean`, `SVM/SBPF/Execute.lean`, `SVM/SBPF/Runner.lean`, `SVM/SBPF/RunnerTests.lean`, and `SVM/SBPF/V3DecodeTests.lean`.

**Interfaces:** V3 execution has the executable text address and slot map needed to translate an indirect call's register value to logical PC. A callx pushes a normal saved-register frame and enforces call-depth and target validity. Version-sensitive effects remain distinguishable from V0.

- [ ] **Step 1: Add failing V3 runner tests** for `callx dst`, return PC, saved `r6`–`r10`, invalid target, 65th frame, all JMP32 signed/unsigned conditions with nonzero upper bits, immediate/register ALU boundaries, and `le`/`be` widths. Each test uses the same instruction bytes in a strict V3 ELF.
- [ ] **Step 2: Run `lake build SVM.SBPF.RunnerTests` and record each failing form against the opcode matrix.**
- [ ] **Step 3: Add program-address/slot-map metadata to the V3 execution context** and implement virtual-address-to-logical-PC translation for callx. Do not silently convert an invalid address to PC 0. Make the call and return stack behavior match the pinned interpreter's `CALL_REG`, `CALL_IMM`, and `EXIT` arms. Keep V0 proof behavior through an explicit compatibility route.
- [ ] **Step 4: Implement remaining V3 opcode effects** until every valid matrix row has a passing execution test. Assert the expected typed fault for invalid memory, target, and arithmetic cases. Use exact boundary values `0`, `0xffffffff`, `0x100000000`, and `0xffffffffffffffff` for width-sensitive tests.
- [ ] **Step 5: Run `lake build`, `lake build SVM.SBPF.RunnerTests`, and `lake build Examples`; commit** with `git commit -m "feat(sbpfv3): execute complete V3 ISA"`.

### Task 5: Differential execution and Stage 1 gate

**Files:** Modify `qedsvm-rs/tests/diff_mollusk.rs`, `qedsvm-rs/tests/fixtures/README.md`, `docs/SBPFV3_ISA_MATRIX.md`, and `.github/workflows/build.yml`; add narrowly scoped V3 `.so` fixtures and sources under `qedsvm-rs/tests/fixtures/`.

**Interfaces:** The differential suite compares one ELF under qedsvm and Mollusk on exit, typed error, memory/account bytes, logs, and compute units. The matrix links each opcode form to Lean and differential evidence.

- [ ] **Step 1: Build source-backed V3 fixtures** with `cargo-build-sbf --arch v3` using platform-tools 1.57. Add hand-assembled strict-header fixtures only for verifier-valid forms LLVM does not emit. Record each source, exact build command, and SHA-256; reject a rebuilt binary whose hash changed unexpectedly.
- [ ] **Step 2: Add red differential cases** for both sides of each JMP32 condition, callx and relative call/return, endian/width boundaries, and a V3 CPI callee's success and rollback. Follow the existing `sbpfv3_compiled_account_matches_mollusk` assertion shape in `diff_mollusk.rs`.
- [ ] **Step 3: Fix only observed semantic discrepancies** in the decoder, runner, or fixture. Update the matrix row with the test name and its measured compute units after it agrees with Mollusk.
- [ ] **Step 4: Add an explicit CI build of `SVM.SBPF.V3DecodeTests`, `SVM.SBPF.ElfTests`, `SVM.SBPF.RunnerTests`, and `SVM.SBPF.BoundedCpi`.** These test modules are outside the production Lean aggregator, so `lake build` alone is not their gate.
- [ ] **Step 5: Run the Stage 1 gates:**

  ```text
  lake build
  lake build SVM.SBPF.V3DecodeTests SVM.SBPF.ElfTests SVM.SBPF.RunnerTests SVM.SBPF.BoundedCpi
  lake build Examples
  cargo test --workspace --quiet
  cargo test --features diff-mollusk --quiet
  cargo clippy --workspace --all-targets --all-features -- -D warnings
  cargo fmt --all -- --check
  ```

  Run cargo commands from `qedsvm-rs/`. Confirm all matrix rows are complete, V0 regressions pass, and no theorem uses `sorry`.
- [ ] **Step 6: Commit** with `git commit -m "test(sbpfv3): gate full V3 execution against Mollusk"`.

## Stage 1 handoff

Stage 1 is complete only when the matrix and conformance gates pass. Stage 2 is specified in `docs/superpowers/plans/2026-09-25-sbpfv3-proof-default.md`; it consumes the versioned instruction and execution semantics produced here.
