# sBPF v3 Verification Support Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Run and prove selected paths of sBPF v3 ELF programs while retaining the existing V0 proof path.

**Architecture:** Carry an explicit version from the ELF header into both Rust and Lean decoders. Use separate V0 section/relocation and V3 program-header loaders, then converge on a versioned instruction array and the existing runner/proof machinery. Add V3 instruction and call semantics before allowing qedlift to emit a v3 theorem.

**Tech Stack:** Lean 4, Rust, `solana-sbpf 0.14.4`, Mollusk, Lake.

**Spec:** `docs/superpowers/specs/2026-09-24-sbpfv3-support-design.md`

## Progress (2026-09-24)

- Completed: version gate and fixtures; strict V3 program-header parsing;
  Lean runner path; versioned static/relative calls and JMP32 execution;
  generic JMP32 one-step specs; pinned V3 concrete execution theorems for
  static calls and an account-byte update; Mollusk differential execution
  for both binaries (including account data and compute units).
- Completed: version-aware Rust symbolic execution and call classification,
  V3 decode pins, a full V3 ELF-to-text pin, and a generated selected-path
  account-byte `cuTripleWithinMem` theorem without `sorry`.
- Remaining scope: a toolchain-built V3 fixture after upgrading local
  platform-tools beyond 1.52. The checked-in fixture is reproducibly
  hand-assembled and compared with Mollusk. V3 lifting deliberately rejects
  JMP32 forms beyond `JEQ32_IMM`, `callx`, unknown syscalls, and shared-text
  mode until their symbolic path specs are implemented.

## Global Constraints

- Preserve V0 fixtures and generated proof output.
- Reject V1, V2, and V4 in the Lean proof path until separately modeled.
- Never interpret a V3 opcode using V0 call or jump semantics.
- Pin ELF version and decoded text in generated proofs.
- Treat unsupported V3 features as errors, not proof obligations satisfied by placeholders.

## Review Focus

- A V3 ELF whose section headers are absent must load through program headers.
- A V3 relative internal call must not be classified by a V0 Murmur3 registry lookup.
- A V3 static syscall hash must not be classified as an internal call.
- A JMP32 with nonzero upper register bits must branch on the low 32 bits only.
- A V0 ELF must retain identical execution and generated proof behavior.

---

### Task 1: Version gate and fixtures

**Files:** `SVM/SBPF/Elf.lean`, `SVM/SBPF/ElfTests.lean`, `qedsvm-rs/qed-analysis/src/image.rs`, `qedsvm-rs/qedlift/tests/public_api.rs`, `qedsvm-rs/tests/fixtures/`.

**Interfaces:** Produce an explicit `SbpfVersion` for Rust analysis and a Lean version tag parsed from `e_flags`; only V0 and V3 are accepted by the new boundary. Later tasks consume these values.

- [ ] Write tests for V0 acceptance, V3 recognition, unsupported versions, and malformed `e_flags`; use a checked-in V3 ELF fixture with documented provenance.
- [ ] Run the focused Rust and Lean tests and observe the V3 recognition failure.
- [ ] Add the version values and reject unsupported versions before code generation; route V3 to an explicit `unsupported_v3` error until later tasks provide the loader.
- [ ] Run focused and workspace tests; commit the gate and fixture.

### Task 2: V3 program-header loader

**Files:** `SVM/SBPF/Elf.lean`, `SVM/SBPF/Runner.lean`, `SVM/SBPF/ElfTests.lean`, `qedsvm-rs/qed-analysis/src/image.rs`.

**Interfaces:** Produce `LoadedProgram { version, textBytes, textAddr, entrySlot, rodata }` in Lean; V0 adapts its existing loader, V3 reads PT_LOAD segments. Later decoder and runner tasks consume this record.

- [ ] Write failing tests for V3 with and without read-only segment, missing executable segment, out-of-range entry, overlapping or out-of-bounds segment, and ignored section headers.
- [ ] Run `lake build SVM.SBPF.ElfTests` and confirm the first V3 case fails for the missing program-header loader.
- [ ] Implement strict V3 header and PT_LOAD parsing using bounded reads; adapt runner initialization to `LoadedProgram`.
- [ ] Run Lean ELF tests and the V0 runner tests, then commit.

### Task 3: Versioned calls and JMP32 semantics

**Files:** `SVM/SBPF/ISA.lean`, `SVM/SBPF/Decode.lean`, `SVM/SBPF/Execute.lean`, `SVM/SBPF/InstructionSpecs/Jump.lean`, `SVM/SBPF/SpecGen.lean`, related decoder tests.

**Interfaces:** `Decode.decodeProgram` accepts the explicit version; V3 call decoding consults the `src` field, V3 `callx` consults `dst`, and `Insn` includes 32-bit conditional branches. Instruction specs expose one-step triples for these new constructors.

- [ ] Write failing decode and execute tests for static syscall, relative internal call, destination-register callx, and JMP32 with high bits set.
- [ ] Run the focused Lean tests and confirm expected V3 failures.
- [ ] Implement versioned decode and execution, preserving the V0 decoder wrapper where required for generated artifacts.
- [ ] Add generic one-step JMP32 proofs and wire their names through `SpecGen`; run `lake build SVM.SBPF.RunnerTests` and commit.

### Task 4: Rust lifting and proof generation

**Files:** `qedsvm-rs/qedlift/src/isa.rs`, `qedsvm-rs/qedlift/src/exec/control.rs`, `qedsvm-rs/qedlift/src/exec/step.rs`, `qedsvm-rs/qedlift/src/spec_call.rs`, `qedsvm-rs/qedlift/src/render.rs`, `qedsvm-rs/qedlift/tests/public_api.rs`.

**Interfaces:** The `Lifter` consumes `ProgramImage.version`; rendered Lean text invokes the matching versioned decoder and pins that version. Unknown V3 opcode or syscall returns a typed diagnostic before artifact emission.

- [ ] Write failing Rust tests using the V3 fixture for static syscall versus relative call and JMP32 branch rendering; assert V0 output remains byte-identical.
- [ ] Run focused `cargo test -p qedlift` and observe the expected failures.
- [ ] Thread version into opcode rendering, call target resolution, symbolic execution, and generated decode theorem.
- [ ] Build a generated V3 module with Lake, run Rust workspace tests and Clippy, then commit.

### Task 5: End-to-end discharge and differential gate

**Files:** `qedsvm-rs/tests/diff_mollusk.rs`, `qedsvm-rs/tests/fixtures/`, `examples/lean/Generated/`, `docs/COVERAGE.md`, `docs/TCB.md`, CI workflow.

**Interfaces:** A checked-in V3 fixture and trace produce a sorry-free selected-path theorem; differential execution yields the same state as Mollusk. The CI gate builds the Lean theorem and runs the focused conformance test.

- [ ] Create a reproducible V3 source fixture with a static syscall, JMP32, internal call, and account update using platform-tools v1.53 or newer; record exact toolchain and ELF hash.
- [ ] Write the differential test and emitted-proof pin, run them red, and identify missing instructions or syscall semantics.
- [ ] Implement the remaining supported subset and regenerate the V3 proof artifact; run the differential test and `lake build Examples` green.
- [ ] Run `cargo test --workspace`, `cargo test --features diff-mollusk`, `cargo fmt --all -- --check`, strict Clippy, `lake build`, and `lake build Examples`; update coverage and TCB limits; commit.
