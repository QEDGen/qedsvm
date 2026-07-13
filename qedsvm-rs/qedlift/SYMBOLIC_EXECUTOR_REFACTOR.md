# Symbolic Executor Refactor Plan

Status: Phases 0–4 implemented; Phase 5 is next

Baseline: `fea7dff` on `refactor/rust-tooling-architecture` / PR #67

Scope: `qedsvm-rs/qedlift` internals; no change to generated Lean semantics

## Objective

Make the symbolic executor easier to navigate and extend without weakening its
fail-closed behavior or perturbing generated proof artifacts.

The refactor should leave a new contributor with clear answers to four
questions:

1. Where is one instruction's symbolic effect implemented?
2. Where is path and trace control flow decided?
3. Where is a syscall registered and connected to its effect emitter?
4. Which state belongs to the symbolic machine, proof construction, memory
   alias planning, and output naming?

## Non-goals

- Do not add new opcodes, syscalls, loop support, or proof capabilities.
- Do not change the public `ProgramImage` / `Lifter` / `LiftOptions` API unless
  an internal boundary cannot be expressed without doing so.
- Do not change theorem names, binder names, generated Lean formatting, CU
  accounting, path selection, or failure messages.
- Do not re-bless golden artifacts to make the refactor pass.
- Do not redesign the Lean proof model or refinement layer.

## Current pressure points

- `src/exec.rs` is about 1,421 lines and contains opcode effects, syscall
  registration, fault-terminal types, path walking, trace interpretation,
  branch selection, and retry orchestration.
- `src/state.rs` is about 446 lines. `SymState` has roughly 30 fields spanning
  machine values, proof obligations, syscall artifacts, memory aliasing, and
  retry plans.
- `src/spec_call.rs` predicts fresh names that `step()` will allocate later.
  This ordering dependency is documented around its load/store/call handling
  and is the most fragile extensibility seam.
- `exec.rs`, `lift.rs`, `spec_call.rs`, `transition.rs`, and `driver.rs` import
  the crate root with `use super::*`, so their real dependencies are implicit.
- `step()` returns `bool`, but the walker handles exits before calling it and
  discards the returned value. Control flow therefore has two partially
  overlapping representations.

## Required invariants

Every phase must preserve all of these:

- All existing `qedlift` golden files remain byte-identical.
- The complete 82-test golden suite remains present; no tests may be deleted or
  weakened.
- Unsupported behavior continues to return the same `DiagnosticKind` and
  displayed message.
- Trace and static-walk branch decisions remain identical.
- The modeled-syscall table remains the single source of truth for rendering,
  dispatch, terminal faults, and coverage classification.
- Fresh-name allocation order remains identical until a phase explicitly
  replaces prediction with reservation and proves byte identity.
- `ProgramImage` and static analysis are reused across multi-arm lifts.
- No phase may use `QEDLIFT_BLESS=1`.

## Target module layout

The intended endpoint is:

```text
src/
├── exec/
│   ├── mod.rs               public(crate) execution facade and shared types
│   ├── step.rs              per-opcode symbolic state transitions
│   ├── control.rs           TraceCursor, branch decisions, typed outcomes
│   ├── syscall_registry.rs  modeled syscall metadata and dispatch lookup
│   └── walk.rs              path execution and alias-retry convergence
├── state.rs                 SymState facade and focused sub-state accessors
├── spec_call.rs             proof-call rendering from prepared step facts
└── syscalls.rs              syscall effect emitters
```

`branch.rs` remains the representation of emitted branch hypotheses;
`exec/control.rs` owns runtime path selection, so the two names do not collide.

The target layout is directional, not a mandate to create empty abstraction
layers. A file should exist only when it owns a coherent type or operation.

## Phase 0 — Pin executor behavior directly

Add small executor-focused tests before moving code. Golden tests remain the
end-to-end oracle, but these tests should localize failures during later phases.

Add tests for:

- static discriminator decisions for `jeq`, `jne`, and `jgt`;
- traced taken/fall-through decisions;
- trace/decoded-target mismatch returning `DiagnosticKind::TraceInput`;
- modeled, unmodeled, and unknown call-hash classification;
- top-level exit versus nested return behavior;
- retry-plan convergence inputs (`new_hot`, `new_blob_splits`) where they can be
  tested without generating a full module.

Exit criteria:

- The new tests exercise typed results rather than matching message substrings.
- The existing 82 golden tests still pass unchanged.

Suggested commit: `test: pin symbolic executor control flow`

## Phase 1 — Make dependencies explicit

Replace production `use super::*` imports with explicit module imports. Start
with `exec.rs`, then `spec_call.rs`, `lift.rs`, `transition.rs`, and `driver.rs`.

While doing this:

- import types from their owning modules rather than relying on crate-root
  forwarding imports;
- keep public re-exports in `lib.rs` limited to the supported library API;
- remove crate-root imports that exist only to make sibling glob imports work;
- do not move functions yet.

This phase exposes the real dependency graph and makes the mechanical split in
Phase 2 reviewable.

Exit criteria:

- No production module uses `use super::*`.
- Public rustdoc still exposes only the intended API.
- There are no generated-output changes.

Suggested commit: `refactor: make qedlift dependencies explicit`

## Phase 2 — Mechanically split `exec.rs`

Move existing code into the target `exec/` files without changing signatures or
logic:

- `step()` and opcode helpers → `step.rs`;
- `AbortKind`, `OobSyscall`, `SyscallModel`, tables, hash lookup, and traced
  dispatch → `syscall_registry.rs`;
- conditional-opcode detection and branch resolution → `control.rs`;
- `FaultTerminal`, `WalkResult`, and `walk_and_exec()` → `walk.rs`;
- narrow re-exports → `exec/mod.rs`.

Do not combine this move with state redesign. Git should recognize most of the
change as moved code.

Clean up only obvious duplicated no-op lines encountered during the move, such
as repeated comments or identical `BTreeMap::insert` calls. Keep those cleanups
separate in the diff when practical.

Exit criteria:

- No execution source file is substantially above roughly 600 lines unless the
  code is one cohesive opcode table.
- The module facade exposes only what `lift`, `driver`, and tests consume.
- Full golden output remains byte-identical.

Suggested commit: `refactor: split symbolic executor modules`

## Phase 3 — Type the walk state and outcomes

Replace positional walk inputs and manual trace arithmetic with focused types:

```rust
struct WalkOptions<'a> {
    trace: Option<&'a [usize]>,
    target_discriminator: Option<i64>,
    arm_entry: Option<usize>,
    program_entry: usize,
}

struct TraceCursor<'a> {
    pcs: &'a [usize],
    index: usize,
}

enum StepOutcome {
    Continue,
    Jump(usize),
    Call(usize),
    Return(usize),
    Exit,
    Fault(FaultTerminal),
}
```

The exact representation may differ, but it must establish one owner for:

- current/next PC;
- trace advancement and bounds checks;
- taken/fall-through validation;
- local call and return routing;
- terminal exit or fault selection.

Resolve the current ambiguous `step() -> Result<bool, LiftError>` contract.
Either `step()` handles control flow and returns `StepOutcome`, or it becomes a
data-effect-only function returning `Result<(), LiftError>` while the walker is
the sole control-flow owner. Do not retain two exit implementations.

Exit criteria:

- No direct `trace[index]` access exists outside `TraceCursor`.
- Empty and exhausted traces are typed errors or typed termination, never
  indexing assumptions.
- Control-flow tests from Phase 0 describe the new types directly.
- Failure messages and output remain unchanged.

Suggested commit: `refactor: type symbolic walk control flow`

## Phase 4 — Eliminate fresh-name prediction

This is the most important semantic refactor and should be isolated in its own
commit.

Today `spec_call_for()` runs before `step()` and predicts names based on
`state.fresh`. Replace prediction with an explicit prepare/apply protocol. One
possible shape is:

```rust
struct PreparedStep {
    spec_call: Option<SpecCall>,
    reserved_names: StepNames,
    control: ControlDecision,
}

fn prepare_step(
    state: &mut SymState,
    instruction: &Insn,
    context: StepContext,
) -> Result<PreparedStep, LiftError>;

fn apply_step(
    state: &mut SymState,
    instruction: &Insn,
    prepared: PreparedStep,
) -> Result<StepOutcome, LiftError>;
```

Requirements:

- one allocator reserves every fresh identifier exactly once;
- spec generation consumes reserved identifiers rather than formatting a future
  counter value;
- instruction execution uses the same reservation when materializing state;
- syscall emitters use the same allocator abstraction;
- no module other than the allocator reads or increments the raw counter.

Prefer a small `FreshNames` type over scattering helper methods. Preserve the
current allocation sequence so all emitted binders remain byte-identical.

Exit criteria:

- `rg 'state\.fresh|\.fresh \+=' src` finds uses only inside the allocator.
- `spec_call.rs` contains no comments or logic about predicting a later name.
- All golden files remain byte-identical without blessing.

Suggested commit: `refactor: reserve symbolic names before execution`

## Phase 5 — Decompose `SymState` behind methods

Do not immediately rewrite every field access into nested public fields. First
make fields private and introduce behavior-oriented methods. Then group storage
only where the call sites demonstrate a stable boundary.

Candidate groups:

```text
SymState
├── machine   registers, memory cells, call stack
├── proof     pre-atoms, region requirements, branch and side hypotheses
├── alias     spans, overlap failures, hot regions, blob split/retry plans
├── syscalls  syscall PCs, CU variables, byte-array effects and hypotheses
└── names     the single fresh-name allocator
```

Key rule: callers should ask the state to perform an operation, not mutate its
collections directly. Examples:

- `record_branch(...)` rather than `branch_hyps.push(...)`;
- `record_aliases(pc)` rather than draining pending vectors in the walker;
- `take_retry_plan()` rather than reading `new_hot` and `new_blob_splits`;
- `finish_syscall(...)` rather than updating four syscall collections;
- `proof_inputs()` for read-only emission data.

This phase can be split into multiple commits. Start with alias/retry state,
because it already has a clear consume-and-retry lifecycle. Move machine and
proof state only after fresh-name allocation is stable.

Exit criteria:

- `SymState` fields are private outside `state.rs` or focused child modules.
- The walker consumes one typed retry result.
- Syscall emitters cannot leave partially registered syscall artifacts.
- Golden output and diagnostic behavior remain unchanged.

Suggested commits:

- `refactor: encapsulate alias retry state`
- `refactor: encapsulate symbolic proof state`
- `refactor: encapsulate syscall effects`

## Phase 6 — Tighten syscall extensibility

Keep the syscall registry as the single source of truth, but make a registry row
declare all relevant behavior visibly:

- symbol/hash identity;
- whether a running effect is modeled;
- running effect handler;
- unconditional terminal fault, if any;
- conditional OOB fault metadata, if any;
- Lean syscall constructor used for rendering.

Add a table-consistency test ensuring that modeled rows have the metadata their
consumers require. Avoid parallel lists such as a separate known-name table when
the registry can answer the same question.

Only after the registry boundary is stable, consider splitting the 1,100-line
`syscalls.rs` by behavior (`memory`, `data`, `crypto`, `system`). Do not split it
solely by file size.

Exit criteria:

- Adding a modeled syscall requires one registry row plus one effect function.
- Rendering, coverage, trace dispatch, and fault detection all derive from that
  row.
- Registry consistency is unit-tested.

Suggested commit: `refactor: make syscall registry self-contained`

## Validation required after every phase

From `qedsvm-rs/`:

```bash
cargo fmt --all -- --check
cargo clippy -p qedlift --all-targets -- -D warnings

# Fast focused checks while iterating.
cargo test -p qedlift tests::bytecode
cargo test -p qedlift tests::metadata
cargo test -p qedlift tests::syscalls
cargo test -p qedlift tests::transitions

# Required before each phase commit.
cargo test -p qedlift
```

From the repository root, verify the public CLI still produces the pinned file:

```bash
cargo run --manifest-path qedsvm-rs/Cargo.toml -p qedlift -- \
  --so qedsvm-rs/tests/fixtures/byte_increment.so \
  --output /tmp/ByteIncrementLifted.lean

cmp /tmp/ByteIncrementLifted.lean \
  examples/lean/Generated/ByteIncrementLifted.lean
```

Before the final PR handoff, also run:

```bash
cargo test -p qedrecover -p qed-artifacts -p qed-analysis
cargo clippy -p qedrecover -p qedlift -p qed-artifacts -p qed-analysis \
  --all-targets -- -D warnings
```

## Stop conditions

Stop and investigate instead of continuing when:

- any generated Lean file differs, even if the theorem still builds;
- binder or fresh-variable names change;
- a failure moves to `DiagnosticKind::Other`;
- a trace mismatch becomes a panic or silent fall-through;
- a syscall is rendered differently from the effect/fault selected by the
  registry;
- analysis or ELF loading moves inside a per-arm loop;
- a phase requires broad public API changes unrelated to execution internals.

If a golden diff is intentional and demonstrably better, handle it as a
separate capability change after this refactor, with its own review. Do not fold
it into these structural commits.

## Recommended next-session sequence

1. Confirm the branch/PR baseline and run `cargo test -p qedlift -- --list`.
2. Read this file plus `exec.rs`, `state.rs`, and the fresh-name comments in
   `spec_call.rs`; do not rediscover the entire repository.
3. Implement Phase 0 and Phase 1 only.
4. Run the full golden suite and commit.
5. Implement the mechanical Phase 2 split and commit separately.
6. Reassess the target types before starting Phase 3; do not assume the example
   structures above are exact.
7. Leave Phases 4–6 for separate, reviewable commits even if earlier phases are
   straightforward.

The safest high-value stopping point for one session is completion of Phases
0–2: direct executor pins, explicit dependencies, and a behavior-preserving
module split. Phases 3–6 change ownership and should proceed only with the
earlier baseline fully green.
