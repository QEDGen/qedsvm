# Proving concrete callees meet CPI contracts

## Intent and success criterion

The composed CPI path theorems (`<M><Name>_cpi_path`) hold for every callee
relation satisfying an explicit contract (`hMem` or `hW : Cpi.writesOnly`).
They do not yet say anything about the runner's actual CPI execution, and no
concrete callee has been shown to meet a contract.

This project connects two real programs end to end. It is complete when a
Lean theorem states that the Lean runner, executing the pinned caller
`sbpfv3_cpi_writer.so` with the pinned callee `sbpfv3_cpi_writer_callee.so`
registered at the invoked program id, from every state satisfying the
caller's precondition (and the side conditions below), exits with code 0,
leaves account `data[0] = 42`, and leaves the heap marker at heap+200 equal
to 43. The theorem must use only the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`) and build without `sorry`.

## Approach

The runner is shown to refine the relational CPI step (`Cpi.Transitions`)
for a callee relation defined from the runner itself; contracts are then
proved about that relation. Nothing about the callee is assumed that the
runner does not compute. Three layers, each reusable beyond the example.

### 1. Runner bridge (`SVM/SBPF/CpiRunner.lean`)

- `Cpi.runnerCallee registry sc fuel runCallee : CalleeSemantics` relates a
  caller state `s` to a result `r` exactly when
  `Runner.cpiCallNextState registry s sc fuel runCallee = Cpi.applyResult s r`.
- `cpiCallNextState_is_transition`: every branch of `cpiCallNextState` has
  that shape for some `r`. The invoke-depth, aliased-writability and
  unregistered/undecodable-callee branches map to `code = 1`,
  `mem = s.mem`, the caller's log and return data, and `cuConsumed = 0`; the
  native branch maps to its `Native.dispatch` result; the BPF branch maps to
  its `commitCallee` result.
- Caller decomposition: when the caller's fetch yields no CPI instruction
  except the invoke at `invokePc`, a runner run
  (`executeFnCpiWithFuel`) equals `executeFn` over the prefix, then the
  `cpiCallNextState` step, then `executeFn` over the suffix, with the fuel
  and compute-unit accounting of each segment stated explicitly. This reuses
  `executeFnCpi_eq_executeFn_of_no_cpi`.
- Consequence: an existing `_cpi_path` theorem instantiated with
  `callee := runnerCallee …` describes actual runner executions.

### 2. Write frames

- `Cpi.writesWithin callee (fp : Nat → Prop)`: every result's memory agrees
  with the caller's outside `fp`. `writesOnly callee addrs` becomes the
  special case `writesWithin callee (· ∈ addrs)`; existing theorems keep
  their statements.
- Generic frame, for any BPF callee: under `hNative`, the result memory of
  `runnerCallee` agrees with the caller's outside the write-back regions of
  the writable accounts parsed at invoke time: data from `dataPtr` up to the
  post-call length, both `data_len` slots, lamports and owner. This follows
  from `commitCallee`'s structure alone (`loadBytesAt` and `writeU64` only
  touch their ranges; violations and failure codes roll back to the
  caller's memory).
- Narrow frame, for the concrete callee: write-back rewrites the whole
  account, so `writesOnly … [data[0]]` needs callee knowledge. The callee's
  lifted triple frames every byte it does not store to, so the re-written
  `data[1]`, lengths, lamports and owner equal the caller's values.

### 3. Callee functional specification

- Serialization read lemmas: for a non-duplicate account, byte `i` of its
  data sits at a fixed offset of the callee input built by `buildCalleeVM`
  (header, data, realloc padding, alignment), and `loadInput` reads it back
  at `INPUT_START + offset`. Stated generically; proofs use `ByteArray`
  append/index lemmas with the padding kept symbolic.
- The callee's lifted path theorem (`Generated.Sbpfv3CpiWriterCalleeLifted`)
  plus its final `exit` gives, via `executeFnCpi_eq_executeFn_of_no_cpi` and
  `run_terminates_with_spec_mem`, the sub-VM's final state: exit code 0,
  byte 42 at the account's `data[0]`, every other framed byte unchanged.
- `commitCallee` read lemmas: for a writable account whose length is
  unchanged (no read-only or realloc violation), the caller memory after
  write-back at `dataPtr + i` equals the sub-VM byte at the account's
  serialized data offset `+ i`, and memory off the write-back footprint is
  unchanged.
- Combined: `runnerCallee` for the concrete callee satisfies
  `writesOnly … [dataPtr]` and `r.code = 0 → r.mem dataPtr = 42`.

### Final theorem

`examples/lean/CpiWriterEndToEnd.lean` instantiates
`Sbpfv3CpiWriterLiftedSuccess_cpi_path` with `callee := runnerCallee …`,
discharges `hW` with the narrow frame, and reads `data[0] = 42` from the
committed byte. Side conditions are hypotheses or decided facts: enough
fuel and compute budget, `invokeDepth = 0`, the caller's single account (no
aliasing), `hNative` for the callee's program id, the callee registered at
that id, and the caller's own path hypotheses.

## Refinements found while planning

- The runner charges one step unit on top of the CPI result, so
  `runnerCallee` relates `chargeCu (stepCpi …)` to `applyResult s r`, where
  `Runner.stepCpi` is the invoke step factored out of `executeFnCpiWithFuel`
  (the callee sub-run passed as a parameter).
- `writesWithin`/`writesOnly` constrain only successful results
  (`r.code = 0`); failed results are rolled back by `applyResult`, and a
  callee that ran out of fuel or faulted then needs no frame.
- The callee's program id, account descriptors and account block are caller
  memory, so contracts are proved for `Cpi.restrict (runnerCallee …) inv`
  with `inv` stating those memory facts; the end-to-end proof supplies `inv`
  at the invoke state.

## Deliverables

- `qedsvm-rs/tests/fixtures/sbpfv3_cpi_writer_callee.so`: hand-assembled
  V3 callee (`mov r2, 42; stxb [r1+96], r2; mov r0, 0; exit`), added to the
  build script and the SHA-256 manifest. The writer's Mollusk differential
  uses it for the success case; the rollback case keeps an inline failing
  callee.
- `Generated.Sbpfv3CpiWriterCalleeLifted` (qedlift output, byte-pinned).
- `SVM/SBPF/CpiRunner.lean` (bridge, decomposition, generic frame) and a
  serialization/write-back read-lemma module, both in the core library.
- `examples/lean/CpiWriterEndToEnd.lean`: the final theorem and a
  `native_decide` sanity run of the Lean runner on the concrete caller and
  callee (a concrete input ends with account data `[42, 0]` and heap
  marker 43).
- `docs/COVERAGE.md` updated to describe the runner bridge and the concrete
  end-to-end result.

## Testing and gates

`lake build`, `lake build Examples`, `lake build ExamplesCpi`, the Lean test
modules, `cargo test --workspace`, `cargo test --features diff-mollusk`,
strict Clippy, `cargo fmt --check`, `git diff --check`, and an axiom check
on every new theorem (standard axioms only).

## Out of scope

Native-program callees (excluded by `hNative`), nested CPIs inside the
callee, callees that reallocate, multi-account callers, and callees with
more than one path. Each is excluded by an explicit hypothesis or by the
fixture's shape, not modelled.

## Risks

- Serialization lemmas over `ByteArray` appends with a 10 KiB padding
  block: must stay symbolic; any proof that unfolds the padding is a bug
  (long compile is a bug smell).
- The fuel/compute-unit bookkeeping in the caller decomposition must match
  the runner exactly, including `chargeCu` and the CPI step's fuel unit.
- `cpiCallNextState` has many branches; each needs its `applyResult`
  witness, but only the BPF branch needs real reasoning.
