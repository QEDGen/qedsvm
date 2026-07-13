# qedlift

`qedlift` turns one selected path through a compiled Solana `.so` into a
machine-checked Lean theorem.

| Input | Output |
| --- | --- |
| Compiled `.so`, targeting metadata, and usually a path trace | A Lean module containing bytecode pins, a bounded Hoare triple, and optionally an account-level refinement |

The theorem starts at the binary bytes. `qedlift` pins every walked instruction
back to the `.so`, symbolically executes the path, synthesizes its memory and
register pre/postconditions, and emits a proof that `lake build` checks.

`qedlift` is path-scoped. It does not automatically prove every path through a
binary, infer loop invariants, or invent semantics for unsupported instructions,
syscalls, or account layouts. Unsupported cases fail closed instead of producing
an unchecked theorem.

## Quick start

From the repository root:

```bash
cargo run --manifest-path qedsvm-rs/Cargo.toml \
  --features qedrecover --bin qedlift -- \
  --so qedsvm-rs/tests/fixtures/byte_increment.so \
  --output examples/lean/Generated/ByteIncrementLifted.lean

lake build ProofDemo
```

This five-instruction fixture is straight-line, so it needs no IDL or trace. The
generated module contains:

- the `.text` bytes extracted from `byte_increment.so`;
- a theorem connecting those bytes to the decoded instructions;
- a `cuTripleWithinMem` theorem with synthesized separation-logic assertions;
- a proof body discharged by qedsvm's instruction specifications and tactics.

## Normal `.so` to proof workflow

For a branchy Solana program, the recommended inputs are:

```text
program.so + program.qedmeta.toml + selected_path.pcs
                         │
                         ▼
                      qedlift
                         │
                         ▼
              Generated/ProgramPath.lean
                         │
                         ▼
                     lake build
```

[`qedrecover`](../../../qedrecover/README.md) produces the hash-pinned
`qedmeta.toml` from the program's `.so`, Codama IDL, and qedsvm overlay. A `.pcs`
trace contains one decimal logical PC per line and selects the concrete path
through branchy bytecode.

```bash
cargo run --manifest-path qedsvm-rs/Cargo.toml \
  --features qedrecover --bin qedlift -- \
  --so qedsvm-rs/tests/fixtures/p_token.so \
  --qedmeta qedsvm-rs/tests/fixtures/p_token.transfer.recovered.qedmeta.toml \
  --trace qedsvm-rs/tests/fixtures/p_token_transfer.pcs \
  --output /tmp/PTokenTransferLifted.lean
```

See the repository-level
[`PIPELINE.md`](../../../../docs/PIPELINE.md) for trace capture and the complete
sidecar contract.

## Modes

| Mode | Main arguments | Result |
| --- | --- | --- |
| Single path | `--so`, `--output`; optional `--trace`, `--target-disc`, `--arm-name`, `--descriptor` | One lift and an optional refinement sibling |
| Sidecar, one arm | `--so`, `--qedmeta`, `--target-name`, `--output`; optional `--trace` | One lift targeted from recovered metadata |
| Sidecar, multiple arms | `--so`, `--qedmeta`, `--output-dir`; optional `--shared-text` | One lift per in-scope sidecar instruction |
| IDL batch | `--so`, `--idl`, `--output-dir` | One module per IDL-described instruction |
| Whole transition | `--so`, `--descriptor`, `--output-dir`, `--transition` | One theorem per discovered path plus a transition bundle |
| Profile | `--so`, `--trace`, `--profile` | Symbolicated folded stacks; emits no Lean |
| Coverage survey | `--so`, `--coverage` | Ranked lift-frontier failures; emits no Lean |

`--shared-text <name>` lets large batch lifts share one bytecode/slot-map module
instead of embedding the same `.text` in every generated file.

## What is and is not proved

Every successful raw lift proves a bounded Hoare triple for the selected path over
the modeled sBPF semantics. Registered or descriptor-driven shapes can additionally
connect those concrete effects to account-level claims such as token balance or
vault-field updates.

A trace is path selection, not a theorem that the path is reachable for every
input. The emitted precondition, branch hypotheses, bytecode pins, and
satisfiability witness are what make the selected-path theorem precise. See
[`COVERAGE.md`](../../../../docs/COVERAGE.md) for the current instruction, syscall,
control-flow, and refinement boundary.

## Regression tests

The emitter suite regenerates every shipped lift/refinement fixture and compares
it byte-for-byte with the checked-in Lean:

```bash
cargo test --manifest-path qedsvm-rs/Cargo.toml \
  --features qedrecover --bin qedlift
```
