# qedsvm

**Verify what runs on Solana, not what you wrote.**

A Lean 4 model of the Solana Virtual Machine. It operates on the compiled `.so`, the same artifact mainnet runs, and does two separate jobs:

- **Execute** a program on a model diff-tested against mollusk/agave. The `qedsvm-rs` crate is this executor, published mainly so the model can be reused by conformance tests, fuzzing, and downstream diff-test harnesses.
- **Verify** a selected bytecode path against a separation-logic spec with a proven compute-unit bound, in Lean. `qedlift` emits machine-checked `cuTripleWithinMem` theorems from compiled bytecode; supported shapes also get abstract refinement corollaries.

> **Execution is not verification.** The Rust crate tells you what a program does on one input; it does not prove what it does on all of them. If you only use `qedsvm-rs`, you have a conformant executor, not a verified program. Verification lives entirely in the Lean layer.

Small trust base: Lean 4 ISA semantics in `SVM/SBPF/{Execute,Decode,Memory}.lean`, explicit crypto trust statements, and the generated proof obligations that `lake build` checks. The Rust executor is not a verifier.

## Install

```lean
require qedsvm from git
  "https://github.com/QEDGen/qedsvm.git" @ "v0.5.0"
```

Prerequisites: Lean (via `elan`) and `cargo` / `rustc`. Lake builds `qedsvm-rs/lean-bridge/` automatically. The public module boundary (both proof engines + the discharge route) is documented in [docs/API.md](docs/API.md).

## Demo

One command per job makes both halves visible in seconds.

```bash
# EXECUTE (conformance): run incrementer + p-token Transfer through qedsvm and
# mollusk side by side. Prints CU, return data, account-data digest, byte+CU verdict.
# This checks the model matches agave; it does not verify a program.
cargo run --release --features diff-mollusk \
  --manifest-path qedsvm-rs/Cargo.toml --example conformance_demo

# VERIFY: type-check the end-to-end witness theorem for a 4-instruction sBPF program.
lake build ProofDemo
```

[`examples/lean/ProofDemo.lean`](examples/lean/ProofDemo.lean) is the entry point; the theorem itself lives in [`examples/lean/ByteIncrement.lean`](examples/lean/ByteIncrement.lean), which chains raw bytes to a discharged separation-logic spec with no `sorry`. No rustc, no external sBPF semantics.

## Use

### From Lean

```lean
-- Run a compiled program
example : Runner.runElfForExit anchorBinary { cuBudget := 200_000 } = some 0 := by
  native_decide

-- Prove a sequence
example : cuTripleWithin 2 0 2 someCode P Q := by sl_block_iter
```

Worked examples: [`examples/lean/ByteIncrement.lean`](examples/lean/ByteIncrement.lean) (raw bytes → witness theorem) · [`examples/lean/PToken/BalanceSpec.lean`](examples/lean/PToken/BalanceSpec.lean) (Solana-data-model refinement target).

### Lift a compiled program to a proof (`qedlift`)

`qedlift` and its sibling `qedrecover` are the lifting front-end. `qedrecover` binds IDL/overlay claims to locations in the binary and emits `qedmeta.toml`; it is an analysis-only standalone crate at `qedsvm-rs/qedrecover/`. `qedlift` consumes binary bytes plus targeting metadata and emits Lean proof modules.

Point it at a `.so` and it emits a Lean module that pins the walked `.text` bytes through `SVM.SBPF.Decode`, states a `cuTripleWithinMem` Hoare triple synthesized by symbolic execution, and discharges the proof. Small binaries use a full `decodeProgram` theorem; large binaries use per-PC decode pins. The proof closes with no `sorry`.

```bash
cargo run --features qedrecover --bin qedlift -- \
  --so qedsvm-rs/tests/fixtures/byte_increment.so \
  --output examples/lean/Generated/ByteIncrementLifted.lean
```

With `--trace`, qedlift follows a concrete path through branchy bytecode. The checked-in lifts under [`examples/lean/Generated/`](examples/lean/Generated/) cover ByteIncrement, Counter, Logger, layout-general Vault examples, heap-bump allocation, and traced p-token arms. Abstract refinements are registered for Transfer, TransferChecked, MintTo, Burn, Counter increment, Vault field update, and heap allocation; other generated traced lifts are raw Hoare triples unless a refinement predicate is registered. Batch mode (`--idl`) targets IDL-described instructions.

For the full `.so` + IDL to proof workflow (qedrecover scoping, trace capture, qedlift, and `lake build`), see [`docs/PIPELINE.md`](docs/PIPELINE.md).

### From Rust (`qedsvm-rs`)

`qedsvm-rs` is the conformant executor, not a verifier. It runs compiled programs on the agave-faithful model and exists mainly so we can diff-test that model against mollusk, and so fuzzing and diff-test harnesses (for example [Janus](https://github.com/saicharanpogul/janus/tree/main/tests-qedsvm)) have a fast SVM to cross-check against. It proves nothing about your program.

```rust
use qedsvm::{ProgramResult, SVM};

let mut svm = SVM::default();
svm.add_program(&program_id, elf_bytes);
let result = svm.process_instruction(&instruction, &accounts)?;
```

Crate-level docs (differential testing, consuming qedsvm downstream, the `solana-account` version split) live in [`qedsvm-rs/README.md`](qedsvm-rs/README.md).

## Coverage

qedsvm has two coverage surfaces:

| Surface | What it means |
| --- | --- |
| Executor conformance | The Lean VM and Rust harness run compiled programs and diff-test observable behavior against mollusk/agave. |
| Proof coverage | `qedlift` emits Lean Hoare triples for selected paths over modeled instructions and modeled lift syscalls. Supported codec shapes get abstract refinements. |

The proof pipeline is path-scoped. It is broad at the raw Hoare-triple layer and narrower at the abstract-refinement layer. See [`docs/COVERAGE.md`](docs/COVERAGE.md) for the precise boundary and [`docs/PIPELINE.md`](docs/PIPELINE.md) for the `.so` → proof toolchain.

## Layout

```
SVM/                  Lean library: interpreter, spec layer, Solana SL predicates
examples/lean/        Hoare-proof examples (ByteIncrement, PToken/, CompilerRt*, …)
examples/lean/Generated/  qedlift output: .so → sorry-free Lean triples
examples/rust/        → qedsvm-rs/examples (symlink)
qedsvm-rs/            Cargo workspace
├── (root)            Mollusk-shaped Rust API + qedlift bin (--features qedrecover)
├── qedrecover/       Scoping tool: .so + IDL → qedmeta sidecar (analysis-only crate)
├── qed-analysis/     Shared sBPF analysis substrate (PC map, IDL account layout)
└── lean-bridge/      Agave-pinned crypto staticlib called by Lean
docs/                 Reference docs (API, PIPELINE, COVERAGE)
```

## License

MIT. See [`LICENSE`](LICENSE).

## Contributing

Issues and PRs welcome. The bar is **small trust base and honest specs**. Additions that broaden the surface without a clear soundness story will get pushback.
