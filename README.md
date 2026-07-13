# qedsvm

**Verify what runs on Solana, not what you wrote.**

qedsvm executes compiled Solana programs and generates machine-checked Lean proofs
about selected bytecode paths. It works on the deployed sBPF `.so`, rather than
the Rust source that produced it, so the program proof is tied to the bytes a
validator executes.

| Mode | Input | Output | What it establishes |
| --- | --- | --- | --- |
| **Execute** | `.so`, instruction, and accounts | Account changes, return data, faults, and compute units | Behavior for one input, on a Lean model differentially tested against Mollusk/Agave |
| **Verify** | `.so`, selected path, and specification | A checked Lean theorem with a compute-unit bound | The stated property for every input satisfying that path's precondition |

The same Lean 4 SVM model is both the reference interpreter and the basis for the
proofs:

```text
Rust or assembly
      │ cargo-build-sbf
      ▼
  program.so
      ├── qedsvm executor ───────────── compare with Mollusk/Agave
      └── qedrecover + qedlift ──────── Lean theorem ── lake build
                 ▲
          IDL, spec, and optional trace
```

> **Scope:** qedsvm does not automatically prove an arbitrary whole program.
> Verification is path-scoped and covers modeled instructions and syscalls.
> Supported program shapes also receive account-level refinement theorems.
> Execution is not verification: running `qedsvm-rs` proves nothing about other
> inputs.

## Try it

Prerequisites: Lean via [`elan`](https://github.com/leanprover/elan) and a Rust
toolchain (`cargo` and `rustc`). The first build compiles the Lean/Rust bridge and
may take several minutes; subsequent runs reuse the build cache.

```bash
# EXECUTE: run incrementer and p-token Transfer through qedsvm and Mollusk.
# The output compares exit status, CU usage, return data, and account bytes.
cargo run --release --features diff-mollusk \
  --manifest-path qedsvm-rs/Cargo.toml --example conformance_demo

# VERIFY: check an end-to-end theorem for compiled sBPF bytes.
lake build ProofDemo
```

The execution demo is a conformance check for the model, not a program proof.
The proof demo starts at [`examples/lean/ProofDemo.lean`](examples/lean/ProofDemo.lean);
[`examples/lean/ByteIncrement.lean`](examples/lean/ByteIncrement.lean) ties raw
bytes to a discharged separation-logic theorem without `sorry`. Rust is used by
the build, but the Rust-to-sBPF compiler is not trusted to preserve a source-level
property: the theorem starts at the compiler's output bytes.

## Install as a Lean dependency

qedsvm is pre-1.0, so pin an exact release:

```lean
require qedsvm from git
  "https://github.com/QEDGen/qedsvm.git" @ "v0.11.0"
```

Lake builds `qedsvm-rs/lean-bridge/` automatically. The supported package surface
is documented in [`docs/API.md`](docs/API.md).

## How verification works

1. **[`qedrecover`](qedsvm-rs/qedrecover/README.md) scopes the claim.** It binds an IDL and qedsvm overlay to
   instruction arms and locations in the compiled binary, producing a
   hash-pinned `qedmeta.toml` sidecar.
2. **[`qedlift`](qedsvm-rs/qedlift/README.md) walks one selected path.** It pins the walked instructions back to
   the `.so` bytes, symbolically executes them, and emits a Lean Hoare triple.
3. **Supported shapes get an abstract refinement.** Registered token, counter,
   vault, heap, and transition shapes connect concrete memory effects to
   account-level claims.
4. **`lake build` is the gate.** The generated module only counts when Lean checks
   its bytecode pins, pre/postconditions, and compute-unit obligations without
   `sorry`.

Branchy paths normally use a concrete `.pcs` trace captured from the differential
harness. See [`docs/PIPELINE.md`](docs/PIPELINE.md) for the complete `.so` + IDL +
trace workflow and [`docs/COVERAGE.md`](docs/COVERAGE.md) for the precise supported
boundary.

## Use

### Lift a compiled program to Lean

This minimal fixture does not need an IDL or trace:

```bash
cargo run --manifest-path qedsvm-rs/Cargo.toml \
  -p qedlift -- \
  --so qedsvm-rs/tests/fixtures/byte_increment.so \
  --output examples/lean/Generated/ByteIncrementLifted.lean
```

The emitted module pins the walked `.text` bytes through `SVM.SBPF.Decode`, states
a `cuTripleWithinMem` theorem synthesized by symbolic execution, and discharges
it. Small binaries use a full `decodeProgram` theorem; large binaries use
kernel-checked per-PC decode pins.

Checked-in output under
[`examples/lean/Generated/`](examples/lean/Generated/) includes ByteIncrement,
Counter, Logger, layout-general Vault examples, heap allocation, and traced
p-token arms. Registered refinements cover Transfer, TransferChecked, MintTo,
Burn, Counter increment, Vault field updates, heap allocation, and transition
paths. Other supported paths receive raw Hoare triples.

### Use the Lean APIs

The core APIs have this shape; the concrete definitions and predicates come from
the program being checked:

```lean
-- Execute a compiled ELF on one input.
example : Runner.runElfForExit programElf { cuBudget := 200_000 } = some 0 := by
  native_decide

-- Compose instruction specifications into a bounded Hoare triple.
example : cuTripleWithin 2 0 2 code precondition postcondition := by
  sl_block_iter
```

Runnable examples:
[`examples/lean/ByteIncrement.lean`](examples/lean/ByteIncrement.lean) goes from
raw bytes to a witness theorem, while
[`examples/lean/PToken/BalanceSpec.lean`](examples/lean/PToken/BalanceSpec.lean)
shows the account-level refinement target.

### Use the Rust executor

`qedsvm-rs` exposes the executor for conformance tests, fuzzers, and downstream
cross-checking harnesses. It is part of this repository rather than a crates.io
package.

```rust
use qedsvm::SVM;

let mut svm = SVM::default();
svm.add_program(&program_id, elf_bytes);
let result = svm.process_instruction(&instruction, &accounts)?;
```

It executes one input; it does not verify a program. Integration details,
including the downstream link helper and the `solana-account` version split,
live in [`qedsvm-rs/README.md`](qedsvm-rs/README.md).

## Coverage and trust

| Surface | Current claim |
| --- | --- |
| Executor conformance | A finite fixture corpus checks observable behavior against Mollusk/Agave. This is strong empirical evidence, not a universal equivalence proof. |
| Raw proof coverage | `qedlift` emits Lean Hoare triples for selected paths over modeled instructions and lift-supported syscalls. |
| Abstract proof coverage | Supported codec and transition shapes connect bytecode effects to account-level state claims. |

The trusted base includes the Lean kernel, qedsvm's sBPF semantics, explicit
crypto/native trust statements where used, and the generated obligations that
Lean checks. Differential testing grounds the model against a production runtime
but does not replace the proof. CI checks the flagship proofs, disallows `sorry`
and unexpected axioms, runs the executor differential suite, and byte-diffs all
generated `qedlift` fixtures.

qedsvm is not a validator, consensus implementation, source-code verifier, or
automatic whole-CFG verifier.

## Repository layout

```text
SVM/                      Lean interpreter, specification layer, and Solana predicates
examples/lean/            Checked Hoare-proof examples
examples/lean/Generated/  qedlift output: .so to sorry-free Lean triples
qedsvm-rs/                Rust workspace
├── (root)                Executor API and CLI
├── qed-artifacts/        Shared metadata and descriptor contracts
├── qedlift/              Selected-path symbolic executor and Lean emitter
├── qedrecover/           .so + IDL + overlay to qedmeta sidecar
├── qed-analysis/         Shared sBPF and account-layout analysis
└── lean-bridge/          Agave-pinned native crypto bridge called by Lean
docs/                     API, proof pipeline, and coverage references
```

## Contributing

Issues and PRs are welcome. The bar is a small trust base and honest
specifications. Additions that broaden the surface need a clear soundness story.

## License

MIT. See [`LICENSE`](LICENSE).
