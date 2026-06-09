# qedsvm

**Verify what runs on Solana, not what you wrote.**

A Lean 4 model of the Solana Virtual Machine. It operates on the compiled `.so`, the same artifact mainnet runs, and does two separate jobs:

- **Execute** a program on a model proven byte-for-byte conformant with agave (differential-tested against mollusk on 32 fixtures, p-token Transfer at 76 CU identical, full suite ~3s). The `qedsvm-rs` crate is this executor, published mainly so the model can be diff-tested against mollusk and reused by fuzzing and diff-test harnesses.
- **Verify** a program against a separation-logic spec with a proven compute-unit bound, in Lean: 142 per-instruction Hoare triples, composition tactics, and `qedlift` to lift a `.so` straight to a machine-checked proof with no `sorry`.

> **Execution is not verification.** The Rust crate tells you what a program does on one input; it does not prove what it does on all of them. If you only use `qedsvm-rs`, you have a conformant executor, not a verified program. Verification lives entirely in the Lean layer.

Small trust base: Lean 4 ISA semantics in `SVM/SBPF/{Execute,Decode,Memory}.lean` plus 21 explicit crypto trust statements. No rustc.

## Install

```lean
require qedsvm from git
  "https://github.com/QEDGen/qedsvm.git" @ "v0.3.0"
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

`qedlift` (and its sibling `qedrecover`) are the lifting front-end: they turn a binary into a proof obligation against the spec layer. This is the surface [qedgen](https://github.com/QEDGen) consumes, and long-term it lives there; it ships here for now, feature-gated behind `qedrecover`, as the most direct demonstration of the binary → proof path.

Point it at a `.so` and it emits a Lean module that embeds the `.text` bytes, proves they decode to the expected `List Insn`, states a `cuTripleWithinMem` Hoare triple synthesized by symbolic execution, and discharges it with `sl_block_auto`. The spec statement is mechanical from the binary, not hand-typed, and the proof closes with no `sorry`.

```bash
cargo run --features qedrecover --bin qedlift -- \
  --so qedsvm-rs/tests/fixtures/byte_increment.so \
  --output examples/lean/Generated/ByteIncrementLifted.lean
```

With `--trace`, qedlift follows the real happy path through branchy bytecode and additionally emits a `*_balance_correct` corollary (clean Nat debit/credit). The checked-in lifts under [`examples/lean/Generated/`](examples/lean/Generated/) cover ByteIncrement, the Counter family, Logger, and six p-token arms (Transfer, TransferChecked, MintTo, Burn, CloseAccount, InitializeMint2), all proof-complete. Batch mode (`--idl`) lifts every instruction in a TOML or Codama IDL.

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

| Layer | Status |
| --- | --- |
| ALU + jumps + memory + call/return | ✅ |
| ELF64 loader (all `R_BPF_64_*`) | ✅ |
| Crypto syscalls (12), agave-pinned crates | ✅ |
| Native programs (System, ComputeBudget, BPF Loader v3, precompiles) | ✅ Firedancer-aligned |
| CPI (Rust + C ABI, depth-2+, PDA signer promotion) | ✅ |
| 142 per-instruction Hoare triples | ✅ |
| Composition tactics (`sl_block_iter`, `sl_branch`, `sl_rw_abs`) | ✅ |
| End-to-end proofs over compiler-emitted bytecode | ✅ 76 / 76 CU on p-token Transfer, exitCode = 0 |
| Bytecode → proof lift (`qedlift`) | ✅ `.so` → `sorry`-free Lean triple + CU bound |

See [`ROADMAP.md`](ROADMAP.md) for the phase-by-phase breakdown and current work.

## Layout

```
SVM/                  Lean library: interpreter, spec layer, Solana SL predicates
examples/lean/        Hoare-proof examples (ByteIncrement, PToken/, CompilerRt*, …)
examples/lean/Generated/  qedlift output: .so → sorry-free Lean triples
examples/rust/        → qedsvm-rs/examples (symlink)
qedsvm-rs/            Cargo workspace
├── (root)            Mollusk-shaped Rust API
├── src/bin/qedlift.rs    Bytecode → Lean-proof lifter (--features qedrecover)
└── lean-bridge/      Agave-pinned crypto staticlib called by Lean
docs/                 Active design notes (docs/archive/ for shipped plans)
```

## Origin

Extracted on 2026-05-12 from [QEDGen/solana-skills](https://github.com/QEDGen/solana-skills). The methodology (separation logic over machine state with bounded Hoare triples) is borrowed from [Verified-zkEVM/evm-asm](https://github.com/Verified-zkEVM/evm-asm), which descends from Kennedy/Benton/Jensen/Dagand, *"Coq: The world's best macro assembler?"* (PPDP 2013).

## License

MIT. See [`LICENSE`](LICENSE).

## Contributing

Issues and PRs welcome. The bar is **small trust base and honest specs**. Additions that broaden the surface without a clear soundness story will get pushback.
