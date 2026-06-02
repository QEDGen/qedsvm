# qedsvm

**Verify what runs on Solana, not what you wrote.**

A Lean 4 model of the Solana Virtual Machine. Operates on the compiled `.so`: the same artifact mainnet runs.

- **Byte-for-byte conformant** with agave on 32 mollusk-cross-checked fixtures, including p-token Transfer at 76 CU identical. Full suite: ~3s.
- **142 per-instruction Hoare triples** in separation logic, composable end-to-end. Every triple carries a verified compute-unit bound.
- **Small trust base.** Lean 4 ISA semantics in `SVM/SBPF/{Execute,Decode,Memory}.lean` plus 21 explicit crypto trust statements. No rustc.
- **One codebase, three deliverables.** Run any compiled program (`Runner.runElf`), prove what it does (`cuTripleWithin`), or lift the `.so` straight to that proof (`qedlift`).

## Install

```lean
require qedsvm from git
  "https://github.com/QEDGen/qedsvm.git" @ "main"
```

Prerequisites: Lean (via `elan`) and `cargo` / `rustc`. Lake builds `qedsvm-rs/lean-bridge/` automatically.

## Demo

Two artifacts make the headline claims visible in seconds.

```bash
# Run incrementer + p-token Transfer through qedsvm and mollusk side by side.
# Prints CU, return data, account-data digest, and a byte+CU verdict.
cargo run --release --features diff-mollusk \
  --manifest-path qedsvm-rs/Cargo.toml --example conformance_demo

# Type-check the end-to-end witness theorem for a 4-instruction sBPF program.
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

`qedlift` closes the loop: point it at a `.so` and it emits a Lean module that embeds the `.text` bytes, proves they decode to the expected `List Insn`, states a `cuTripleWithinMem` Hoare triple synthesized by symbolic execution, and discharges it with `sl_block_auto`. The spec statement is mechanical from the binary, not hand-typed, and the proof closes with no `sorry`.

```bash
cargo run --features qedrecover --bin qedlift -- \
  --so qedsvm-rs/tests/fixtures/byte_increment.so \
  --output examples/lean/Generated/ByteIncrementLifted.lean
```

With `--trace`, qedlift follows the real happy path through branchy bytecode and additionally emits a `*_balance_correct` corollary (clean Nat debit/credit). The checked-in lifts under [`examples/lean/Generated/`](examples/lean/Generated/) cover ByteIncrement, the Counter family, Logger, and six p-token arms (Transfer, TransferChecked, MintTo, Burn, CloseAccount, InitializeMint2), all proof-complete. Batch mode (`--idl`) lifts every instruction in a TOML or Codama IDL.

### From Rust (`qedsvm-rs`)

```rust
use qedsvm::{ProgramResult, SVM};

let mut svm = SVM::default();
svm.add_program(&program_id, elf_bytes);
let result = svm.process_instruction(&instruction, &accounts)?;
```

Types pin to agave master (`solana-pubkey`, `solana-instruction`, `solana-account`), so a Mollusk test passes data straight in. Differential testing against Mollusk:

```bash
cargo test --manifest-path qedsvm-rs/Cargo.toml --features diff-mollusk
```

#### Consuming qedsvm from a downstream crate

Cargo doesn't propagate `cargo:rustc-link-arg` directives from a dependency's `build.rs` to dependent crates' link commands, so a downstream crate depending on `qedsvm` link-fails on the ~80 Lean dylibs and the forced-load `lean_*` crypto bridge symbols unless it re-emits them itself. The `qedsvm-buildscript` helper crate handles all of that in one call:

```toml
# Your Cargo.toml
[dependencies]
qedsvm = { path = "../qedsvm/qedsvm-rs", features = ["diff-mollusk"] }

[build-dependencies]
qedsvm-buildscript = { path = "../qedsvm/qedsvm-rs/qedsvm-buildscript" }
```

```rust
// Your build.rs
fn main() {
    let qedsvm_root = std::env::var("QEDSVM_ROOT")
        .unwrap_or_else(|_| "../qedsvm".to_string());
    qedsvm_buildscript::emit_link_args(std::path::Path::new(&qedsvm_root))
        .expect("emit qedsvm link args");
}
```

Run `lake build` in the qedsvm checkout first so the helper has a populated `.lake/build/`.

#### Diff-test crates: handling the `solana-account` version split

`qedsvm::Svm::process_instruction` takes `(Pubkey, AccountSharedData)` from `solana-account 4.x`. `mollusk-svm 0.12.1-agave-4.0::process_instruction` takes the same shape but from `solana-account 3.x` (mollusk's interface crate hasn't moved to 4.x yet). Cargo pulls both versions; they share names but are not directly interconvertible.

A one-line dev-dep alias for mollusk's older copy is the established workaround:

```toml
[dev-dependencies]
qedsvm = { path = "...", features = ["diff-mollusk"] }
mollusk-svm = "0.12.1-agave-4.0"
solana-account = "4.3.0"
# Aliased name lets you construct the version mollusk expects without
# colliding with qedsvm's 4.x.
mollusk-account = { package = "solana-account", version = "3.4.0" }
```

For the actual conversion, use the helpers under `qedsvm::diff::*` (gated by `diff-mollusk`) so you're not rewriting the field copy in every diff-test crate:

```rust
use qedsvm::diff::{mollusk_to_qedsvm, qedsvm_to_mollusk};

// Build the fixture once in mollusk shape, run on both engines.
let qedsvm_accounts = mollusk_to_qedsvm(&mollusk_accounts);
let mollusk_result = mollusk.process_instruction(&ix, &mollusk_accounts);
let qedsvm_result  = svm.process_instruction(&ix, &qedsvm_accounts);

// Round-trip works the other way too (e.g. fuzzers that drive qedsvm
// first and then cross-check with mollusk).
let mollusk_accounts_back = qedsvm_to_mollusk(&qedsvm_accounts);
```

The Janus differential-test harness ([`saicharanpogul/janus/tests-qedsvm`](https://github.com/saicharanpogul/janus/tree/main/tests-qedsvm)) is a complete working example.

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
