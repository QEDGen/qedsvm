# qedsvm

**Verify what runs on Solana, not what you wrote.**

A Lean 4 model of the Solana Virtual Machine. Operates on the compiled `.so`: the same artifact mainnet runs.

- **Byte-for-byte conformant** with agave on 26 mollusk-cross-checked fixtures, including p-token Transfer at 76 CU identical. Full suite: ~3s.
- **142 per-instruction Hoare triples** in separation logic, composable end-to-end. Every triple carries a verified compute-unit bound.
- **Small trust base.** Lean 4 ISA semantics in `SVM/SBPF/{Execute,Decode,Memory}.lean` plus 21 explicit crypto trust statements. No rustc.
- **One codebase, two deliverables.** Run any compiled program (`Runner.runElf`); prove what it does (`cuTripleWithin`).

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

See [`ROADMAP.md`](ROADMAP.md) for the phase-by-phase breakdown and current work.

## Layout

```
SVM/                  Lean library: interpreter, spec layer, Solana SL predicates
examples/lean/        Hoare-proof examples (ByteIncrement, PToken/, CompilerRt*, …)
examples/rust/        → qedsvm-rs/examples (symlink)
qedsvm-rs/            Cargo workspace
├── (root)            Mollusk-shaped Rust API
└── lean-bridge/      Agave-pinned crypto staticlib called by Lean
docs/                 Active design notes (docs/archive/ for shipped plans)
```

## Origin

Extracted on 2026-05-12 from [QEDGen/solana-skills](https://github.com/QEDGen/solana-skills). The methodology (separation logic over machine state with bounded Hoare triples) is borrowed from [Verified-zkEVM/evm-asm](https://github.com/Verified-zkEVM/evm-asm), which descends from Kennedy/Benton/Jensen/Dagand, *"Coq: The world's best macro assembler?"* (PPDP 2013).

## License

MIT. See [`LICENSE`](LICENSE).

## Contributing

Issues and PRs welcome. The bar is **small trust base and honest specs**. Additions that broaden the surface without a clear soundness story will get pushback.
