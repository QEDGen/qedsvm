# qedsvm-rs

The Rust executor for [qedsvm](../README.md). It runs compiled Solana programs
through qedsvm's Lean SVM and is differentially tested against Mollusk/Agave for
byte-level account changes, return values, faults, and compute units. The finite
test corpus is conformance evidence, not a universal equivalence proof.

The crate is part of this repository rather than a crates.io package. It is
intended for fuzzers, differential harnesses, and simulations that need a second
SVM implementation to cross-check.

**This crate executes, it does not verify.** It tells you what a program does on one input, not what it does on all of them. Verification lives in qedsvm's Lean layer; see the top-level [README](../README.md).

## Run a program

```rust
use qedsvm::{ProgramResult, SVM};

let mut svm = SVM::default();
svm.add_program(&program_id, elf_bytes);
let result = svm.process_instruction(&instruction, &accounts)?;
```

The public types use the pinned Solana interface crates listed in
[`Cargo.toml`](Cargo.toml), so most Mollusk-shaped test data passes straight in.

## Differential testing against mollusk

```bash
cargo test --manifest-path qedsvm-rs/Cargo.toml --features diff-mollusk
```

The Janus harness ([`saicharanpogul/janus/tests-qedsvm`](https://github.com/saicharanpogul/janus/tree/main/tests-qedsvm)) is a complete working example of driving qedsvm and mollusk side by side.

## Proof tooling

The Rust workspace also contains the two analysis stages used by qedsvm's Lean
proof pipeline:

- [`qedrecover`](qedrecover/README.md) maps IDL/overlay claims to locations and
  account layouts in a compiled `.so`, then emits a hash-pinned sidecar. It is
  analysis only and does not link Lean.
- [`qedlift`](src/bin/qedlift/README.md) symbolically executes a selected bytecode
  path and emits the Lean theorem, decode pins, CU bound, and supported abstract
  refinements.

The top-level [`PIPELINE.md`](../docs/PIPELINE.md) shows how the two stages and
`lake build` fit together.

## Consuming qedsvm from a downstream crate

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

## Diff-test crates: handling the `solana-account` version split

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
