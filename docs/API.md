# Public API

This is the package boundary downstream consumers should pin against:

```lean
require qedsvm from git
  "https://github.com/QEDGen/qedsvm.git" @ "v0.11.0"
```

The public Lean surface is `lean_lib SVM`. The `Examples` library is a proof and generated-artifact suite; it is useful for reference and regression coverage, but it is not API.

## Package Boundary

| Surface | API status | Notes |
| --- | --- | --- |
| `SVM.*` Lean modules | Public | Importable package surface. |
| `examples/lean/*` | Not API | Demo proofs, generated lifts, and regression pins. |
| `qedsvm-rs` library crate | Public Rust executor surface | Conformant execution and diff-test support. |
| Rust binaries and analysis tools | Tooling, not API | Includes `qedlift`, `disasm_to_lean`, `cli`, `qedrecover`, and `qed-analysis`. |

## Lift Engine

These modules define the separation-logic proof target emitted by `qedlift`:

| Module | Provides |
| --- | --- |
| `SVM.SBPF.SepLogic` | Assertion language, memory/register atoms, and `cuTripleWithinMem`. |
| `SVM.SBPF.Tactic.SL` | `sl_block_auto`, `sl_exact`, and block-composition automation. |
| `SVM.SBPF.SpecGen` | Dispatch from decoded instructions to instruction specs. |
| `SVM.SBPF.InstructionSpecs.*` | Per-instruction and syscall Hoare triples. |
| `SVM.SBPF.Decode` | Byte decoding, `CodeReq` pinning, slot maps, and per-PC decode pins. |
| `SVM.SBPF.AccountCodec` | Layout-general account field codecs: `FieldVal`, `codecCoarse`, `account_agg`, `codecCoarse_eq_fine`. |
| `SVM.SBPF.SegAggregation` | `memBytesIs_segs` and byte-segment aggregation lemmas. |
| `SVM.SBPF.HeapSL` | Heap predicates: `heapBumpPtr`, `heapBlockU64`, `heapBlock`. |
| `SVM.SBPF.SatWitness` | Generated precondition satisfiability witnesses. |

## Execution / WP Engine

These modules define bounded execution and exit-code proofs:

| Module | Provides |
| --- | --- |
| `SVM.SBPF.Execute` | `executeFn`, `initState`, and step semantics. |
| `SVM.SBPF.Tactic.WP` | `wp_exec` and related bounded-execution tactics. |
| `SVM.SBPF.Runner` | ELF execution helpers over the Lean VM. |
| `SVM.SBPF.RunnerBridge` | Bridge used by runtime execution and trace capture. |

## Discharge Route

`SVM.SBPF.Tactic.Discharge` provides `qedsvm_discharge`, the tactic used to discharge field-level obligations from a lifted `cuTripleWithinMem` theorem. Generated refinements use it to connect concrete memory cells to codec accessors such as account balances, mint supply, and layout-general field updates.

## Core Semantics

The following modules are part of the public model surface:

| Module family | Provides |
| --- | --- |
| `SVM.SBPF.{ISA,Machine,Memory,Region,Elf}` | sBPF instruction set, machine state, memory model, region table, and ELF loading. |
| `SVM.SBPF.{Murmur3,SyscallHash,CryptoTrust}` | Syscall hashing and explicit crypto trust statements. |
| `SVM.Syscalls.*` | Modeled Solana syscall behavior. |
| `SVM.Native.*` | Native program models: System, ComputeBudget, precompiles, and loader behavior. |
| `SVM.Solana.*` | Solana account/CPI/PDA data structures and account codecs. |
| `SVM.Pubkey` | Pubkey representation. |

## Refinement Surface

Generated abstract refinements target `SVM.Solana.Abstract.Refinement`.

| Predicate | Current use |
| --- | --- |
| `AsmRefinesFieldUpdate` | Layout-general single-account field update over `codecCoarse base fields`; the form qedgen's discharge adapter consumes. |
| `AsmRefinesFieldUpdates` | N-account generalization (one `(base, preFields, postFields)` triple per account); target of the SPL `Transfer`/`TransferChecked`/`MintTo`/`Burn` generated refinements. |
| `AsmRefinesCounterIncrement` | Counter increment generated refinement. |

For new integrations, prefer field-codec obligations and accessors where possible. The record-keyed `AsmRefinesToken*` predicates are retired (#25): token arms emit the layout-general N-account obligation directly off the lift.

## Rust Surface

The `qedsvm-rs` library crate exposes the conformant executor and harness-facing APIs:

| Area | Files |
| --- | --- |
| Executor API | `lib.rs`, `svm.rs` |
| Diff/conformance support | `diff.rs` |
| Lean FFI bridge | `ffi.rs` |
| Solana wire/account serialization | `serialize`, `deserialize`, `wire` modules |

The Rust crate executes programs on the qedsvm model. It does not prove program properties by itself; verification is through generated Lean and `lake build`.

## Versioning

qedsvm is pre-1.0. Consumers should pin an exact tag. Breaking changes to the `SVM` Lean surface are expected to receive a new minor tag. `Examples` modules and Rust binaries/tools may change without API compatibility guarantees.
