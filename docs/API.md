# Public API: the stable Lean package surface

This is the module boundary that downstream consumers (qedgen / QEDGen/solana-skills) pin against:

```lean
require qedsvm from git
  "https://github.com/QEDGen/qedsvm.git" @ "v0.3.0"
```

The rule is one line: **`lean_lib SVM` is the frozen surface; `lean_lib Examples` is never API.** Everything importable under the `SVM` namespace is public, with one flagged exception (the bridging predicates, below). `examples/lean/` holds one-time proofs and generated lift demos; nothing in `SVM` imports from it, and nothing in it is stable.

## What the surface contains

qedsvm owns the sBPF semantics and both engines that prove things about the binary. Both are importable API, not forked:

### The SL / lift engine

Separation-logic triples over decoded instruction blocks, with proven compute-unit bounds. This is the engine `qedlift` targets.

- `SVM.SBPF.SepLogic`: the assertion language (`↦U64`, `↦Bytes`, `memU64Is`, `memBytesIs`) and `cuTripleWithinMem`, the triple shape every lift produces
- `SVM.SBPF.Tactic.SL`: `sl_block_auto` and the block-composition tactics
- `SVM.SBPF.SpecGen`, `SVM.SBPF.InstructionSpecs.*`: the per-instruction Hoare triples (142) and their dispatch
- `SVM.SBPF.Decode` + the `CodeReq` pinning: how program bytes are tied to the decoded instructions a proof talks about
- `SVM.SBPF.AccountCodec`: the layout-general field codec (`FieldVal`, `codecCoarse`) and the keystone reshape lemmas `account_agg` / `codecCoarse_eq_fine` (coarse whole-account bytes vs fine per-field views, for any field layout)
- `SVM.SBPF.SegAggregation`: `memBytesIs_segs`, the segment-list aggregation `account_agg` is built on
- `SVM.SBPF.HeapSL`: `heapBumpPtr` / `heapBlockU64` / `heapBlock`, the heap-allocation predicates

### The WP / fuel engine

Bounded execution to an exit code. This is the engine qedgen's guard DSL (`qedguards`) relies on: a `requires` obligation is literally `(executeFn prog (initState r1 mem) fuel).exitCode = some <errCode>`.

- `SVM.SBPF.Execute`: `executeFn`, `initState`, the step semantics
- `SVM.SBPF.Tactic.WP`: `wp_exec`, the one-shot discharge tactic for exit-code goals
- `SVM.SBPF.Runner` / `SVM.SBPF.RunnerBridge`: `runElfForExit` and the ELF-to-execution plumbing

### The discharge route

`SVM.SBPF.Tactic.Discharge` provides `qedsvm_discharge`: the tactic qedgen's generated parametric obligations (`accessor post = accessor pre ± amount`, the `ensures_axiom` shape) are discharged with, on top of a lifted triple. This replaced the MIR pilot (#24, #25): consumers state field-level claims against the codec accessors and discharge them directly; there is no intermediate abstract machine.

### The rest of the library surface

- `SVM.SBPF.{ISA, Machine, Memory, Elf}`: the core semantics and data model
- `SVM.SBPF.{Murmur3, SyscallHash, CryptoTrust}`: syscall hashing and the explicit crypto trust statements
- `SVM.Syscalls.*` and `SVM.SBPF.InstructionSpecs.Syscalls.*`: syscall semantics and their specs
- `SVM.Native.*`: native program models (System, ComputeBudget, precompiles, loader)
- Solana primitives: `SVM.Solana.{AccountInfo, Cpi, Pda}` and `SVM.Pubkey`
- The `qedsvm-rs` Rust library crate (`lib.rs`, `svm.rs`, `diff.rs`, `ffi.rs`, `serialize` / `deserialize` / `wire`): the conformant executor and diff-testing surface. The Rust *bins* (`qedlift`, `qedrecover`, `disasm_to_lean`, `cli`) are tools, not library API.

## The one evolving piece: the bridging predicates

`SVM.Solana.Abstract.{State, Refinement}` and the field codecs (`SVM.Solana.{Token,Mint,Counter}AccountCodec`, `TokenAccount`, `{Token,Mint}FieldCodec`) are the **bridging surface** between lifted asm triples and abstract claims. Within it:

- **Stable target:** `AsmRefinesFieldUpdate`, the layout-parameterized obligation (one predicate over `codecCoarse base [FieldVal list]` for any account shape), plus the `account_agg` / `codecCoarse_eq_fine` reshape route it rides on.
- **Evolving, do not pin:** the record-keyed `AsmRefinesToken*` / `AsmRefinesCounterIncrement` predicates and the abstract-record codecs they key on. They are kept for historical continuity and are scheduled to converge onto the field-codec route as qedgen consumes this surface (QEDGen/solana-skills#86); expect deletion, not deprecation cycles.

If you are integrating today: state obligations via `AsmRefinesFieldUpdate` and the codec accessors, not via the `AsmRefinesToken*` records.

## Versioning

Pre-1.0: pin an exact tag (`@ "v0.3.0"`). Within the frozen surface above, breaking changes bump the minor version and get a new tag; the bridging predicates flagged as evolving may change or disappear without a major signal until #86 lands. `lean_lib Examples` and the Rust bins may change at any time.
