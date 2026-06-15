# qedsvm Roadmap

A correct, semantic-baseline SVM that (1) executes compiled Solana programs byte-for-byte against agave and (2) lets tools verify those same programs against separation-logic specs.

## Scope

qedsvm is the model and spec layer downstream verification tools sit on, not a validator-grade runtime competing with agave.

- **Correctness**: an auditable Lean 4 operational semantics for sBPF.
- **Semantic baseline**: byte-for-byte conformance with agave on real `cargo-build-sbf` output, enforced by differential testing against mollusk.
- **Execution**: load and run arbitrary compiled Solana programs (ELF `.so` → decoded → executed) including crypto syscalls and CPI.
- **Spec layer**: per-instruction Hoare triples covering the full user-facing ISA, plus composition tactics, so a decompiled `List Insn` can be proved against a separation-logic spec with a verified CU bound.

## Status

| Phase | Status |
| --- | --- |
| 0. Axiom cleanup | ✅ shipped |
| A. Foundations (`SepLogic`, `CPSSpec`, `InstructionSpecs`) | ✅ shipped |
| B. Full ISA spec coverage | ✅ shipped |
| C. Tactic suite (`sl_block_iter`, `sl_branch`, `sl_rw_abs`) | ✅ shipped |
| D. sBPF macro library | ✅ mostly shipped |
| E. Solana program library | ⚠️ partial, System `Transfer` end-to-end; SPL Token / ATA / Anchor patterns pending |
| F. Differential testing (mollusk fixtures) | ✅ 46 fixtures byte+CU equal |
| G. ELF loader + arbitrary program execution | ✅ shipped |
| H. Crypto syscalls (12), agave-pinned crates | ✅ shipped |
| Solana data-model SL predicates (`SVM/Solana/`) | ✅ 3 shipped; ~10 more queued |

**Headline numbers.** 142 per-instruction Hoare triples · 46 diff-mollusk fixtures including p-token Transfer at 76 CU byte+CU identical to mollusk · full suite in seconds · end-to-end Hoare-triple proof over compiler-emitted bytecode covering **76 of 76 CU** on the p-token Transfer happy path, terminating with exitCode = 0 · `qedlift` lifts a `.so` straight to a `sorry`-free Lean triple.

## Next: the discharge route

The hand-built abstract MIR pilot (`Mir.lean` / `Triples.lean`) is retired: it validated the refinement mechanism on real bytecode, then converged onto a layout-general route. The current target is `qedsvm_discharge` (`SVM/SBPF/Tactic/Discharge.lean`), which proves a qedgen-emitted `ensures_axiom`-shaped obligation (`accessor post = accessor pre ± amount`) against pinned bytecode by projecting the lifted `cuTripleWithinMem` through the codec reshape. Remaining work: collapse the bespoke `AsmRefinesToken*` predicates onto the one layout-general `AsmRefinesFieldUpdate` obligation as qedgen consumes the surface ([QEDGen/solana-skills#86](https://github.com/QEDGen/solana-skills/issues/86)), and broaden codec/syscall coverage (see [`docs/COVERAGE.md`](docs/COVERAGE.md)).

## Later

- **Broader differential fixtures**: SPL Token, ATA, Anchor program coverage; fuzz / sweep harness.
- **Crypto success-path triples**: ~400-line `sol_create_program_address`-style proofs per primitive (error-paths + trust statements already shipped).
- **Verified-macro authoring (Phases D/E)**: off the production critical path; useful for writing sBPF directly in Lean.
- **Pure-Lean crypto ports**: long-horizon TCB tightening via fiat-crypto / verified-crypto-primitives. The Rust FFI bridge remains the production path.

## Methodology

The separation-logic / bounded-Hoare-triple methodology is lifted from [Verified-zkEVM/evm-asm](https://github.com/Verified-zkEVM/evm-asm), which descends from Kennedy/Benton/Jensen/Dagand, *"Coq: The world's best macro assembler?"* (PPDP 2013). evm-asm's primary use is *authoring* verified RV64IM macros; qedsvm's primary use is *verifying decompiled* sBPF against specs.
