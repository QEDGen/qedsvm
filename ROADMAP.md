# qedsvm Roadmap

A correct, semantic-baseline SVM that (1) executes compiled Solana programs byte-for-byte against agave and (2) lets tools verify those same programs against separation-logic specs.

## Scope

**In scope.**
- **Correctness** — an auditable Lean 4 operational semantics for sBPF.
- **Semantic baseline** — byte-for-byte conformance with agave on real `cargo-build-sbf` output, enforced by differential testing against mollusk.
- **Execution** — load and run arbitrary compiled Solana programs (ELF `.so` → decoded → executed) including crypto syscalls and CPI.
- **Spec layer** — per-instruction Hoare triples covering the full user-facing ISA, plus composition tactics, so a decompiled `List Insn` can be proved against a separation-logic spec with a verified CU bound.

**Out of scope.**
- **Validator-grade runtime.** No bank, slot lifecycle, account commits, consensus, gossip, leader schedule, vote processing.
- **zkSVM target.** CU bounds remain meaningful in Lean without a zk backend.
- **sBPF-in-Lean as the primary authoring story.** A small in-tree macro library exists; a full verified macro library for SPL Token / ATA / Anchor patterns is a longer-horizon track and does not gate production.
- **A new verification tool.** qedsvm is the model and the spec layer that tools sit on; consumers live elsewhere.

## Status

| Phase | Status |
| --- | --- |
| 0 — Axiom cleanup | ✅ shipped |
| A — Foundations (`SepLogic`, `CPSSpec`, `InstructionSpecs`) | ✅ shipped |
| B — Full ISA spec coverage | ✅ shipped |
| C — Tactic suite (`sl_block_iter`, `sl_branch`, `sl_rw_abs`) | ✅ shipped |
| D — sBPF macro library | ✅ mostly shipped |
| E — Solana program library | ⚠️ partial — System `Transfer` end-to-end; SPL Token / ATA / Anchor patterns pending |
| F — Differential testing (mollusk fixtures) | ✅ 26 fixtures byte+CU equal |
| G — ELF loader + arbitrary program execution | ✅ shipped |
| H — Crypto syscalls (12) — agave-pinned crates | ✅ shipped |
| Solana data-model SL predicates (`SVM/Solana/`) | ✅ 3 shipped; ~10 more queued |

**Headline numbers.** 142 per-instruction Hoare triples · 26 diff-mollusk fixtures including p-token Transfer at 76 CU byte+CU identical to mollusk · full suite ~3 s · end-to-end Hoare-triple proofs over compiler-emitted bytecode reaching **75 of 76 CU** on the p-token Transfer happy path.

## Now — Layer 3b closure

The remaining 1 CU of p-token Transfer:

1. **Account-mutation block** at the far-jump target (~200–300 insns, 2–3 compiler-rt calls). Acceptance: a single `p_token_transfer_arm_happy_path_spec` triple covering 76 CU end-to-end with account-mutation postconditions.
2. **Refinement step** discharging the `sorry` in [`examples/lean/PToken/BalanceSpec.lean`](examples/lean/PToken/BalanceSpec.lean) to land the high-level `tokenAcctBalance` shift.

Estimate: 3–5 elapsed days. No blockers.

## Next — Direction-A MIR pivot

Per [QEDGen/solana-skills#66](https://github.com/QEDGen/solana-skills/issues/66): grow the `SVM/Solana/` SL-predicate library as each MIR intrinsic (`Stmt::TokenTransfer`, `Stmt::SystemTransfer`, `Stmt::Pda`, …) surfaces a refinement target. ~10 more predicates at half a day each.

## Later

- **Broader differential fixtures** — SPL Token, ATA, Anchor program coverage; fuzz / sweep harness.
- **Crypto success-path triples** — ~400-line `sol_create_program_address`-style proofs per primitive (error-paths + trust statements already shipped).
- **Verified-macro authoring (Phases D/E)** — off the production critical path; useful for writing sBPF directly in Lean.
- **Pure-Lean crypto ports** — long-horizon TCB tightening via fiat-crypto / verified-crypto-primitives. The Rust FFI bridge remains the production path.

## Methodology

The separation-logic / bounded-Hoare-triple methodology is lifted from [Verified-zkEVM/evm-asm](https://github.com/Verified-zkEVM/evm-asm), which descends from Kennedy/Benton/Jensen/Dagand, *"Coq: The world's best macro assembler?"* (PPDP 2013). evm-asm's primary use is *authoring* verified RV64IM macros; qedsvm's primary use is *verifying decompiled* sBPF against specs.

---

Tooling-track ideas: [`docs/improvement-plan.md`](docs/improvement-plan.md). Founding rationale: [`docs/founding-rationale.md`](docs/founding-rationale.md).
