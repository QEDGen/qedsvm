# formal-svm

A Lean 4 reference semantics for the Solana Virtual Machine.

This is the **spec layer** the SVM is missing — an executable formal description that downstream verification tools, auditors, and multi-client conformance teams can target. It is not a replacement for the Agave runtime.

## What this is (and isn't)

**This is** an early-stage Lean 4 model of:
- the sBPF instruction set and its operational semantics,
- a pubkey + account data model,
- the `invoke_signed` CPI envelope and a registry of well-known program IDs and instruction discriminators.

**This is not** a verified replacement runtime. There is no plan to extract and ship executable Lean as a substitute for `solana-program-runtime`. If you want CompCert-for-Solana, this isn't it. The README is honest about scope on purpose — see `docs/founding-rationale.md` for the F1-vs-F2 distinction.

**Don't ship this against mainnet value.** The sBPF instruction semantics here are hand-written and have not been differential-tested against Agave's `solana-sbpf` or Firedancer's VM. The `Svm.Account` list-update lemmas are still axioms. Closing both is on the roadmap; they are not closed today.

## What's in it

```
Svm.lean                  — package root
Svm/
├── Account.lean          — Pubkey (4-chunk LE U64), Account, findBy{Key,Authority}
├── Cpi.lean              — CpiInstruction envelope, program ID registry, SPL/System/ATA discriminators
├── SBPF.lean             — top-level aggregator for the sBPF kernel
└── SBPF/
    ├── ISA.lean          — instruction encoding and opcode set
    ├── Memory.lean       — byte-addressable Mem, region layout, disjointness lemmas
    ├── Region.lean       — region IDs (input/stack/heap/program)
    ├── Pubkey.lean       — sBPF-level pubkey reads
    ├── Execute.lean      — RegFile, machine State, step function, executeFn
    ├── Patterns.lean     — common composition lemmas (executeFn_compose, etc.)
    ├── Tactic.lean       — misc tactics
    └── WPTactic.lean     — wp_exec weakest-precondition tactic
```

Total: ~3k lines of Lean. Zero `sorry`. Five explicit axioms in `Svm/Account.lean` (list-update lemmas), all comments label "axiom for now — full proof would require more complex induction." They are provable in Mathlib and are slated for Phase 0 of the roadmap.

The implicit trust base is larger than the explicit axiom count suggests — see `docs/founding-rationale.md` for the audit.

## Use it

Add to your `lakefile.lean`:

```lean
require formalSvm from git
  "https://github.com/QEDGen/formal-svm.git" @ "main"
```

Then `import Svm` (or selectively `import Svm.Account`, `import Svm.SBPF`, etc.).

Standalone build:

```bash
lake build
```

Lean toolchain pin: see `lean-toolchain`.

## Origin

This repo was extracted on 2026-05-12 from the [QEDGen](https://github.com/QEDGen) skill, which has used it as the runtime model for spec-driven verification of Solana programs since 2026. The split is to give the SVM model its own life as an ecosystem artifact rather than a QEDGen-internal dependency. Commit history is preserved.

The strategic rationale — why a reference SVM, why now, what F1 (this) buys versus F2 (verified extractable replacement, explicitly out of scope) — is in `docs/founding-rationale.md`.

## Status and roadmap

Phase 0 (axiom cleanup) and Phase 1 (CPI small-step semantics) are the near-term tracks. The full phased path is in `ROADMAP.md`.

Honest framing: this repo is the executable-spec foundation for verification of Solana programs. It is not the verification tool itself. If you want spec-driven verification today, use [QEDGen](https://github.com/QEDGen). If you want the model `Svm` provides as a building block for your own tools — an audit framework, a zk-SVM circuit, a differential oracle, a Firedancer/Agave conformance reference — this is for you.

## License

MIT. See `LICENSE`.

## Contributing

Issues and PRs welcome. The roadmap describes the planned phases; out-of-roadmap contributions need a short rationale before they land. We aim to keep the trust base small and the model honest — additions that broaden the surface area without a clear soundness story will get pushback.
