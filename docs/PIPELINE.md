# From `.so` + IDL to a proof: the toolchain pipeline

Date: 2026-06-02
Status: reference for the current (fixture-driven) pipeline
Related: `qedsvm-rs/src/bin/qedrecover.rs`, `qedsvm-rs/src/bin/qedlift.rs`, `examples/lean/Generated/`, [COVERAGE.md](COVERAGE.md) (what an arbitrary `.so` + IDL actually gets you), [MIR.md](MIR.md) (the abstract layer the lifted triple refines)

How a compiled Solana program plus its IDL becomes a machine-checked Hoare triple. This documents what the toolchain does today, including the seams that are still manual. Everything below is grounded in the `p_token` fixtures under `qedsvm-rs/tests/fixtures/`.

## Inputs

All three are off-chain. None is embedded in the deployed binary: on-chain bytes are byte-identical to a build that knows nothing about qedsvm.

| Artifact | Example | Carries |
| --- | --- | --- |
| `.so` | `p_token.so` | The compiled SBF bytecode, the deployed artifact itself. |
| Codama IDL | `spl_token.codama.json` | Discriminators, account layout, argument types. |
| qedsvm overlay | `p_token.qedoverlay.toml` | The qedsvm-specific bits no IDL describes: which instructions are in scope, the MIR intrinsic each refines (`transfer` to `Mir.tokenTransfer`), and the CU budget claimed (`76`). |

In the production path, qedgen emits the overlay and sidecar from source-level annotations at compile time, the way Anchor or Codama emit an IDL. The overlay plus `qedrecover` exist for third-party binaries: pinocchio p-token has no qedgen annotations, so the same file shape is recovered by scanning the binary. The verifier consumes the same TOML either way.

## The flow

```
   p_token.so  ───────────────┐
   spl_token.codama.json  ─────┤
   p_token.qedoverlay.toml  ───┘
        │
        ▼
┌──────────────────────────────────────────────────────────────┐
│ STAGE 1 — qedrecover    (.so + IDL + overlay -> metadata)     │
│  - solana-sbpf static_analysis::Analysis builds the CFG       │
│  - dispatcher recognition: locate the discriminator-register  │
│    load + the compare-jump for disc=3                         │
│        -> dispatchLoadPc / dispatchJeqPc / armEntryPc          │
│  - slice the reachable CFG blocks from the arm entry          │
│  emits:                                                       │
│   - p_token.qedmeta.toml          sidecar: sha256-pins the    │
│       .so and IDL, program id, per-instruction PCs (off-chain)│
│   - p_token_transfer.recovered.lean   Lean defs:              │
│       refinesIntrinsic, cuBudget, accountRoles,               │
│       discriminatorValue/Width, armEntryPc, reachableBlocks   │
└──────────────────────────────────────────────────────────────┘
        │  binds WHAT to prove to WHERE it lives in the binary
        ▼
┌──────────────────────────────────────────────────────────────┐
│ STAGE 2 — trace capture   (optional, for real happy paths)    │
│  - run the instruction through qedsvm's Lean reference VM     │
│    (TRACE_STEPS) inside the diff_mollusk test, with concrete  │
│    inputs (amount=250, src=1000, dst=0)                       │
│  emits: p_token_transfer.pcs                                  │
│    76 logical PCs in execution order (75 CU + terminal exit), │
│    cross-checked against mollusk                              │
└──────────────────────────────────────────────────────────────┘
        │
        ▼
┌──────────────────────────────────────────────────────────────┐
│ STAGE 3 — qedlift    (.so [+ --idl + --trace .pcs] -> proof)  │
│  - decode .text via SVM.SBPF.Decode (checked by native_decide)│
│  - --idl: derive (name, discriminator) per arm;               │
│    --target-disc 3 selects the transfer arm                   │
│  - --trace: load_trace() walks the recorded PC sequence       │
│    exactly (walk_cap = len + 8), so the lift follows the real │
│    happy path through branches, calls, and balance writes     │
│  - symbolic exec synthesizes pre/post atoms, states a         │
│    cuTripleWithinMem triple, discharges it with sl_block_auto │
│  emits: examples/lean/Generated/PTokenTransferTracedLifted.lean│
│   - PTokenTransfer_lifted_spec      the Hoare triple + CU bound│
│   - PTokenTransfer_balance_correct  Nat debit/credit corollary │
│   ...sorry-free                                               │
└──────────────────────────────────────────────────────────────┘
        │
        ▼
┌──────────────────────────────────────────────────────────────┐
│ STAGE 4 — lake build    (the verification gate)               │
│  type-checks the generated module: the proof closes, no sorry │
└──────────────────────────────────────────────────────────────┘

  ── in parallel, certifying the model is faithful ──
  qedsvm-rs diff-tests the SAME p_token.so against mollusk/agave
  (p_token_transfer_matches_mollusk): byte + 76 CU identical.
  The proofs reason over the same decode the conformance run validates.
```

## The two binaries

- **qedrecover = scope.** Binds an IDL/overlay claim to a location in the binary: which discriminator arm, which entry PC, which reachable blocks, what CU budget. Output is descriptive metadata (`qedmeta.toml` plus the `recovered.lean` defs). It does not prove anything. Today it stops at "reachable blocks" (happy and sad); narrowing to the happy path needs a trace.
- **qedlift = prove.** Takes a region of bytecode and produces a discharged `cuTripleWithinMem` triple with a verified CU bound. Output is a machine-checked theorem plus, under `--trace`, a `*_balance_correct` corollary.

They are meant to compose. qedrecover's `discriminatorValue`, `armEntryPc`, and `cuBudget` are exactly what target qedlift (`--target-disc` and the budget assertion), and the `.pcs` trace narrows qedrecover's full reachable-block slice down to the one real happy path.

## Current seams (where this is still a demo, not one command)

1. **qedlift does not read `qedmeta.toml` yet.** It re-derives discriminators straight from the IDL, so qedrecover and qedlift run in parallel rather than strictly piped. Wiring qedlift to consume the sidecar is the join point.
2. **Trace capture is manual.** Flip `TRACE_STEPS := true` in `SVM/SBPF/Runner.lean`, run the matching `diff_mollusk` test with `--nocapture`, and post-process the `STEP pc=` lines into a `.pcs` file. The exact recipe is in the header comment of each `.pcs`.
3. **Happy/sad-path tagging in qedrecover is pending** (needs the same mollusk trace). Until then `reachableBlocks` lists both.

These are consistent with qedrecover/qedlift being the lifting front-end that moves into qedgen long-term; qedgen is expected to emit the overlay/sidecar at compile time and own the one-command path. See the [README](../README.md) and [ROADMAP](../ROADMAP.md).
