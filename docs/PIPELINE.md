# From `.so` + IDL to a proof: the toolchain pipeline

Date: 2026-06-15
Status: reference for the current (fixture-driven) pipeline
Related: `qedsvm-rs/qedrecover/`, `qedsvm-rs/src/bin/qedlift.rs`, `examples/lean/Generated/`, [COVERAGE.md](COVERAGE.md) (what an arbitrary `.so` + IDL actually gets you), [API.md](API.md) (the stable package surface the lifted triple targets)

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

- **qedrecover = scope.** Binds an IDL/overlay claim to a location in the binary: which discriminator arm, which entry PC, which reachable blocks, what CU budget. Output is descriptive metadata (`qedmeta.toml` plus the `recovered.lean` defs). It does not prove anything. Today it stops at "reachable blocks" (happy and sad); narrowing to the happy path needs a trace. It is a standalone, analysis-only crate (`cargo run -p qedrecover`), so it builds without the Lean bridge.
- **qedlift = prove.** Takes a region of bytecode and produces a discharged `cuTripleWithinMem` triple with a verified CU bound. Output is a machine-checked theorem plus, under `--trace`, a `*_balance_correct` corollary.

They are meant to compose. qedrecover's `discriminatorValue`, `armEntryPc`, and `cuBudget` are exactly what target qedlift (`--target-disc` and the budget assertion), and the `.pcs` trace narrows qedrecover's full reachable-block slice down to the one real happy path.

## How recovery works: disassembly, dispatcher recognition, overlay + IDL

### Disassembly: bytes to analysed instructions

qedrecover loads the `.so` with `solana_sbpf::elf::Executable::load` and runs `static_analysis::Analysis::from_executable`, which yields the three structures it reasons over:

- `analysis.instructions`: the decoded instruction list. `lddw` (`LD_DW_IMM`) is laid out in the binary as two 8-byte slots, but `augment_lddw_unchecked` merges them into one decoded instruction whose `imm` is the full 64-bit value.
- `analysis.cfg_nodes`: basic blocks keyed by start PC, each carrying its instruction range and `destinations` (successor blocks).
- `analysis.functions`: function entry PCs, used to bound a slice to one function.

Two PC spaces coexist and must not be mixed:

- **Slot PC**: the raw 8-byte slot index. This is the space `cfg_nodes` is keyed in, and the space a jump's `ptr` / `off` fields live in. `lddw` spans 2 slots.
- **Logical PC**: the decoded-array index (`analysis.instructions[i]`). This is the space Lean's `Decode.decodeProgram`, qedlift, and `.pcs` traces use. `lddw` is 1 element.

The two agree until the first `lddw`, then drift by one per `lddw` thereafter. `qed_analysis::PcMap` (`PcMap::from_insns`) is the single converter both tools route through; mixing the spaces was a real bug (transfer's arm entry came back as logical 309 instead of slot 336 / logical 304). qedrecover computes dispatcher results in slot space and converts with `slot_to_logical` before reporting them or comparing against a `.pcs` trace.

The Lean side independently re-decodes the same `.text` (`SVM.SBPF.Decode.decodeProgram`, checked by `native_decide`), so a wrong disassembly cannot pass the downstream proof: it is fail-closed (TCB section 5).

### Overlay + IDL: who supplies what

Recovery takes two off-chain inputs that split cleanly along "standard metadata" versus "qedsvm intent":

| Fact | Source | How it is encoded |
| --- | --- | --- |
| Which instructions are in scope | overlay | one `[[instruction]]` block per claimed instruction, by `name`; anything absent is skipped |
| MIR intrinsic each refines | overlay | `refines = "Mir.tokenTransfer"` |
| Claimed CU budget | overlay | `cu_budget = 76` |
| Path to the IDL | overlay | `idl = "spl_token.codama.json"`, relative to the overlay file |
| Discriminator value + width | Codama IDL | the instruction's `discriminator` argument: `type` is a `numberTypeNode` whose `format` (`u8`..`u64`) gives the width, and `defaultValue` is a `numberValueNode` whose `number` gives the value (e.g. 3) |
| Account roles | Codama IDL | per-account `name`, `isWritable`, `isSigner` |
| Account field layout | Codama IDL | `qed_analysis::layout::parse_account_layout` walks the account type nodes into a `FieldVal` offset/size list |

The overlay is the only qedsvm-specific file. In the production path qedgen emits it (and the sidecar) from source-level annotations at compile time, the way Anchor / Codama emit an IDL. For a third-party binary with no qedgen annotations (pinocchio p-token), the same fields are hand-written once and qedrecover scans the binary to bind them to PCs.

### qedrecover: from IDL instruction to bound metadata

For each in-scope instruction (`recover_one`):

1. **Read the discriminator from the IDL.** Find the argument named `discriminator`; its `format` maps to the load width via `discriminator_load_opc` (`u8 -> ldxb`, `u16 -> ldxh`, `u32 -> ldxw`, `u64 -> ldxdw`), and its `defaultValue.number` is the value to match. A missing, non-numeric, or unsupported-width discriminator makes the instruction "not analysable" (skipped, not an error).
2. **Recognise the dispatcher arm** (`find_dispatch_arm`). Scan for a load `ldxX rD, [r1 + 0]`: the source must be `r1` (the Solana input pointer) at offset 0, which avoids matching account-parsing loads on other pointers. Then, within a 64-instruction window that ends as soon as `rD` is overwritten (so a cluster of sibling arms reusing one load is handled), look for a compare-jump on `rD` against the discriminator value:
   - `jeq rD, disc`: the taken branch is the arm, entry slot = `jump.ptr + 1 + jump.off`.
   - `jne rD, disc`: the fall-through is the arm, entry slot = `jump.ptr + 1`.
3. **Slice the CFG** (`slice_cfg`). BFS from the arm entry over `cfg_nodes` `destinations`, bounded to the enclosing function's block set (`function_block_set`, derived from `analysis.functions`) so shared helper functions do not leak into the arm. The result is the arm's reachable blocks, happy and sad together.
4. **Classify constant error exits** (`error_exit_code`). For a block that terminates into `exit` (directly or via `ja`), scan backward for the last write to `r0`: a `mov r0, imm` / `lddw r0` is a static error code, whereas an `r0` produced by a `call` or set in an upstream block is not a constant and is left unclassified.
5. **Narrow to the happy path** (`--trace`, optional). A `.pcs` trace (one logical PC per executed CU, captured by `scripts/capture_trace.sh`) tags the on-trace blocks as `happyPathBlocks`, separating the executed path from error handlers and untaken branches in the full `reachableBlocks` slice.

It emits the `recovered.lean` defs (`refinesIntrinsic`, `cuBudget`, `accountRoles`, `discriminatorValue` / `Width`, `armEntryPc`, `reachableBlocks`) and, via `--qedmeta-out`, the `qedmeta.toml` sidecar (SHA-256 pins of the `.so` and IDL, program id, per-instruction discriminator + accounts + recovered PCs, plus the v0.2 idiom / happy-tag / const-exit tables). None of this proves anything; it binds the overlay/IDL claim to a location in the binary that qedlift then targets.

## Former seams (each now closed)

1. **qedlift reads `qedmeta.toml`** (closed 2026-06-02). `qedlift --qedmeta <toml>` drives targeting (`{discriminator.value, name, cu_budget}` per in-scope instruction) from the qedrecover sidecar instead of manual `--target-disc`/`--arm-name` flags.
2. **Trace capture is one command** (closed 2026-06-10). `scripts/capture_trace.sh <diff_mollusk_test> <out.pcs>` runs the test with `QEDSVM_TRACE_OUT` set; the Lean reference VM's runtime `traceStep` hook (`SVM/SBPF/Runner.lean` -> lean-bridge) writes decimal PCs directly. No source edits, no rebuild, no stderr post-processing (the old flip-`TRACE_STEPS` ritual survives only as a reg-dump debug knob).
3. **Happy/sad-path tagging works** (closed 2026-06-10). `qedrecover --trace <pcs>` tags on-trace blocks: the emitted metadata gains `happyPathBlocks`, separating the executed happy path from error handlers and untaken branches in `reachableBlocks`. (Closing this also surfaced and fixed a slot/logical PC-space mixing bug in dispatcher recovery — see the `transfer_arm_entry_spaces` pin test.)

The remaining gap to "one command" is orchestration only: scope (qedrecover) -> trace (capture_trace.sh) -> prove (qedlift) still run as three invocations. That composition belongs to qedgen long-term; qedgen is expected to emit the overlay/sidecar at compile time and own the one-command path. See the [README](../README.md).
