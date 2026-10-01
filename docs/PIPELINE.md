# From `.so` + IDL to a Proof

Status: current toolchain reference
Related: `qedsvm-rs/qedrecover/`, `qedsvm-rs/qedlift/`, `examples/lean/Generated/`, [COVERAGE.md](COVERAGE.md), [API.md](API.md)

This document describes the current qedsvm pipeline for turning a compiled Solana program into a machine-checked Lean Hoare triple. The pipeline is scoped: it proves a selected instruction path over modeled bytecode and modeled syscalls. See [COVERAGE.md](COVERAGE.md) for the exact boundary.

## Inputs

All verification metadata is off-chain. The deployed `.so` is byte-identical to a build that does not know about qedsvm.

| Artifact | Example | Carries |
| --- | --- | --- |
| `.so` | `p_token.so` | Compiled SBF bytecode, the deployed artifact itself. |
| Codama IDL | `spl_token.codama.json` | Discriminators, account layout, argument types. |
| qedsvm overlay | `p_token.qedoverlay.toml` | qedsvm-specific intent: which instructions are in scope, the intrinsic each instruction refines, and the claimed CU budget. |
| execution trace | `p_token_transfer.pcs` | Optional logical-PC sequence for a concrete path. Required in practice for branchy happy-path lifts. |

`qedrecover` consumes `.so + IDL + overlay` and emits `qedmeta.toml`; when a trace is supplied, it also emits happy-path block tags. `qedlift` consumes `.so + qedmeta` and, when needed, a `.pcs` trace. In an annotated build, qedgen can emit the same sidecar shape directly.

## Flow

```
Optional trace:

  diff_mollusk fixture
        │
        ▼
┌──────────────────────────────────────────────────────────────┐
│ scripts/capture_trace.sh                                      │
│  - run a concrete fixture through qedsvm's Lean reference VM  │
│  - write logical PCs via QEDSVM_TRACE_OUT                     │
│  - emit a .pcs file for path tags and path walking            │
└──────────────────────────────────────────────────────────────┘

Main proof path:

  program.so + program.codama.json + program.qedoverlay.toml
        │
        │ optional: program.pcs
        ▼
┌──────────────────────────────────────────────────────────────┐
│ STAGE 1 - qedrecover  (.so + IDL + overlay [+ trace])         │
│  - load and analyze the SBF executable with solana-sbpf       │
│  - identify each in-scope discriminator arm                   │
│  - compute logical PCs for dispatch and arm entry             │
│  - slice reachable CFG blocks from the arm entry              │
│  - emit qedmeta.toml and optional recovered Lean metadata     │
└──────────────────────────────────────────────────────────────┘
        │
        │ program.qedmeta.toml
        │ optional: program.pcs
        ▼
┌──────────────────────────────────────────────────────────────┐
│ STAGE 2 - qedlift  (.so + qedmeta [+ trace] -> Lean proof)    │
│  - pin walked .text bytes with SVM.SBPF.Decode                │
│  - walk the selected bytecode path symbolically               │
│  - synthesize pre/post separation-logic atoms                 │
│  - state and discharge a cuTripleWithinMem theorem            │
│  - emit generated Lean modules under examples/lean/Generated/ │
└──────────────────────────────────────────────────────────────┘
        │
        ▼
┌──────────────────────────────────────────────────────────────┐
│ STAGE 3 - lake build  (verification gate)                     │
│  - type-check generated Lean                                  │
│  - fail if the proof, decode pins, or CU obligations fail     │
└──────────────────────────────────────────────────────────────┘

In parallel, the Rust harness diff-tests the same `.so` against mollusk/agave. That is a conformance signal for the qedsvm model, not the proof itself.
```

## Tool Roles

- **qedrecover** binds the off-chain verification claim to binary locations. It emits descriptive metadata: discriminator values, account roles, recovered PCs, reachable blocks, optional path tags, constant exits, and hash pins for the `.so` and IDL. It does not prove the program.
- **qedlift** consumes binary bytes plus targeting metadata and emits Lean theorems. The main theorem is a discharged `cuTripleWithinMem` triple with a CU bound. For supported refinement shapes, it also emits abstract corollaries such as token balance updates.
- **lake build** is the checker. A generated module only counts after Lean type-checks it without `sorry`.

## Current Commands

Capture a path trace from a diff-mollusk fixture:

```bash
scripts/capture_trace.sh \
  p_token_transfer_matches_mollusk \
  qedsvm-rs/tests/fixtures/p_token_transfer.pcs
```

Recover sidecar metadata:

```bash
cargo run --manifest-path qedsvm-rs/qedrecover/Cargo.toml -- \
  --so qedsvm-rs/tests/fixtures/p_token.so \
  --overlay qedsvm-rs/tests/fixtures/p_token.qedoverlay.toml \
  --trace qedsvm-rs/tests/fixtures/p_token_transfer.pcs \
  --qedmeta-out qedsvm-rs/tests/fixtures/p_token.transfer.recovered.qedmeta.toml
```

Lift through `qedmeta`:

```bash
cargo run --manifest-path qedsvm-rs/Cargo.toml -p qedlift -- \
  --so qedsvm-rs/tests/fixtures/p_token.so \
  --qedmeta qedsvm-rs/tests/fixtures/p_token.transfer.recovered.qedmeta.toml \
  --trace qedsvm-rs/tests/fixtures/p_token_transfer.pcs \
  --output examples/lean/Generated/PTokenTransferTracedLifted.lean
```

Check generated proofs:

```bash
lake build Examples
```

## Source-built v3 vault example

The retained `sbpfv3_vault_deposit` fixture exercises aligned input serialization
and a structured account with a pubkey, total, and bump. Recover its deposit arm
and check the sidecar handoff on the successful execution trace:

```bash
cargo run --manifest-path qedsvm-rs/Cargo.toml -p qedrecover -- \
  --so qedsvm-rs/tests/fixtures/sbpfv3_vault_deposit.so \
  --overlay qedsvm-rs/tests/fixtures/sbpfv3_vault_deposit.qedoverlay.toml \
  --trace qedsvm-rs/tests/fixtures/sbpfv3_vault_deposit_success.pcs \
  --qedmeta-out /tmp/sbpfv3_vault_deposit.qedmeta.toml

cargo run --manifest-path qedsvm-rs/Cargo.toml -p qedlift -- \
  --so qedsvm-rs/tests/fixtures/sbpfv3_vault_deposit.so \
  --qedmeta /tmp/sbpfv3_vault_deposit.qedmeta.toml \
  --idl qedsvm-rs/tests/fixtures/sbpfv3_vault_deposit.codama.json \
  --trace qedsvm-rs/tests/fixtures/sbpfv3_vault_deposit_success.pcs \
  --output examples/lean/Generated/Sbpfv3VaultDepositDepositLifted.lean
```

Separately, emit structured transitions from the same ELF, IDL, descriptor, and
four captured traces. This mode consumes the descriptor directly:

```bash
cargo run --manifest-path qedsvm-rs/Cargo.toml -p qedlift -- \
  --so qedsvm-rs/tests/fixtures/sbpfv3_vault_deposit.so \
  --idl qedsvm-rs/tests/fixtures/sbpfv3_vault_deposit.codama.json \
  --descriptor qedsvm-rs/tests/fixtures/sbpfv3_vault_deposit.descriptor.json \
  --transition --output-dir examples/lean/Generated
lake build Examples
```

The bundle proves the guarded success, zero-amount, overflow, and unknown-
discriminator transitions. `VaultDepositTransitionWitness.lean` instantiates
each branch, and `AxiomAudit` checks their axiom dependencies. The fixed account
lengths are explicit input assumptions; the trace bundle does not establish
exhaustive coverage of arbitrary executions.

The next fixture, `sbpfv3_vault_authorized`, parses a supported two-account schema:
a 41-byte writable vault and an empty signer authority. It checks the record
markers and lengths before advancing, exact 16-byte instruction length, all four
limbs of the vault's program owner, and all four limbs of the stored authority
key. Its counter update has no fund transfer or CPI.

Repeat the commands above with `sbpfv3_vault_authorized` as the fixture stem and
`Sbpfv3VaultAuthorizedDepositLifted.lean` as the recovered lift output. Recovery
finds discriminator load/compare/arm PCs 48/49/50. The transition mode emits 19
captured cases, including success, malformed inputs, missing signature, each
owner-key mismatch, zero amount, and overflow. Every case agrees with Mollusk
on exit, account state, return data, and CU. The full bundle and concrete branch
witnesses are included in `lake build Examples` and the axiom audit.

The descriptor's `[41, 0]` account lengths still describe the proof's memory
layout. For an early schema rejection, the theorem frames the declared vault
codec; it does not turn a malformed account into a valid IDL account or prove
that every arbitrary serialized buffer satisfies that codec. These are guarded
transition proofs over captured paths, not an exhaustive parser verification.

## PC Spaces

Two PC spaces are used:

| Space | Meaning | Used by |
| --- | --- | --- |
| Slot PC | Raw 8-byte instruction slot index. `lddw` occupies two slots. | solana-sbpf CFG nodes and raw jump offsets. |
| Logical PC | Decoded instruction-array index. `lddw` is one instruction. | Lean decode, `qedlift`, `.pcs` traces, and emitted proof metadata. |

`qed_analysis::PcMap` converts between them. `qedrecover` computes dispatcher facts in slot space and reports logical PCs in `qedmeta`, so `qedlift` and Lean consume one numbering scheme.

## Decode Pinning

Generated proofs are tied back to the binary bytes through `SVM.SBPF.Decode`:

- Small binaries use a full `Decode.decodeProgram` theorem checked by `native_decide`.
- Large binaries embed the full `.text` as hex, compute the slot map in Lean, and prove one `Decode.decodeInsn` pin per walked PC, also checked by `native_decide`.

The Hoare triple reasons over `CodeReq` singletons for the walked PCs. If those singleton instructions do not decode from the `.so` bytes, the generated Lean module fails to build.

## Metadata Contract

The qedsvm overlay supplies qedsvm-specific intent:

| Fact | Source |
| --- | --- |
| Instructions in scope | overlay `[[instruction]]` entries |
| Claimed refinement target | overlay `refines` |
| Claimed CU budget | overlay `cu_budget` |
| Instruction account layout bindings | overlay `[instruction.account_layouts]` |
| IDL path | overlay `idl` |

The Codama IDL supplies standard program metadata:

| Fact | Source |
| --- | --- |
| Discriminator value and width | instruction discriminator argument |
| Account roles | per-instruction account list |
| Account field layout | account type nodes parsed by `qed_analysis::layout` |

The emitted `qedmeta.toml` binds these facts to one binary using SHA-256 pins for the `.so` and IDL.

## Recovery Behavior

For each in-scope instruction, `qedrecover`:

1. Reads the discriminator value and width from the IDL.
2. Finds a discriminator load from the Solana input pointer.
3. Finds the compare-jump for that discriminator.
4. Computes the arm entry PC.
5. Slices reachable CFG blocks within the enclosing function.
6. Classifies static constant-exit blocks when possible.
7. Tags on-trace blocks as `happyPathBlocks` when `--trace` is provided.

Missing or unsupported IDL discriminator shapes make an instruction not analyzable; they do not create a proof obligation.

## Trace Contract

A `.pcs` trace is one decimal logical PC per line. `scripts/capture_trace.sh` writes this file by running a single diff-mollusk test with `QEDSVM_TRACE_OUT` set.

The trace records only the top-level program (CPI depth 0), so a run that crosses a CPI yields the caller-only path; the runner logs the invoke PC after the callee returns. Set `QEDSVM_TRACE_ALL_DEPTHS=1` to include nested callee PCs. For `--cpi-suffix`, each suffix `.pcs` starts at the PC right after the invoke.

When `qedlift` receives both `--qedmeta` and `--trace`, it cross-checks the recovered `arm_entry_pc` against the trace. If the sidecar describes a different arm than the trace executes, the lift fails.

## Limits

- `qedrecover` metadata is descriptive; it is not a proof.
- `qedlift` is a single-path symbolic executor. A trace gives bounded path proof, not a loop invariant or whole-CFG proof.
- Each lifted instruction arm is independent. There is no theorem that a set of arms covers the whole program.
- Unsupported opcodes, unsupported syscall semantics, missing refinement shapes, or CU-budget overruns fail the lift or the Lean build.
- Diff-testing against mollusk/agave supports model conformance. It does not replace the Lean proof.
