# Reproducing the existing p-token success proofs

This is the stage-1 baseline for [#82](https://github.com/QEDGen/qedsvm/issues/82).
It preserves PR #80's release fixture and proof coverage. It does not discover debug
labels, replace the binary, or add success paths. The recovered `guards_lean.py`,
`gen_paths.py`, `EmitIG.lean` and `gen_inputs.py` have been replaced by committed
Rust in `qedsvm-rs/qed-analysis/src/success_proofs*`. No scratchpad file, Python
package, `.debug` sidecar, or Lean runtime is needed for generation.

Run from the repository root:

```sh
cargo run --locked --manifest-path qedsvm-rs/Cargo.toml \
  -p qed-analysis --bin qed-success-proofs -- \
  qedsvm-rs/tests/fixtures/p_token.so \
  examples/lean/PToken/success-proof-inputs.json examples/lean/PToken
```

Append `--check` to generate in memory and reject any byte drift without writing.
The output directory contains `SuccessPaths.lean`, `SuccessInputs.lean` and
`ReadableFields.lean`. Both original success modules reproduce **byte for byte**.
The Rust CI job runs this check, and generator/fixture changes trigger the existing
Lean examples job (including its no-sorry and axiom-audit gates).

Then check the proofs, independently of the producer:

```sh
lake build PToken.SuccessPaths PToken.SuccessInputs PToken.ReadableFields \
  PToken.TransferSpec AxiomAudit
```

The ordinary `lake build Examples` also includes these modules. It needs the
repository's pinned Lean toolchain and native bridge dependencies, as before.

## Artifact identity

| Item | Pin |
| --- | --- |
| Fixture | `qedsvm-rs/tests/fixtures/p_token.so` (108600 bytes), sBPF V0 |
| ELF SHA-256 | `8190d3f7ceb6cb7a7a8d8924bff89f9f611e15ce1f806f2b6237f3311a98f697` |
| Loaded `.text` | 102608 bytes, embedded in `Generated/PTokenText.lean` |
| Entry | Logical PC 198 (PCs count an `lddw` once) |
| Program exit | Logical PC 3542 |
| No-return helpers | Logical PCs 11177 and 10881 |

The generator requires the exact ELF SHA-256 before producing output. A Rust test
compares **all** loaded `.text` bytes and the load-time function registry against
the existing Lean embedding; its slot map is still computed in Lean. This ties the
emitted guards and the proof checker to the same artifact, without changing any
bytecode or decode pin. The fixture's original build recipe is not established;
[#84](https://github.com/QEDGen/qedsvm/issues/84) and
[#87](https://github.com/QEDGen/qedsvm/issues/87) track provenance and migration.
The proofs concern these exact bytes, regardless of source-build reproducibility.

## Generated and authored inventory

| Module/input | Ownership and role |
| --- | --- |
| `success-proof-inputs.json` | Schema v1, artifact-bound **manual, untrusted** coverage/interpretation bindings; not proof assumptions. |
| `PToken/SuccessPaths.lean` | Generated guards, four route choices per edge, `check<edge>` native checks and `path<edge>` theorems. |
| `PToken/SuccessInputs.lean` | Generated input pins, unchanged Lean `ptAbsMap`/`absOk`, `pins<edge>` native checks and `inputs<edge>` theorems. |
| `PToken/ReadableFields.lean` | Generated numeric offset/width abbreviations; authored readable predicates consume these offsets. No axioms or proof facts. |
| `PToken/TransferSpec.lean` | Authored readable predicates and three Transfer requirements theorems. Only field positions now refer to generated abbreviations; requirements are definitionally unchanged. |
| `Generated/PTokenText.lean` | Existing qedlift-generated full `.text` and V0 function registry; unchanged. |
| `PToken/ErrorConvert`, `ErrorTail`, `PanicChain` | Authored failure-side proofs; unchanged. |
| Their `*Pins` modules | Authored concrete checker instantiations on the embedded binary; unchanged. `SuccessPaths` imports `PanicChainPins`. |
| `PToken/DispatchComplete` | Authored routing completeness proof; unchanged. |
| `SVM/SBPF/{CalleeReturn,BudgetMono,FailClosed,StaticReach,PathCond,AbsInterp,InputGuards}` | Generic authored checking interfaces and soundness theorems; unchanged. |
| `AxiomAudit.lean` | Existing axiom gate over the soundness layer and audited program theorems; unchanged. |
| `qed-analysis/src/success_proofs/*.lean.in` | Fixed Lean presentation/proof templates extracted from the original modules. They contain no computed guard lists or input-pin tables. |

All paths in this table are under `examples/lean/` unless otherwise qualified.
The versioned input format rejects unknown JSON fields and unsupported versions.
The library interface accepts `ProgramImage` plus deserialized `BaselineInputs`;
it does not depend on where those bindings came from. Stage 2 can supply discovered
bindings through that interface, without #81 labels being required for this binary.

## Baseline coverage

| Success edge | Operation | Guard occurrences | Input-pin occurrences |
| --- | --- | ---: | ---: |
| 4825 | Transfer, amount moved | 122 | 101 |
| 4832 | Transfer, native SOL | 127 | 106 |
| 5250 | Transfer, zero amount | 157 | 136 |
| 5063 | TransferChecked, amount moved | 167 | 141 |
| 5070 | TransferChecked, native SOL | 172 | 146 |
| 5473 | TransferChecked, zero amount | 202 | 176 |
| **Total** | **6 of 25 success edges** | **947** | **806** |

Counts include repetitions across the dominating list and four pre/post route
lists per edge; they are not counts of distinct instructions. There are 54 guard
lists, 24 edge/route combinations and 8 distinct authority checkpoints:

- Transfer: 4816 (owner signer), 5216 (delegate signer), 5715 (owner multisig),
  6233 (delegate multisig).
- TransferChecked: 5053 (owner signer), 5438 (delegate signer), 5995 (owner multisig),
  6432 (delegate multisig).

The three authored readable statements remain `transfer_requires`,
`transfer_native_requires` and `transfer_zero_requires`. They cover the original
layout/account-state/mint/authority requirements, the native tag on 4832, and the
original token-program owner checks on 5250 (four source words, three destination
words). The multisig branches remain initialized multisigs with `m = 0`; no new
signer-counting proof or InitializeMultisig invariant is assumed.

Unsupported success edges remain 3575, 3584, 4065, 4141, 4177, 4226, 4237, 4310,
4346, 4391, 4401, 4527, 4556, 4672, 4679, 4759, 4793, 5159 and 5426: the 19
paths behind loops (the Batch SCC at 429 and multisig signer counting). The
141 unpinned guard occurrences remain register facts, including amount and
instruction-length reads through data-length-dependent pointers. TransferChecked
still has no authored readable requirements theorem.

## Temporary manual inputs and their replacement

| JSON input | How it is used/checked now | Stage-2 responsibility |
| --- | --- | --- |
| `artifact_sha256`, `entry` | Exact ELF identity and loaded entry validation. | Bind discovered requirements to the same-build artifact; #87 changes p-token's fixture only after this baseline. |
| `noreturn` | Two explicit helper PCs; Rust requires recovered no-return functions and Lean retains `ptNoret_sound` from the existing panic proofs. | Discover bindings and retain independently checked no-return evidence. |
| `edges[].pc`, descriptions | Explicit ordered six-edge selection and documentation. Rust requires actual recovered success edges. | Discover selected success outcomes from the small same-build fixture and preserve an explicit coverage record. |
| `edges[].checkpoints` | Ordered four authority routes, including signer/multisig choices. Rust rejects invalid/unreachable/non-cut selections; Lean still checks every route cut. | Discover checkpoint/route bindings; do not interpret labels alone as semantic truth. |
| `guard_pins` | An explicit dispatcher guard/direction anchor for edge 4825; Rust requires a real, dominating, target-ward guard. All emitted guards are independently discovered and Lean-checked. | Replace manual anchors with checked discovered requirements. |
| `readable_fields` | All readable field base positions/widths are explicit (including header owner fields). Generated abbreviations replace positions in authored predicates; Lean proves those predicates from the existing byte pins. Names/widths are explanatory bindings, not inferred source/account semantics. | Derive layout/field bindings and check readable requirements against the byte-level facts. Token-program ID, enum values, key-limb encoding and readable proof composition remain authored until that stage. |

Rust computes guards by backward reachability, forward reachability and dominance
with the candidate guard removed. It mirrors Lean `callSucc` (returning calls fall
through; only the selected internal no-return helpers stop). Its small provenance
worklist mirrors `AbsInterp.absMap`: constant/input/frame provenance, written input
ranges and conservative forgetting across calls/syscalls. No Rust result is
trusted: the **unchanged** Lean map, post-fixpoint check, guard/route checks and
`native_decide` pins remain necessary. The generator checks its own post-fixpoint
to diagnose drift early, without adding a proof assumption.

Regression tests cover exact baseline bytes/counts, full artifact-to-Lean embedding,
wrong artifact identity (including no output creation), bad schema/unknown fields,
invalid checkpoints, a missing route, the wrong guard direction, invalid readable
names and CLI drift rejection without writes. Run:

```sh
cargo test --manifest-path qedsvm-rs/Cargo.toml -p qed-analysis
cargo clippy --manifest-path qedsvm-rs/Cargo.toml -p qed-analysis --all-targets -- -D warnings
cargo fmt --manifest-path qedsvm-rs/Cargo.toml --all -- --check
```

## Binary-derived bindings: the label-vault fixture

[solana-skills#450](https://github.com/QEDGen/solana-skills/issues/450) replaces the
manual inputs above with bindings that `qed-discover` finds in a same-build binary pair
(see `docs/BINDINGS.md`). The fixture is a small Pinocchio program built with
`qedgen build --arch v0 --tools-version v1.57` and `debug = 2`. Its source lives in
solana-skills (`crates/qedgen/tests/fixtures/pinocchio-fixtures/label-vault`). The pair is
`qedsvm-rs/tests/fixtures/label_vault{,.debug}.so`.

From `qedsvm-rs/`:

```sh
cargo run -p qed-analysis --bin qed-concept-map -- tests/fixtures/label_vault.so tests/fixtures/label_vault.debug.so > lv.concepts.json
cargo run -p qed-analysis --bin qed-discover -- tests/fixtures/label_vault.so tests/fixtures/label_vault.debug.so lv.concepts.json > tests/fixtures/label_vault.bindings.json
cargo run -p qed-analysis --bin qed-success-proofs -- --bindings tests/fixtures/label_vault.bindings.json \
  --names LabelVault tests/fixtures/label_vault.so ../examples/lean/LabelVault
cd .. && lake build LabelVault.Success AxiomAudit
```

`examples/lean/LabelVault/Success.lean` proves `readable53`: a run that reaches the one
success edge started from an input that meets the edge's checks and one instruction's
checks. For `increment` that includes discriminator 1, `initialized == 1`, account 1
signed, and account 1's key equal to the stored `authority`. Nothing in the module was
entered by hand. `decodes` checks that the text decodes, so the `insns?.all` checks
cannot hold vacuously. Guards whose operands are not pinned (for `increment`, the
instruction-length and overflow checks) are listed in the route's doc comment and in
`coverage.json`, not stated.

The same program built with `qedgen build --arch v3` is
`qedsvm-rs/tests/fixtures/label_vault_v3{,.debug}.so`, with modules in
`examples/lean/LabelVaultV3/` (prefix `LabelVaultV3`). The emitter decodes v3 text with
`Decode.decodeProgram text [] .v3`, as `Runner.runElfV3WithFuel` does: v3 calls are
relative, so there is no function registry. The frame model, the abstract interpreter and
the checkers are the same for both versions. Discovery and coverage match V0 exactly: the
same instructions, success edge, pinned guards and authority facts.

What changes against the p_token baseline:

| p_token manual input | label-vault source |
| --- | --- |
| `noreturn` | `noRetCheck` witness (`SVM/SBPF/NoReturnCheck.lean`), proved generically |
| `edges[].pc` | success edges reached through a dispatch arm |
| `edges[].checkpoints` | dispatch arms (one route per instruction) |
| `guard_pins` | none needed |
| `readable_fields` | Solana input-layout names and DWARF field labels |
| fixed offsets | `absStepA` with assumed account lengths (`lengths53` hypothesis) |

Known gaps: the bytecode checks still use `native_decide` (`AxiomAudit` allows only those
per-use axioms through `#assert_native_decide_axioms`; qedsvm#98). The authority
account's data length is not checked by the program, so the theorem assumes it is 0.
Handlers must be inlined into the entrypoint.
