# qedrecover

`qedrecover` locates IDL-described instruction arms inside a compiled Solana
program and emits the metadata that `qedlift` uses to target a proof.

| Input | Output |
| --- | --- |
| `.so` + Codama IDL + qedsvm overlay, optionally a `.pcs` trace | Dispatcher/CFG analysis and a hash-pinned `qedmeta.toml` sidecar |

It answers questions such as:

- Where does each instruction discriminator dispatch in the binary?
- Which logical PC begins the instruction arm?
- Which CFG blocks are reachable from that arm?
- Which account layouts and claimed CU budget belong to the proof target?
- Does an optional execution trace actually pass through the recovered arm?

`qedrecover` is analysis only. It does not execute the program, prove the overlay's
claim, or link the Lean runtime. The sidecar becomes proof-relevant only when
`qedlift` consumes it and Lean checks the generated theorem.

## Quick start

The overlay names its Codama IDL with a path relative to the overlay file. From
the repository root:

```bash
cargo run --manifest-path qedsvm-rs/qedrecover/Cargo.toml -- \
  --so qedsvm-rs/tests/fixtures/p_token.so \
  --overlay qedsvm-rs/tests/fixtures/p_token.qedoverlay.toml \
  --trace qedsvm-rs/tests/fixtures/p_token_transfer.pcs \
  --output /tmp/p_token.transfer.recovered.lean \
  --qedmeta-out /tmp/p_token.transfer.qedmeta.toml
```

The command prints a compact recovery table, writes recovered Lean metadata, and
writes a sidecar containing the binary/IDL hash pins, recovered arm PCs,
reachable blocks, account layouts, and overlay claims.

The handoff is:

```text
program.so + IDL + overlay [+ trace]
                  │
                  ▼
              qedrecover
                  │
                  ▼
           program.qedmeta.toml
                  │
                  ▼
               qedlift
                  │
                  ▼
            checked Lean theorem
```

See [`PIPELINE.md`](../../docs/PIPELINE.md) for the complete workflow and
[`qedlift`](../qedlift/README.md) for the proof-emission stage.

## Arguments

| Argument | Required | Meaning |
| --- | --- | --- |
| `--so <path>` | Yes | Compiled Solana ELF to analyze |
| `--overlay <path>` | Yes | qedsvm TOML overlay; also locates the IDL |
| `--qedmeta-out <path>` | No | Write the TOML sidecar consumed by `qedlift` |
| `--trace <path>` | No | Tag the selected instruction's happy-path blocks; requires exactly one claimed instruction |
| `--output <path>` | No | Emit recovered Lean metadata for the claimed instruction |

Without an output flag, `qedrecover` still prints its recovery report. An overlay
claim identifies what the user wants to verify; recovery does not establish that
the claimed refinement is true.

## Fail-closed checks

Recovery refuses or reports unsupported inputs rather than guessing when:

- the IDL discriminator shape is not analyzable;
- the overlay names a missing instruction or account layout;
- a dispatcher pattern cannot be found in the binary;
- a trace is supplied for an overlay that claims multiple instructions;
- the trace and recovered instruction metadata disagree downstream in `qedlift`.

The sidecar pins both the `.so` and IDL with SHA-256 so a proof cannot silently be
retargeted to different artifacts.

## Tests

`qedrecover` and the shared analysis crate are Lean-free and run in the fast Rust
CI job:

```bash
cargo test --manifest-path qedsvm-rs/Cargo.toml \
  -p qedrecover -p qed-analysis
```
