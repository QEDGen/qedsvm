# qedsvm examples

Worked examples demonstrating qedsvm's reach: running real
hand-written sBPF programs through the Lean reference VM, and proving
Lean Hoare specs over them.

The examples are **independent of the core library** — modifying or
removing them doesn't touch `Svm.SBPF.*`. Lean proofs live under
`Examples.*` (separate `lean_lib`); shell scripts run via
`qedsvm-cli`.

## Operational demo (cargo example)

### `doppler` — production oracle from https://github.com/blueshift-gg/doppler

```
cargo run --release --example doppler --manifest-path qedsvm-rs/Cargo.toml
```

Drives the doppler oracle program through `Svm::process_instruction`
(the mollusk-shaped Rust API), exercising all three code paths:

| Scenario | Path | Result |
|---|---|---|
| Admin OK + new_seq > current_seq | full update | `r0=0`, 21 CU, oracle state mutated 100→101 |
| Bad admin pubkey | `Admin::check` inline asm | `r0=1`, 7 CU (`lddw r0, 1; exit`) |
| Stale sequence (new ≤ current) | `Oracle::check_and_update` inline asm | `r0=2`, 19 CU (`lddw r0, 2; exit`) |

The example constructs Solana-shaped accounts and lets
`qedsvm::serialize_parameters` place the bytes at the offsets
doppler reads from — no manual buffer construction needed.

**Self-bootstrap**: the first run clones doppler, patches the
`#[no_mangle]`-on-panic_handler issue, runs `cargo-build-sbf`, and
caches the `.so` under `qedsvm-rs/target/examples-cache/doppler/`.
Subsequent runs hit the cache. Requires `cargo-build-sbf` on PATH.

To override the auto-bootstrap (e.g. with a pre-built .so):

```
DOPPLER_SO=/path/to/doppler_program.so \
  cargo run --release --example doppler --manifest-path qedsvm-rs/Cargo.toml
```

## Lean Hoare proofs

```
lake build Examples
```

builds the proofs in `examples/lean/`. They import from `Svm.SBPF.*`
but are NOT imported back into the core library.

### `examples/lean/ByteIncrement.lean`

Two variants of the byte-increment demo:

- `byteIncrementBytes` / `byteIncrementInsns` — 32 bytes hand-encoded
  in Lean. Three instructions (`ldx, add64, stx`) + `exit`.
- `byteIncrementSoText` / `byteIncrementSoInsns` — the 40 `.text`
  bytes of `byte_increment.so` produced by `cargo-build-sbf` from
  `qedsvm-rs/tests/fixtures/byte_increment_src/`. LLVM emits 5
  instructions (the macro + `mov r0, 0` + `exit`).

For each, theorems show:
- `*_decodes` — `Decode.decodeProgram bytes = some insns` (via `native_decide`).
- `*_run_is_executeFn` — `Runner.run` agrees with the pure
  `executeFn` of the decoded array (uses Session-1's
  `executeFnCpi_eq_executeFn_of_no_cpi_array`).
- `*_macro_witness` — applies `byte_increment_macro_spec` via
  `cuTripleWithinMem.toExec` to produce a k≤3 witness state where Q
  holds.
- `*_run_terminates` — full end-to-end: `Runner.run` returns a halted
  state equal to `step Insn.exit s_witness`, exitCode reflects the
  witness's r0.

The first end-to-end "raw bytes → Lean spec on `Runner.run`'s halted
output" theorem chain in the repo, on both hand-encoded and
LLVM-compiled bytes.

### `examples/lean/AsmTimeout.lean`

Embeds the 56-byte `.text` of `asm-timeout.so` (a real
hand-written sBPF program from blueshift) and proves:

- `asmTimeout_decodes` — the 56 bytes decode to a 6-element `Array Insn`.
- `asm_timeout_prefix_spec` — the first 3 instructions (`ldxdw +
  ldxdw + jgt`) load `current_slot` from `[r1+0x60]` and
  `target_slot` from `[r1+0x2898]`, then conditionally land at pc=4
  (timeout path) or pc=3 (in-window exit) based on `current > target`.

First Hoare proof in the repo over a hand-written sBPF program from
outside the qedsvm test fixtures.

## Why two halves

**Operational** demos prove "this binary works under qedsvm" — a
single program, one input, one output. Cheap, broad coverage, ideal
for showing the VM matches expectations.

**Hoare** proofs prove "this binary satisfies *this property* for *all*
inputs" — a precondition + postcondition + invariants. Expensive per
program, narrow coverage, ideal for security-critical kernels.

Together: the VM is faithful enough that proofs *in* it mean something
about real programs (operational evidence), and we have the machinery
to actually do those proofs (Hoare).
