# Test fixtures

## `hello.elf` (289 bytes)
Hand-assembled minimal ELF64 sBPF binary: `mov64 r0, 42; exit`.
Identical to `Svm.SBPF.RunnerDemo.helloElf` (Demo 8). Used by
`smoke.rs` and `svm_api.rs` for the simplest possible end-to-end
round trip through the Lean runtime.

It does *not* satisfy agave's stricter loader (no `.dynsym`, no
exported `entrypoint`), so it isn't used in `diff_mollusk.rs`.

## `noop.so` (~18 KB)
Real `cargo-build-sbf`-produced ELF of a no-op Solana program
(returns `Ok(())` without touching accounts). Source in `noop_src/`.

Used by `diff_mollusk.rs` to run the same instruction through
formal-svm and Mollusk and assert observable outputs agree.

## `solana_noop.so` / `logger.so` / `incrementer.so`
Same shape, progressively more program behavior:
- `solana_noop.so` — real `entrypoint!()` macro, zero account work.
- `logger.so` — `entrypoint!()` + a single `msg!("hi")` syscall.
- `incrementer.so` — `entrypoint!()` + reads a u64 from
  `accounts[0].data[0..8]`, increments, writes back. First fixture
  that actually mutates account data, exercising
  `deserialize_account_writes`.

### Rebuilding any `.so`

```
cd tests/fixtures/<name>_src
cargo-build-sbf
cp target/deploy/formal_svm_<name>.so ../<name>.so
```

Requires the Solana toolchain (cargo-build-sbf) on PATH.

## `cpi_caller.so` / `cpi_increment_caller.so`

Two CPI fixtures, both from `cargo-build-sbf`:

- `cpi_caller.so` — reads a 32-byte target pubkey from
  `instruction_data[0..32]`, invokes it via `solana_program::invoke`
  with no accounts and no data. Exercises the **zero-account CPI**
  path (sub-input is 48 bytes: `num_acc=0, ix_data_len=0, program_id`).
  Source in `cpi_caller_src/`.
- `cpi_increment_caller.so` — same target-pubkey shape, but forwards
  its one writable account through the CPI's `Instruction.accounts`.
  Exercises **one-account CPI with write-back** when registered against
  `incrementer.so`: the callee mutates the data, the caller's
  post-state reflects the mutation. Source in
  `cpi_increment_caller_src/`.

## Third-party `.so` fixtures (no `_src/`)

These three `.so` files were vendored verbatim from
[`blueshift-gg/sbpf`](https://github.com/blueshift-gg/sbpf) at
`crates/runtime/tests/fixtures/` (dual-licensed Apache-2.0 / MIT):

- `token.so` (134 KB) — SPL Token program, real on-chain binary.
- `associated_token.so` (105 KB) — SPL Associated Token Account
  program. CPIs into Token, so most ATA paths need our CPI stub
  replaced with real CPI before they'll diff cleanly.
- `libupstream_pinocchio_escrow.so` (28 KB) — Pinocchio-based escrow
  example. Bare-metal style program; smaller surface than token.

All three are V0 (`e_flags = 0`), so the V0 stack-frame model
applies. We use them as cross-engine diff inputs only; we don't
build or modify them in this repo.
