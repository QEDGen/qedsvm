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
