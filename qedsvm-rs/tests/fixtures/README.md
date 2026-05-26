# Test fixtures

## `hello.elf` (289 bytes)
Hand-assembled minimal ELF64 sBPF binary: `mov64 r0, 42; exit`.
Identical to `SVM.SBPF.RunnerDemo.helloElf` (Demo 8). Used by
`smoke.rs` and `svm_api.rs` for the simplest possible end-to-end
round trip through the Lean runtime.

It does *not* satisfy agave's stricter loader (no `.dynsym`, no
exported `entrypoint`), so it isn't used in `diff_mollusk.rs`.

## `noop.so` (~18 KB)
Real `cargo-build-sbf`-produced ELF of a no-op Solana program
(returns `Ok(())` without touching accounts). Source in `noop_src/`.

Used by `diff_mollusk.rs` to run the same instruction through
qedsvm and Mollusk and assert observable outputs agree.

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
cp target/deploy/qedsvm_<name>.so ../<name>.so
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

## `p_token.so` (106 KB)

p-token (the pinocchio-based SPL Token reimplementation by Anza /
Solana Program Library team), release `p-token@v1.0.0-rc.1`
(April 2025). Drop-in for `TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA`,
byte-for-byte compatible account layouts with the canonical SPL
Token (`Mint` = 82 bytes, `TokenAccount` = 165 bytes), so our existing
`build_token_account` helper applies unchanged.

Source: <https://github.com/solana-program/token/releases/tag/p-token%40v1.0.0-rc.1>
(asset `spl_p_token.so`).

SHA-256: `8190d3f7ceb6cb7a7a8d8924bff89f9f611e15ce1f806f2b6237f3311a98f697`

V0 (`e_flags = 0`). First major recognizable mainnet-track program
in the harness — exercises pinocchio's zero-copy account access
pattern (raw pointer casts into the serialized input buffer, no
Borsh) against our memory model. Used as a cross-engine diff input;
not built in this repo.

## `janus_pyth_price_resolver_devnet.so` (13 KB)

`janus-pyth-price-resolver` (Pinocchio 0.8), pulled from devnet via
`solana program dump --url devnet 3WDargKHd1UaP9UKPhJY8pF5bv5zJnaFAYDA9uahs5aL`
at 2026-05-26.

SHA-256: `0b891f14ed0945fc2ace325a974be59f0f0d88e695536df5dc3bfbfdd70f0a16`

Source: <https://github.com/saicharanpogul/janus> (the program the
issue #2 reporter used). Used by
`tests/pinocchio_program_error.rs` to confirm Pinocchio's
`(error_code << 32)` r0 encoding round-trips through
`ProgramResult::from_bpf_r0` into the typed `ProgramError` variant
that matches mollusk's `Failure(InstructionError::ProgramError(_))`
surface.

## `janus_slot_height_resolver_devnet.so` (12 KB)

`janus-slot-height-resolver` (Pinocchio 0.8), pulled from devnet via
`solana program dump --url devnet 3y75gGqFK1KhNF5k1sMy6ydnw6WLcbn1SPRoYbyRkjMj`
at 2026-05-26.

SHA-256: `cf989fab1e8c4712723831766ddeb28a1162f55a4a43050dfb7c88258fb989db`

Source: <https://github.com/saicharanpogul/janus> (sibling program
to the pyth-price-resolver fixture above; same reporter). Used by
`diff_mollusk.rs`'s
`janus_slot_height_resolver_initialize_matches_mollusk` to confirm
`sol_invoke_signed_c` + PDA-target `CreateAccount` CPI works
end-to-end. The synthetic `system_create_account_cpi_matches_mollusk`
covers the simpler Rust-ABI / hard-signer case; this fixture
specifically exercises the C-ABI `CpiAccount` parsing path that
issue #10 was about.
