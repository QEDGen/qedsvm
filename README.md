# qedsvm

**Verify what runs on Solana — not what you wrote.**

qedsvm is a Lean 4 model of the Solana Virtual Machine. It works on the compiled `.so` — the same artifact mainnet runs.

Byte-for-byte conformant with agave on real `cargo-build-sbf` output — 26 mollusk-cross-checked fixtures including p-token Transfer at **76 CU identical**, full suite in ~3 seconds. 142 per-instruction Hoare triples in separation logic, composable end-to-end with verified compute-unit bounds. No rustc in the trust base.

## What this is

qedsvm has two production deliverables, both from the same Lean 4 codebase:

**Run any compiled Solana program.** Hand qedsvm an ELF `.so` produced by `cargo-build-sbf`, an instruction, and accounts; get back `program_result`, `return_data`, modified `resulting_accounts`, and `compute_units_consumed` — byte-for-byte conformant with agave on every fixture in the harness.

**Prove what those programs do.** Decode the same `.so` to `List Insn` and compose 142 per-instruction separation-logic Hoare triples into a property proof. Every triple carries a step count that doubles as a verified compute-unit bound — proofs are CU-conscious by construction.

The trust base on the verification side is the Lean 4 ISA semantics in `SVM/SBPF/{Execute,Decode,Memory}.lean` plus 21 explicit crypto trust statements in `SVM/SBPF/CryptoTrust.lean`. No rustc. No external sBPF semantics.

For the layer-by-layer breakdown of what's proven vs what's still hand-verified, see [`ROADMAP.md`](ROADMAP.md).

## Use it — from Lean

```lean
require qedsvm from git
  "https://github.com/QEDGen/qedsvm.git" @ "main"
```

Then `import SVM` (or import selectively — `import SVM.SBPF.Runner` for the executor, `import SVM.SBPF.InstructionSpecs` for the spec layer). Standalone build: `lake build`. Toolchain pin: `lean-toolchain`. Prerequisites: Lean (via `elan`) and `cargo`/`rustc` (any stable toolchain) — Lake invokes `cargo build --release` for `qedsvm-rs/lean-bridge/` automatically.

**Run a compiled program:**

```lean
example : Runner.runElfForExit anchorBinary { cuBudget := 200_000 } = some 0 := by
  native_decide
```

**Prove a sequence:**

```lean
example : cuTripleWithin 2 0 2 someCode P Q := by sl_block_iter
```

Worked examples: `examples/lean/ByteIncrement.lean` for the complete bytes-to-witness chain on a hand-encoded program; `examples/lean/PToken/BalanceSpec.lean` for the high-level Solana-data-model refinement-target shape.

## Use it — from Rust (`qedsvm-rs`)

A sibling crate exposes the Lean runner via a Mollusk-shaped API for differential testing.

```rust
use qedsvm::{ProgramResult, SVM};

let mut svm = SVM::default();
svm.add_program(&program_id, elf_bytes);
let result = svm.process_instruction(&instruction, &accounts)?;
```

Types (`Pubkey`, `Instruction`, `AccountMeta`, `AccountSharedData`) are the published `solana-pubkey` / `solana-instruction` / `solana-account` crates pinned to agave master, so a real Mollusk test passes its data straight in. The crate handles agave-conformant input-buffer serialization, post-execution buffer parsing, CU accounting, and thread-safe Lean runtime access.

Differential testing against Mollusk (gated):

```bash
cd qedsvm-rs && cargo test --features diff-mollusk
```

**Prerequisites:** `lake build` has run at least once in the repo root.

## What's covered

**Execution.** Full ALU (64- and 32-bit, imm and reg sources), all jumps, full memory ops, `exit`/`call`/`callx`, two-pass decoder for `lddw` + branch offsets. ELF64 loader with all `R_BPF_64_*` relocations. V0 stack frames (`call_local` push, `exit` restore). Region-bounds enforcement traps OOR accesses with `ERR_ACCESS_VIOLATION`. Syscall hash dispatch via pure-Lean Murmur3-32. Real CPI (program registry + recursive `executeFn`, Rust + C ABI deserialization, account write-back, PDA signer promotion, depth-2+ recursion). Native programs aligned with Firedancer (System / ComputeBudget / BPF Loader v3 Upgradeable / ed25519+secp256k1+secp256r1 precompiles).

**Crypto syscalls** — every primitive calls the same crate agave's runtime calls, version-pinned to agave's master `Cargo.toml`:

| Syscall | Crate (agave master pin) |
|---|---|
| `sol_sha256` | pure-Lean FIPS-180-4, audited against `sha2 = 0.10.8` |
| `sol_sha512` | `sha2 = 0.10.8` |
| `sol_keccak256` | `sha3 = 0.10.8` (Solana variant, 0x01 padding) |
| `sol_blake3` | `blake3 = 1.8.5` |
| `sol_secp256k1_recover` | `libsecp256k1 = 0.7.2` (paritytech) |
| `sol_curve_validate_point` / `_group_op` / `_multiscalar_mul` | `curve25519-dalek = 4.1.3` (Edwards + Ristretto) |
| `sol_curve_decompress` / `_pairing_map` | `solana-bls12-381-syscall = 0.1.0` (→ `blstrs = 0.7.1`) |
| `sol_alt_bn128_group_op` / `_compression` | `solana-bn254 = 3.2.1` |
| `sol_poseidon` (BN254 x⁵) | `light-poseidon = 0.4.0`, `ark-bn254 = 0.5.0` |
| `sol_big_mod_exp` | `solana-big-mod-exp = 3.0.0` |

When agave bumps a crypto crate, `qedsvm-rs/lean-bridge/Cargo.toml` bumps in lockstep — that's the *whole point* of the crate. A `native_decide`-verified audit confirms the pure-Lean SHA-256 is byte-equivalent to `sha2 = 0.10.8` across a sweep of inputs.

**Other syscalls.** Logging (`sol_log_*` with agave-parity formatting), memory ops (`sol_mem{cpy,move,set,cmp}` with real byte-level semantics), `sol_set/get_return_data` round-trip, sysvar getters, **pure-Lean PDA derivation** (`sol_create_program_address` / `sol_try_find_program_address` via `Sha256.hash` + `Curve25519.validateEdwards`), real CPI via `sol_invoke_signed{,_c}`, `abort` / `sol_panic_`.

**Spec layer.** 142 per-instruction Hoare triples in `SVM/SBPF/InstructionSpecs.lean` covering the full user-facing ISA + call/return + 24+ syscalls, stated over a `PartialState` partial heap in `SVM/SBPF/SepLogic.lean`. Composition tactics — `sl_block_iter` (linear chain), `sl_branch` (if/else), `sl_rw_abs` (structural-reduction workaround) — in `SVM/SBPF/Tactic/SL.lean`. Small Solana data-model predicate library in `SVM/Solana/{TokenAccount,AccountInfo,Pda}.lean` for stating high-level handler theorems against bundled SL atoms. Trust base: the Lean 4 ISA semantics + 21 axioms in `SVM/SBPF/CryptoTrust.lean`. Composition tactics live in `SVM/SBPF/Tactic/{SL,WP,Base}.lean`.

**Differential testing.** 26 `cargo-build-sbf` fixtures cross-checked against `mollusk_svm::Mollusk`, each asserting byte-for-byte equality on `(program_result, return_data, resulting_accounts, compute_units_consumed)`. Headline: **p-token Transfer at 76 CU, byte+CU identical to mollusk** (Anza's pinocchio-based SPL Token reimplementation, the first mainnet-track program in the harness). Compared to canonical SPL Token Transfer at 4645 CU on the same instruction — the 61× ratio is the pinocchio-optimization story in numbers. Full suite runs in ~3 s.

**End-to-end proofs over real bytecode.** Layer 3a (hand-encoded sBPF → witness theorem): shipped in `examples/lean/ByteIncrement.lean`. Layer 3b (compiler-emitted bytecode): 7 incremental triples on p-token Transfer happy path reaching 52 of 76 CU. See [`ROADMAP.md`](ROADMAP.md) for the artifact-by-artifact breakdown and the closure punchlist; [`docs/archive/p-token-spike.md`](docs/archive/p-token-spike.md) for the original methodology validation.

## Layout

```
SVM/                 — Lean library
├── SBPF/            — interpreter + spec layer
│   ├── Tactic/      — SL block-iter, WP, base simp lemmas
│   └── …            — ISA, Memory, Execute, SepLogic, InstructionSpecs,
│                      Macros, Patterns, …
├── Syscalls/        — syscall bodies (one logical group per file)
├── Native/          — native programs (System, ComputeBudget, ...)
├── Pubkey.lean      — Pubkey + Account data model
└── Solana/          — Solana data-model SL predicates + CPI envelope
                      (tokenAcctBalance, accountInfoHeader, isPda, Cpi)

examples/lean/       — separate Examples lean_lib (ByteIncrement, AsmTimeout,
│                      CompilerRt*, MinimalTransferAsm, …)
└── PToken/          — p-token Transfer happy-path proof family
    ├── TransferArm/ — L1Setup → L5ThirdCall layered triples
    └── …            — ValidationPrelude, BalanceSpec, RefinesTransfer
examples/rust/       → qedsvm-rs/examples (symlink — cargo wants examples
                      under the crate; symlink keeps the two halves visible)

qedsvm-rs/           — Cargo workspace
├── (root crate)     — Mollusk-shaped Rust crate that calls Lean
└── lean-bridge/     — staticlib called by Lean for agave-pinned crypto

docs/                — active design notes (founding rationale, improvement
                       plan, production parity); docs/archive/ for shipped
                       plan docs
ROADMAP.md           — phase plan, status snapshot, headline numbers,
                       Layer 3b closure punchlist
```

For the full file-by-file tree, see `SVM.lean`'s import chain.

## Roadmap

See [`ROADMAP.md`](ROADMAP.md) for the phase-by-phase status snapshot, headline numbers, current Layer 3b closure punchlist, and the Direction-A MIR integration plans tracked in [QEDGen/solana-skills#66](https://github.com/QEDGen/solana-skills/issues/66).

## Origin

Extracted on 2026-05-12 from [QEDGen/solana-skills](https://github.com/QEDGen/solana-skills), which used it as the runtime model for spec-driven verification of Solana programs. The split gives the SVM model its own life as an ecosystem artifact. qedgen continues to vendor a copy of qedsvm's sBPF tree at `lean_solana/QEDGen/Solana/SBPF/` during the migration to a Lake `require`; integration plans are tracked in [QEDGen/solana-skills#66](https://github.com/QEDGen/solana-skills/issues/66) (Solana-native MIR proposal).

The separation-logic / bounded-Hoare-triple methodology is borrowed from [Verified-zkEVM/evm-asm](https://github.com/Verified-zkEVM/evm-asm), which descends from Kennedy/Benton/Jensen/Dagand, *"Coq: The world's best macro assembler?"* (PPDP 2013). evm-asm built a verified macro assembler for RV64IM and used it to author EVM opcodes as RISC-V macros with machine-checked specs. qedsvm takes the same spec machinery but applies it primarily to **verifying compiled programs** (the decompile-and-prove direction), with macro authoring as a secondary, in-tree track.

## License

MIT. See `LICENSE`.

## Contributing

Issues and PRs welcome. The roadmap describes the planned phases; out-of-roadmap contributions need a short rationale before they land. The bar is small trust base and honest specs — additions that broaden the surface without a clear soundness story will get pushback.
