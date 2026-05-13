# formal-svm

A reference interpreter for the Solana Virtual Machine, in Lean 4, on the path to a verified macro assembler. Every sBPF instruction and every crypto syscall has a formal operational meaning the kernel can commit to.

formal-svm is Lean's role compounded: **assembler**, **macro language**, **specification language**, **proof assistant**, and **runtime**, all at once. You can hand it real Solana ELF bytecode and get back a kernel-committed final `State` (registers, memory, exit code, logs, return data). And you can — once the spec layer is further along — write sBPF directly as Lean terms, specify each instruction or macro with a separation-logic Hoare triple, and have Lean check that the implementation meets the spec. Triples are bounded: every spec carries an explicit step count `N` that doubles as a verified compute-unit budget.

The methodology is borrowed from [Verified-zkEVM/evm-asm](https://github.com/Verified-zkEVM/evm-asm), which descends from Kennedy/Benton/Jensen/Dagand, *"Coq: The world's best macro assembler?"* (PPDP 2013). They built a verified macro assembler for RV64IM and used it to implement EVM opcodes as RISC-V macros with machine-checked specs. We do the same thing for sBPF, targeting Solana programs.

## What it's for

Solana programs ship as sBPF bytecode produced by rustc → LLVM → sBPF. The compiler is in the trusted computing base of every program on mainnet. A bug in the toolchain — or a divergence between what the developer reasoned about in Rust and what the bytecode actually does — silently undermines correctness even if the source code is right.

formal-svm explores an alternative path for programs where this matters: **write the sBPF directly in Lean, prove it correct, and ship the bytecode**. The rustc pipeline never enters the picture. For CPI patterns, ATA derivations, signature checks, and the small handful of operations that bear most of the value on Solana, that compiler-free path is a soundness floor that no amount of source-level review reaches.

The same semantics, run the other way, is a **reference interpreter** with agave-conformant crypto. That's what's shipped today.

## What's shipped

The reference-interpreter layer is functionally complete. **101 lake jobs green, zero new sorry/axiom** beyond the 13 pre-existing `Memory.lean` coherence axioms (scheduled for removal by the byte-level separation-logic migration in Phase A).

### sBPF runner — `Svm/SBPF/Runner.lean`

```lean
structure RunConfig where
  input            : ByteArray      := ByteArray.empty   -- → INPUT_START, r1 set there
  cuBudget         : Nat            := 200_000
  programRegistry  : Nat → Option ByteArray := fun _ => none  -- CPI callees

Runner.run           : ByteArray → RunConfig → Option State   -- raw bytecode
Runner.runElf        : ByteArray → RunConfig → Option State   -- ELF64 binary
Runner.runForExit    : ByteArray → RunConfig → Option Nat
Runner.runElfForExit : ByteArray → RunConfig → Option Nat
```

- Full ALU (64- and 32-bit, imm and reg sources), all conditional + unconditional jumps, `exit`, `call`, load/store across all four widths. Two-pass decoder so `lddw` (which occupies two 8-byte slots) and branch offsets resolve correctly.
- **ELF64** loader: header + section table walk, name lookup in `.shstrtab`, `.text` and `.rodata` extraction with their `sh_addr`s. **R_BPF_64_64 relocations** applied before decode — the universal pattern across Anchor, Pinocchio, native-Rust, and Quasar binaries.
- **Syscall hash dispatch**: pure-Lean Murmur3-32, precomputed hashes for all 43 names in the `Syscall` enum (matches agave's full registry). The decoder's `call` arm produces *typed* `Syscall` variants directly from the bytes.
- **Observable side channels**: `State.log` and `State.returnData`, populated by `sol_log_*` and `sol_set_return_data` and untouched by separation-logic assertions, so existing Hoare triples stay unaffected.
- **CPI v1**: `Runner.executeFnCpi` is a CPI-aware execution loop. For `sol_invoke_signed[_c]` it consults `programRegistry`, decodes the callee, runs it recursively with caller memory inherited, and writes the callee's exit code into caller `r0`. v1 stubs documented in `docs/next-session-plan.md` (no `SolInstruction` reader, no account write-back, no PDA seeds, no CU split).

### Crypto syscalls — agave-conformant via `rust-bridge/`

Every cryptographic primitive calls the same crate agave's runtime calls, version-pinned to agave's master `Cargo.toml`:

| Syscall | Crate (agave master pin) | Status |
|---|---|---|
| `sol_sha256` | pure-Lean FIPS-180-4, audited against `sha2 = 0.10.8` | ✅ |
| `sol_sha512` | `sha2 = 0.10.8` | ✅ |
| `sol_keccak256` | `sha3 = 0.10.8` (Solana variant, 0x01 padding) | ✅ |
| `sol_blake3` | `blake3 = 1.8.5` | ✅ |
| `sol_secp256k1_recover` | `libsecp256k1 = 0.7.2` (paritytech) | ✅ |
| `sol_curve_validate_point` (Edwards + Ristretto) | `curve25519-dalek = 4.1.3` | ✅ |
| `sol_curve_group_op` (ADD/SUB/MUL × Edwards/Ristretto) | `curve25519-dalek = 4.1.3` | ✅ |
| `sol_curve_multiscalar_mul` (Edwards + Ristretto) | `curve25519-dalek = 4.1.3` | ✅ |
| `sol_curve_decompress` (BLS12-381 G1/G2) | `solana-bls12-381-syscall = 0.1.0` (→ `blstrs = 0.7.1`) | ✅ |
| `sol_curve_pairing_map` (BLS12-381) | `solana-bls12-381-syscall = 0.1.0` | ✅ |
| `sol_alt_bn128_group_op` (ADD/MUL/PAIRING × G1/G2 × BE/LE) | `solana-bn254 = 3.2.1` | ✅ |
| `sol_alt_bn128_compression` (compress/decompress × G1/G2 × BE/LE) | `solana-bn254 = 3.2.1` | ✅ |
| `sol_poseidon` (BN254 x⁵) | `light-poseidon = 0.4.0`, `ark-bn254 = 0.5.0` | ✅ |
| `sol_big_mod_exp` | `solana-big-mod-exp = 3.0.0` (→ `num-bigint`) | ✅ |

A `native_decide`-verified audit (`Svm/SBPF/RunnerDemo.lean` Demo 28) confirms the pure-Lean SHA-256 is byte-equivalent to `sha2 = 0.10.8` across a sweep of inputs (empty / single byte / "abc" / fox pangram / 256B / 1025B / 4096B). Production paths for Keccak and BLAKE3 go through the same crates directly, so the audit there is structural rather than empirical.

### Other syscalls

| Syscall | Behavior |
|---|---|
| `sol_log_`, `sol_log_pubkey` | Append bytes to `State.log` |
| `sol_log_64_`, `sol_log_compute_units_`, `sol_log_data` | Empty marker push (full formatting TODO) |
| `sol_memcpy`, `sol_memmove`, `sol_memset`, `sol_memcmp` | Real byte-level semantics on `Mem` |
| `sol_set_return_data`, `sol_get_return_data` | Round-trip via `State.returnData` |
| `sol_get_stack_height` | Returns 1 (top-level depth; CPI depth tracking deferred) |
| `sol_get_clock_sysvar`, `sol_get_rent_sysvar`, `sol_get_epoch_schedule_sysvar`, `sol_get_last_restart_slot`, `sol_get_fees_sysvar`, `sol_get_epoch_rewards_sysvar` | Zero-fill the output buffer (real sysvar values vary by epoch; zero is the safe default) |
| `sol_create_program_address`, `sol_try_find_program_address` | **Pure-Lean PDA derivation** (no new bridge code; composed of `Sha256.hash` + `Curve25519.validateEdwards` for the off-curve check) |
| `sol_invoke_signed`, `sol_invoke_signed_c` | CPI v1 (via `executeFnCpi`) |
| `abort`, `sol_panic_` | Set `exitCode := some ERR_ABORT`; `sol_panic_` also pushes the panic message to `State.log` |
| `sol_alloc_free_`, `sol_get_epoch_stake` | Documented stubs (deprecated / unmodeled) |

### Verification — `Svm/SBPF/RunnerDemo.lean`

38 demos / 108 `native_decide`-verified assertions, kept out of the production aggregator. Coverage:

- Raw ALU + jumps + memory ops + backward-loop counting.
- ELF round trips: `.text`-only, with `.rodata`, with `R_BPF_64_64` relocations.
- Typed syscall dispatch via Murmur3 round trip.
- `sol_memcpy` / `sol_memset` / `sol_memcmp` byte-level verification.
- `sol_log_` content inspection, return-data round trip, sysvar zero-fill.
- SHA-256 / Keccak / Blake3 / Sha512 against known test vectors + the SHA-256 ↔ agave conformance audit.
- secp256k1 recovery with a deterministic signature + `invalidRecoveryId` + `invalidSignature` + signature malleability.
- Full curve25519: basepoint validation, group ops (ADD/SUB/MUL × Edwards/Ristretto) against pre-computed doubled basepoints, MSM with N=1, N=2, distinct scalars.
- BLS12-381 G1/G2 decompression + pairing `e(g1, g2)` on the canonical generators.
- alt_bn128 ADD/MUL on the BN254 generator (1, 2), compression round-trip.
- Poseidon BN254 x⁵ in BE and LE against the official `solana-poseidon` test vector.
- PDA: well-known agave vector (`["Talking", "Squirrels"]`, BPFLoaderUpgradeable → `2fnQrn...`), plus negative tests for over-length seeds, too-many seeds, malformed pubkey.
- CPI: two-program registry, callee exits with `0x77`, caller propagates; unknown-pid → `r0 := 1`.
- `abort` → exit with `ERR_ABORT`.
- `sol_big_mod_exp` test vectors (3² mod 5, 2¹⁰ mod 1000, edge cases).

### Architecture — `rust-bridge/` + `lean_glue.c`

Crypto goes through a single 8-file Rust staticlib (`rust-bridge/`) pinning agave's exact dependency versions. The ~30-line `rust-bridge/lean_glue.c` re-exports Lean's `static inline` runtime helpers (`lean_alloc_sarray`, `lean_alloc_ctor`, `lean_box`, …) as out-of-line symbols so Rust can call them at the FFI boundary; that's the only C in the project. `build.rs` runs `lean --print-prefix` to find `lean/lean.h` and compiles `lean_glue.c` via `cc-rs`. Lake's `target rustBridge` invokes `cargo build --release` automatically during `lake build`.

When agave bumps a crypto crate version, `rust-bridge/Cargo.toml` bumps in lockstep — that is the *whole point* of the crate.

## What's not done yet

Honest framing — the substrate is built; the verification machinery on top is early.

- **Bounded Hoare triples / spec layer.** `Svm/SBPF/{SepLogic,CPSSpec,InstructionSpecs}.lean` define `cuTripleWithin`, frame, seq, weaken, and the first per-instruction triple (`mov64_imm_spec`). Most of the spec library is ahead. `Svm/SBPF/MacroDemo.lean` shows two verified two-instruction macros as a proof of pattern.
- **13 axioms in `Svm/SBPF/Memory.lean`** for the flat-memory coherence lemmas. These disappear with the byte-level separation-logic migration (Phase A); they're not load-bearing in the spec layer.
- **Differential test against agave shipped end-to-end.** `formal-svm-rs/tests/diff_mollusk.rs` runs the same `Instruction` through `formal_svm::Svm` and `mollusk_svm::Mollusk`. Three program shapes cross-checked, each asserting byte-for-byte equality on `program_result`, `return_data`, `resulting_accounts`, *and* `compute_units_consumed`:
  - **Minimal noop** (`mov64 r0, 0; exit`, 2 instructions) — CU 2 on both sides.
  - **Real `solana_program::entrypoint!` noop** (~1923 sBPF instructions, full input-buffer deserializer macro) — CU 98 on both sides. Exercises proper call/return through the `.call_local`/`.exit` push-PC/pop-PC plumbing.
  - **Logger** (`msg!("hi")` → `sol_log_`) — CU 202 on both sides. Exercises:
    - `R_BPF_64_32` relocation patching: imm gets overwritten with `Murmur3-32("sol_log_") = 0x207559bd` at load time
    - the unified function-key decoder (0x85 → if `SyscallHash.fromHash imm` is a known syscall, route to `.call syscall`; else `.call_local`)
    - the agave-conformant per-syscall CU table (`syscall_base_cost = 100`, with variable-length-aware costs for `sol_log_`, `sol_memcpy_`, sha256/keccak/blake3, secp256k1, BLS12-381, alt_bn128, big_mod_exp, Poseidon, PDA derivation, CPI, sysvars).
- **Call-frame caveat.** The return stack tracks return PCs only; callee-saved register preservation (r6–r9, r10 / frame-pointer arithmetic) is *not* modeled. Programs that rely on r6–r9 surviving across a call (rather than spilling them explicitly, which `cargo-build-sbf` typically does) will misbehave — full call-frame modeling is Phase D.
- **`sol_get_processed_sibling_instruction`** — needs an instruction-trace state we don't model (single-instruction execution today).
- **`sol_get_sysvar` (generic accessor)** — needs a sysvar registry keyed by sysvar-id.
- **CPI v2 deferments**: no `SolInstruction` reader, no callee account-input serialization, no account write-back, no PDA-signer seed validation, no CU-budget split, no stack-depth tracking. Today's CPI works for tests that pass program-id as a `Nat` directly via `r1`.

## Layout

```
Svm.lean                       — package root
Svm/
├── Account.lean               — Pubkey, Account, findBy{Key,Authority}
├── Cpi.lean                   — CpiInstruction envelope, program-ID registry,
│                                SPL/System/ATA discriminators
├── SBPF.lean                  — sBPF kernel aggregator
└── SBPF/
    ├── ISA.lean               — Insn + Syscall enums (43 variants, full agave registry)
    ├── Memory.lean            — byte-addressable Mem, region layout
    ├── Region.lean            — region IDs (rodata/bytecode/stack/heap/input)
    ├── Pubkey.lean            — sBPF-level pubkey reads
    ├── Execute.lean           — RegFile, machine State, step, executeFn,
    │                            execSyscall (every syscall arm in one place)
    ├── Decode.lean            — sBPF bytecode parser (lddw + jump-target resolution)
    ├── Elf.lean               — ELF64 loader (header, sections, .rodata, R_BPF_64_64)
    ├── Murmur3.lean           — pure-Lean Murmur3-32
    ├── SyscallHash.lean       — name → hash → typed Syscall (43 known)
    ├── Runner.lean            — production entrypoint + executeFnCpi (CPI v1)
    ├── RunnerDemo.lean        — 38 demos / 108 native_decide assertions
    │                            (kept out of the production aggregator)
    │
    │   ─ Crypto modules (each calls rust-bridge with agave-pinned crates) ─
    ├── Sha256.lean             — pure-Lean FIPS-180-4 + hashAgave audit hook
    ├── Sha512.lean             — sha2 = 0.10.8
    ├── Keccak256.lean          — sha3 = 0.10.8
    ├── Blake3.lean             — blake3 = 1.8.5
    ├── Secp256k1.lean          — libsecp256k1 = 0.7.2 (paritytech)
    ├── Curve25519.lean         — curve25519-dalek = 4.1.3
    │                             validate + group_op + multiscalar_mul
    ├── Bls12_381.lean          — solana-bls12-381-syscall = 0.1.0
    │                             decompress + pairing_map
    ├── AltBn128.lean           — solana-bn254 = 3.2.1
    │                             group_op + compression
    ├── Poseidon.lean           — light-poseidon = 0.4.0, BN254 x⁵
    ├── BigModExp.lean          — solana-big-mod-exp = 3.0.0
    ├── Pda.lean                — pure-Lean PDA derivation
    │                             (Sha256.hash + Curve25519.validateEdwards)
    │
    │   ─ Spec layer (early) ─
    ├── SepLogic.lean           — PartialState, separation logic, points-to
    ├── CPSSpec.lean            — cuTripleWithin, frame, seq, weaken
    ├── InstructionSpecs.lean   — per-instruction triples (first one in)
    ├── MacroDemo.lean          — verified two-instruction macros (proof of pattern)
    ├── Patterns.lean           — concrete-fetch composition lemmas
    ├── Tactic.lean             — misc tactics
    └── WPTactic.lean           — wp_exec (legacy, for concrete programs)

rust-bridge/                   — cargo staticlib called BY Lean for crypto syscalls
├── Cargo.toml                  — pinned versions matching agave master
├── Cargo.lock                  — checked in for reproducibility
├── build.rs                    — compiles lean_glue.c via cc-rs
├── lean_glue.c                 — ~30 lines: re-exports Lean's static-inline
│                                runtime helpers as out-of-line symbols
└── src/
    ├── lib.rs                  — extern "C" functions, one per @[extern] decl
    └── lean_ffi.rs             — Rust bindings to Lean's lean_object ABI

Svm/Ffi.lean                   — @[export formal_svm_run_elf_buffer] entry
                                  (ByteArray wire format the Rust crate decodes)

formal-svm-rs/                 — cargo crate that CALLS Lean — runs programs
                                  against the formal-svm via a Mollusk-shape API
├── Cargo.toml                  — solana-pubkey/instruction/account pinned to
│                                agave master; mollusk-svm optional
├── build.rs                    — auto-enumerates Lake's 33 dylib outputs
├── csrc/init_glue.c            — wrappers for Lean's static-inline init/IO helpers
└── src/
    ├── ffi.rs                  — Lean runtime lock + alloc/dec_ref/init
    ├── wire.rs                 — decode the Lean-side ByteArray result
    ├── serialize.rs            — accounts → BPF input buffer (agave-conformant)
    ├── deserialize.rs          — post-execution buffer → modified accounts
    └── svm.rs                  — Svm::process_instruction → InstructionResult
```

## Lean as several things at once

```lean
-- 1. Reference interpreter — runs real ELF binaries
example : Runner.runElfForExit anchorBinary { cuBudget := 200_000 } = some 0 := by
  native_decide

-- 2. Macro language: any Lean function producing instructions
def push_const (n : Nat) (dst : Reg) : List Insn :=
  if n = 0 then [.mov64 dst (.imm 0)] else [.lddw dst (.ofNat n)]

-- 3. Specification language: separation-logic Hoare triples
theorem mov64_reg_spec (dst src : Reg) (vOld v : Nat) (pc : Nat) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.mov64 dst (.reg src)))
      ((dst ↦ᵣ vOld) ** (src ↦ᵣ v))
      ((dst ↦ᵣ v)    ** (src ↦ᵣ v)) := by ...

-- 4. Proof assistant: Lean's kernel checks the proof
```

(1) is shipped end-to-end. (3) and (4) work for the small handful of instruction specs in `InstructionSpecs.lean` plus the two macros in `MacroDemo.lean`; growing that library to full ISA coverage is Phase B.

## Use it — from Lean

```lean
require formalSvm from git
  "https://github.com/QEDGen/formal-svm.git" @ "main"
```

Then `import Svm` (or import selectively, e.g. `import Svm.SBPF.Runner`).

Standalone build: `lake build`. Lean toolchain pin: `lean-toolchain`.

**Build prerequisites:** Lean (per `lean-toolchain`, fetched by `elan`) and `cargo` / `rustc` (any stable toolchain). Lake invokes `cargo build --release` automatically during `lake build`. No system crypto libraries required.

## Use it — from Rust (`formal-svm-rs`)

A sibling crate exposes the Lean runner via a Mollusk-shaped API for differential testing of Solana programs against the formal semantics.

```rust
use formal_svm::{ProgramResult, Svm};
use solana_instruction::Instruction;
use solana_pubkey::Pubkey;

let mut svm = Svm::default();
svm.add_program(&program_id, elf_bytes);

let result = svm.process_instruction(&instruction, &accounts)?;
assert_eq!(result.program_result, ProgramResult::Success);
assert_eq!(result.compute_units_consumed, 2);
```

Types (`Pubkey`, `Instruction`, `AccountMeta`, `AccountSharedData`) are the published `solana-pubkey` / `solana-instruction` / `solana-account` crates pinned to agave master, so a real Mollusk test can pass its `Vec<(Pubkey, AccountSharedData)>` and `Instruction` straight in. The crate handles:

- agave-conformant input-buffer serialization (round-trip-tested against `solana_program_entrypoint::deserialize`)
- post-execution buffer parsing into `resulting_accounts`
- CU accounting (per-instruction, matches Mollusk's reported count)
- thread-safe Lean runtime access (process-wide Mutex)

Differential testing against Mollusk (gated behind `--features diff-mollusk`):

```bash
cd formal-svm-rs && cargo test --features diff-mollusk
```

`tests/diff_mollusk.rs` runs a real `cargo-build-sbf`-produced ELF through both engines and asserts equality on `(program_result, return_data, resulting_accounts, compute_units_consumed)`.

**Prerequisites:** `lake build` has run at least once in the repo root (the build script auto-enumerates the 33 `formalSvm_*.dylib` outputs from `.lake/build/`).

## Roadmap

See `ROADMAP.md`. Headline phases:

- **A — Foundations**: SepLogic, bounded triples, first instruction specs *(in progress)*
- **B — Full ISA coverage**: one Hoare-triple spec per `Insn` constructor
- **C — Tactic suite**: composition automation (`runBlock`, frame inference, etc.)
- **D — Macro library**: memory ops, stack frames, control flow, CPI envelopes as verified sBPF macros
- **E — Solana program library**: System program ops, SPL Token transfers, ATA derive, common CPI patterns — each a verified macro with proven CU bound
- **F — Differential testing**: oracle alignment against `solana-sbpf` / Firedancer
- **G — ELF loader + execution** ✅ shipped
- **H — Crypto syscalls + zkSVM target**: ✅ crypto shipped; zkSVM target outstanding

## Origin

Extracted on 2026-05-12 from [QEDGen/solana-skills](https://github.com/QEDGen/solana-skills), which used it as the runtime model for spec-driven verification of Solana programs. The split gives the SVM model its own life as an ecosystem artifact.

The v0.3 re-scope to a verified macro assembler tracks the methodology of [Verified-zkEVM/evm-asm](https://github.com/Verified-zkEVM/evm-asm) — read their README and the PPDP 2013 paper if you want the methodology in its original form.

## License

MIT. See `LICENSE`.

## Contributing

Issues and PRs welcome. The roadmap describes the planned phases; out-of-roadmap contributions need a short rationale before they land. The bar is small trust base and honest specs — additions that broaden the surface without a clear soundness story will get pushback.
