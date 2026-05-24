# qedsvm

A reference interpreter and verification substrate for the Solana Virtual Machine, formalized in Lean 4. Runs real `cargo-build-sbf`-produced Solana programs byte-for-byte against agave (25 diff-mollusk fixtures, full suite in ~3 s), with a per-instruction Hoare-triple spec layer (142 theorems) for proving properties of those programs.

## Two production deliverables

**1. Run compiled programs.** Hand `qedsvm` a Solana `.so` produced by `cargo-build-sbf`, accounts, and an instruction; get back `program_result`, `return_data`, modified `resulting_accounts`, and `compute_units_consumed` — byte-for-byte conformant with agave / mollusk on every fixture we've thrown at it. Crypto syscalls call the same Rust crates agave does, version-pinned to agave's master `Cargo.toml`.

**2. Verify compiled programs against specs.** Decode the same ELF to `List Insn`, then use per-instruction separation-logic Hoare triples and composition tactics to prove the program meets a property. Triples are bounded: every spec carries an explicit step count `N` that doubles as a verified compute-unit budget. This is the path for programs you didn't author — take an externally compiled `.so`, decompile to sBPF, prove its observable behavior equals a separation-logic spec.

The two together: ground-truth execution **and** provable properties on the same model, with no rustc in the trust base on the verification side.

## Scope

**In scope** (production goals):

- **Correctness** — an auditable Lean 4 operational semantics for sBPF.
- **Semantic baseline** — byte-for-byte conformance with agave on real `cargo-build-sbf` output, enforced by differential testing against mollusk.
- **Execution** — load and run arbitrary compiled Solana programs (ELF .so → decoded → executed), including crypto syscalls and CPI.
- **Spec layer** — per-instruction Hoare triples covering the full user-facing ISA, with composition tactics so a decompiled program can be proved against a separation-logic spec, carrying a verified CU bound.

**Out of scope**:

- **Validator-grade runtime.** Bank, slot lifecycle, account commits, consensus, gossip, leader schedule, vote processing — none of it. This is the program-execution layer, not the validator.
- **zkSVM target.** Compiling to a zkVM is not pursued. CU bounds remain meaningful in Lean alone.
- **Writing sBPF directly in Lean as the program-authoring story.** A small in-tree macro library exists as a proof-of-pattern (lamport transfer, PDA derivation, 2-way dispatch, fixed-size memcpy), but a full verified macro library for SPL Token / ATA / Anchor patterns is a longer-horizon track, not gating production.
- **A new verification tool.** This is the model + the spec layer that tools sit on. QEDGen and other consumers live elsewhere.

## What's shipped — execution

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

- Full ALU (64- and 32-bit, imm and reg sources), all conditional + unconditional jumps, `exit`, `call`, load/store across all four widths. Two-pass decoder so `lddw` (two 8-byte slots) and branch offsets resolve correctly.
- **ELF64** loader: header + section table walk, name lookup in `.shstrtab`, `.text` and `.rodata` extraction with their `sh_addr`s. `R_BPF_64_64`, `R_BPF_64_32`, and `R_BPF_64_RELATIVE` relocations applied before decode — the universal pattern across Anchor, Pinocchio, native-Rust, and Quasar binaries.
- **V0 stack frames** (`solana-sbpf::Interpreter::push_frame` semantics): `.call_local` pushes a `CallFrame(retPc, savedR6..savedR10)` and bumps `r10 += 0x2000`; `.exit` restores all six. Required for cargo-build-sbf's entrypoint deserializer not to alias spilled locals across sub-calls.
- **Region bounds enforcement**: `Memory.RegionTable` traps OOR accesses with `ERR_ACCESS_VIOLATION` on `.ldx`/`.st`/`.stx`.
- **Syscall hash dispatch**: pure-Lean Murmur3-32, precomputed hashes for all names in the `Syscall` enum (matches agave's full registry). The decoder's `call` arm produces *typed* `Syscall` variants directly from the bytes.
- **CPI (real)**: `Runner.executeFnCpiWithFuel` — program registry + recursive `executeFn`, ABI deserialization (Rust + C), account write-back, log/returnData propagation, proportional CU split, account aliasing detection, depth-2+ recursion, ixData propagation, **PDA signer-seed promotion** (r4/r5 → `create_program_address(seeds, callerPid)` → promote matching AccountInfo to `is_signer=true`).
- **Native programs** (Firedancer-aligned): System, ComputeBudget, BPF Loader v3 Upgradeable, ed25519 / secp256k1 / secp256r1 precompile dispatch.

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

A `native_decide`-verified audit confirms the pure-Lean SHA-256 is byte-equivalent to `sha2 = 0.10.8` across a sweep of inputs. Per-byte CU costs match agave's `mem_op_base_cost.max(byte_cost.saturating_mul(len / 2))` per-slice formula.

### Other syscalls

| Syscall | Behavior |
|---|---|
| `sol_log_`, `sol_log_pubkey` | Append bytes to `State.log` |
| `sol_log_64_`, `sol_log_compute_units_`, `sol_log_data` | Agave-parity formatting (`compute_units_` matches mollusk; `log_data` base64-encodes per slice) |
| `sol_memcpy`, `sol_memmove`, `sol_memset`, `sol_memcmp` | Real byte-level semantics on `Mem` |
| `sol_set_return_data`, `sol_get_return_data` | Round-trip via `State.returnData` |
| `sol_get_stack_height` | Tracks CPI depth |
| `sol_get_{clock,rent,epoch_schedule,last_restart_slot,fees,epoch_rewards}_sysvar` | Zero-fill the output buffer (real sysvar values vary by epoch; zero is the safe default) |
| `sol_create_program_address`, `sol_try_find_program_address` | **Pure-Lean PDA derivation** (`Sha256.hash` + `Curve25519.validateEdwards`) |
| `sol_invoke_signed`, `sol_invoke_signed_c` | Real CPI (see Runner above) |
| `abort`, `sol_panic_` | Set `exitCode := some ERR_ABORT`; `sol_panic_` also pushes the panic message |

### Differential testing — `qedsvm-rs/tests/diff_mollusk.rs`

25 real `cargo-build-sbf` fixtures cross-checked against `mollusk_svm::Mollusk`, each asserting byte-for-byte equality on `(program_result, return_data, resulting_accounts, compute_units_consumed)`. Highlights:

- Minimal noop (CU 2), `solana_program::entrypoint!` noop (~1923 instructions, CU 98), `msg!("hi")` logger (CU 202), incrementer with `try_borrow_mut_data()` write-back (CU 321), Doppler-style account-data manipulation.
- CPI: depth-2 recursion, returnData round-trip, PDA signer promotion.
- OOR access faults `ERR_ACCESS_VIOLATION` on both engines.
- SPL Token, ATA, Pinocchio fixtures (validate `.data.rel.ro` relocations).

After the 2026-05-20 `Mem` refactor (struct + `Std.HashMap` overlay, see `Memory.lean`), the full diff-mollusk suite finishes in **~3 s** vs. ~50 min previously (~1000× speedup).

## What's shipped — verification (spec layer)

The spec layer turns a decoded `List Insn` into something you can prove against a separation-logic spec.

### Foundations — `Svm/SBPF/{SepLogic,CPSSpec}.lean`

- **`PartialState`** — partial heap over registers, memory bytes, PC, returnData, callStack.
- **`Assertion := PartialState → Prop`** with separating conjunction `**`, `emp`, points-to `r ↦ᵣ v`, `addr ↦ₘ b`, `pcIs v`, `returnDataIs rd`, `callStackIs cs`.
- **`holdsFor : Assertion → State → Prop`** bridge to the executable `State`.
- **`cuTripleWithin (N : Nat) (entry exit_ : Nat) (cr : CodeReq) (P Q : Assertion) : Prop`** — bounded Hoare triple. `N` is the verified step count / CU bound.
- **`cuBranchWithin`** — two-exit variant for conditional jumps.
- **`cuTripleAbortsWithin`** — terminating-instruction variant for `exit` / `abort` / `sol_panic_`.
- **Structural rules**: `weaken`, `seq`, `frame` (baked into the definition), `mono_nSteps`, `refl`, `branch_merge`.

### Per-instruction triples — `Svm/SBPF/InstructionSpecs.lean`

**142 theorems covering the user-facing ISA + call/return + the mem-op and sysvar-getter syscall families**:

- **ALU 64-bit** (13 ops × {imm, reg}) — `mov`, `add`, `sub`, `mul`, `div`, `mod`, `or`, `and`, `xor`, `lsh`, `rsh`, `arsh`, `neg`.
- **ALU 32-bit** (13 ops × {imm, reg}) — same op set, result zero-extended.
- **Conditional jumps** (11 ops × {imm, reg}) — `jeq`, `jne`, `jgt`, `jge`, `jlt`, `jle`, `jsgt`, `jsge`, `jslt`, `jsle`, `jset`.
- **Unconditional**: `ja`, `lddw`, `callx` (value-dependent exit PC).
- **Memory** (byte-level `↦ₘ` predicate): `ldxb/h/w/dw`, `stxb/h/w/dw`, `stb`.
- **Call / return**: `call_local_spec` (push frame, bump `r10 += 0x1000`, jump to target) and `exit_pops_spec` (pop frame, restore `r6..r10`, jump to saved retPc), both over the `callStackIs` atom.
- **Terminating instructions**: `exit`, `abort`, `sol_panic_` via `cuTripleAbortsWithin`.
- **Syscall specs (24+)**:
  - **Round-trip via `returnDataIs`**: `sol_set_return_data` (post owns `returnDataIs bsIn`) and `sol_get_return_data` (exact-fit case).
  - **PDA** (both variants): `sol_create_program_address` n=0 and n=1.
  - **Mem-op family**: `sol_memset`, `sol_memcpy`, `sol_memmove`, `sol_memcmp`.
  - **Sysvar-getter family**: `sol_get_clock_sysvar`, `sol_get_epoch_rewards_sysvar`, `sol_get_rent_sysvar`, `sol_get_epoch_schedule_sysvar`, `sol_get_fees_sysvar`, `sol_get_last_restart_slot`.
  - **r0-only writes** (factored into `cuTripleWithin_syscall_writes_r0_only`): the 5 `sol_log_*` variants, `sol_get_stack_height`, `sol_get_epoch_stake`, `sol_get_processed_sibling_instruction`, `sol_get_sysvar` (generic), `.unknown` (parametric over hash). Each concrete spec reduces to ~12 lines.
  - **Other**: `sol_remaining_compute_units`, 6 crypto error-path triples.

Open per-instruction gaps:
- **Crypto syscall success-path triples** — each ~400-line `sol_create_program_address`-style proof. Error-path triples and 21 trust statements landed at commit `9948b3a`; success-path is the remaining slice.
- **Store-immediate at non-byte widths** (`sth` / `stw` / `stdw`) — need ~150-line helper lemmas per width.
- **Truncated-copy variant of `sol_get_return_data`** — exact-fit case shipped; truncated case is a small follow-up.

### Composition tactics — `Svm/SBPF/{SLTactic,SpecGen,Patterns}.lean`

- **`sl_block_iter`** — auto-applies per-instruction specs left-to-right over a `List Insn`, summing CU bounds and threading PCs.
- **`sl_branch`** — drives `cuBranchWithin` through `branch_merge` for if/else patterns.
- **`sl_rw_abs`** — rewriting under abstraction, mitigating Lean's structural-reduction ceiling for large fetch maps.
- **`sl_block_auto`** — hand-dispatched per-Insn spec lookup. Dispatches the full 64-bit and 32-bit ALU (imm + reg) including `neg64`/`neg32`, `lddw`, and `ldx`/`stx` at all four widths. `div`/`mod` not auto-dispatched (their specs carry a `divisor ≠ 0` side condition the helper doesn't auto-supply — use `sl_block_iter` with manual hypotheses). The foundation a decompile-and-verify tool would compose against.
- **`Patterns.lean`** — concrete-fetch composition lemmas for end-to-end `executeFn`-level statements.

### Trust base

- **Lean 4 ISA semantics** in `Svm/SBPF/{Execute,Decode,Memory}.lean` — every instruction modeled explicitly; nothing imported from an external sBPF spec.
- **Crypto primitives** through `rust-bridge/` to agave-pinned crates (explicit per-syscall trust statement; 21 `axiom` declarations in `Svm/SBPF/CryptoTrust.lean`).

Everything else is proved. The 13 memory-coherence axioms previously in `Memory.lean` were eliminated at commit `2b86be5` (now theorems).

## What's shipped — verified macro library (in-tree, off the production critical path)

`Svm/SBPF/Macros.lean` carries 13 macros, each a list-of-`Insn` definition + a bounded Hoare triple + a verified CU bound:

- **Simple ALU**: `two_mov`, `add_constants`, `mov_then_add_reg`, `load_then_add`.
- **Memory**: `byte_increment`, `u64_memcpy_16` (fixed-size 16-byte copy).
- **Lamports**: `lamport_transfer` (read both balances, sub from src, add to dst, write back).
- **Control flow**: `if_else`, `spl_token_2way_dispatch` (discriminator switch).
- **PDA**: `pda_n0`, `pda_n1`, `pda_n1_stack` (three configurations — no seeds, one seed in regs, one seed via stack VmSlice).

These are **proof-of-pattern**, not a shipping verified-macro library. They demonstrate that:

1. Sequences proved with per-instruction triples actually compose under the tactic suite.
2. Real on-chain patterns (lamport math, PDA derive, dispatch) admit clean separation-logic specs.
3. The macros can be reused as *recognizable shapes* when verifying decompiled programs — a future tool could spot a `lamport_transfer`-shaped instruction sequence in compiled output and discharge it with the existing triple.

Authoring new macros to cover SPL Token / ATA / full Anchor patterns is a longer-horizon track — not gating production.

## What's not done yet

- **Crypto syscall success-path triples.** The 21 trust statements + 6 error-path triples ship at commit `9948b3a`. Success-path triples for the 13 crypto syscalls (sha256, sha512, keccak256, blake3, secp256k1, curve25519, BLS12-381, alt_bn128, big_mod_exp, poseidon, PDA) remain open. Next step: a `cuTripleWithin_syscall_writesR3Bytes_r1r2` helper to cover the hash family; 5 instantiations × ~30 lines.
- **Store-immediate triples for non-byte widths.** `stb_spec` ships via a 165-line helper; `sth` / `stw` / `stdw` need parallel helpers at the same scale.
- **Phase F broader fixture coverage** — more SPL Token / ATA / Pinocchio escrow positive paths, plus a fuzz/sweep harness over generated `Vec<Insn>`. Cheap surface, high regression-catch rate.
- **`sol_get_processed_sibling_instruction`** — needs an instruction-trace state we don't model.
- **`sol_get_sysvar` (generic accessor)** — needs a sysvar registry keyed by sysvar-id.

## Architecture — `rust-bridge/` + `lean_glue.c`

Crypto goes through a single 8-file Rust staticlib (`rust-bridge/`) pinning agave's exact dependency versions. The ~30-line `rust-bridge/lean_glue.c` re-exports Lean's `static inline` runtime helpers (`lean_alloc_sarray`, `lean_alloc_ctor`, `lean_box`, …) as out-of-line symbols so Rust can call them at the FFI boundary; that's the only C in the project. `build.rs` runs `lean --print-prefix` to find `lean/lean.h` and compiles `lean_glue.c` via `cc-rs`. Lake's `target rustBridge` invokes `cargo build --release` automatically during `lake build`.

When agave bumps a crypto crate version, `rust-bridge/Cargo.toml` bumps in lockstep — that is the *whole point* of the crate.

## Layout

```
Svm.lean                       — package root
Svm/
├── Account.lean               — Pubkey, Account, findBy{Key,Authority}
├── Cpi.lean                   — CpiInstruction envelope, program-ID registry,
│                                SPL/System/ATA discriminators
├── Ffi.lean                   — @[export qedsvm_run_elf_buffer] entry
├── SBPF.lean                  — sBPF kernel aggregator
├── SBPF/                      — sBPF interpreter + spec layer
├── Syscalls/                  — syscall bodies (one file per logical group)
└── Native/                    — native programs (System, ComputeBudget,
                                 BPF Loader v3 Upgradeable, precompile dispatch)

Svm/SBPF/                      — interpreter + spec layer
├── ISA.lean                   — Insn + Syscall enums (full agave registry)
├── Memory.lean                — byte-addressable Mem (struct + HashMap overlay)
├── Region.lean                — region IDs (rodata/bytecode/stack/heap/input)
├── Pubkey.lean                — sBPF-level pubkey reads
├── Machine.lean               — State, RegFile, CallFrame, shared body helpers
├── Execute.lean               — step, executeFn; execSyscall/syscallCu dispatchers
├── Decode.lean                — bytecode parser (lddw + jump-target resolution)
├── Elf.lean                   — ELF64 loader (R_BPF_64_{64,32,RELATIVE})
├── Murmur3.lean               — pure-Lean Murmur3-32 (kernel-reducible)
├── SyscallHash.lean           — name → hash → typed Syscall
├── Runner.lean                — production entrypoint + executeFnCpiWithFuel
├── RunnerBridge.lean          — FFI wrapper consumed by Svm/Ffi.lean
├── RunnerTests.lean           — native_decide runs over Runner.run on
│                                hand-encoded bytecode + ELF
│
│   ─ Spec layer ─
├── SepLogic.lean              — PartialState, separation logic, points-to
├── CPSSpec.lean               — cuTripleWithin, frame, seq, weaken, branch_merge
├── InstructionSpecs.lean      — 142 per-instruction Hoare triples
├── SpecGen.lean               — sl_block_auto: hand-dispatched per-Insn lookup
├── Patterns.lean              — concrete-fetch composition lemmas
├── SLTactic.lean              — sl_block_iter / sl_branch / sl_rw_abs tactics
├── Macros.lean                — 13 in-tree macros (proof-of-pattern; off the
│                                production critical path)
├── Tactic.lean                — misc tactics
└── WPTactic.lean              — wp_exec (legacy, for concrete programs)

Svm/Syscalls/                  — every syscall body (one logical group per file)
├── Abort.lean                 — abort, sol_panic_
├── Logging.lean               — sol_log_, sol_log_pubkey, sol_log_data, …
├── MemOps.lean                — sol_memcpy_/memmove_/memset_/memcmp_
├── ReturnData.lean            — sol_set_return_data / sol_get_return_data
├── Sysvar.lean                — sol_get_{clock,rent,epoch_schedule,…}_sysvar
├── Cpi.lean                   — sol_invoke_signed_c / sol_invoke_signed_rust
├── Misc.lean                  — sol_get_stack_height + other small syscalls
│
│   ─ Crypto (rust-bridge with agave-pinned crates;
│             Sha256/Murmur3 are pure-Lean) ─
├── Sha256.lean                — pure-Lean FIPS-180-4 + hashAgave audit hook
├── Sha512.lean, Keccak256.lean, Blake3.lean
├── Secp256k1.lean, Curve25519.lean
├── Bls12_381.lean, AltBn128.lean
├── Poseidon.lean, BigModExp.lean
└── Pda.lean                   — sol_create_program_address +
                                 sol_try_find_program_address

examples/lean/                 — separate Examples lean_lib
├── ByteIncrement.lean         — hand-encoded byte_increment program + spec
└── AsmTimeout.lean            — sBPF + Hoare spec for the asm-timeout demo

rust-bridge/                   — cargo staticlib called BY Lean for crypto
├── Cargo.toml                  — pinned versions matching agave master
├── build.rs, lean_glue.c
└── src/{lib.rs,lean_ffi.rs}

qedsvm-rs/                     — cargo crate that CALLS Lean — runs programs
                                 against qedsvm via a Mollusk-shape API
├── Cargo.toml                  — solana-pubkey/instruction/account pinned to
│                                agave master; mollusk-svm optional
├── build.rs                    — auto-enumerates Lake's dylib outputs
├── csrc/init_glue.c            — wrappers for Lean's init/IO helpers
└── src/
    ├── ffi.rs                  — Lean runtime lock + alloc/dec_ref/init
    ├── wire.rs                 — decode the Lean-side ByteArray result
    ├── serialize.rs            — accounts → BPF input buffer (agave-conformant)
    ├── deserialize.rs          — post-execution buffer → modified accounts
    └── svm.rs                  — Svm::process_instruction → InstructionResult
```

## Use it — from Lean

```lean
require qedsvm from git
  "https://github.com/QEDGen/qedsvm.git" @ "main"
```

Then `import Svm` (or import selectively, e.g. `import Svm.SBPF.Runner` for the executor, `import Svm.SBPF.InstructionSpecs` for the spec layer).

Standalone build: `lake build`. Lean toolchain pin: `lean-toolchain`.

**Build prerequisites:** Lean (per `lean-toolchain`, fetched by `elan`) and `cargo` / `rustc` (any stable toolchain). Lake invokes `cargo build --release` automatically during `lake build`. No system crypto libraries required.

### Run a compiled program

```lean
example : Runner.runElfForExit anchorBinary { cuBudget := 200_000 } = some 0 := by
  native_decide
```

### Prove a sequence against a spec

```lean
-- Per-instruction triple from InstructionSpecs.lean
theorem mov64_reg_spec (dst src : Reg) (vOld v : Nat) (pc : Nat) :
    cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc (.mov64 dst (.reg src)))
      ((dst ↦ᵣ vOld) ** (src ↦ᵣ v))
      ((dst ↦ᵣ v)    ** (src ↦ᵣ v))

-- Composed via sl_block_iter for a decoded List Insn
example : cuTripleWithin 2 0 2 someCode P Q := by sl_block_iter
```

## Use it — from Rust (`qedsvm-rs`)

A sibling crate exposes the Lean runner via a Mollusk-shaped API for differential testing of Solana programs against the formal semantics.

```rust
use qedsvm::{ProgramResult, Svm};
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
cd qedsvm-rs && cargo test --features diff-mollusk
```

`tests/diff_mollusk.rs` runs real `cargo-build-sbf`-produced ELFs through both engines and asserts equality on `(program_result, return_data, resulting_accounts, compute_units_consumed)`.

**Prerequisites:** `lake build` has run at least once in the repo root (the build script auto-enumerates the `qedsvm_*.dylib` outputs from `.lake/build/`).

## Roadmap

See `ROADMAP.md`. Production track:

- **Phase A — Foundations**: SepLogic, bounded triples, first instruction specs ✅
- **Phase B — Full ISA coverage**: per-instruction Hoare triples ✅ (142 theorems)
- **Phase C — Tactic suite**: composition automation (`sl_block_iter`, `sl_branch`, `sl_rw_abs`) ✅
- **Phase F — Differential testing**: byte-for-byte cross-engine agreement on `cargo-build-sbf` output ✅ (25 fixtures + 5 precompile + 11 svm_api + rent + thread-safety; broader fixture / fuzz harness open)
- **Phase G — ELF loader + execution** ✅
- **Phase H — Crypto syscalls** ✅

Off the production critical path (in-tree, longer horizon):

- **Phase D — sBPF macro library**: stack-frame patterns, sized memcmp, more control-flow combinators.
- **Phase E — Solana program library**: SPL Token / ATA / Anchor patterns as verified macros.

## Origin

Extracted on 2026-05-12 from [QEDGen/solana-skills](https://github.com/QEDGen/solana-skills), which used it as the runtime model for spec-driven verification of Solana programs. The split gives the SVM model its own life as an ecosystem artifact.

The separation-logic / bounded-Hoare-triple methodology is borrowed from [Verified-zkEVM/evm-asm](https://github.com/Verified-zkEVM/evm-asm), which descends from Kennedy/Benton/Jensen/Dagand, *"Coq: The world's best macro assembler?"* (PPDP 2013). evm-asm built a verified macro assembler for RV64IM and used it to author EVM opcodes as RISC-V macros with machine-checked specs. qedsvm takes the same spec machinery but applies it primarily to **verifying compiled programs** (the decompile-and-prove direction), with macro authoring as a secondary, in-tree track.

## License

MIT. See `LICENSE`.

## Contributing

Issues and PRs welcome. The roadmap describes the planned phases; out-of-roadmap contributions need a short rationale before they land. The bar is small trust base and honest specs — additions that broaden the surface without a clear soundness story will get pushback.
