# qedsvm Roadmap

The path to a correct, semantic-baseline SVM that can execute compiled Solana programs.

## Scope

**In scope (production goals):**
- Correctness: a hand-written, auditable operational semantics for sBPF, with separation-logic Hoare triples per instruction.
- Semantic baseline: byte-for-byte conformance with agave on real `cargo-build-sbf` output, enforced by differential testing.
- Execution: load and run arbitrary compiled Solana programs (ELF .so → decoded → executed) including crypto syscalls and CPI.

**Out of scope:**
- **Validator-grade runtime.** Bank, slot lifecycle, account commits, consensus, gossip, leader schedule, vote processing — none of it. This is the program-execution layer, not the validator.
- **zkSVM target.** Compiling the macro library to a zkVM is not pursued. CU bounds remain meaningful in Lean without a zk backend.
- **A new verification tool.** This is the model + the assembler + the macro library. Tools that use it — QEDGen and others — live elsewhere.

The v0.3 re-scope replaces the earlier phase plan (Phase 0 axiom cleanup → Phase 1 CPI small-step → ... → Phase 6 crypto) with a methodology lifted from [Verified-zkEVM/evm-asm](https://github.com/Verified-zkEVM/evm-asm): separation logic over machine state, bounded Hoare triples, per-instruction specs, then macros built and verified compositionally on top. The original CPI work isn't dropped — it reappears as Phase D/E (CPI envelope and per-program effects, written as verified sBPF macros). The verified-macro track (Phase D/E) is a longer-horizon deliverable that lets people *write* programs in Lean; it is not on the critical path to executing compiled programs.

## Status snapshot — 2026-05-18

| Phase | Status | Notes |
| --- | --- | --- |
| Phase 0 — Axiom cleanup | ✅ shipped (v0.2.0) | `Account.lean` axioms eliminated; flat-`Mem` axioms naturally dropped once Phase A landed |
| Phase A — Foundations | ✅ shipped | `SepLogic.lean`, `CPSSpec.lean`, `InstructionSpecs.lean` all live; pure-ALU + memory + branch specs in |
| Phase B — Full ISA spec coverage | ✅ shipped | `SpecGen.lean` hand-dispatches a Hoare triple per `Insn` constructor (`sl_block_auto`) |
| Phase C — Tactic suite | ✅ shipped (with one mitigation) | `sl_block_iter`, `sl_branch`, `sl_rw_abs` elab tactics in `SLTactic.lean`. Gap 3 (structural reduction ceiling) closed-with-mitigation via `sl_rw_abs` — kernel-attribute path confirmed dead |
| Phase D — sBPF macro library | ✅ mostly shipped | Memory (`u64_memcpy_16`), control flow (`if_else`, 2-way dispatch), CPI envelope pieces (PDA n=0, n=1, full stack-VmSlice variant) all proven in `MacroDemo.lean`. Stack frame setup/teardown library polish + sized memcmp still open |
| Phase E — Solana program library | ⚠️ partial | System `Transfer` shipped end-to-end via the `Native` path (byte + CU parity vs mollusk); rent-exempt enforcement integration tests landed. SPL Token / ATA / Anchor patterns not yet written as verified macros (Token + ATA are Core-BPF, so they ride the BPF VM + Loader v3 path today rather than a native dispatcher) |
| Phase F — Differential testing | ✅ mostly shipped | 25 diff-mollusk fixtures + 5 precompile-dispatch + 11 svm_api + rent + thread-safety; PT_LOAD-only ELFs + fuzz/sweep harness still open |
| Phase G — ELF loader + arbitrary program execution | ✅ shipped | Tier-1 #1 (region bounds — `RegionTable` in `Memory.lean` traps OOR accesses with `ERR_ACCESS_VIOLATION`), Tier-1 #2 (native programs aligned with Firedancer: System + ComputeBudget + BPF Loader v3 Upgradeable + ed25519/secp256k1/secp256r1 precompiles), Tier-1 #2b (precompile dispatch), all Tier-2 ship-blockers (rent enforcement, log-data base64, `sol_log_compute_units_` agave-parity, top-level CU limit). `executeFnCpi ≡ executeFn` bridge for non-CPI programs landed. **Real CPI shipped**: program registry + recursive `executeFn`, ABI deserialization (Rust + C), account write-back, log/returnData propagation, proportional CU split, account aliasing detection, depth-2+ recursion, ixData propagation to callee, **PDA signer-seed promotion** (r4/r5 → `create_program_address(seeds, callerPid)` → promote matching AccountInfo to `is_signer=true`). **R_BPF_64_RELATIVE** applied to `.text` (lddw imm bump via `applyRelRelativeText`) and `.data.rel.ro` (pointer field shifts via `applyDataRelocations`). **Per-byte hash CU** (`hashSliceCost` in `Machine.lean`: `max(10, len/2)` per slice + 85 base) for sha256/sha512/keccak256/blake3, matching agave. PT_LOAD-only ELFs verified out of scope (agave rejects them). Remaining: `@[implemented_by]` native compile (throughput only — the functional `Mem` makes hot reads O(write-chain-length)) |
| Phase H — Crypto syscalls | ✅ mostly shipped | All 12 crypto syscalls (sha256/sha512/keccak256/blake3, secp256k1, curve25519, BLS12-381, alt_bn128, big_mod_exp, poseidon, PDA) shipped via Rust FFI bridge to the same crates agave uses — explicit trust statements per syscall. SHA-256 + Murmur3 are pure-Lean and kernel-reducible. Pure-Lean ports of the remaining syscalls are a long-horizon followup, not on the production critical path |

**Headline numbers**: 155 Lean jobs green, ~58 Rust tests green (25 diff-mollusk + 5 precompile + 11 svm_api + 17 other).

**Rough completeness, weighted by impact, not LOC**:
- *Production critical path* (Phases 0–C, F, G, H): Phases 0–C done, F ~82%, G ~100% (correctness), H ~90%. Aggregate: **~97% shipped on correctness**. Remaining: Phase F broader fixture coverage / fuzz harness. Throughput-only follow-up: Phase G `@[implemented_by]` native compile to speed up the functional `Mem` reads (the full diff-mollusk suite takes ~50min, dominated by `encodeRun`'s byte-by-byte `readBytes` walking the Mem write chain).
- *Verified-macro track* (Phases D, E — not on the production critical path): D ~85%, E ~20%. Useful for writing programs in Lean; not required to execute compiled Solana programs.

**Tooling-track ideas** live in [`docs/improvement-plan.md`](docs/improvement-plan.md) — orthogonal to the phase plan above.

## Shipped

### v0.2.0 — Phase 0: Axiom cleanup (partial) ✅

Removed the five `axiom` declarations in `Svm/Account.lean` (list-update lemmas, now real theorems in core Lean). The 13 read/write-coherence axioms in `Svm/SBPF/Memory.lean` were left as a follow-up — they don't disappear with `simp` lemmas on the flat `Mem` model, but they're naturally eliminated by the byte-level separation-logic memory introduced in Phase A. After Phase A, the macro library uses byte-level `↦ₘ` predicates, the flat `Mem` axioms drop out, and the trust base is the hand-written ISA semantics + crypto primitives only.

## Current track: v0.3.x — Verified macro assembler

### Phase A — Foundations ✅

The minimum needed to write the first Hoare-triple instruction spec.

- `Svm/SBPF/SepLogic.lean`
  - `PartialState` (partial heap over registers, memory bytes, PC)
  - `Assertion := PartialState → Prop`, separating conjunction `**`, `emp`
  - Points-to: `r ↦ᵣ v`, `addr ↦ₘ b` (byte), `pcIs v`
  - `holdsFor : Assertion → State → Prop` bridge to the executable `State`
  - Structural lemmas: `Disjoint.symm`, `union_comm_of_disjoint`, `sepConj_comm/assoc`, `emp` identities
- `Svm/SBPF/CPSSpec.lean`
  - `CodeReq := Nat → Option Insn`, `CodeReq.SatisfiedBy fetch`, `union`, `Disjoint`
  - `cuTripleWithin (N : Nat) (entry exit_ : Nat) (cr : CodeReq) (P Q : Assertion) : Prop`
  - `cuBranchWithin` two-exit variant for conditional jumps
  - Structural rules: `weaken`, `seq`, `frame` (already baked into the definition), `mono_nSteps`, `refl`, `branch_merge`
- `Svm/SBPF/InstructionSpecs.lean` (first half)
  - `mov64` reg→reg as the proof-of-pattern
  - extend through the pure-ALU 64-bit ops (`add64`, `sub64`, `and64`, `or64`, `xor64`, etc.)

**Outcome**: any sBPF program built from those instructions can be specified and verified compositionally, with a CU bound.

**Estimate**: 4–6 weeks.

### Phase B — Full ISA spec coverage

One bounded Hoare triple for every constructor of `Insn`:
- 32-bit ALU (`add32` … `neg32`)
- Memory ops (`ldx`, `st`, `stx` per width) — the first specs that exercise the byte-level `↦ₘ` predicate
- Control flow (`jeq` … `jset`, `ja`) — exercises `cuBranchWithin`
- `lddw`, `exit`, `call` (per-syscall specs in Phase D)

**Estimate**: 4–8 weeks.

### Phase C — Tactic suite

Composition becomes mechanical:
- `runBlock` — auto-apply per-instruction specs left-to-right, summing CU bounds and threading PCs
- `xperm` / `xcancel` — separation-logic permutation and cancellation
- `seqFrame` — auto frame inference for `cuTripleWithin_seq`
- `liftSpec` — go from per-limb / per-byte specs to whole-word specs
- `@[spec_gen]` attribute for the instruction-spec database

These are direct ports of evm-asm's tactic suite (`EvmAsm/Rv64/Tactics/`).

**Estimate**: 4–6 weeks.

### Phase D — sBPF macro library

Verified building blocks above the per-instruction layer:
- Memory: 64-bit aligned loads/stores, byte-by-byte copy, sized memcmp
- Stack: frame setup/teardown, spill/restore patterns (sBPF stack frames are caller-managed via r10)
- Control flow: `if_eq` / `if_lt` / `while_lt` macros with branch specs
- CPI envelope: `invoke_signed` register layout, signer-seed serialization
- Syscall calling conventions: argument layout in r1–r5, return in r0

Each item is a list-of-`Insn` macro + a Hoare triple + a verified CU bound.

**Estimate**: 6–10 weeks.

### Phase E — Solana program library

Concrete, ship-grade verified macros for the on-chain operations that matter:
- **System program**: `CreateAccount`, `Transfer`, `Allocate`, `Assign`
- **SPL Token**: `Transfer`, `TransferChecked`, `Approve`, `Burn`, `MintTo`
- **ATA**: derivation, `CreateAssociatedTokenAccount`
- **Common Anchor patterns**: account validation, discriminator checks, PDA seed verification

Each ships as: an sBPF macro (in Lean), a Hoare triple (with separation logic over account-data assertions), and a CU bound. Programs that use these macros as building blocks get end-to-end verified CU budgets and correctness, **with no rustc → sBPF compiler in the TCB**.

**Estimate**: 12–20 weeks.

### Phase F — Differential testing *(byte-for-byte cross-engine agreement on real cargo-build-sbf output)*

Extract the sBPF semantics (`Svm.SBPF.Execute`) to executable Lean / native and oracle-align against:
- Firedancer's `vm-fuzz` corpus
- Agave's `solana-sbpf` test suite
- A curated mainnet program corpus

Every disagreement is either a bug in our semantics or evidence of cross-client divergence worth surfacing. This is the empirical answer to the "is the hand-written ISA correct" question — until it passes, every Phase-E spec inherits this uncertainty.

**What's shipped (through 2026-05-14):**
- `qedsvm-rs/` Rust crate exposes the Lean runner via a Mollusk-shaped API (`Svm::process_instruction(&ix, &accounts) -> InstructionResult`). Same types as published agave-master pins (`solana-pubkey`, `solana-instruction`, `solana-account`), so Mollusk tests can swap engines by changing one type name.
- Agave-conformant input-buffer serializer with round-trip test against `solana_program_entrypoint::deserialize`, plus byte-level known-offset checks.
- Thread-safe Lean runtime access (process-wide `Mutex`, stress-tested at 8 threads × 50 iters × varied input sizes).
- `tests/diff_mollusk.rs` (gated `--features diff-mollusk`): runs the same `Instruction` through `qedsvm::Svm` and `mollusk_svm::Mollusk`, asserting equality on `program_result`, `return_data`, `resulting_accounts`, `compute_units_consumed`.
- **Five real `cargo-build-sbf` fixtures pass byte-for-byte cross-engine equality**: minimal noop (CU=2), `solana_program::entrypoint!` noop (CU=98), `msg!("hi")` logger (CU=202), incrementer that mutates `accounts[0].data` and writes back (CU=321), and noop+instruction-data. The incrementer is the strongest end-to-end conformance claim: `entrypoint!()` deserializes input, `try_borrow_mut_data()` succeeds, `u64+1` write-back is byte-identical to mollusk's resulting accounts.
- ELF + decoder coverage for actual `cargo-build-sbf` (3.1.11 / platform-tools v1.52) output: `e_entry` honored, `R_BPF_64_32` Murmur3 relocations applied, `0x85` call decoder is src-agnostic (syscall hash lookup first, else `.call_local` PC-relative), `0x8d callx` (indirect call) decoded.
- **V0 stack frames** (`solana-sbpf::Interpreter::push_frame` semantics): `.call_local` pushes a `CallFrame(retPc, savedR6..savedR10)` and bumps `r10 += 0x2000` (stack_frame_gaps); `.exit` restores all six fields. Without this LLVM-emitted entrypoint deserializers iterate forever because their loop counter spills to the same `r10 + const` offset across sub-calls.

**What's left:**
- More real-program fixtures (SPL Token, Associated Token Account, Pinocchio-style escrow). Cheap test surface, high catch rate for regressions. Apache-2.0 `.so` files harvestable from blueshift-gg/sbpf.
- `R_BPF_64_RELATIVE` relocations (shift `.rodata` to `MM_PROGRAM_START + sh_addr`, patch `lddw` imms).
- SBPF V1/V2 manual stack-frame bump (SIMD-0166) — current emit by cargo-build-sbf 3.1.11 is V0, so unblocked.
- Region bounds enforcement: `Mem` is total; agave faults on OOR access. Most observable on adversarial inputs.
- Fuzz/sweep harness over generated `Vec<Insn>` programs.
- Firedancer comparison at the primitive level via `fd_ballet` FFI (per-hash, per-curve diff). Syscall-level diff vs agave is already covered by mollusk fixtures.

**Remaining estimate**: 1–2 weeks for additional fixture coverage + `R_BPF_64_RELATIVE`; the diff harness itself is done.

### Phase G — ELF loader + arbitrary program execution *(architectural deliverable shipped)*

The full pipeline runs end-to-end: `ByteArray` → Decoder → typed
`Syscall` dispatch → executor with observable side channels → result.

**Bytecode parsing — `Svm/SBPF/Decode.lean`**: 8-byte (and 16-byte
`lddw`) instruction encoding for the full ALU set (64-bit and 32-bit,
imm and reg sources), all conditional and unconditional jumps (imm and
reg), `exit`, `call`, and load/store across all four widths. Two-pass
design with a byte-slot → logical-PC map so jump offsets resolve
correctly when `lddw` is mixed with branches.

**ELF loading — `Svm/SBPF/Elf.lean`**: ELF64 header parse with magic /
class / endianness validation, section header table walk, name lookup
in `.shstrtab`, `.text` and `.rodata` extraction with their `sh_addr`s.

**Syscall hash dispatch — `Svm/SBPF/Murmur3.lean` +
`Svm/SBPF/SyscallHash.lean`**: pure-Lean Murmur3-32 implementation
(kernel-reducible for `native_decide`), precomputed hashes for all 25
syscall names in the `Syscall` enum, `fromHash : Nat → Syscall`
resolver. The decoder's `call` arm produces *typed* `Syscall` variants
straight from the bytes.

**Production runner — `Svm/SBPF/Runner.lean`**:

```lean
structure RunConfig where
  input    : ByteArray := ByteArray.empty   -- → INPUT_START, with r1 set there
  cuBudget : Nat       := 200_000           -- Solana per-program default

Runner.run         : ByteArray → RunConfig → Option State   -- raw bytecode
Runner.runElf      : ByteArray → RunConfig → Option State   -- ELF64 binary, maps .rodata
Runner.runForExit  : ByteArray → RunConfig → Option Nat
Runner.runElfForExit : ByteArray → RunConfig → Option Nat
```

**Observable side channels — `State` has `log` and `returnData`
fields** (untouched by separation-logic assertions, so existing Hoare
triples are unaffected).

**Syscall semantics implemented in `Svm/SBPF/Execute.lean`**:
- `sol_log_`, `sol_log_pubkey` — append message bytes to `state.log`
- `sol_log_64_`, `sol_log_compute_units_`, `sol_log_data` — empty-marker push (full formatting TODO)
- `sol_memcpy_`, `sol_memmove_` — actual byte copy in `Mem`
- `sol_memset_` — actual byte fill
- `sol_memcmp_` — byte-by-byte compare with i32 result written via `Memory.writeU32`
- `sol_set_return_data`, `sol_get_return_data` — round-trip through `state.returnData`
- `sol_get_stack_height` — returns 1 (top-level depth)
- `sol_get_clock_sysvar`, `sol_get_rent_sysvar`, `sol_get_epoch_schedule_sysvar`,
  `sol_get_last_restart_slot` — zero-fill the output buffer at `*r1`
  (real sysvar values aren't tracked; zero is the safe default)

**Verification — `Svm/SBPF/RunnerDemo.lean`** (separate target, not in
the production aggregator): 21 `native_decide`-proved end-to-end runs
including raw ALU, backward-jump loops, `lddw`, ELF round trip (`.text`
only and with `.rodata`), typed syscall dispatch with Murmur3 round
trip, memcpy / memset / memcmp byte-level verification, log content
inspection, return-data round trip, stack-height query, and
clock-sysvar zero-fill.

**What's shipped since the original Phase-G writeup (through 2026-05-14):**

- **Hash syscalls**: `sol_sha256` (pure-Lean FIPS-180-4, kernel-reducible),
  `sol_sha512` / `sol_keccak256` / `sol_blake3` (rust-bridge to the same
  crates agave uses — `sha2`, `sha3`, `blake3`). All four produce real
  digests via `readSlices` + `writeBytes` helpers in `Svm/SBPF/Machine.lean`.
- **Curve syscalls**: `sol_secp256k1_recover` (paritytech `libsecp256k1`),
  full `sol_curve_*` family for Curve25519 (validate / group_op / MSM),
  `sol_curve_decompress` + `sol_curve_pairing_map` for BLS12-381,
  `sol_alt_bn128_group_op` + `sol_alt_bn128_compression` for BN254.
- **`sol_big_mod_exp`** via `num-bigint::modpow` (matches agave's
  `solana-big-mod-exp`).
- **`sol_poseidon`** via `light-poseidon` + `ark-bn254`.
- **PDA derivation** (`sol_create_program_address`,
  `sol_try_find_program_address`): real implementation backed by the
  pure-Lean SHA-256, with on-curve rejection via Curve25519 validate.
- **R_BPF_64_32 relocations** applied at ELF load: writes
  `Murmur3-32(symbol_name)` into the instruction imm at `r_offset + 4`.
- **Per-syscall CU table** mirroring agave's
  `SVMTransactionExecutionCost::default()`. Variable-length syscalls
  read length args from `State.regs`. Cross-engine CU equality verified
  against mollusk on 5 fixtures.
- **Syscall colocation refactor**: every `Syscall` variant now dispatches
  to a per-module `exec` / `cu` defined next to its primitive.
  `Execute.lean` shrank from 1332 to 640 lines; `execSyscall` and
  `syscallCu` are pure 50-line dispatchers. New file
  `Svm/SBPF/Machine.lean` carries `State`, `RegFile`, `CallFrame`, and
  the shared body helpers; new directory `Svm/Syscalls/` hosts the
  previously-inline syscalls (logging, mem ops, sysvar, return data,
  abort, misc, CPI).

**What's left to call Phase G done-done:**

- **PT_LOAD program headers** ~~alternative section-free load path~~ —
  **dropped from roadmap.** Verified that agave's SBF loader requires
  section headers (mollusk rejects an ELF with `e_shoff=0` as
  `FailedToParse("invalid file header")`). PT_LOAD-only ELFs are not
  valid Solana programs in agave; no support is needed.
- **`@[implemented_by]` native compilation / Mem refactor**:
  `State.mem` is a functional `Nat → Nat` (`abbrev`), so each `writeU*`
  returns a fresh closure. After N writes the closure chain is N deep
  and each byte read walks the whole chain — `diff_mollusk` takes
  ~50 min, dominated by `encodeRun`'s FFI-return-path read loop.
  Throughput-only, not correctness; defer until dev-loop pain forces
  it. Full pickup-plan in [`docs/mem-refactor-plan.md`](docs/mem-refactor-plan.md)
  — diagnosis, the 2026-05-20 attempted fix that was rolled back, the
  ~25 InstructionSpecs proof failures it surfaced, the sequencing for
  the next dedicated session, and 1–2 day estimate.

**CPI status (2026-05-19)**: real CPI shipped through `executeFnCpiWithFuel`
in `Svm/SBPF/Runner.lean`. Verified by 12 `diff_mollusk` fixtures (9 prior
+ 3 new probers — depth-2 chain, returnData round-trip, PDA signer
promotion), all byte+CU-equal to mollusk. The dead `r0:=0` stub in
`Svm/Syscalls/Cpi.lean` is only reached by `executeFn` (the non-CPI
spec stepper); the production path goes through `executeFnCpi`.

**R_BPF_64_RELATIVE status (2026-05-19)**: shipped for `.text` (lddw
imm `+= MM_REGION_SIZE`) and `.data.rel.ro` (pointer-field shifts).
Verified by `rodata_addr_returner_matches_mollusk` (`.text` case) and
by SPL Token / ATA / Pinocchio fixtures passing (depend on
`.data.rel.ro` relocations). `.rodata`-content relocations are *not*
applied — toolchain output puts relocatable pointers in
`.data.rel.ro`, not `.rodata`, so the fast path is correct.

**Region bounds status (2026-05-19)**: shipped via `Memory.RegionTable`.
`step` consults it on `.ldx`/`.st`/`.stx` and routes misses to
`ERR_ACCESS_VIOLATION`. Verified by `oob_read_fails_on_both` (both
engines fault on OOR access).

**Per-byte hash CU status (2026-05-19)**: shipped via `hashSliceCost`
(`Machine.lean`), used by all four hash syscalls: `cu = 85 + Σ max(10,
len_i / 2)`. Matches agave's `mem_op_base_cost.max(sha256_byte_cost
.saturating_mul(len / 2))` per-slice formula.

**Estimate to "done-done"**: only PT_LOAD (small) for completeness;
native compile is throughput, not correctness. Pure-Lean kernel crypto
is Phase H follow-up, not on the production critical path.

### Phase H — Crypto syscalls

All 12 crypto syscalls ship via Rust FFI to the same crates agave uses (`sha2`, `sha3`, `blake3`, `libsecp256k1`, `curve25519-dalek`, `ark-bn254`, `light-poseidon`, `num-bigint`), with explicit trust statements per syscall. SHA-256 and Murmur3 are pure-Lean and kernel-reducible.

**Long-horizon followup (not production-critical):** pure-Lean ports of the remaining crypto primitives via fiat-crypto / verified-crypto-primitives. The Rust FFI bridge is the production path; pure-Lean ports tighten the TCB but aren't required to ship.

**Production status**: shipped.
