# formal-svm Roadmap

The path from operational sBPF semantics to a usable verified macro assembler.

The v0.3 re-scope replaces the earlier phase plan (Phase 0 axiom cleanup → Phase 1 CPI small-step → ... → Phase 6 crypto) with a methodology lifted from [Verified-zkEVM/evm-asm](https://github.com/Verified-zkEVM/evm-asm): separation logic over machine state, bounded Hoare triples, per-instruction specs, then macros built and verified compositionally on top. The original CPI work isn't dropped — it reappears as Phase D/E (CPI envelope and per-program effects, written as verified sBPF macros).

## Shipped

### v0.2.0 — Phase 0: Axiom cleanup (partial) ✅

Removed the five `axiom` declarations in `Svm/Account.lean` (list-update lemmas, now real theorems in core Lean). The 13 read/write-coherence axioms in `Svm/SBPF/Memory.lean` were left as a follow-up — they don't disappear with `simp` lemmas on the flat `Mem` model, but they're naturally eliminated by the byte-level separation-logic memory introduced in Phase A. After Phase A, the macro library uses byte-level `↦ₘ` predicates, the flat `Mem` axioms drop out, and the trust base is the hand-written ISA semantics + crypto primitives only.

## Current track: v0.3.x — Verified macro assembler

### Phase A — Foundations *(in progress)*

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

### Phase F — Differential testing *(infrastructure shipped; coverage scaling)*

Extract the sBPF semantics (`Svm.SBPF.Execute`) to executable Lean / native and oracle-align against:
- Firedancer's `vm-fuzz` corpus
- Agave's `solana-sbpf` test suite
- A curated mainnet program corpus

Every disagreement is either a bug in our semantics or evidence of cross-client divergence worth surfacing. This is the empirical answer to the "is the hand-written ISA correct" question — until it passes, every Phase-E spec inherits this uncertainty.

**What's shipped (2026-05-13):**
- `formal-svm-rs/` Rust crate exposes the Lean runner via a Mollusk-shaped API (`Svm::process_instruction(&ix, &accounts) -> InstructionResult`). Same types as published agave-master pins (`solana-pubkey`, `solana-instruction`, `solana-account`), so Mollusk tests can swap engines by changing one type name.
- Agave-conformant input-buffer serializer with round-trip test against `solana_program_entrypoint::deserialize`, plus byte-level known-offset checks.
- CU accounting that matches agave's reported count (verified against `mollusk_svm::Mollusk` on a real `cargo-build-sbf` noop).
- Thread-safe Lean runtime access (process-wide `Mutex`, stress-tested at 8 threads × 50 iters × varied input sizes).
- `tests/diff_mollusk.rs` (gated `--features diff-mollusk`): runs the same `Instruction` through `formal_svm::Svm` and `mollusk_svm::Mollusk`, asserting equality on `program_result`, `return_data`, `resulting_accounts`, `compute_units_consumed`.

**What's left:**
- ELF + decoder coverage for the full sBPF feature set used by `cargo-build-sbf`-produced programs (`R_BPF_64_RELATIVE` relocations; the syscalls real programs actually invoke). Today's smallest real fixture is a hand-written `extern "C" fn entrypoint(_:*mut u8) -> u64 { 0 }`, which emits exactly `mov64 r0, 0; exit` — the only `cargo-build-sbf` output formal-svm parses end-to-end.
- Fuzz/sweep harness over generated `Vec<Insn>` programs to drive both engines on randomized inputs (the diff plumbing is in place; just needs a generator).
- Firedancer comparison (separate language, separate harness — deferred until agave-side diff is on a richer fixture corpus).

**Remaining estimate**: 2–4 weeks for ELF/decoder coverage of common cargo-build-sbf output; the diff harness is the easy part.

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

**What's left to call Phase G done-done** (each is scope-bounded):

- **CPI** (`sol_invoke_signed_c`, `sol_invoke_signed_rust`): defaults to
  `r0 := 0` (success but no actual cross-call). Real semantics needs a
  program registry, instruction-context construction, and recursive
  `executeFn` invocation — this overlaps Phase D/E (Solana program
  library) and is best landed there.
- **PDA derivation** (`sol_create_program_address`,
  `sol_try_find_program_address`): defaults to `r0 := 0`. Needs real
  SHA-256 to compute the program address.
- **Crypto syscalls** (`sol_sha256`, `sol_keccak256`, `sol_blake3`,
  `sol_secp256k1_recover`): defaults to `r0 := 0`. Each needs a
  verified-correct implementation of the underlying primitive — a
  separate, substantial project (Phase H).
- **Relocations** (R_BPF_64_32, R_BPF_64_64): not applied. Pinocchio is
  largely relocation-free; Anchor / native-Rust binaries depend on them
  for absolute-address lookups into `.rodata`. Implement as a separate
  pass between ELF parse and decode.
- **`.bss` mapping**: not blocking — our default `Mem` returns 0 for
  un-overlaid addresses, which matches `.bss` semantics. Adding
  explicit handling is cosmetic for future memory representations.
- **PT_LOAD program headers**: alternative section-free load path used
  by some stripped ELFs.
- **`@[implemented_by]` native compilation**: `executeFn` runs through
  Lean's kernel for `native_decide`; for real CLI throughput, wire the
  hot functions to compiled C/Rust implementations.

**Estimate to "done-done"**: ~4 weeks of focused work for relocations +
PT_LOAD + CPI stub-with-recursion + native compile hookups. Real
crypto (Phase H) is its own multi-month project.

### Phase H — Crypto syscalls + zkSVM target

- Crypto syscalls (Ed25519, secp256k1 recovery, sha2/sha3, alt_bn128). Likely path: Lean port of fiat-crypto / verified-crypto-primitives. Until shipped, these remain axiomatized with explicit trust statements.
- Compile the macro library to a zkVM target (RISC-V-of-zk choice TBD). The same CU bound from each Hoare triple becomes the per-proof cycle budget.

**Estimate**: substantial. Crypto alone is its own project. zkSVM is a long horizon.

## What is *not* on the roadmap

**F2 — verified extractable runtime.** A Lean implementation that replaces `solana-program-runtime` end-to-end (validator-grade) is a multi-year, multi-team effort. Phases A–H build the substrate it would start from, but shipping the runtime itself is out of scope.

**Solana-side state.** Bank, slot lifecycle, account commits, consensus, gossip, leader schedule, vote processing. All out of scope. This repo is the *program execution* layer of the SVM, not the validator.

**A new verification tool.** This is the model + the assembler + the macro library. Tools that use it — QEDGen and others — live elsewhere.
