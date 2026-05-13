# formal-svm

A verified macro assembler for the Solana Virtual Machine, in Lean 4.

formal-svm is Lean's role compounded: **assembler**, **macro language**, **specification language**, and **proof assistant**, all at once. You write sBPF directly as Lean terms, specify what each instruction (and each macro built from instructions) does with a separation-logic Hoare triple, and Lean's kernel checks that the implementation meets the spec. Triples are bounded — every spec carries an explicit step count `N` that doubles as a verified compute-unit budget.

The methodology is borrowed wholesale from [Verified-zkEVM/evm-asm](https://github.com/Verified-zkEVM/evm-asm), which in turn descends from Kennedy/Benton/Jensen/Dagand, *"Coq: The world's best macro assembler?"* (PPDP 2013). They built a verified macro assembler for RV64IM and used it to implement EVM opcodes as RISC-V macros with machine-checked specs. We do the same thing for sBPF, targeting Solana programs.

## What it's for

Solana programs ship as sBPF bytecode produced by rustc → LLVM → sBPF. The compiler is in the trusted computing base of every program on mainnet. A bug in the toolchain — or a difference between what the developer reasoned about in Rust and what the bytecode actually does — silently undermines correctness even if the source code is right.

formal-svm explores an alternative path for programs where this matters: **write the sBPF directly in Lean, prove it correct, and ship the bytecode**. The rustc pipeline never enters the picture. For CPI patterns, ATA derivations, signature checks, and the small handful of operations that bear most of the value on Solana, that compiler-free path is a soundness floor that no amount of source-level review reaches.

The same semantics, run the other way, is a **reference interpreter**. Hand `Svm.SBPF.Runner.run` / `Runner.runElf` either an ELF64 binary or a raw `ByteArray` of sBPF bytes, with a `RunConfig` carrying input bytes (mapped to `INPUT_START`, `r1` set there) and a CU budget, and the kernel commits to the resulting `State` — final registers, memory, exit code, plus the observable `log` and `returnData` side channels populated by `sol_log_*` and `sol_set_return_data`. `.rodata` is loaded into `Mem` at its `sh_addr`, matching the universal pattern across Anchor / Pinocchio / native-Rust / Quasar binaries. `call <hash>` instructions resolve to typed `Syscall` variants via a pure-Lean Murmur3-32 implementation; memory syscalls (`sol_memcpy_` / `sol_memmove_` / `sol_memset_` / `sol_memcmp_`), log syscalls, return-data syscalls, stack-height, and sysvar getters all have real semantics. `Svm/SBPF/RunnerDemo.lean` (separate target, not in the aggregator) ships 21 `native_decide`-verified end-to-end runs covering every part of the pipeline.

Two concrete payoffs from bounded triples:

1. **Verified compute-unit budgets.** Every macro carries an upper bound `N` on the steps it executes. Compose macros and the bounds add. You can prove a whole program fits inside a CU budget without running it.
2. **zk-SVM cycle budgets.** When the same code targets a zkVM, `N` is the worst-case cycle cap per proof.

## Status

**Experimental research prototype. Do not ship anything written with this against mainnet value yet.**

- The sBPF ISA semantics in `Svm/SBPF/Execute.lean` are hand-written and have *not* been differential-tested against Agave's `solana-sbpf` or Firedancer's VM. Closing that gap (Phase F) is the load-bearing soundness question.
- `Svm/Account.lean` is `axiom`-free (Phase 0 / v0.2.0). `Svm/SBPF/Memory.lean` still has 13 read/write coherence axioms on the flat `Mem` model; these become unnecessary in the new byte-level separation-logic memory and are slated for removal as Phase A lands.
- The separation-logic + bounded-triple layer (this repo's current focus) is being built in v0.3.x. The first per-instruction Hoare triple (`mov64_imm_spec` in `Svm/SBPF/InstructionSpecs.lean`) is in.

## Layout

```
Svm.lean                  — package root
Svm/
├── Account.lean          — Pubkey (4-chunk LE U64), Account, findBy{Key,Authority}
├── Cpi.lean              — CpiInstruction envelope, program-ID registry, SPL/System/ATA discriminators
├── SBPF.lean             — sBPF kernel aggregator
└── SBPF/
    ├── ISA.lean          — instruction encoding and opcode set
    ├── Memory.lean       — byte-addressable Mem, region layout
    ├── Region.lean       — region IDs (rodata/bytecode/stack/heap/input)
    ├── Pubkey.lean       — sBPF-level pubkey reads
    ├── Execute.lean      — RegFile, machine State, step, executeFn (operational semantics)
    ├── SepLogic.lean     — PartialState, separation logic, points-to predicates  (v0.3)
    ├── CPSSpec.lean      — bounded Hoare triple `cuTripleWithin`, frame, seq, weaken  (v0.3)
    ├── InstructionSpecs.lean — per-instruction triples (CU = 1 each) + 1-reg-write helper  (v0.3+)
    ├── MacroDemo.lean    — verified two-instruction macros  (v0.3)
    ├── Decode.lean       — sBPF bytecode parser (two-pass; correct lddw + jump interaction)  (v0.3)
    ├── Murmur3.lean      — pure-Lean Murmur3-32 (used for syscall hash dispatch)  (v0.3)
    ├── SyscallHash.lean  — name → hash → typed Syscall for all 25 known syscalls  (v0.3)
    ├── Elf.lean          — ELF64 loader (header, section table, .text + .rodata extraction)  (v0.3)
    ├── Runner.lean       — production entrypoint: Runner.run / Runner.runElf with RunConfig  (v0.3)
    ├── RunnerDemo.lean   — 21 native_decide-verified end-to-end demos (raw bytecode, ELFs with .rodata, typed syscall dispatch, memory ops, log content, return data, sysvars) — kept out of the aggregator  (v0.3)
    ├── Patterns.lean     — concrete-fetch composition lemmas (predecessor to the macro library)
    ├── Tactic.lean       — misc tactics
    └── WPTactic.lean     — wp_exec weakest-precondition tactic (legacy, for concrete programs)
```

## Lean as four things at once

```lean
-- 1. Assembler: instructions are inductive terms
def my_macro (dst src : Reg) : List Insn := [.mov64 dst (.reg src), .exit]

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

## Use it

```lean
require formalSvm from git
  "https://github.com/QEDGen/formal-svm.git" @ "main"
```

Then `import Svm` (or import selectively).

Standalone build: `lake build`. Lean toolchain pin: `lean-toolchain`.

**Build prerequisites:** Lean (per `lean-toolchain`, fetched by `elan`)
and `cargo` / `rustc` (any stable toolchain). The Rust bridge in
`rust-bridge/` pulls the exact crates agave's runtime uses
(`libsecp256k1 = "0.7.2"` paritytech, `curve25519-dalek = "4.1.3"`,
`sha2`, `sha3`, `blake3`) and exposes each crypto syscall to Lean
via its `@[extern "lean_*"]` declaration directly — no intermediate
C shim layer. (A tiny `rust-bridge/lean_glue.c` re-exports six
`static inline` Lean runtime helpers so Rust can call them at the
FFI boundary; that's the only C in the project.) Lake invokes
`cargo build --release` automatically during `lake build`. No system
crypto libraries required.

## Roadmap (re-scoped for v0.3+)

See `ROADMAP.md`. Headline phases:

- **A — Foundations**: SepLogic, bounded triples, first instruction specs *(in progress)*
- **B — Full ISA coverage**: one Hoare-triple spec per `Insn` constructor
- **C — Tactic suite**: composition automation (`runBlock`, frame inference, etc.)
- **D — Macro library**: memory ops, stack frames, control flow, CPI envelopes as verified sBPF macros
- **E — Solana program library**: System program ops, SPL Token transfers, ATA derive, common CPI patterns — each a verified macro with proven CU bound
- **F — Differential testing**: oracle alignment against `solana-sbpf` / Firedancer
- **G — ELF loader + execution**: load real Solana programs and run them under the Lean semantics
- **H — Crypto syscalls + zkSVM target**

The phases preceding v0.3 — Phase 0 (axiom cleanup) and the original Phase 1 (CPI small-step semantics) — have been folded into this structure. The CPI envelope work is now Phase D/E; the executable semantics underpinning everything is Phase G's responsibility.

## Origin

This repo was extracted on 2026-05-12 from [QEDGen/solana-skills](https://github.com/QEDGen/solana-skills), which used it as the runtime model for spec-driven verification of Solana programs. The split gives the SVM model its own life as an ecosystem artifact.

The v0.3 re-scope to a verified macro assembler tracks the methodology of [Verified-zkEVM/evm-asm](https://github.com/Verified-zkEVM/evm-asm) — read their README and the PPDP 2013 paper if you want the methodology in its original form.

## License

MIT. See `LICENSE`.

## Contributing

Issues and PRs welcome. The roadmap describes the planned phases; out-of-roadmap contributions need a short rationale before they land. The bar is small trust base and honest specs — additions that broaden the surface without a clear soundness story will get pushback.
