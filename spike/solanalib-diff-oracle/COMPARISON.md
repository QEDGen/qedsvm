# qedsvm vs solanalib: feature comparison

Local review doc. Compares **qedsvm** (this repo) against the Solana
Foundation's **[leanprover-solanalib](https://github.com/solana-foundation/leanprover-solanalib)**,
whose `SBPF/` layer is a Lean 4 port of the OOPSLA 2025 Isabelle/HOL sBPF
formalization. Grounded in a direct read of both codebases plus the differential
oracle run in this branch (`spike/solanalib-diff-oracle`).

## TL;DR

They are not the same kind of thing. solanalib is a young, Mathlib-backed
**library of reusable models and theorems** ("Mathlib for Solana") with a clean
CPU-level sBPF interpreter and a high-level DeFi-shape layer. qedsvm is a
**production verification engine**: it executes real `.so` programs, diff-tests
byte-for-byte against agave/mollusk, models the full syscall + CPI + PDA runtime,
and mechanically lifts bytecode to proofs.

- solanalib leads on: **v2 ISA coverage**, a proven **verifier safety theorem**,
  a reusable **high-level numeric/finance library**, Mathlib integration, and
  academic/standardization positioning.
- qedsvm leads on: **syscalls, CPI, PDA, native crypto**, **execution grounding**
  (real `.so`, agave/mollusk parity), the **lifting pipeline** (qedlift/qedgen),
  a **typed fault model**, and a closed **soundness audit**.
- The overlap (the instruction core) is **cross-validated**: 2394/2394 agreement,
  including the 32-bit sign-extension boundary (see this branch's README).

## Side-by-side

| Dimension | qedsvm | solanalib |
|---|---|---|
| **Purpose** | Production SVM verification engine: correctness + semantic baseline + execute compiled `.so` | Reusable Lean library of models + verified theorems ("Mathlib for Solana") |
| **Status** | Mature, soundness-audited, in active production use | Experimental prototype, exploring framework shape |
| **Backing** | This project | Solana Foundation |
| **Toolchain** | Lean 4.30, **Mathlib-free** by design (downstream consumers add Mathlib) | Lean 4.31, **requires Mathlib** (high-level layer); SBPF layer is Mathlib-free |
| **sBPF interpreter** | Total, executable (`executeFn` over `step`) | Total, executable (`bpfInterp` over `step`) |
| **State repr** | `Nat` registers + struct `State`, logical-PC-indexed | `BitVec` registers + `BpfState` inductive, slot-PC-indexed |
| **ISA versions** | v1 only | **v1 and v2** (`isV1` flag) |
| **ISA breadth** | Full base ALU/jump/mem/call/exit; no byteswap, no PQR, no hor64 | Base ALU + **byteswap (le/be)**, **PQR family**, **hor64**, addStk |
| **Decoder** | Two-pass, **folds agave verifier rejections** (fail-closed) | Single decode, verifier kept separate |
| **Verifier** | Rejections folded into decode + regression pins (M4Pin etc.) | **`step_ne_err` theorem** (Lemma 6.4: accepted insns never fault) via `Std.Tactic.BVDecide` |
| **Memory model** | Region table (stack/heap/input), access-violation traps, `serialize_parameters` layout, `Rc<RefCell>` AccountInfo parsing | Flat `Mem` + single program base (`0x100000000`), `ldx/st` bound-check to `.eflag` |
| **Compute units** | `cuConsumed/cuBudget`, **exact agave costs** (SIMD-0339: MSM 5325, CPI 946, ...) | `curCu/remainCu`, +1 per step (no syscall costs) |
| **Syscalls** | **~40 modeled**, many end-to-end (memops, logging, hashing, return data, sysvars, PDA) | **None** (host boundary not modeled) |
| **Native crypto** | **Rust bridge** pinning agave's exact crates (sha2/sha3/blake3/secp256k1/curve25519-dalek/...) | None |
| **CPI** | `sol_invoke_signed{,_c}`, sub-input marshaling, write-back, realloc, depth cap, privilege clamping | None |
| **PDA** | `sol_create_program_address` end-to-end, off-curve handling | None |
| **Fault model** | **Typed `VmError`** (12 variants) + agave sentinels + **M14 cross-engine `ProgramError` mapping** + `ExitOutcome` wire | Coarse: `.eflag` / `.err` / `.success` / `.ok` |
| **Execution grounding** | **Real `.so` exec**, `diff_mollusk` byte-identical incl. CU (41/41 fixtures) | None: diff vs a reference VM (`spinoza`) on random programs only |
| **Lifting / proof gen** | **qedlift** (bytecode → sorry-free refinement proofs) + **qedgen** (`.qedspec` → tests/proofs/CI), operational | **Aeneas** integration on the roadmap (source Rust → Lean), not yet present |
| **High-level domain lib** | None (specs are per-program, machine-generated) | **Primitives / Numeric / Account / Instruction / Finance** (Q68.60 fixed-point, decay/growth/compound interest/withdrawal-cap/AMM), 64+ theorems, Mathlib-backed |
| **Soundness posture** | Closed audit: axiom-audit gate, typed faults, `StateBounded` invariant, internal-call registry, dispatch completeness | Validated by differential testing + the `step_ne_err` safety theorem |
| **End-to-end refinement** | Bytecode → spec, proven on real p_token arms (`AsmRefinesToken*`) | Stated goal (bytecode → protocol invariant); high and low layers not yet bridged |

## Where the nuance matters

### Instruction core (the overlap)

Both are total, executable interpreters over the same base machine. solanalib is
broader at the raw-ISA level: it carries v2 (the `isV1` flag drives sub-imm
reversal, PQR availability, byteswap, hor64) where qedsvm models v1 only and
omits byteswap/PQR/hor64 entirely (it rejects them at decode). For the v1 ops
both model, they agree exactly: the differential oracle in this branch found
**0 divergences over 2394 register-only value comparisons**, including the
subtle case where `add32/sub32/mul32` sign-extend their 32-bit result while the
other 32-bit ops zero-extend. This is the strongest evidence in the comparison:
two independently authored Lean models, one diff-tested against agave and one
ported from the OOPSLA Isabelle spec, compute identical results.

### Verifier safety theorem (solanalib's clean win)

solanalib proves `step_ne_err`: a verifier-accepted instruction never faults at
runtime (their Lemma 6.4, discharged with the bit-vector decision procedure
`bvdecide`). qedsvm does not have this exact meta-theorem. It instead folds the
verifier's rejections into the decoder (fail-closed) and backs that with
regression pins and the mollusk diff. Different philosophy, and solanalib's is
the cleaner *stated property*. Worth noting their own `sbpf-oracle` bypasses the
verifier, which is why our `reject` outcomes line up against their executed
results in the edge corpus.

### The runtime boundary (qedsvm's decisive lead)

solanalib stops at the CPU. It has no syscalls, no CPI, no PDA, no host runtime,
no real crypto, and it never executes a deployed program. qedsvm models all of
that and validates it byte-for-byte against mollusk, including exact compute-unit
accounting. For anything involving a real Solana program (which is to say, every
real program: they all log, hash, derive PDAs, or CPI), solanalib's interpreter
cannot run it and qedsvm can. This is the gap that makes solanalib non-viable as
a drop-in and qedsvm non-trivial to replicate.

### High-level library (solanalib's genuinely additive layer)

solanalib's `Finance`/`Numeric` layer is the one part with no qedsvm counterpart:
reusable, Mathlib-backed verified primitives (fixed-point arithmetic with error
bounds, withdrawal-cap invariants, AMM constant-product, compound interest). Our
specs are per-program and machine-generated; we have no shared invariant
vocabulary. If qedgen ever needs a high-level *target* invariant for a DeFi lift,
this is ready-made. It sits near the parked "claim-first specs" workstream, off
the production critical path, but it is the clearest candidate for "additive."

### Lifting strategy (parallel, not competing yet)

Both aim at end-to-end refinement from bytecode to high-level properties. qedsvm
has it working bottom-up: qedlift mechanically emits sorry-free refinement proofs
from `.so` + IDL, and qedgen drives the spec/test/CI loop. solanalib plans to come
top-down via **Aeneas** (translate Rust source to Lean). Aeneas is the one
roadmap item that would become a *competing* front-end to qedlift rather than a
complement, so it is the thing to watch.

## Who leads, by area

- **solanalib ahead:** v2 ISA coverage; the `step_ne_err` verifier theorem;
  the high-level numeric/finance library; Mathlib ecosystem integration;
  academic grounding (OOPSLA 2025) and standardization positioning.
- **qedsvm ahead:** syscalls, CPI, PDA, native crypto; execution grounding
  (real `.so`, agave/mollusk byte parity, exact CU); the qedlift/qedgen lifting
  pipeline; the typed fault model + cross-engine error mapping; the closed
  soundness audit; proven refinement on real programs.
- **Cross-validated equal:** the v1 instruction core (2394/2394 agreement).

## Strategic notes

1. **Harvest the oracle, not the code.** solanalib's OOPSLA-derived `step` is a
   free, independent cross-check on our instruction semantics. Keep the
   differential oracle (this branch); it is the one piece that buys us something
   we do not already have.
2. **Do not adopt or depend on it.** As engine/infrastructure it is a strict
   subset of qedsvm and pulls Mathlib + a newer toolchain.
3. **Watch two roadmap items:** PDAs/sysvars (would shrink their runtime gap) and
   Aeneas (a competing source-level lifting path to qedlift).
4. **Consider naming alignment** only if "Mathlib for Solana" gains traction as a
   community standard; qedsvm would then sit as the execution + lifting engine
   beneath their high-level library.

## Provenance

- solanalib facts: direct read of `Oracle.lean`, `Solanalib/SBPF/{Interpreter,
  Decoder,State,Memory,Syntax,CommType}.lean`, `Verifier.lean`, `lakefile.lean`
  at `main` (cloned this session), plus building and running their `sbpf-oracle`.
- qedsvm facts: `SVM/SBPF/{Decode,ISA,Execute,Machine,Runner}.lean` and the
  project's soundness-audit history.
- Cross-validation numbers: the oracle run recorded in this branch's `README.md`.
