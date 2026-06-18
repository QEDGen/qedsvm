# qedsvm vs solanalib

A review of **qedsvm** (this repo) against the Solana Foundation's
**[leanprover-solanalib](https://github.com/solana-foundation/leanprover-solanalib)**,
whose `SBPF/` layer is a Lean 4 port of the OOPSLA 2025 Isabelle/HOL sBPF
formalization.

Every claim here was checked against source this session (file:line evidence,
not memory or READMEs), and the differential oracle in this branch was rebuilt
and re-run. The vendored solanalib copy is spike-modified (Mathlib stripped so
its `sbpf-oracle` builds Mathlib-free); upstream-vs-spike differences are noted
where they matter. Provenance is at the end.

## TL;DR

Today they are not the same kind of thing. solanalib is a young **library of
models and theorems** ("Mathlib for Solana"): a clean CPU-level sBPF interpreter,
a partial verifier with one safety theorem, and a high-level numeric/finance
layer. qedsvm is a **production verification engine**: it executes real `.so`
programs, diff-tests them byte-for-byte against agave/mollusk, models the full
syscall + CPI + PDA runtime, and mechanically lifts bytecode to sorry-free
refinement proofs.

Their stated end goal is the same north star (deployed bytecode, up to a proven
high-level invariant), so the live question is not "do they overlap" but "will
the artifacts converge." That is treated in *Same goal, or not?* below.

- solanalib leads on: **v2 ISA coverage**, a clean (if narrow) **verifier safety
  theorem**, a **high-level invariant library**, and academic/standardization
  positioning.
- qedsvm leads on: **syscalls, CPI, PDA, native crypto**, **execution grounding**
  (real `.so`, agave/mollusk byte + CU parity), the **lifting pipeline**, a
  **typed fault model**, and a closed **soundness audit**.
- Cross-validated equal: the **v1 instruction core**, 0 divergences across 3000
  register-only vectors (reproduced this session).

## Side-by-side

| Dimension | qedsvm | solanalib |
|---|---|---|
| **Purpose** | Production SVM verification engine: correctness + semantic baseline + execute compiled `.so` | Reusable Lean library of models + verified theorems ("Mathlib for Solana") |
| **Status** | Mature, soundness-audited, in production use | Experimental prototype, exploring framework shape |
| **Backing** | This project | Solana Foundation |
| **Toolchain** | Lean 4.30, **Mathlib-free** by design | Lean 4.31; **requires Mathlib** (for style linters only); SBPF layer Mathlib-free |
| **sBPF interpreter** | Total, executable (`executeFn` over `step`) | Total, executable (`bpfInterp` over `step`) |
| **State repr** | `Nat` registers + struct `State`, logical-PC-indexed | `BitVec` registers + `BpfState` inductive, slot-PC-indexed |
| **ISA versions** | v1 only | **v1 and v2** (`SBPFV`/`isV1` flag) |
| **ISA breadth** | Base ALU/jump/mem/call/exit; no byteswap, PQR, hor64 (rejected at decode) | Base ALU + **byteswap (le/be)**, **PQR family**, **hor64**, addStk |
| **Decoder** | Two-pass, **folds agave verifier rejections** (fail-closed) | Single decode; verifier kept separate |
| **Verifier** | Rejections folded into decode + regression pins | **`step_ne_err`** (Lemma 6.4) via `bv_decide`: accepted insn never reaches the malformed `.err` state (NOT runtime `.eflag` freedom; modeled verifier is partial) |
| **Memory model** | Region table (stack/heap/input), access-violation traps, `serialize_parameters` layout, `Rc<RefCell>` AccountInfo parsing | Partial map `Mem : U64 → Option U8` (region bases stack `0x200000000`/input `0x400000000`; `0x100000000` is the program VM addr, not a mem base); `ldx/st` fault implicitly (unmapped → `.eflag`) |
| **Compute units** | `cuConsumed/cuBudget`, **exact agave costs** (CPI invoke 946 = `INVOKE_UNITS_COST_SIMD_0339`; MSM formula `2273+(n−1)·758` edwards / `2303+(n−1)·788` ristretto, asserted vs mollusk) | `curCu/remainCu`, +1 per step (no syscall costs) |
| **Syscalls** | **42 modeled** (+ `unknown` catch-all); memops, logging, sha256, return-data, PDA wired end-to-end with generated lifts (sysvars diff-tested + spec'd) | **None** (host boundary not modeled) |
| **Native crypto** | **Rust bridge** pinning agave's exact crates (sha2/sha3/blake3/curve25519-dalek/secp256k1/bn254/...); sha256 also has a pure-Lean path | None |
| **CPI** | `sol_invoke_signed{,_c}`, marshaling, write-back, realloc, depth cap, privilege clamping (executable Runner path) | None |
| **PDA** | `sol_create_program_address` end-to-end; off-curve as a surfaced hypothesis | None |
| **Fault model** | **Typed `VmError`** (12 variants) + `State.vmError` + agave sentinels + **M14 cross-engine `ProgramError` mapping** + `ExitOutcome::Faulted` wire | Coarse: `.ok` / `.success` / `.eflag` / `.err` |
| **Execution grounding** | **Real `.so` exec**, `diff_mollusk` byte-identical incl. CU (62 fixtures) | None: differential testing vs an external reference VM (`spinoza`) on random programs |
| **Lifting / proof gen** | **qedlift** (bytecode → sorry-free refinement proofs) + **qedgen** (`.qedspec` → tests/proofs/CI, separate repo), operational | **Aeneas** (Rust source → Lean) on the roadmap, not present |
| **High-level domain lib** | None (specs are per-program, machine-generated) | **Primitives / Numeric / Account / Instruction / Finance**: ~68 declarations, ~20 substantive (see soundness section); AMM is roadmap, not built |
| **Soundness posture** | Closed audit: axiom-audit gate, typed faults, `StateBounded` invariant, internal-call registry, dispatch completeness | Sorry/axiom-free; validated by differential testing + the (narrow) `step_ne_err` theorem |
| **End-to-end refinement** | Bytecode → spec, proven on real p_token arms (`AsmRefinesToken*`) | Stated goal; high and low layers not yet bridged |

## The overlap: cross-validated instruction semantics

Both are total, executable interpreters over the same base machine, and on the
instructions both model they agree exactly. The differential oracle in this
branch speaks solanalib's `sbpf-oracle` text contract from both sides and diffs
the observable result. Reproduced this session:

- **3000 v1 register-only vectors: 0 divergences** (2394 agree on an exact
  returned `r0`, 606 agree on faulting).
- 12 "sharp" probes targeting the 32-bit sign-extension boundary
  (`add32/sub32/mul32` sign-extend their result; other 32-bit ops zero-extend):
  all agree.
- 7 "edge" probes: 5 are qedsvm-stricter (it rejects at decode where solanalib
  executes), 1 agree-not-ok, 1 agree-fault.

This is the strongest single piece of evidence in the comparison: two
independently authored Lean models, one diff-tested against agave and one ported
from the OOPSLA Isabelle spec, compute identical results. Precise scope: it
compares only the observable outcome (`r0`, or fault-vs-clean-exit) from a zeroed
state. It does not diff the full register file, memory, PC, or CU; it is v1-only;
and the verifier is bypassed on both sides. It is Lean-vs-Lean cross-validation,
not agave grounding, which lives elsewhere in qedsvm.

## Where they diverge

### The runtime boundary (qedsvm's decisive lead)

solanalib stops at the CPU. It has no syscalls, no CPI, no PDA, no host runtime,
no real crypto, and it never executes a deployed program. qedsvm models all of
that and validates it byte-for-byte against mollusk, including exact compute-unit
accounting. Every real Solana program logs, hashes, derives PDAs, or invokes
other programs, so solanalib's interpreter cannot run any of them and qedsvm can.
This is the gap that makes solanalib non-viable as a drop-in and qedsvm
non-trivial to replicate.

One honest scoping caveat on the qedsvm side: CPI is fully modeled and
diff-tested on the executable Runner path, but the proof-side syscall
(`Cpi.exec`) fails closed, so the Hoare-spec layer does not yet prove CPI callee
bodies.

### The verifier safety theorem (solanalib's, read precisely)

solanalib proves `step_ne_err` (their Lemma 6.4, discharged with the bit-vector
decision procedure `bv_decide`). Read it precisely: it proves a verifier-accepted
instruction never reaches the *malformed* `.err` state. It does not prove freedom
from runtime `.eflag` faults (OOB memory, fuel exhaustion), and the verifier it
models is deliberately partial (it omits byte-level checks like `check_load_dw`).
So it is a real, clean meta-theorem, but narrower than "accepted instructions
never fault."

qedsvm has no analogue. Its closest is `step_bounded`/`executeFn_bounded` (the
`StateBounded` invariant), which proves boundedness, not fault-freedom. qedsvm
instead folds the verifier's rejections into the decoder (fail-closed) and backs
that with regression pins and the mollusk diff. Different philosophy; solanalib's
is the cleaner *stated property*, within its scope.

### The high-level invariant library (solanalib's genuinely additive layer)

solanalib's `Numeric`/`Account`/`Finance` layer is the one part with no qedsvm
counterpart: reusable verified primitives over hand-authored models. qedsvm has
no shared invariant vocabulary; its specs are per-program and machine-generated.
If a qedgen DeFi lift ever needs a high-level *target* invariant, this is the
clearest "additive" candidate. How strong it actually is gets its own section
below, because the answer is more nuanced than the marketing.

## Same goal, or not? (the convergence question)

It is fair to ask whether solanalib is just building qedsvm from the other end.
The honest answer: the *ambitions* converge, the *artifacts* do not yet, and
solanalib's own goal is ambiguous between two readings that resolve the question
in opposite directions.

- **Reading A, a substrate ("Mathlib for Solana").** A reusable library of models
  and verified theorems that other tools build on. Under this reading solanalib is
  not doing what qedsvm does; it is the layer a lifting engine sits beneath or
  consumes. Complementary, not competing. Most of what they have actually *built*
  (the numeric/finance library, the verifier theorem, the clean CPU model) fits
  here.
- **Reading B, a full-stack verifier.** Bytecode (or Rust via Aeneas) up to a
  proven protocol invariant, with their own runtime. Under this reading they are
  building qedsvm top-down where qedsvm built it bottom-up. The roadmap signals
  (Aeneas, "bytecode to invariant" as a stated goal) point here, but the runtime
  needed to make it real does not exist.

solanalib has not visibly committed to A or B, and that ambiguity is the real
status: it gestures at qedsvm's goal while having built the substrate, not the
verifier.

**Opposite ends of one claim.** The claim "bytecode → high-level invariant" is a
vertical span with two endpoints. qedsvm built bottom-up and owns the bottom
(real `.so`, faithful runtime, chain grounding) plus the connecting span (the
lift); its weak point is the *top* (its proofs land on machine-generated specs,
not human-meaningful invariants). solanalib built top-down and owns the top (a
high-level invariant vocabulary); it is missing the entire bottom and span (no
loader, no runtime, no lift, no bridge, no grounding). They are ahead on the
endpoint the other lacks.

**Two differences are durable even if both reach end-to-end refinement:**

1. **What the guarantee is grounded in.** qedsvm proves "correct as agave/mollusk
   actually behaves, byte-for-byte." solanalib proves "correct per the model,
   validated against the OOPSLA spec and a reference VM." Even when both conclude
   "bytecode refines invariant," those are not the same theorem for a
   mainnet-deployment decision.
2. **Per-program generated specs vs a shared invariant theory.** qedsvm's specs
   are per-program and machine-emitted; the shared invariant vocabulary is parked
   (the "claim-first specs" workstream). solanalib's value proposition *is* that
   shared library. At convergence you would still get two different products.

**The asymmetry that decides "who is closer."** qedsvm has already done the
expensive, unglamorous part: the runtime (syscalls, CPI, PDA, native crypto, real
`.so` execution, exact CU), and it has traversed the full arrow on real p_token
bytecode. Its remaining work is raising the *altitude* of the proven property, an
extension of a working pipeline. solanalib's remaining work is building the entire
pipeline below its invariants. Having the destination without a road to it is much
further from the claim than having the whole road proven to a modest destination.
qedsvm is substantially closer.

The one signal that flips this: **do they start modeling the host runtime?** The
moment solanalib adds syscalls/CPI, Reading A is turning into Reading B. Aeneas is
the secondary watch item. Until the runtime exists, the convergence is ambition,
not capability.

## How sound are solanalib's high-level invariants?

A statement-level review of every theorem in the `Numeric`/`Account`/`Finance`
layer (judging the statements and the definitions they quantify over, given the
proofs are already known sorry/axiom-free). Three senses of "sound" split apart:

1. **Proofs valid:** yes (sorry-free, admit-free, axiom-free; conservative
   tactics `omega`/`simp`/`decide`; no `native_decide`).
2. **Statements non-vacuous and honestly scoped:** yes, and this is the genuinely
   good finding. Across ~53 reviewed theorems, **0 vacuity-risk**: no unsatisfiable
   hypotheses, no degenerate-only (n=0/empty/zero-rate) results, no "≥ 0 for a
   `Nat`" fake bounds. Where a property is only locally true, it is correctly
   restricted in the statement rather than over-claimed.
3. **Statements as strong as their labels:** no. The theorems are true but
   systematically narrower than the prose around them.

**Claimed vs actually proven:**

| Headline | What is actually proven | Gap |
|---|---|---|
| "Fixed-point arithmetic **with error bounds**" | `Fraction` is an **unbounded `Nat`** wrapper. `mul`/`div` truncate, but the only theorems touching them (`mul_one`, `div_one`) live in the exact/divisible case. | **No error bound exists.** The ULP/associativity bound is explicitly deferred. Truncation, the whole point of fixed-point, is unconstrained. No overflow/u128 model. |
| "Withdrawal **cap / rate limit**" | `tryAdd_preserves_invariant`: each step preserves `current ≤ capacity` with a real no-wrap argument; reset-on-window; rejection completeness. | **Fixed-window, not sliding.** No cross-window cumulative theorem; draining `capacity` just before and after a reset is permitted and unaddressed. |
| "**Compound interest**" | `balance_monotone`: multi-step monotone growth through truncating division; `balance_ge_principal`. | **Direction only, no magnitude.** No closed-form `(1+r)^n` correctness (deferred). Arbitrary truncated factors satisfy every theorem. |
| "Decay / growth curves" | `value_le_peak`, `value_antitone_in_window` are genuinely substantive (all-inputs bound, honest in-window monotonicity). | The `Decay`/`Growth`/`MonotoneSequence` theorems are deliberate trivial projections of structure-field hypotheses; strength lives in the constructors. |

**The count reality.** Of ~68 headline declarations, the substantive set is **~20**
(≈8 in Numeric/Account, ≈12 in Finance). The rest are `@[simp]` field accessors,
order laws inherited verbatim from `Nat` (`le_trans`, `add_comm`, ...), and
one-line echoes of structure-field hypotheses (`MonotoneSequence.apply_le_of_le`
is literally `s.monotone h`). The "60+ verified theorems" framing overstates the
substantive invariant count by roughly 3x.

**The genuinely strong ones** (would catch real bug classes: wrap, off-by-one,
reset-forgetting, non-monotonicity):

- `transfer_preserves_total` (`Account/Transfer.lean`): true two-account lamport
  conservation, stated in `Nat`, with load-bearing no-underflow/no-overflow
  hypotheses. The strongest result in the set.
- `credit_lamports_toNat` / `debit_lamports_toNat` (`Account/Basic.lean`): the
  `checked_add`/`checked_sub` claim, u64 arithmetic equals `Nat` under no-wrap.
- `tryAdd_preserves_invariant` (`Finance/WithdrawalCap.lean`) and
  `balance_monotone` (`Finance/CompoundInterest.lean`).

**Verdict.** Sound the way a careful, honest set of building-block lemmas about a
simplified spec model is sound. The risk here is not false theorems or vacuity
(there is none); it is *over-trust from the labels*. A reader who sees "fixed-point
with error bounds," "rate limit," and "compound interest" and assumes the strong
guarantee would be wrong on all three. The proven content is per-step / per-window
/ direction-only, over an unbounded-`Nat` / `UInt64` model that is itself
disconnected from the chain (the grounding gap applies even to the substantive
ones: `transfer_preserves_total` ignores rent, fees, and the system program). Clean
and trustworthy as a foundation; not yet shipped protocol guarantees, and the prose
oversells where the proofs land.

## Who leads, by area

- **solanalib ahead:** v2 ISA coverage; the `step_ne_err` verifier theorem (within
  its scope); the high-level invariant library; academic grounding (OOPSLA 2025)
  and standardization positioning.
- **qedsvm ahead:** syscalls, CPI, PDA, native crypto; execution grounding (real
  `.so`, agave/mollusk byte + CU parity); the qedlift/qedgen lifting pipeline; the
  typed fault model + cross-engine error mapping; the closed soundness audit;
  proven refinement on real programs.
- **Cross-validated equal:** the v1 instruction core (0 divergences across 3000
  register-only vectors).

## Strategic notes

1. **Harvest the oracle, not the code.** solanalib's OOPSLA-derived `step` is a
   free, independent cross-check on our instruction semantics. Keep the
   differential oracle in this branch; it is the one piece that buys us something
   we do not already have.
2. **Do not adopt or depend on it.** As engine/infrastructure it is a strict
   subset of qedsvm and pulls Mathlib + a newer toolchain.
3. **The one signal that matters: do they start modeling the host runtime?** The
   moment solanalib adds syscalls/CPI, "Mathlib for Solana" (Reading A) is turning
   into "we are building qedsvm too" (Reading B). PDAs/sysvars would be the first
   concrete sign; Aeneas is the secondary watch item.
4. **Consider naming alignment** only if "Mathlib for Solana" gains traction as a
   community standard; qedsvm would then sit as the execution + lifting engine
   beneath their high-level library, with our refinements eventually targeting
   their (hardened) invariants.

## Provenance

Every claim was re-audited against source this session, with file:line evidence;
the statement-level soundness review read the high-level layer in full.

- solanalib facts: direct read of `Oracle.lean`, `Verifier.lean`, `lakefile.lean`,
  `lean-toolchain`, and `Solanalib/{SBPF/*,Primitives,Numeric,Account,Instruction,
  Finance}/*.lean` in the vendored copy (spike-modified, Mathlib stripped;
  upstream-vs-spike differences called out where they matter).
- qedsvm facts: `SVM/SBPF/{Decode,ISA,Execute,Machine,Bounded,Runner}.lean`,
  `SVM/Syscalls/*` and `SVM/SBPF/InstructionSpecs/*`, `qedsvm-rs/` (`lean-bridge`,
  `diff_mollusk.rs`, `serialize.rs`), and `examples/lean/` generated lifts.
- Cross-validation: rebuilt and re-ran both oracle binaries; reproduced core 2394
  AGREE-OK / 606 AGREE-FAULT / 0 divergences over 3000 vectors, sharp 12 AGREE-OK,
  edge 5 STRICTER + 1 AGREE-NOTOK + 1 AGREE-FAULT.
