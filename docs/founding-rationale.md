# Verified SVM in Lean — Spike

Date: 2026-05-12
Status: design spike, not committed

## The question

Hirai's "final form" post argues that AI-driven asm + Lean is the endgame for verified software. The natural follow-on for QEDGen is: **what would a Lean model of the SVM look like, and what does it buy us?**

We already ship `lean_solana/` — a partial model — but it lives as a mix of executable definitions, theorems, and axioms. The spike here is to map the design space, the costs, and the benefits *concretely against QEDGen's current trust base*, not against an aspirational "verified Solana" hand-wave.

## Three flavors

The phrase "verified SVM in Lean" collapses three quite different proposals. Costs and benefits differ by ~order of magnitude across them.

### F1 — Reference SVM semantics

A Lean model that **is the spec**: a formal, executable description of how an SVM runtime *should* behave. User programs are verified against this model; Agave/Firedancer remain the production implementations, but they're now answerable to a written-down semantics.

This is the Sail-RISC-V analog for Solana. The CompCert analog of the *source language*, not of the compiler.

- **Cost**: person-quarters to person-years, scoped iteratively.
- **What it replaces**: the implicit "Agave behavior" that QEDGen proofs currently trust as the operational floor.
- **Who consumes it**: QEDGen proofs, third-party auditors, Firedancer/Agave conformance teams, future zk-SVM circuit authors.

### F2 — Verified extractable SVM implementation

A Lean implementation of the SVM that **extracts to executable code**. The CompCert analog of the *compiler itself*. Eventually replaces (or runs alongside) Agave's `solana_program_runtime` for use cases that need a small, audited TCB — most concretely, the guest side of a zk-SVM.

- **Cost**: many person-years. seL4 (8.7k LOC C kernel) was 25 person-years. Agave's `solana_program_runtime` + `solana_sbpf` is ~35k LOC of Rust before counting loader, syscalls, and crypto.
- **What it replaces**: rustc + Agave runtime in the trust base, *if* anyone actually runs the extracted code in production.
- **Who consumes it**: a zk-SVM project, eventually. Not QEDGen users directly.

### F3 — Validated sBPF kernel only

Tighten and validate what we already have. Audit `lean_solana/` end-to-end: kill the axioms that are actually theorems, document the axioms that aren't, validate the sBPF ISA model against Firedancer's vm-fuzz corpus, and call that the deliverable.

- **Cost**: weeks.
- **What it replaces**: nothing in the trust base — it *confirms* that the existing axioms are sound.
- **Who consumes it**: QEDGen users get a hardened trust statement; no new capability.

The recommendation at the end of this doc lands on **F1 + F3, sequenced, with F2 explicitly out of scope**.

## Current state: what `lean_solana/` actually covers

Surveyed 2026-05-12:

| Module | LOC | Content | Status |
|---|---|---|---|
| `Account.lean` | 138 | `Pubkey` (4-chunk U64), `Account` struct, `canWrite`, `findByKey`/`findByAuthority`, **4 axioms** for list-update lemmas | Mixed: structs are concrete, list lemmas labeled "axiom for now" but are provable |
| `Cpi.lean` | 217 | `AccountMeta`, `CpiInstruction` envelope, well-known program IDs, SPL/System/ATA discriminators, `targetsProgram`/`accountAt`/`hasDiscriminator` predicates | Envelope-only: no execution semantics |
| `State.lean` | 64 | `Lifecycle` (open/closed), irreversibility theorems | Concrete, fully proven |
| `Valid.lean` | 54 | U8..U128 bound constants, `valid_uN` predicates | Concrete |
| `Arithmetic.lean` | 194 | Checked/saturating/wrapping helpers | Concrete |
| `Bridge.lean` | 296 | Spec ↔ Lean translation lemmas | Concrete |
| `Spec.lean` | 626 | Spec-level vocabulary (requires/effects/ensures shape) | Concrete |
| `Guards.lean` | 510 | RuntimeGuard predicates (signer, owner, key, etc.) | Concrete |
| `Verify.lean` | 64 | Proof-stamp interface | Concrete |
| `CommandBuilders.lean` | 182 | Cpi builder helpers | Concrete |
| `SBPF/ISA.lean` | 161 | Instruction encoding, opcodes | Concrete |
| `SBPF/Memory.lean` | 294 | `Mem`, region addresses, read/write, disjointness lemmas | Concrete + 0 axioms |
| `SBPF/Execute.lean` | 566 | `RegFile`, `State`, `step`, `executeFn`, exit semantics | Concrete |
| `SBPF/Patterns.lean` | 514 | Common proof patterns (e.g. `executeFn_compose`) | Concrete |
| `SBPF/Region.lean` | 126 | Region IDs (input/stack/heap/program) | Concrete |
| `SBPF/Pubkey.lean` | 83 | sBPF-level pubkey reads | Concrete |
| `SBPF/WPTactic.lean` | 175 | `wp_exec` tactic | Tactic-level |
| `SBPF/Tactic.lean` | 22 | Misc tactics | Tactic-level |

**Total: 4,294 lines.** sBPF kernel is the largest concrete chunk (1.9k LOC across Execute/Memory/Patterns/ISA). Spec/Guards/Bridge (1.4k LOC) cover the spec-level proof vocabulary. Account/CPI (350 LOC) cover the *envelope* of the runtime — what an instruction *looks like* — but not the runtime's behavior.

### Axiom audit

Explicit `axiom` declarations across `lean_solana/`:

```
Account.lean: find_map_pred_preserved
Account.lean: find_map_update_other
Account.lean: find_map_update_same
Account.lean: find_by_key_map_update_other
Account.lean: find_by_key_map_update_same
```

That's it. Five axioms, all comments label "axiom for now — full proof would require more complex induction." All five are standard `List.map`/`List.find?` interaction lemmas. They are **provable in Mathlib** — they're axioms purely because nobody wrote the induction yet. Phase 0 removes them in days, not weeks.

What's *not* in the explicit axiom list but is functionally axiomatic:
1. **The sBPF ISA model itself.** `SBPF/ISA.lean` says what each instruction *means*; it's a hand-written interpreter. There is no proof that this matches Agave's sBPF interpreter, Firedancer's VM, or any "official" sBPF spec — there is no official sBPF spec. This is the largest implicit trust in the system.
2. **`CpiInstruction` envelope correspondence.** We model `invoke_signed` as producing a `CpiInstruction`. Agave actually produces an `Instruction` from `solana_program::instruction`. We trust the codegen translates between them faithfully.
3. **Account loading + Anchor constraint discharge.** Anchor's `#[account(...)]` attributes generate per-handler validation; QEDGen's codegen claims this validation discharges `RuntimeGuard` predicates. There's no Lean-level statement of what Anchor actually does at load time.
4. **Syscall semantics.** Anything beyond pure arithmetic — `sol_log`, `sol_invoke_signed_c`, `sol_get_clock_sysvar`, crypto syscalls — is not modeled at all.
5. **Compute budget metering.** Not modeled.
6. **Loader v3/v4 deserialization.** Not modeled.

The explicit-axiom count understates the trust base by ~10x.

## The honest comparison: evm-asm

`Verified-zkEVM/evm-asm` (Hirai, ~April 2026) is the most direct prior art. Concretely:

- **24 EVM opcodes fully proven**, zero `sorry`. Bitwise, arithmetic, comparisons, shifts, stack ops.
- **99.7% Lean.** Bounded Hoare triples with separation logic; per-opcode cycle bounds.
- **Trust anchor is in progress, not done.** The README warns "DO NOT USE THIS PROJECT FOR ANYTHING OF VALUE." The RISC-V instruction semantics are "vibe-generated" and not validated against the official Sail spec. The fix is tracked as issue #93 — they're building abstraction-relation proofs in `EvmAsm/Rv64/SailEquiv/` to tie hand-written specs to Sail-generated RISC-V semantics.
- **TODO list**: EXP, ADDMOD, MULMOD, SDIV, SMOD, MLOAD, MSTORE, interpreter loop, state transition, sail-riscv-lean connection, EVM spec integration, conformance testing.

Two observations matter for the SVM analog:

**1. The "vibe-generated semantics" problem is structurally worse for sBPF.** RISC-V has an official ISA reference and a Sail model — Hirai can point at issue #93 and say "we'll close this gap." Solana has neither. The closest things are (a) Agave's interpreter, (b) Firedancer's interpreter, (c) sBPF fuzz corpora maintained by both teams. There is no Sail-RISC-V for sBPF. A reference SVM semantics in Lean has to *become* the missing spec — there's nothing upstream to align to.

This is simultaneously the strongest argument *for* doing this (someone has to write the spec) and the strongest argument *against* doing it under QEDGen's branding (it's bigger than spec-driven verification of user programs).

**2. Per-opcode is the right granularity to start.** evm-asm shipped 24 opcodes before any system-level integration. The same shape works for sBPF: prove the small-step semantics of each `Insn` constructor matches a reference oracle, then build composition. We already have `SBPF/Execute.lean`'s `step` function — what's missing is the oracle to validate against.

## Benefits, by audience

### QEDGen users (today's audience)

- **Shrunken trust statement.** Today's VERIFICATION_SCOPE.md trusts "the runtime axioms in `lean_solana`." Post-spike, that line either disappears (Phase 0 axioms become theorems) or becomes concrete and bounded (Phase 1+ replaces hand-wavy "we trust Anchor" with "we trust this 200-line account-loading model, which is differential-tested against Agave").
- **Compositional CPI.** Today's v2.8 G3 ensures-as-axiom CPI theorems carry `:= by sorry`. A reference runtime + an imported callee proof closes that hole structurally rather than by lockfile pinning. This is the single biggest user-visible verification gap right now.
- **Account-constraint soundness.** Today's RuntimeGuard predicates (`Guards.lean`) are *claims* about Anchor's behavior. With an account-loading model they become *theorems*: "the codegen-emitted Anchor attributes discharge `RuntimeGuard.signer(authority)` because the load step rejects any tx where `authority.is_signer = false`."

### Auditors

- A precise statement of what an instruction sees: which account fields are populated when, which CPIs can mutate which fields, what compute budget remains. Today auditors read Agave's Rust to derive this.
- A differential oracle for divergence claims. "Agave and Firedancer disagree on edge case X" is currently an empirical fuzz finding; against a reference, it's a soundness statement.

### Ecosystem (Firedancer/Agave/Jito/zk-SVM)

- A Lean reference is the natural target for differential testing across multi-client implementations.
- For any zk-SVM (zk proofs of SVM execution for rollups / L2s), the reference *is* what the zk circuit has to be sound against. Without a reference, "zk-SVM" is "zk-of-whatever-Agave-does-this-week."

### QEDGen the product (positioning)

- "QEDGen verifies your program against the SVM's executable reference semantics" is a much stronger claim than "QEDGen verifies your program against our hand-rolled axioms." This is genuinely truer post-spike, not just marketing.
- It also dramatically widens what QEDGen *can* verify — anything currently axiomatized (cross-account effects, CPI return values, account-loading edge cases) becomes provable.

## Costs and risks

### Direct effort

| Phase | What it covers | Person-time estimate | Confidence |
|---|---|---|---|
| 0 — axiom cleanup | Replace 5 Account.lean axioms with proofs | 3-5 days | High |
| 1 — CPI small-step | Operational semantics for `invoke_signed` over CpiInstruction, including signer-seed validation as a Prop | 4-8 weeks | Medium |
| 2 — Account loading | Anchor constraint discharge as theorems; transaction-context → instruction-context model | 6-12 weeks | Medium-low |
| 3 — Syscalls (non-crypto) | `sol_log`, `sol_get_clock_sysvar`, `sol_get_rent_sysvar`, `sol_alloc_free`, others not currently axiomatized; crypto syscalls stay axiomatized | 4-8 weeks | Medium |
| 4 — Differential testing | Extract Lean SVM (interpreter mode), run against Firedancer's vm-fuzz corpus + Agave's solana-sbpf | 4-6 weeks | Medium |
| 5 — sBPF ISA validation | Per-opcode oracle alignment, Phase-4 corpus extended to per-instruction coverage | 6-10 weeks | Low |
| 6 — Crypto primitives | Ed25519, secp256k1 recovery, sha2, sha3, alt_bn128 — likely import a fiat-crypto port or stay axiomatized | 6+ months or N/A | N/A |
| 7 — Verified extractable (F2) | Productionize Phase 0-6 to an executable replacement for solana_sbpf interpreter | 2-5 person-years | Low |

Phase 0+1+3+4 — the realistic F1 scope — is ~4-6 person-months. Phase 2 is the wildcard: account loading is where most adoption value lives (it's what unlocks honest Anchor verification), but it's also the most likely to discover that Anchor's behavior is under-specified.

### Maintenance tax

Agave ships SIMD features continuously (SIMD-0001 through SIMD-0321+ as of this writing). A reference model that lags reality is a model nobody uses. Options:

- **Pin a feature set per release** (analog of evm-asm's "Cancun-ish" approach). Honest, but limits adoption.
- **Continuous tracking.** ~0.25-0.5 FTE indefinitely.
- **Reference is opt-in per QEDGen release**, like a lockfile. Each QEDGen version pins a reference version; users opt to upgrade.

The third is the most realistic and is the same shape as the existing `qed.lock` mechanism.

### Strategic risk

- **Scope drift away from QEDGen's wedge.** QEDGen's adoption story is "drop a `.qedspec`, get proofs." A reference SVM doesn't directly help adoption — it improves *soundness*, which is a quality argument, not a usage argument. Spending 4+ months on F1 means not spending 4+ months on the auditor subagent, the Anchor adapter, or the embedded-spec macros — all of which have nearer-term revenue paths.
- **"Who owns the SVM spec" politics.** Anchoring QEDGen to a Lean reference SVM puts us in implicit competition for "what is the SVM" with Agave + Firedancer teams. Better outcome is to collaborate: contribute the reference upstream to Solana Foundation / Firedancer fuzz infrastructure rather than ship it as QEDGen's private model.
- **F2 trap.** It is tempting to slide from "reference semantics" (F1) to "verified replacement runtime" (F2). F2 is a CompCert-class project and is not what QEDGen does. Stay in F1 explicitly.

### What can't be axiomatized away

Even with F1 fully built out, the residual trust base remains:

1. **Lean kernel + Mathlib.**
2. **The sBPF ISA model.** Differential testing reduces but does not eliminate trust — fuzz corpora aren't exhaustive.
3. **Crypto primitives** (unless Phase 6 happens, which it won't).
4. **rustc + LLVM sBPF backend.** The asm-level proof path bypasses this for sBPF-asm-authored programs, but it remains in scope for Rust-authored programs.

The asm-level path Hirai advocates is, in QEDGen terms, the existing sBPF lane: write asm, prove against the Lean ISA model. That path closes #4 above. It still trusts #1-3.

## Recommended path

### Phase 0 — Axiom cleanup (3-5 days)

Replace the five Account.lean `axiom` declarations with Mathlib-backed proofs. This is pure technical debt; no design questions. Outcome: the explicit axiom count for `lean_solana` is zero. Documentation pivots from "we axiomatize List operations" to "we axiomatize the sBPF ISA, account-loading model, and syscall semantics (concretely listed)."

### Phase 1 — CPI small-step semantics (4-8 weeks)

Today's `Cpi.lean` defines `CpiInstruction` as a struct and `targetsProgram` / `accountAt` / `hasDiscriminator` as predicates over it. Extend with:

```lean
-- A CPI either succeeds, runs out of compute, or returns a program error.
inductive CpiResult
  | ok (effects : List AccountEffect)
  | err (code : Nat)
  | depthExceeded

-- Small-step CPI semantics: given a calling instruction, signer seeds,
-- account state, and the target program's spec-level behavior,
-- compute the result.
def stepCpi (cpi : CpiInstruction)
            (signers : List SignerSeeds)
            (state : RuntimeState)
            (callee : ProgramSpec) : CpiResult
```

`ProgramSpec` is the per-program effect contract — for well-known programs (System, Token, Token-2022, ATA) we ship reference specs; for user programs, the qedspec acts as the callee spec. This is the structural fix for v2.8 G3's `:= by sorry` problem.

**Deliverable**: an example escrow `transfer` CPI proven against the model end-to-end, with no `sorry`, no ensures-as-axiom.

### Phase 2 — Account loading (6-12 weeks)

Model the transaction → instruction context pipeline. Then prove that the codegen-emitted Anchor `#[account(...)]` constraints discharge each `RuntimeGuard` in `Guards.lean`.

This is the highest-leverage phase for QEDGen users: it converts "the codegen claims this guard is enforced" into "the codegen proves this guard is enforced." The Anchor adapter that's currently a stack of lints becomes a proven translator.

**Risk**: Anchor's account-loading is under-documented. Expect to find behaviors that aren't in any spec and have to be co-discovered with Anchor maintainers.

### Phase 3 — Non-crypto syscalls (4-8 weeks)

Each non-crypto syscall as a `State → State` Lean function. Crypto syscalls stay explicitly axiomatized — document the trust boundary, don't paper over it.

### Phase 4 — Differential testing (4-6 weeks)

Extract `lean_solana`'s sBPF interpreter to executable Lean (via `lean_compile` or native code). Run against:
- Firedancer's `vm-fuzz` corpus
- Agave's `solana-sbpf` test suite
- A QEDGen-curated mainnet program corpus

Outcome: a passing diff oracle, and a list of edge cases where Agave/Firedancer/our-model disagree — every such case is either a bug in our model or evidence of multi-client divergence worth surfacing.

### Phases 5-6 (defer)

sBPF ISA validation (5) is gated on Phase 4 producing a corpus rich enough to be a real oracle. Crypto primitives (6) are deferred indefinitely — fiat-crypto exists but is in Coq, not Lean; the porting effort is its own project.

### F2 is explicitly out of scope

A verified extractable replacement for `solana_program_runtime` is a multi-year, multi-team effort. It is not what QEDGen is for. If the ecosystem decides it wants this — most plausibly driven by a zk-SVM project — F1 is the right substrate to start from, but the team is not QEDGen's.

## Decision points / open questions

1. **Sequencing vs. parallel work.** Does the SVM spike block (or run alongside) the auditor subagent, Anchor adapter, and embedded-spec macros? The current memory state suggests these are the active near-term tracks. Phase 0 fits trivially; Phase 1+ wants a clear "this is the next big rock."

2. **Internal vs. ecosystem framing.** Ship F1 as `lean_solana/` v3, or pitch it to Solana Foundation / Firedancer as a multi-client conformance project? The latter is strategically better but operationally slower.

3. **Hoare triples vs. WP?** evm-asm uses bounded Hoare triples with separation logic. QEDGen uses WP-style `executeFn` reasoning via `wp_exec`. They compose differently. Worth a side-by-side prototype on one example before committing.

4. **Spec for sBPF.** Is there an opportunity to drive a "sBPF reference spec" with the Firedancer team? Without an authoritative spec, F1 is QEDGen's private model. With one, it's an ecosystem deliverable.

5. **What does "verified SVM" buy that proptest+Kani doesn't?** For most QEDGen properties, proptest+Kani already gives high confidence cheaply. The Lean reference unlocks (a) compositional CPI, (b) account-loading soundness, (c) the trust-base shrinkage marketing/auditor story. These are real but should be explicit — don't sell F1 as solving problems the cheaper backends already cover.

## Bottom line

A verified SVM in Lean is real and tractable in its **reference-semantics** form (F1). It is **not** the "final form of software development" Hirai advertises — it's the spec layer that's missing from today's stack, and writing it in Lean lets QEDGen's existing proofs target something concrete instead of axiomatic.

Phase 0 is a no-brainer this quarter. Phase 1 (CPI small-step) closes the largest remaining unsound-by-design hole in QEDGen and is worth a serious scoping pass before committing.

F2 is the wrong shape for QEDGen and should be declined when (not if) it's proposed.
