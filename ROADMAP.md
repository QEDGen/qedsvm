# formal-svm Roadmap

The phased path to a usable F1 reference SVM. See `docs/founding-rationale.md` for the strategic frame and the F1-vs-F2 scope decision.

## Phase 0 — Axiom cleanup

Replace the five `axiom` declarations in `Svm/Account.lean` (`find_map_pred_preserved`, `find_map_update_other`, `find_map_update_same`, `find_by_key_map_update_other`, `find_by_key_map_update_same`) with Mathlib-backed proofs. These are standard `List.map` / `List.find?` interaction lemmas; the axiom labels are technical debt, not soundness commitments.

**Outcome**: `grep -r '^axiom' Svm/` returns nothing. Documentation pivots from "we axiomatize list operations" to "we axiomatize the sBPF ISA, account loading, and crypto syscalls (concretely listed)."

**Estimate**: 3-5 days.

## Phase 1 — CPI small-step semantics

`Svm.Cpi` today defines `CpiInstruction` as a struct and `targetsProgram` / `accountAt` / `hasDiscriminator` as envelope predicates. It does **not** model what happens when a CPI executes.

Extend with operational semantics for `invoke_signed`:

```lean
inductive CpiResult
  | ok (effects : List AccountEffect)
  | err (code : Nat)
  | depthExceeded

def stepCpi (cpi : CpiInstruction)
            (signers : List SignerSeeds)
            (state : RuntimeState)
            (callee : ProgramSpec) : CpiResult
```

`ProgramSpec` is the per-program effect contract. For well-known programs (System, SPL Token, Token-2022, ATA) we ship reference specs. For user programs, downstream verifiers (QEDGen and similar) pass in the program's spec.

**Outcome**: downstream tools can prove CPI correctness end-to-end without axiomatizing the callee. Closes the largest soundness gap in current spec-driven Solana verification.

**Estimate**: 4-8 weeks.

## Phase 2 — Account loading

Model the transaction → instruction context pipeline: how `TransactionContext` materializes `InstructionContext`, how `InstructionAccount`s populate `is_signer` / `is_writable` flags, how runtime-rejected loads short-circuit before user code runs.

This is the layer that lets downstream verifiers prove "the framework's account-constraint annotations actually discharge the runtime guards I'm relying on" rather than asserting it.

**Risk**: Solana's account loading is under-documented at the edges. Expect to co-discover behaviors with Anchor / Firedancer maintainers.

**Estimate**: 6-12 weeks.

## Phase 3 — Non-crypto syscalls

Each non-crypto syscall as a Lean `State → State` function: `sol_log`, `sol_get_clock_sysvar`, `sol_get_rent_sysvar`, `sol_alloc_free`, etc. Crypto syscalls (Ed25519, secp256k1 recovery, sha2/sha3, alt_bn128) stay axiomatized with explicit trust statements — see Phase 6.

**Estimate**: 4-8 weeks.

## Phase 4 — Differential testing

Extract `Svm.SBPF` to executable Lean (`lean_compile` or native), run against:

- Firedancer's `vm-fuzz` corpus
- Agave's `solana-sbpf` test suite
- A curated mainnet program corpus

Every disagreement is either a bug in our model or evidence of multi-client divergence worth surfacing. This is the empirical answer to the "are the sBPF semantics actually correct" question — without it, the model is a hand-written guess.

**Estimate**: 4-6 weeks.

## Phase 5 — sBPF ISA validation

Per-opcode oracle alignment against Phase 4's corpora, extended to per-instruction coverage. Goal: every `Insn` constructor in `Svm/SBPF/ISA.lean` has a passing differential check.

**Estimate**: 6-10 weeks. Gated on Phase 4 producing a corpus rich enough to be a real oracle.

## Phase 6 — Crypto primitives (deferred)

Ed25519, secp256k1 recovery, sha2, sha3, alt_bn128. Most likely path is a Lean port of fiat-crypto, which exists in Coq. The effort is substantial enough to be its own project. Until then, crypto syscalls are axiomatized with explicit trust documentation.

## What is *not* on the roadmap

**F2 — verified extractable runtime.** A Lean implementation that replaces `solana-program-runtime` in production is a multi-year, multi-team effort. It is not the scope of this repo. If the ecosystem decides it wants this — most plausibly driven by a zk-SVM project — the phases above are the right substrate to start from, but the team is not this one.

**Solana-side state.** Bank, slot lifecycle, account commits, consensus, gossip, leader schedule, vote processing. All out of scope. This repo is the *program execution* layer of the SVM, not the validator.

**A new verification tool.** This is the model, not the tool. Tools that use the model — QEDGen and others — live elsewhere.
