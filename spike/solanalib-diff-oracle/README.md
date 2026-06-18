# Spike: solanalib differential oracle

Branch: `spike/solanalib-diff-oracle`

Cross-validate qedsvm's sBPF interpreter against the Solana Foundation's
[`leanprover-solanalib`](https://github.com/solana-foundation/leanprover-solanalib),
whose `SBPF/` layer is a Lean 4 port of the **OOPSLA 2025 Isabelle/HOL sBPF
formalization**. Two independently authored Lean models of the same machine,
run on the same programs, must agree. Where they do, we get cross-engine
soundness signal on our step semantics. Where they don't, we get a finding.

This is the one piece of solanalib worth harvesting: as engine/infrastructure
it is strictly behind us (no syscalls, no CPI/PDA, not execution-grounded
against agave/mollusk, no lifting pipeline), but its OOPSLA-derived `step` is a
free, independent oracle.

## How it works

solanalib ships an `sbpf-oracle` executable (`Oracle.lean`) used by their own
`spinoza` differential harness. Its stdin/stdout contract is trivially simple
and text-based, which sidesteps the structural mismatch between the two models
(qedsvm is `Nat` + logical-PC-resolved jumps; solanalib is `BitVec` +
slot-relative jumps with a separate verifier). We never reconcile state types
or PC indexing: we only compare the **observable result** of running the same
bytes from a zeroed state.

```
INPUT  (one vector/line):  <version> <fuel> <byte0> <byte1> ...
OUTPUT (one line/vector):  ok <r0>  |  fault  |  error: <reason>
```

`DiffOracle.lean` (built as `qedsvm-oracle`) speaks the same protocol against
qedsvm's `executeFn` from a zeroed `State`. It adds one outcome solanalib
cannot produce: **`reject`**, when qedsvm's decoder refuses the program. qedsvm
folds agave's verifier rejections into `decode` (fail-closed); solanalib runs a
verifier-less interpreter. `reject` is bucketed separately from `fault`.

We model **SBPFv1** (neg/mul/div/mod in the base ALU; no PQR, no byteswap), so
the corpus drives both with `version = 1`.

## Run it

```bash
# qedsvm side (Lean 4.30, already in the project)
lake build qedsvm-oracle

# solanalib side (Lean 4.31). build_solanalib.sh clones + builds; the vendored
# copy here neutralizes Solanalib/Init.lean's Mathlib linter imports and drops
# the `require mathlib` so the oracle closure builds Mathlib-free in ~30s.
./build_solanalib.sh

# generate corpora + diff
python3 gen_corpus.py --mode core --n 3000 --seed 1 > corpus_core.txt
python3 gen_corpus.py --mode sharp > corpus_sharp.txt
python3 gen_corpus.py --mode edge  > corpus_edge.txt
SOLANALIB_EXE=vendor/leanprover-solanalib/.lake/build/bin/sbpf-oracle \
  ./run_both.sh corpus_core.txt
```

`diff.py` buckets each `(qedsvm, solanalib)` pair. The buckets that matter:
`DIVERGE-VALUE` (both `ok`, different `r0`) and `DIVERGE-*-notok/ok` are real
semantic-bug signal; `STRICTER q-reject/s-ok` is the qedsvm-decode-fold axis,
expected and not a bug.

## Results

**Core corpus** — 3000 random register-only SBPFv1 programs (ALU 32/64 imm+reg,
mov, neg, shifts, div/mod, conditional/unconditional jumps, lddw), ending in
EXIT:

```
2394  AGREE-OK        (both ok, identical r0)
 606  AGREE-FAULT
   0  HARD DIVERGENCES
```

2394 independent value comparisons across the full shared ALU/jump/exit core,
**zero divergences**. qedsvm's interpreter is observationally identical to the
OOPSLA-derived model on every one.

**Sharp corpus** — 12 hand-built probes of the highest-risk boundary: how a
32-bit ALU result is widened to 64 bits. All 12 `AGREE-OK`. Both engines:

| probe                | result (both)            | extension |
|----------------------|--------------------------|-----------|
| `sub32` 0−1          | `0xFFFFFFFFFFFFFFFF`     | **sign**  |
| `add32` →0x80000000  | `0xFFFFFFFF80000000`    | **sign**  |
| `mul32` 0xFFFF²      | `0xFFFFFFFFFFFE0001`    | **sign**  |
| `mov32`, `neg32`     | `0xFFFFFFFF`            | zero      |
| `arsh32/rsh32/lsh32` | `0xF8000000` / …        | zero      |
| `div32` 0xFFFFFFFF/2 | `0x7FFFFFFF`            | zero      |
| `add64` wrap, `arsh64` | `0`, `0xF8…00`        | (64-bit)  |

**Edge corpus** — 7 deliberate probes of the divergence axes:

```
5  STRICTER q-reject/s-ok   (r10 write, imm shift>=width x2, byteswap le/be)
1  AGREE-NOTOK (qedsvm-reject)  (PQR-class 0x86 under v1)
1  AGREE-FAULT                  (div-by-zero immediate)
```

These are exactly the known, expected differences: qedsvm fails closed at decode
on agave verifier violations (`CannotWriteR10`, `ShiftWithOverflow`) and on ops
it does not model (byteswap, PQR), where solanalib's verifier-less interpreter
masks the shift / executes the op. Not bugs; qedsvm's fold-into-decode is the
more faithful model of the deployed agave verify-then-execute pipeline. (Their
`step_ne_err` / Lemma 6.4 verifier is what *should* gate these in their stack,
but their oracle bypasses it.)

## Finding (applied)

The probes proved both engines **sign-extend `add32/sub32/mul32`** and
zero-extend the other 32-bit ops. qedsvm's *code* is correct and intentional
(`wrapAdd32`/`wrapSub32`/`wrapMul32` apply `signExtend32`; `Machine.lean:505`
pins this as agave V0 behavior, diff-tested against mollusk). But two *comments*
claimed the opposite:

- `SVM/SBPF/Execute.lean:235` — "32-bit ALU: result zero-extended to 64 bits"
- `SVM/SBPF/ISA.lean:134` — "ALU 32-bit (result zero-extended to 64 bits)"

Both corrected on this branch. A documentation inaccuracy on the subtlest
semantic boundary, surfaced by the oracle. No semantics changed.

## Verdict

The differential oracle is **cheap and worth keeping**: both sides build in
~1 minute, the contract is 3 lines, and it cross-validates our step semantics
against an independent, academically-grounded model. The headline result is
reassuring (0 divergences across 3000 vectors: 2394 agree on an exact r0, 606 on
faulting, including the sign-extension boundary), which
is exactly what you want from a second oracle: it found no semantic hole, and
the one thing it did surface (the comments) is now fixed.

Recommended next steps if we invest further (not done here):
- **Wire into CI** as a fast nightly: regenerate a seeded corpus, run both,
  fail on any `DIVERGE-VALUE` / `DIVERGE-*notok/ok`. Catches regressions in
  either model. Cost: a 4.31 toolchain + the Mathlib-free vendored oracle.
- **Widen the corpus** to memory ops once we agree an initial memory image and
  region map with solanalib's `0x100000000` program base (currently
  register-only to keep the contract clean).
- **Track their roadmap**: PDAs/sysvars and the Aeneas source-level bridge are
  the parts that would become genuinely additive (Aeneas is a *competing*
  source-Rust→Lean lifting path to our bytecode→Lean qedlift).

## Files

```
DiffOracle.lean       qedsvm oracle (lean_exe qedsvm-oracle, wired in lakefile.lean)
gen_corpus.py         corpus generator: --mode core|sharp|edge
diff.py               buckets paired outcomes, flags hard divergences
run_both.sh           run both oracles on a corpus + diff
build_solanalib.sh    clone + build solanalib's sbpf-oracle
vendor/               vendored solanalib (Init.lean + lakefile patched, Mathlib-free)
corpus_*.txt          generated corpora
*.out                 oracle outputs
```
