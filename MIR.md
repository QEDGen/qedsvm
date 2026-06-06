# The Solana-native MIR: abstract semantics and the refinement bridge

Date: 2026-06-06
Status: reference for the current (Direction-A pilot) MIR
Verified against: `6407d35` (`SVM/Solana/Mir.lean`, `SVM/Solana/Abstract/{State,Triples,Refinement}.lean`)
Related: [PIPELINE.md](PIPELINE.md), [COVERAGE.md](COVERAGE.md), `docs/mir-readability-spike.md`

The MIR is the layer that says what a compiled program *means*. PIPELINE.md ends at a
machine-checked `cuTripleWithinMem`: a faithful but byte-level Hoare triple over registers and
memory cells. That triple is correct and unreadable. The MIR is the abstract counterpart: a
small set of Solana-native intrinsics with an operational semantics over decoded accounts, and a
refinement bridge that connects "these bytes shift this way" to "this program performs a token
transfer." A consumer cites one short intrinsic-level theorem; the byte-level proof is plumbing
underneath it.

This is Direction A (qedgen issue #66): a Solana-aware MIR (token transfer, mint, burn, counter,
growing toward ~20 intrinsics plus escape hatches), not a generic three-address IR. The design
bet is that naming Solana operations directly makes both the specs and the proofs smaller.

## The two-layer split

```
  ABSTRACT side  (this document)            CONCRETE side  (PIPELINE.md)
  ----------------------------              ---------------------------
  AbstractState: decoded accounts           SVM.SBPF.Memory.Mem: byte cells
  Pubkey -> Option TokenAccount             registers, mem ranges, CU
  MirStmt + runStep semantics               sBPF decode + per-insn specs
  absTriple over runMir                     cuTripleWithinMem
        \                                        /
         \______ Refinement bridge _____________/
                 (AsmRefines<Intrinsic>)
```

The abstract side reasons over `TokenAccount` / `Mint` / `CounterAccount` records, never over
byte ranges. The concrete side is the existing sBPF `PartialState`. The bridge in
`Abstract/Refinement.lean` packages the two halves so a consumer can quote a single combined
claim. Crucially, the bridge does NOT prove a layout map `Pubkey -> Nat` is correct; that stays a
per-program obligation discharged by the codec reshape (see "How qedlift uses this" below).

## The stack, top to bottom

```
┌──────────────────────────────────────────────────────────────┐
│ Layer 0  Domain vocabulary   (Abstract/Domain.lean)           │
│   balance s key, validTransfer s … — what a Solana engineer   │
│   reads. tokenTransfer_correct is the external statement;      │
│   tokenTransfer_spec is the internal SL obligation. Same       │
│   denotation, friendlier surface. Footprint.lean adds          │
│   `agreesOutside keys` for the "every other account unchanged" │
│   clause.                                                      │
├──────────────────────────────────────────────────────────────┤
│ Layer 1  Refinement bridge   (Abstract/Refinement.lean)       │
│   AsmRefines<Intrinsic> obligation predicates + bundled        │
│   <Intrinsic>Refinement structures + *_intro constructors.    │
│   This is the library qedsvm consumers cite.                  │
├──────────────────────────────────────────────────────────────┤
│ Layer 2  Abstract triples    (Abstract/Triples.lean)          │
│   absTriple prog P Q over runMir. One proven, parametric       │
│   theorem per intrinsic (tokenTransfer_spec, …). SL pre/post   │
│   over a partial heap of decoded accounts.                    │
├──────────────────────────────────────────────────────────────┤
│ Layer 3  Operational semantics   (Mir.lean)                   │
│   MirStmt (one constructor per intrinsic), runStep (pure       │
│   Except MirError AbstractState), runMir (stop-on-first-error  │
│   sequencing).                                                │
├──────────────────────────────────────────────────────────────┤
│ Layer 4  Abstract state      (Abstract/State.lean)            │
│   AbstractState = three partial heaps (accounts / mints /     │
│   counters) of decoded records. get/set/update per resource.  │
└──────────────────────────────────────────────────────────────┘
```

## The intrinsic set (today)

`MirStmt` has one constructor per intrinsic. Four are implemented; each is a pure state
transition with named failure modes (`MirError`).

| Intrinsic | Effect | Errors on |
| --- | --- | --- |
| `tokenTransfer src dst amount` | `src.amount -= amount`, `dst.amount += amount`; mint/owner/rest flow through | account missing, `src = dst` (`selfTransfer`), insufficient funds, dest u64 overflow |
| `tokenMintTo mint dest amount` | `mint.supply += amount`, `dest.amount += amount` | mint/dest missing, supply or dest overflow |
| `tokenBurn account mint amount` | `account.amount -= amount`, `mint.supply -= amount` | account/mint missing, insufficient funds |
| `counterIncrement key` | `counter += 1`; the first NON-token intrinsic (no mint/owner scaffolding) | counter missing, u64 overflow |

`runStep` is a total function returning `Except MirError AbstractState`; `runMir` sequences a
`List MirStmt` with standard stop-on-first-error monad semantics. Mint equality is deliberately
not enforced on `tokenTransfer`, matching SPL Token's unchecked Transfer. `selfTransfer` is an
explicit error rather than a silent no-op (see the soundness invariant below).

## The abstract state

`AbstractState` is three partial heaps, growing as later pilots demand resources:

```
structure AbstractState where
  accounts : Pubkey → Option TokenAccount   -- {mint, owner, amount, rest}
  mints    : Pubkey → Option Mint           -- {preAuth, supply, rest}
  counters : Pubkey → Option CounterAccount -- {counter}
```

Each record carries only the fields a Transfer-class theorem mutates plus opaque flow-through
tails (`rest`, `preAuth`). There is deliberately NO signer set, instruction data, return data,
CU counter, or CPI log yet: those land when an intrinsic that needs them (a `RequireSigner`,
`Cpi`, …) is added, not preemptively. Each heap has the same `get` / `set` / `update` shape, with
the cross-heap framing lemmas (`set_mints`, `setMint_accounts`, …) that keep an update to one
resource from disturbing the others.

## The abstract triples

`absTriple prog P Q` is partial correctness over the decoded heap: if the pre-assertion holds for
a state, `runMir prog` succeeds and the post-assertion holds for the result. Assertions are
separation logic over the partial heap, with one atom per resource:

- `key ↦ₐ t` — token account, `key ↦ₘ m` — mint, `key ↦cnt c` — counter, joined by `**`.

There is one proven, parametric triple per intrinsic (`tokenTransfer_spec`, `tokenMintTo_spec`,
`tokenBurn_spec`, `counterIncrement_spec`). `src ≠ dst` for transfer is NOT an explicit
hypothesis: it is derived inside the proof from the `Disjoint` of the two singleton atoms in the
precondition. Triples are single-statement today; multi-statement composition (an SL frame rule
analogous to `sl_block_iter`) is future work, and the bridge consumes the atomic triples
directly.

## The refinement bridge

For each intrinsic, `Abstract/Refinement.lean` declares two things plus a constructor:

1. An **asm-side obligation** `AsmRefines<Intrinsic>`: the exact shape a byte-level
   `cuTripleWithinMem` must take to count as a refinement. For `tokenTransfer` it is a triple
   whose pre owns `setupPre ** tokenAcctBalanceOf srcAddr tSrc ** tokenAcctBalanceOf dstAddr tDst`
   and whose post applies the `withAmount` shift. The `tokenAcctBalanceOf` wrapper is the
   byte-level codec of the decoded record.

2. A **bundled refinement** `<Intrinsic>Refinement` structure with two fields: `abs_spec` (the
   already-proven abstract triple) and `asm_spec` (the per-program asm obligation). The
   `*_intro` constructor discharges `abs_spec` from the library triple, so a per-program proof
   only has to supply `asm_spec`.

The two halves are independent by construction: the abstract triple is proven once, parametric in
the account values; the asm obligation is whatever the lift produced. The bridge does the
bookkeeping so consumers quote a single combined theorem. The note that matters: it does not link
`Pubkey` keys to byte addresses; `srcAddr`/`dstAddr` are free, and a concrete proof's layout
discharge is what ties them down.

### The layout-general escape hatch

`AsmRefinesFieldUpdate` is the one obligation NOT tied to a fixed intrinsic record. It is a
`cuTripleWithinMem` over `codecCoarse base preFields` / `codecCoarse base postFields`, where the
field list is a `List (Nat × FieldVal)` parsed from the IDL. ONE predicate covers any account
shape: the proof reshapes both coarse codecs to their fine (scattered) form via `account_agg` /
`codecCoarse_eq_fine` (keystone #2, `SVM/SBPF/AccountCodec.lean`) and frames the untouched fields.
This is what qedlift emits for a non-token field-update program (counter, vault). Note the honest
gap: `AsmRefinesFieldUpdate` is the asm-side codec-reshape obligation only; it does not yet have a
matching abstract `runStep` semantics (no generic `fieldUpdate` `MirStmt`), so it proves "this
bytecode performs a layout-general single-field update" without an abstract-heap denotation. A
generic field-update intrinsic is future work; see COVERAGE.md.

## The soundness invariant for adding an intrinsic

Every intrinsic must obey: **MIR's failure modes are a subset of the asm-side failure modes for
the refining codegen pattern.** If MIR errors on case X but the bytecode silently succeeds, the
refinement is unsound, and the user-facing triple must declare X as a precondition rather than
have MIR error on it. `tokenTransfer`'s `selfTransfer` error is the worked example: SPL Token's
unchecked Transfer no-ops the self case, but the pilot's downstream proof carries a disjointness
precondition that already excludes `src = dst`, so surfacing it as an explicit MIR error keeps the
precondition visible in the spec rather than hidden.

## Adding a new intrinsic (the four-step protocol)

From the `Mir.lean` docstring. Each addition is local; the surrounding machinery (`runMir`
sequencing, the SL frame rule, the bridge bookkeeping) does not change:

1. A constructor in `MirStmt` (`Mir.lean`).
2. A clause in `runStep` (`Mir.lean`).
3. A parametric abstract triple in `Abstract/Triples.lean`.
4. An `AsmRefines<Intrinsic>` obligation + bundled refinement + `*_intro` in
   `Abstract/Refinement.lean`.

If the new state-transition semantics needs a new resource (signers, return data, CU), add the
field to `AbstractState` and the cross-heap framing lemmas first. A program that only updates one
account field and needs no new semantics can skip steps 1 to 3 entirely and reuse
`AsmRefinesFieldUpdate` (the escape hatch).

## How qedlift uses this

qedlift (PIPELINE.md stage 3) mechanically emits the `AsmRefines<Intrinsic>` obligation for a
lifted arm: it matches the arm name against `refine_registry` (`Transfer` ->
`AsmRefinesTokenTransfer`, `MintTo` -> `AsmRefinesTokenMintTo`, `counterIncrement` ->
`AsmRefinesCounterIncrement`, `VaultIncrement` -> `AsmRefinesFieldUpdate`) and renders a
`refines_asm` theorem that discharges the asm obligation from the lift triple, reshaping the
account codec through `account_agg`. The abstract half is never re-proven per program: it is the
library triple in `Abstract/Triples.lean`. So a new program in an already-modeled shape costs a
qedspec and a lift, no new Lean. See COVERAGE.md for which shapes are mechanical today.

## Current scope and what is not here yet

- Four intrinsics implemented (transfer, mint, burn, counter); the Solana-native set is intended
  to grow toward ~20 plus escape hatches.
- Single-statement triples only; multi-statement composition via an SL frame rule is future work.
- No signers, instruction data, return data, CU, or CPI in the abstract state; added per pilot,
  not preemptively.
- `AsmRefinesFieldUpdate` (layout-general) has no abstract `runStep` counterpart yet.
- The readability stack (Domain / Footprint vocabulary) is partially landed; see
  `docs/mir-readability-spike.md` for the five-layer plan and what remains.
