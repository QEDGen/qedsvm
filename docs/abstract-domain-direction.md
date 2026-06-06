# Direction: retire the Lean MIR, ship a discharge tactic

Date: 2026-06-06
Status: direction note (decision recorded, not yet executed)
Related: [MIR.md](MIR.md), [PIPELINE.md](PIPELINE.md), `SVM/Solana/Abstract/{State,Mir,Triples,Refinement}.lean`,
`../leanstral-solana-skill/crates/qedgen/data/proofs/spl/Token.lean`

## Decision

qedsvm should NOT maintain its own abstract Solana program domain. The abstract domain
(account state, the meaning of a handler, the per-property obligation) is generated for free by
qedgen from a `.qedspec`, and qedgen already states it in a form that is strictly more general
than qedsvm's hand-built MIR. qedsvm's job is the bytecode prover underneath it: a
`qedsvm_discharge` tactic that proves a qedgen-emitted obligation against pinned bytecode. The
`SVM/Solana/Abstract/{State,Mir,Triples}` layer plus the per-intrinsic `AsmRefinesToken*` family
is pilot scaffolding to converge away, not a durable architectural layer.

## The evidence

qedgen's generated SPL proof package states the transfer contract parametrically
(`crates/qedgen/data/proofs/spl/Token.lean`):

```lean
axiom ensures_axiom_0 {State : Type} [Inhabited State]
    (pre post : State) (amount : Nat) (from_balance : State → Nat) :
  (from_balance post) = (from_balance pre) - amount
```

The whole axiom set is one uniform schema, `accessor post = accessor pre ± amount`, over an
opaque `State : Type` and an accessor `State → Nat`: transfer (`from_balance -`, `to_balance +`),
`mint_to` (`total_supply +`, `to_balance +`), `burn` (`total_supply -`, `from_balance -`). It
commits to no record shape.

The file header states the integration plan in qedgen's own words: in v3.0 each `axiom
ensures_axiom_i` becomes `theorem ... := by qedsvm_discharge "<binary_hash>" "<handler>"`, and the
tactic "decodes the ELF, applies the bundled SL spec via `sl_block_auto`, and projects onto the
abstract State accessor." So the contract between the two projects is a TACTIC over a parametric
obligation, never a shared (or duplicated) data model.

## What qedsvm already proves lands on that target

The lifted Transfer (`examples/lean/Generated/PTokenTransferTracedLifted.lean`,
`PTokenTransfer_balance_correct`) already carries the accessor shift directly in the post-state
bytes, at the IDL offsets:

```
(effectiveAddr baseAddr 160   ↦U64 oldMemD_11 - oldMemD_10) **   -- src.amount  - amount
(effectiveAddr baseAddr 10664 ↦U64 oldMemD_30 + oldMemD_10) **   -- dst.amount  + amount
```

That is `ensures_axiom_0/1` expressed in `↦U64` atoms. So the bytecode triple witnesses the
abstract balance shift with no `runStep` hop in between. The remaining piece for a
`qedsvm_discharge` is a thin projection: read the post `↦U64` cell at the accessor's IDL offset
and restate it as `accessor post = accessor pre ± amount`. The hard parts already exist:

- the lift (`sl_block_auto`) and the CU-bounded triple,
- the codec reshape coarse to fine (`account_agg`, `codecCoarse_eq_fine`),
- the IDL-driven field offset / layout (`FieldVal`, `parse_account_layout`).

The `AsmRefinesFieldUpdate` / vault work is the same instinct already in flight: layout-general,
IDL-driven, projecting a field by offset rather than through a bespoke record. It is converging on
qedgen's `(accessor : State → Nat)` obligation from the other side.

## Keep / converge / retire

| Component | Verdict | Why |
| --- | --- | --- |
| sBPF VM + diff-test (`SVM/SBPF/*`, `qedsvm-rs`) | **Keep** | The differentiated core; nobody else has a conformant Lean SVM. |
| Lift + codec reshape (`sl_block_auto`, `account_agg`, `FieldVal` layout, the balance corollary) | **Keep** | This is 90% of a discharge tactic. |
| `Abstract/State.lean` records (`TokenAccount`/`Mint`/`CounterAccount`) | **Converge** | A concrete re-encoding of qedgen's parametric `State`; reduce to "the IDL layout + an accessor offset." |
| `Mir.lean` (`MirStmt`/`runStep`/`runMir`) | **Retire** | Off the discharge path; an intermediate semantics the tactic never traverses. |
| `Abstract/Triples.lean` (`tokenTransfer_spec`, …) | **Retire** | Re-proves obligations qedgen already generates per program. |
| `AsmRefinesToken*` family (`Abstract/Refinement.lean`) | **Converge** | Collapse the four bespoke predicates into one accessor-projection discharge. |

## Why the MIR existed (so this is not a recrimination)

The concrete MIR was the right pilot. Landing `tokenTransfer` end to end, and the 76-CU pinocchio
Transfer proof, is how the refinement MECHANISM was validated on real bytecode before either the
`.qedspec` generator or the `qedsvm_discharge` tactic existed. That is scaffolding, not waste. The
thing to stop doing is extending it: each new hand-built intrinsic (the `tokenTransfer` ->
`counterIncrement` -> `FieldUpdate` treadmill) is qesvm re-deriving, one case at a time, a domain
qedgen emits generically.

## The convergence path

1. Define the discharge obligation shape qesvm targets: given a binary hash, a handler, an account
   layout (IDL), and an accessor offset, prove `accessor post = f (accessor pre) args` from the
   lifted triple. Parametric in the accessor, as qedgen's axiom is.
2. Write the projection lemma: post `↦U64` cell at the accessor offset -> the Nat equation. This is
   the only genuinely new Lean.
3. Package it as a `qedsvm_discharge` tactic (decode ELF -> `sl_block_auto` -> reshape -> project)
   that closes a qedgen `ensures_axiom_i` directly.
4. Once one real handler discharges through it, retire `Mir.lean` + `Triples.lean` and collapse
   `AsmRefinesToken*`. `MIR.md` then describes history.

## Open questions / caveats

- **Non-balance ensures.** Many `.qedspec` properties are access control, lifecycle, or CPI
  contracts that qedgen discharges at the source/spec level and that never need bytecode. qesvm
  only owns the state-mutation ensures (the `accessor post = f(accessor pre)` shapes). The
  discharge tactic is for those, not all obligations.
- **Multi-statement handlers.** A handler that mutates several fields or calls CPI needs the
  obligation projected per accessor and an SL frame across statements. The single-statement triple
  is enough for the atomic SPL handlers; composition is the same frame-rule gap noted in MIR.md.
- **The projection across the layout** still relies on the codec reshape being faithful for the
  handler's account; that is the `account_agg` / `COVERAGE.md` story and bounds which handlers can
  discharge mechanically today.
