# Solana Pattern Proof Library (design)

Status: design + Layer-1 skeleton. Local scratch doc (gitignored under `docs/`).

## Why

The Solana exploit landscape is not DeFi math. It is overwhelmingly *missing or
incorrect low-level checks*: missing owner check, missing signer check, PDA
substitution, type confusion from a skipped discriminator, unchecked arithmetic
on balances. qedsvm today proves layout-level refinement of real bytecode
(`AsmRefinesToken*`) but has no reusable, security-meaningful vocabulary to state
those checks. This library is the "altitude" layer we have been deferring, aimed
at the right target.

Three properties make this library worth building (and distinguish it from a
generic library of abstract invariants):

1. **Grounded.** Each predicate is defined over qedsvm's agave-faithful `State`
   and serialized-account model, so it means something on the real chain, not over
   a hand-authored abstraction.
2. **Mathlib-free-compatible.** Pubkey equality, discriminator match, balance
   comparison, and PDA derivation are concrete byte/`Nat` operations. None need
   `ring`/`Finset`/ℝ, so this lives in the core without the toolchain cost.
3. **The qedgen target.** A `.qedspec` that says "owner check dominates the write"
   only means something if the library defines and can prove or refute it.

## Architecture: three layers

Value climbs steeply from L1 to L3.

- **L1 Predicates** (`Patterns/Predicates.lean`, this skeleton): reusable state
  predicates. `Assertion := PartialState → Prop`. Cheap, immediately useful as
  spec vocabulary for hand-written and qedgen specs. Low risk.
- **L2 Recognizers** (`Patterns/Recognizers.lean`, future): lemmas that a bytecode
  idiom *refines* a predicate. This is the part that depends on having a grounded
  execution model under the predicates, and where our refinement machinery pays
  off. Critical design rule: **recognize
  semantically, not syntactically.** A discriminator check or pubkey-eq compiles
  to many sequences (inlined loop, `memcmp` syscall, unrolled). Matching exact
  bytes is brittle and unsound; instead prove the sequence *computes* the
  predicate, reusing `account_agg` / `memBytesIs_segs` / `codecCoarse_eq_fine` and
  the `cuTripleWithinMem` / `AsmRefinesFieldUpdate` obligations.
- **L3 Guards / domination** (`Patterns/Guards.lean`, future): the security
  property is rarely a data fact, it is control flow: "the write to `acct` is
  dominated by an owner check on every path," "no debit without a preceding
  sufficient-balance check." Needs a domination relation over the CFG, leaning on
  the dispatch substrate (`dispatch_routing_complete`). This is the bug-finding
  layer: it detects *missing* checks.

## Two address-space views (do not conflate)

The map of the codebase revealed two distinct places "account fields" live.

- **Input-region account block** (SBF aligned-v1 serialized form). Runtime
  privileges and identity. Per-account block offsets relative to the block base
  (mirrors `qedsvm-rs/src/serialize.rs` and `SVM/SBPF/Runner.lean`
  `parseInputPrivileges`):

  | offset | size | field |
  |---|---|---|
  | 0 | 1 | dup marker (`0xFF` = non-dup) |
  | 1 | 1 | is_signer |
  | 2 | 1 | is_writable |
  | 3 | 1 | executable |
  | 8 | 32 | key (Pubkey) |
  | 40 | 32 | owner program (Pubkey) |
  | 72 | 8 | lamports (u64 LE) |
  | 80 | 8 | data_len (u64 LE) |
  | 88 | data_len | data |

  First block is at `INPUT_START + 8` (`INPUT_START = 0x400000000`); subsequent
  blocks stride by `nonDupBlockSize` (`Runner.lean`). A multi-account locator is an
  open item (below).

- **Account-data view.** What lives inside the account's `data` bytes:
  discriminator / state byte, token fields. SPL token data layout
  (`SVM/Solana/TokenAccount.lean`): `mint@0`, `owner@32`, `amount@64`, `rest@72`,
  size 165. Generic shapes via `codecCoarse base (List (Nat x FieldVal))`.

The two `owner`s are different: the input block's owner@40 is the *owning program*;
the token-data owner@32 is the token *holder*. The predicate names disambiguate
(`ownedByProgram` vs token-account owner).

## L1 predicate catalog (this skeleton)

| Predicate | View | Basis |
|---|---|---|
| `isSigner b` / `notSigner b` | input block | `(b+1) ↦ₘ 1` / `↦ₘ 0` |
| `isWritable b` / `isExecutable b` | input block | `(b+2)/(b+3) ↦ₘ 1` |
| `keyIs b k` | input block | `(b+8) ↦Pubkey k` |
| `ownedByProgram b prog` | input block | `(b+40) ↦Pubkey prog` |
| `lamportsIs b v` / `lamportsAtLeast b n` | input block | `(b+72) ↦U64 v` |
| `dataLenIs b n` | input block | `(b+80) ↦U64 n` |
| `pubkeyEq a b` | pure | `Pubkey` `DecidableEq` |
| `hasDiscriminator8 d disc` / `hasDiscriminator d tag` | data | `d ↦ₘ disc` / `d ↦Bytes tag` |
| `balanceAtLeast ata n` | token data | `∃ v, n ≤ v ∧ (ata+64) ↦U64 v` |
| `isPda` / `isPdaWithBump` | derivation | reuse `SVM.Solana.*` (ByteArray; off-curve = `hOffCurve` hyp) |

Soundness side-conditions baked in: flag predicates pin the exact byte (`↦ₘ 1`),
since `memByteIs` stores raw; `lamportsAtLeast`/`balanceAtLeast` are existential
over the cell value with a `≤` bound (a real lower bound, not a degenerate one).

## L2 recognizer sketch (future)

Each pattern ships a lemma of the shape "this code window establishes the
predicate," e.g. (illustrative):

```
theorem recognize_owner_check
    (cr : CodeReq) (entry exit b : Nat) (prog : Pubkey) ... :
  cuTripleWithinMem nSteps nCu entry exit cr
    (ownedByProgram b prog ** P) (ownedByProgram b prog ** P) rr
```

proven by the existing aggregation/refinement reshaping, not by byte-matching.

## Catalog roadmap

1. **SPL Token first**, seeded by harvest: re-express the owner/balance reasoning
   already inside `AsmRefinesToken*` in terms of L1 predicates. This gives a real,
   grounded catalog entry by construction and validates the predicate shapes
   against actual bytecode before generalizing.
2. ATA, System program, Token-2022, common Anchor patterns.

## Soundness discipline

- Define predicates over the *grounded* state (real serialized flags and offsets),
  never a convenient abstraction. This is what avoids the "over-trust from labels"
  trap, where a verified library's names promise a stronger guarantee than its
  theorems actually establish.
- Recognizers must be semantic and non-vacuous. A recognizer that matches one
  compiler's exact output is near-useless.
- Stay Mathlib-free: every predicate here is a concrete byte/`Nat` operation.

## Placement / build

- `SVM/Solana/Patterns/{Predicates,Recognizers,Guards}.lean`.
- The `SVM` lib roots glob from `SVM`; build the skeleton standalone with
  `lake build SVM.Solana.Patterns.Predicates`. To include it in the CI lib build,
  import it from an aggregator (e.g. `SVM/Solana/Abstract.lean`) once it is stable;
  hold off while it is a skeleton so a gap cannot break the lib build.
- Any theorems (L2/L3) go behind the `AxiomAudit` gate, like the refinements.

## Open items

- `Pubkey ↔ ByteArray` bridge, to give a `Pubkey`-typed `isPdaPubkey`
  (`SVM/Solana/Pda.lean:16` notes this is not yet built).
- CFG domination substrate for L3 (build on `dispatch_routing_complete`).
- Multi-account input-block locator (the `nonDupBlockSize` stride walk) if
  predicates need to address the Nth account rather than a caller-supplied base.
