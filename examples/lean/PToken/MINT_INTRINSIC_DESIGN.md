# Mint intrinsic design (MintTo / Burn refinement)

**STATUS: SHIPPED (2026-06-01).** All decisions below were implemented as
written (second heap, `Mint = preAuth/supply/rest`, `tokenMintTo`/`tokenBurn`,
the codec + aggregation). Both `MintToRefinement.lean` and `BurnRefinement.lean`
close; full build green. Burn's account reuses Transfer's `src_account_eq`; its
mint reads only supply + is_init, so it uses a leaner `mint_supply_eq` (opaque
preAuth) rather than the full `mint_account_eq`. The "abstracted bases" risk
noted at the end resolved cleanly — the codec-fold simp + per-atom bridge needed
no changes.

Original design draft (kept for reference): Goal: close
`PTokenMintTo` and `PTokenBurn` against new abstract intrinsics, the same way
Transfer / TransferChecked close against `tokenTransfer`.

## What the two arms actually do (from the proven lifts)

Concrete mutated cells (balance-correct corollary form, clean Nat `±`):

| arm    | token-acct amount cell        | mint-acct supply cell         | amount var   |
|--------|-------------------------------|-------------------------------|--------------|
| MintTo | `addr4 + 152 ↦ d.amt + amt`   | `addr5 + 124 ↦ supply + amt`  | `oldMemD_36` |
| Burn   | `addr4 + 152 ↦ a.amt - amt`   | `addr5 + 124 ↦ supply - amt`  | `oldMemD_20` |

Both put the **token account at base `addrX + 88`** (amount at `base+64 = +152`)
and the **mint account at base `addr5 + 88`** (supply at `base+36 = +124`).
`addr4`/`addr5` are alignment-rounded account-data pointers (`wrapAdd`/`&&&`
chains) — abstracted Nat params, not `baseAddr + const`. The aggregation lemmas
are parametric in `base`, so this is fine; the per-arm refinement supplies
`base := addr4 + 88` / `addr5 + 88`, exactly as TransferChecked supplied
`baseAddr + 21024`.

So semantically:
- `MintTo(mint, dest, amount)`: `mint.supply += amount`; `dest.amount += amount`.
- `Burn(account, mint, amount)`: `account.amount -= amount`; `mint.supply -= amount`.

## Decision 1 — how the Mint account enters the abstract heap

The abstract heap today is `accounts : Pubkey → Option TokenAccount`
(`AbstractState`, `State.lean`). MintTo/Burn need a **Mint** resource too, and a
pre-state owning *both* a mint and a token account: `(mint ↦ₘ m) ** (dest ↦ₐ t)`.

**Recommended: a second heap field `mints : Pubkey → Option Mint`** (added to
both `AbstractState` and `PartialAbstractState`), with a new atom
`key ↦ₘ Mint`. This is exactly the "one clause per resource" extension the
`State.lean` docstring anticipates: each new resource adds one clause to
`Disjoint` / `union` / `CompatibleWith` and one `singletonMint` lemma family.

- **Pro:** the proven `tokenTransfer` path is untouched — `tokenTransfer_spec`,
  `AsmRefinesTokenTransfer`, and both shipped refinements keep compiling
  verbatim. The `accounts`-clause lemmas are a copy-paste template for the
  `mints`-clause.
- **Con:** mirrors ~8 singleton/Disjoint/union/CompatibleWith lemmas for the new
  clause (mechanical).

**Rejected alternative: unify into `Account = token TokenAccount | mint Mint`**
in the single existing heap. Cleaner heap, no second clause — but it widens the
heap value type, so `tokenTransfer_spec` and the existing Transfer/TransferChecked
abstract halves all have to re-wrap as `.token tSrc`. Rippling into the proven
path to save boilerplate isn't worth it.

## Decision 2 — the Mint structure + codec

SPL Mint layout (82 bytes): `mint_authority : COption<Pubkey>` (36B, offsets
0–35) · `supply : u64` (36–43) · `decimals : u8` (44) · `is_initialized : bool`
(45) · `freeze_authority : COption<Pubkey>` (46–81). MintTo/Burn only mutate
`supply`; everything else flows through opaque.

```
-- abstract side (State.lean)
structure Mint where
  preAuth : ByteArray   -- 36B: mint_authority COption, opaque
  supply  : Nat
  rest    : ByteArray   -- 38B: decimals/is_init/freeze_authority, opaque
  deriving Inhabited

def Mint.withSupply (m : Mint) (s : Nat) : Mint := { m with supply := s }
```

```
-- concrete codec (new SVM/Solana/MintAccountCodec.lean, mirrors TokenAccountCodec)
def mintAcctSupply (base : Nat) (preAuth : ByteArray) (supply : Nat) (rest : ByteArray) : Assertion :=
  (base        ↦Bytes preAuth) **    -- 36B
  (base + 36   ↦U64   supply)  **
  (base + 44   ↦Bytes rest)          -- 38B

def mintSupplyOf (base : Nat) (m : Mint) : Assertion :=
  mintAcctSupply base m.preAuth m.supply m.rest
```

`supply` is mid-struct (offset 36, after the 36-byte authority), so unlike
`TokenAccount` it can't be a single trailing `rest`; modeling it as
`preAuth ++ supply ++ rest` is the minimal faithful shape.

## Decision 3 — MIR statements + error modes

```
-- Mir.lean: two new MirStmt constructors
| tokenMintTo (mint dest : Pubkey) (amount : Nat)
| tokenBurn   (account mint : Pubkey) (amount : Nat)
```

`runStep` clauses (error modes must be a *superset* of asm's — soundness
invariant in `Mir.lean`):
- `tokenMintTo`: `accountMissing` (mint or dest), `overflow` on `supply+amount`
  *or* `dest.amount+amount`.
- `tokenBurn`: `accountMissing`, `insufficientFunds` on `account.amount < amount`
  (and on `supply < amount`, though `supply ≥ account.amount` is an invariant we
  don't model — the asm checks account funds, so that's the binding guard).

New `MirError` constructors may be needed only if the existing
`overflow`/`insufficientFunds`/`accountMissing` don't fit — they do, keyed by
`Pubkey`, so no `MirError` change expected.

## Decision 4 — specs + refinement predicates (mirror tokenTransfer)

- `Triples.lean`: `tokenMintTo_spec`, `tokenBurn_spec` — same proof skeleton as
  `tokenTransfer_spec` but over `(mint ↦ₘ m) ** (dest ↦ₐ t)`. The `mint ≠ dest`
  / key-distinctness comes from the same Disjoint argument (cross-heap atoms are
  trivially disjoint since they touch different clauses — actually *simpler* than
  the same-heap Transfer case).
- `Refinement.lean`: `AsmRefinesTokenMintTo` / `…Burn` predicates +
  `TokenMintToRefinement` / `…Burn` structures + `…_intro` constructors, mirroring
  the `tokenTransfer` trio. The asm obligation pre/post use
  `mintSupplyOf mintAddr m ** tokenAcctBalanceOf destAddr t`.

## Decision 5 — concrete aggregation lemma

New `MintAggregation.lean` (sibling of `TransferAggregation.lean`):
`mint_account_eq` — `mintSupplyOf base m ↔ <scattered lift cells>`. The lift owns
`supply` as a `↦U64` dword at `base+36`; `preAuth` and `rest` are opaque framed
gaps (the lift never reads the authority/decimals on the happy path beyond
is_initialized, which is a single owned byte → one `memByteIs` + gaps, same
pattern as the token-account `rest` split). The token account (dest/source)
reuses the **existing** `src_account_eq` / `dst_account_eq` verbatim.

## File-by-file plan (once design is approved)

1. `State.lean` — `Mint` structure + `withSupply` lemmas; `AbstractState.mints`
   field + get/set/update lemmas (copy the `accounts` family).
2. `Abstract/SepLogic.lean` — `PartialAbstractState.mints` field; `singletonMint`,
   `mintIs` (`↦ₘ`), one clause each in `Disjoint`/`union`/`CompatibleWith` + the
   mirrored lemma family.
3. `Mir.lean` — two constructors + `runStep` clauses.
4. `Triples.lean` — `tokenMintTo_spec`, `tokenBurn_spec`.
5. `Abstract/Refinement.lean` — `AsmRefinesTokenMintTo/Burn` + structures + intros.
6. `SVM/Solana/MintAccountCodec.lean` — `mintAcctSupply` / `mintSupplyOf`.
7. `examples/lean/PToken/MintAggregation.lean` — `mint_account_eq`.
8. `examples/lean/PToken/MintToRefinement.lean` + `BurnRefinement.lean` (+
   generators) — apply the recipe with `mintSupplyOf` for the mint and the
   existing token aggregation for the token account.

## Risk notes

- **Heaviest item is step 2** (the second SL clause): the `Disjoint`/`union`/
  `CompatibleWith` proofs gain a `mints` obligation everywhere. Mechanical but
  touches the load-bearing SL infra — full build is the regression guard.
- **Abstracted bases** (`addr4`/`addr5`): the aggregation runs at `base = addr5 + 88`
  etc. The recipe's `simp only [Nat.add_assoc, Nat.reduceAdd]` won't fold a
  symbolic `addr5 + 88 + 36`; the per-atom `buildDefeqBridge` in `sl_exact`
  handles `effectiveAddr addr5 124` vs `addr5 + 88 + 36` the same way it handled
  the Transfer address-form gap. May need to confirm the fold/bridge interplay on
  the first build (the one genuinely new wrinkle vs TransferChecked).
- Everything else is a faithful copy of the `tokenTransfer` machinery.
