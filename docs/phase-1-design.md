# Phase 1 Design — CPI Small-Step Semantics

Date: 2026-05-12
Status: design proposal, pre-implementation

## What Phase 1 ships

A small-step operational semantics for Solana's `invoke_signed` such that:

1. Well-known program IDs (System, SPL Token, Token-2022, ATA) have shipped reference specs that take a `CpiInstruction` + runtime state and produce a deterministic account-state transition.
2. User programs supply their own `ProgramSpec` (typically derived from a qedspec or hand-written) to participate as CPI callees.
3. Downstream verifiers (QEDGen and similar) can discharge per-callsite "after this CPI, account X has property P" theorems by reducing `stepCpi` symbolically — not by axiomatization.

This closes the largest soundness gap in current Solana spec-driven verification: today, every cross-program effect collapses to an ensures-as-axiom `:= by sorry`, trusting that the imported callee's `ensures` clause matches what the callee actually does. Phase 1 replaces that trust with executable semantics.

## What Phase 1 does NOT ship

- **Syscalls.** `sol_log`, `sol_get_clock_sysvar`, `sol_get_rent_sysvar`, `sol_alloc_free`, etc. are Phase 3. CPI is mostly orthogonal — `invoke_signed` is the dispatch, syscall handlers operate on VM state directly.
- **Compute budget metering.** Phase 1 treats compute as out of scope. A `CpiResult.depthExceeded` constructor reserves the slot for when we model it.
- **Re-entrancy.** Solana doesn't support reentrant CPIs in practice (account locks prevent it). Phase 1 assumes well-formed input — the caller-side framework rejects reentrant attempts before `stepCpi` ever runs.
- **Account data at the byte level.** The reference semantics use structured views (e.g., SPL Token account = `{ mint, owner, amount, delegate, ... }`) rather than serialized bytes. Byte-faithful semantics is a Phase 1.5 concern.
- **Cross-instruction state.** The Bank/`TransactionContext` model is Phase 2 (Account Loading). Phase 1's `RuntimeState` is per-instruction.
- **Verified extraction (F2).** Phase 1 is reference semantics (F1), not a replacement runtime. See `docs/founding-rationale.md`.

## Goal: an end-to-end provable example

The shippable demonstration: an escrow-style `transfer` CPI proven end-to-end against the System Program reference spec. Pseudo-Lean:

```lean
example (from to : Pubkey) (amount : U64) (s : RuntimeState)
    (h_from_funded : (s.account from).lamports ≥ amount)
    (h_signer : signerAt from s) :
    let cpi := Svm.Cpi.System.buildTransfer from to amount
    let result := Svm.Cpi.stepCpi cpi [] s Svm.Cpi.System.spec
    result.ok ∧
    (result.accountAfter from).lamports = (s.account from).lamports - amount ∧
    (result.accountAfter to).lamports = (s.account to).lamports + amount := by
  simp [Svm.Cpi.stepCpi, Svm.Cpi.System.spec, Svm.Cpi.System.buildTransfer]
  ...
```

No `sorry`. No ensures-as-axiom. A real theorem about a real CPI.

## Type design

### `CpiResult`

```lean
inductive CpiResult where
  | ok (effects : List AccountEffect) (state : RuntimeState)
  | err (code : ErrorCode)
  | depthExceeded
```

- `ok` carries both the list of effects (for declarative reasoning) and the resulting `RuntimeState` (for chaining). This dual representation matters: some proofs are about effects (conservation), some are about state after (per-account lookups).
- `err` carries a structured `ErrorCode`, not a `Nat`. Solana's error model is well-structured — `SystemError::InsufficientFunds`, `TokenError::OwnerMismatch` — and we want proofs to talk about specific errors, not opaque numbers.
- `depthExceeded` reserves the slot for compute-budget modeling. A no-op for now (Phase 1 assumes unbounded budget).

### `ErrorCode`

```lean
inductive ErrorCode where
  -- Generic / framework
  | invalidAccountData
  | accountNotFound (pk : Pubkey)
  | missingSigner (pk : Pubkey)
  | unauthorized
  -- System Program
  | sysInsufficientFunds
  | sysAccountAlreadyInUse
  | sysInvalidAccountOwner
  -- SPL Token
  | tokenOwnerMismatch
  | tokenInsufficientFunds
  | tokenMintMismatch
  -- ... extensible per program
```

Open question: should this be flat (one big inductive) or hierarchical (per-program error namespaces)? Flat is simpler for proofs; hierarchical is more composable. Recommendation: start flat, refactor if it gets unwieldy past ~30 constructors.

### `AccountEffect`

The most debated type. Three approaches considered:

**A. Atomic VM ops.** `setLamports / setData / setOwner / setExecutable`. Most faithful to Solana's actual runtime mutations. Verbose — a System transfer becomes 4 ops (decrement source, increment dest, possibly reassign on receive).

**B. Per-program semantic ops.** `Svm.Cpi.System.Effect.lamportsTransferred`, `Svm.Cpi.SplToken.Effect.tokenTransferred`. Most readable. Couples the result type to the callee's program. Hard to compose when a CPI sequence touches multiple programs.

**C. Generic functional updates.** `AccountEffect = { pubkey : Pubkey, before : Account, after : Account }`. Maximum flexibility, minimum semantic structure — hard to write properties like "no balance changed except for these two."

**Recommendation: A**, with helper constructors per program.

```lean
inductive AccountEffectKind where
  | lamportsDelta (delta : Int)        -- signed: + for receive, - for transfer
  | dataReplaced (newData : List U8)
  | ownerReassigned (newOwner : Pubkey)
  | executableSet (executable : Bool)

structure AccountEffect where
  pubkey : Pubkey
  kind : AccountEffectKind
```

Why A over B/C:
- (A) lets a single proof reason uniformly across CPIs to different programs ("no AccountEffect with `kind := lamportsDelta` outside this list of pubkeys" is a clean conservation statement).
- The signed `lamportsDelta` is the key insight — `transferLamports` and `receiveLamports` collapse into one constructor with sign carrying the direction. Cleaner conservation: `Σ (effects.filter .lamportsDelta).delta = 0` (for transfers within tracked accounts).
- Per-program helpers (`Svm.Cpi.System.buildTransferEffects from to amount = [⟨from, lamportsDelta (-amount)⟩, ⟨to, lamportsDelta amount⟩]`) keep callsite code readable without locking the result type.

Open question: do we model `dataReplaced` at the byte level, or with a structured "token-account-data-update" overlay? Phase 1a is byte-level for simplicity; Phase 1b adds structured overlays for SPL Token / Token-2022 to make their proofs ergonomic. Both can coexist — `dataReplaced` is the load-bearing constructor, structured overlays are sugar.

### `SignerSeeds`

```lean
structure SignerSeeds where
  programId : Pubkey
  seeds : List (List U8)
  bump : U8
```

The set of PDA seeds the caller is signing with. Each PDA the CPI uses must have its seeds + bump match one entry in `List SignerSeeds`. `stepCpi` validates this against the account list's `is_signer` flags.

Phase 1a uses PDA derivation as an axiomatized predicate: `pdaValid : Pubkey → SignerSeeds → Prop`. Phase 1b can replace this with an actual sha256-based derivation if the crypto syscalls (Phase 6) ever get implemented. Until then, PDA validity is on the trusted side of the boundary.

### `RuntimeState`

```lean
structure RuntimeState where
  accounts : Pubkey → Option Account
  signers : List Pubkey
  -- writable_set : List Pubkey  -- TBD: derive from CpiInstruction.accounts or carry separately?
```

A function-typed `accounts` field (rather than `List Account`) makes lookups extensional — `state.accounts pk = some acc` is decidable and rewrites cleanly. We can lift the existing `findByKey` / `findByAuthority` from `Svm.Account` to operate over `RuntimeState`.

Open question: explicit writable-account set or derive from the `CpiInstruction.accounts` flags? The runtime tracks both: an account is writable in a given instruction iff its `AccountMeta.isWritable` is true AND the parent instruction passed it as writable. For Phase 1, derive from the metas — keeps the type smaller.

### `ProgramSpec`

```lean
abbrev ProgramSpec :=
  (cpi : CpiInstruction) → (signers : List SignerSeeds) → (state : RuntimeState) → CpiResult
```

Just a function. The contract: given the CPI envelope, the signer seeds, and the current state, produce the result.

Well-known program specs live in `Svm/Cpi/<Program>.lean`:

- `Svm/Cpi/System.lean` — `System.spec : ProgramSpec`, dispatching on `cpi.data`'s discriminator to `System.handleTransfer`, `System.handleAllocate`, `System.handleAssign`, `System.handleCreateAccount`.
- `Svm/Cpi/SplToken.lean` — `SplToken.spec : ProgramSpec`, dispatching on the single-byte discriminator.
- `Svm/Cpi/Token2022.lean` — similar shape.
- `Svm/Cpi/Ata.lean` — Associated Token Account program.

User programs construct their own `ProgramSpec` from their qedspec via QEDGen-side codegen (out of scope for formal-svm itself; QEDGen v2.18+ handles the bridge).

### `stepCpi`

```lean
def stepCpi
    (cpi : CpiInstruction)
    (signers : List SignerSeeds)
    (state : RuntimeState)
    (callee : ProgramSpec) : CpiResult :=
  callee cpi signers state
```

The entire body is `callee cpi signers state`. `stepCpi` is just a renaming — the real work happens in each `ProgramSpec`. This is intentional: it gives us a stable callsite name (`Svm.Cpi.stepCpi`) for downstream proofs to target, while letting individual program specs evolve.

The dispatch happens inside each `ProgramSpec`. For example:

```lean
def Svm.Cpi.System.spec : ProgramSpec := fun cpi signers state =>
  if cpi.programId ≠ SYSTEM_PROGRAM_ID then
    CpiResult.err ErrorCode.invalidAccountData
  else if cpi.data.take 4 = DISC_SYS_TRANSFER then
    handleTransfer cpi signers state
  else if cpi.data.take 4 = DISC_SYS_ALLOCATE then
    handleAllocate cpi signers state
  -- ...
  else
    CpiResult.err ErrorCode.invalidAccountData
```

`handleTransfer` etc. are the per-instruction semantic handlers.

## Reference spec: System Program

The four System Program instructions covered in Phase 1a:

| Discriminator | Handler | Effect |
|---|---|---|
| `[0,0,0,0]` (CreateAccount) | `handleCreateAccount` | Lamports transfer + owner reassign + data alloc on a new account |
| `[1,0,0,0]` (Assign) | `handleAssign` | Owner reassign on existing account |
| `[2,0,0,0]` (Transfer) | `handleTransfer` | Lamports delta on two accounts |
| `[8,0,0,0]` (Allocate) | `handleAllocate` | Data allocation on an account |

`handleTransfer` is the canonical example:

```lean
def Svm.Cpi.System.handleTransfer
    (cpi : CpiInstruction) (signers : List SignerSeeds) (state : RuntimeState) : CpiResult :=
  -- Parse: data tail (after 4-byte discriminator) is 8-byte LE u64 amount
  let amount := parseLeU64 (cpi.data.drop 4) |>.getD 0
  -- Expected accounts: [from (writable, signer), to (writable)]
  match cpi.accounts with
  | [⟨from, true, true⟩, ⟨to, _, true⟩] =>
      match state.accounts from, state.accounts to with
      | some fromAcc, some toAcc =>
          if fromAcc.lamports < amount then
            CpiResult.err ErrorCode.sysInsufficientFunds
          else if from ∉ state.signers then
            CpiResult.err (ErrorCode.missingSigner from)
          else
            let effects := [
              ⟨from, AccountEffectKind.lamportsDelta (-(amount : Int))⟩,
              ⟨to, AccountEffectKind.lamportsDelta (amount : Int)⟩
            ]
            let newState := state |> applyEffects effects
            CpiResult.ok effects newState
      | _, _ => CpiResult.err (ErrorCode.accountNotFound from)
  | _ => CpiResult.err ErrorCode.invalidAccountData
```

`applyEffects` is a helper: `RuntimeState → List AccountEffect → RuntimeState`. It's the bridge between the effects-as-data view (good for proofs) and the state-after view (good for chaining).

Provable property (the shippable theorem):

```lean
theorem System.transfer_correct
    (from to : Pubkey) (amount : U64) (state : RuntimeState)
    (h_distinct : from ≠ to)
    (h_from : ∃ fromAcc, state.accounts from = some fromAcc ∧ fromAcc.lamports ≥ amount)
    (h_to : ∃ toAcc, state.accounts to = some toAcc)
    (h_signer : from ∈ state.signers) :
    let cpi := Svm.Cpi.System.buildTransfer from to amount
    let result := stepCpi cpi [] state Svm.Cpi.System.spec
    ∃ effects newState fromAcc' toAcc',
      result = CpiResult.ok effects newState ∧
      newState.accounts from = some fromAcc' ∧
      newState.accounts to = some toAcc' ∧
      fromAcc'.lamports = (Classical.choose h_from).lamports - amount ∧
      toAcc'.lamports = (Classical.choose h_to).lamports + amount := by
  simp [Svm.Cpi.stepCpi, Svm.Cpi.System.spec, Svm.Cpi.System.handleTransfer,
        Svm.Cpi.System.buildTransfer]
  -- ... case analysis on h_from, h_to, h_signer
  sorry  -- finished in implementation, not here
```

## Reference spec: SPL Token

Phase 1b ships SPL Token transfer. The full SPL Token surface is 20+ instructions; we ship the common subset (transfer, mint_to, burn, close_account) and defer the rest.

Open question: model token-account data structurally or as bytes? **Recommendation: structurally**, with an abstraction barrier:

```lean
structure Svm.Cpi.SplToken.TokenAccount where
  mint : Pubkey
  owner : Pubkey
  amount : U64
  delegate : Option Pubkey
  state : Svm.Cpi.SplToken.AccountState  -- Initialized | Frozen | Uninitialized
  isNative : Option U64
  delegatedAmount : U64
  closeAuthority : Option Pubkey

-- Bridge: parse bytes ↔ structure
def parseTokenAccount : List U8 → Option TokenAccount
def serializeTokenAccount : TokenAccount → List U8

-- Axiom (to be discharged in Phase 1c via differential testing):
-- parseTokenAccount (serializeTokenAccount t) = some t
```

This lets SPL Token proofs talk about `tokenAccount.amount`, not `data.drop 64 |>.take 8`. The serialization round-trip is axiomatized in v0.3.0 and proven in v0.4.0 once the byte-level harness exists.

## Integration with `Svm.Cpi` envelope predicates

The existing predicates (`targetsProgram`, `accountAt`, `hasDiscriminator`, `hasNAccounts`, `wellFormed`) stay. They describe the SHAPE of the CPI instruction; `stepCpi` consumes the same shape and produces effects.

A natural pattern in proofs:

1. Caller constructs a `CpiInstruction` using a helper builder (`System.buildTransfer`, `SplToken.buildTransfer`).
2. Caller proves shape via the existing predicates (mostly `by rfl` since builders produce concrete instructions).
3. Caller invokes `stepCpi` and proves the resulting `CpiResult` via `simp` on the spec's `unfold` chain.
4. Caller's higher-level theorem (account balance changed by N) follows from the effects list.

The Phase 1 design preserves the existing `cpi_correct` theorems QEDGen emits — they're now provable as `targetsProgram ... ∧ accountAt ... ∧ hasDiscriminator ...`, which the builders satisfy by construction.

## Integration with QEDGen

QEDGen's v2.8 G3 ensures-as-axiom CPI theorems become provable after Phase 1 + a QEDGen-side bridge. The bridge isn't formal-svm's job; this is just the contract we're offering.

The bridge, from QEDGen's side, looks like:

1. QEDGen's spec declares `calls: TOKEN_PROGRAM_ID DISC_TRANSFER(src writable, dst writable, auth signer)`.
2. QEDGen-codegen produces a Lean theorem statement that previously body-mapped to `:= by sorry`.
3. Post-Phase 1: the same theorem body becomes a call to `stepCpi` against `Svm.Cpi.SplToken.spec`, plus simp-reduction to extract the post-state.
4. Codegen produces the proof body too (mostly `simp` + `decide` after the unfolds).

Net effect: today's `theorem op_initialize_post_callee : ... := by sorry` becomes `:= by simp [stepCpi, SplToken.spec, ...]; decide`. Real proof, no axiom.

This bridge is QEDGen v2.18 work, gated on Phase 1a shipping in formal-svm.

## Trust boundaries after Phase 1

What's verified:
- Per-CPI account effects, given the program spec and the runtime state.
- Caller-side composition (multiple CPIs in sequence — though sequence-level reasoning may need helpers).

What's trusted:
- Each `Svm.Cpi.<Program>.spec` matches the actual program's runtime behavior. Differential testing against Agave/Firedancer (Phase 4) is how we discharge this.
- PDA derivation (Phase 6).
- The instruction data parsers (`parseLeU64`, `parseTokenAccount`) — round-trip lemmas are axiomatized until byte-level harness exists.
- Anything not modeled (compute budget, syscalls, cross-instruction state).

## Open questions

1. **Effect granularity for SPL Token**: byte-level vs. structured TokenAccount. Recommendation: structured with axiomatized round-trip. Open until a real proof exposes friction.
2. **PDA validation**: hash-faithful vs. axiomatized? Axiomatized in Phase 1, faithful blocked on Phase 6.
3. **Conservation properties**: how do we prove "no other account is touched"? Effects-list filtering should be sufficient. Need a clean `effects.touchedAccounts ⊆ cpi.accounts.map .pubkey` invariant.
4. **Sequence of CPIs**: a transaction can have multiple top-level instructions, each with nested CPIs. Phase 1 is per-CPI; multi-instruction is a sequence-of-`stepCpi` fold. Helpers for this in Phase 1d?
5. **`signers` semantics**: is the runtime `signers` list the top-level transaction's signers, or the current-instruction's pass-through signers? Probably the latter, but need to nail this in the spec.
6. **Error-code granularity**: flat enum vs. per-program namespace. Flat in Phase 1, refactor if needed.
7. **Naming**: `stepCpi` vs. `invokeSignedCpi` vs. `interpretCpi`? Bikeshed. Recommendation: `stepCpi` (short, matches the "step" terminology in our sBPF executor).
8. **Computability vs. propositional**: should `stepCpi` be `def` (computable, reducible by `simp` / `decide`) or `noncomputable def` (allows quotients, dependent types)? Recommendation: keep `def` — every well-known spec's body is decidable; trade flexibility for proof ergonomics.

## Implementation plan

### Phase 1a — v0.3.0-rc (~1 session)

- Define types: `CpiResult`, `ErrorCode`, `AccountEffect`, `AccountEffectKind`, `SignerSeeds`, `RuntimeState`, `ProgramSpec`.
- Define `stepCpi`.
- Define `applyEffects : RuntimeState → List AccountEffect → RuntimeState`.
- System Program: `System.spec`, `System.buildTransfer`, `System.handleTransfer`.
- Theorem: `System.transfer_correct`.
- Tests: smoke test that `System.transfer_correct` discharges.
- Ship as `v0.3.0-rc.0`.

### Phase 1b — v0.3.0 (~1-2 sessions)

- Complete System Program: `handleAllocate`, `handleAssign`, `handleCreateAccount`.
- SPL Token: `SplToken.spec`, structured `TokenAccount`, axiomatized round-trip, `handleTransfer`.
- Theorem: `SplToken.transfer_correct`.
- Tag `v0.3.0`.

### Phase 1c — v0.3.1 (~1-2 sessions)

- SPL Token: `handleMintTo`, `handleBurn`, `handleCloseAccount`.
- ATA: `Ata.spec`, `Ata.buildCreate`, `Ata.handleCreate`.
- Token-2022: `Token2022.spec` (largely a rewrap of SplToken with extension-aware handlers — defer extensions).

### Phase 1d — v0.3.2 (~1 session)

- Edge cases: integer overflow paths, missing-account paths, wrong-signer paths.
- Sequence-of-CPIs helpers: `stepCpiSeq : List CpiInstruction → RuntimeState → ProgramSpec → CpiResult`.
- Conservation lemmas: total lamports preserved across `applyEffects` for the right CPIs.
- Documentation pass: each `Svm/Cpi/<Program>.lean` gets a module docstring + a "this models X version of the program, last validated against Y" trust statement.

### Phase 1e — v0.3.3 (optional, ~1 session)

- Sequence integration with QEDGen's CPI builders. End-to-end escrow example: `transfer` + `cancel` proven against the System Program spec, no sorries, no ensures-as-axiom.
- QEDGen-side bridge work happens in QEDGen v2.18.

### Total Phase 1: ~4-7 sessions

vs. the spike's 4-8 weeks estimate, which assumed less LLM-driven iteration.

## Validation plan

Phase 1 ships as reference semantics — it's our best model of the programs. Validation comes in later phases:

- **Phase 4 (differential testing)** runs the reference specs against Agave's actual program implementations on a corpus of mainnet transactions. Every disagreement is either a model bug or a real Agave/Firedancer divergence.
- **Phase 5 (sBPF ISA validation)** does the same for the sBPF interpreter. Phase 1 and Phase 5 together give a fully-tested model.

Until Phase 4 lands, Phase 1's reference specs are *plausible* but unvalidated. The README continues to say "Don't ship this against mainnet value."

## Risks

- **Scope creep on `AccountEffect` granularity.** If structural ops can't express something a real SPL Token CPI does, we're stuck mid-Phase-1b. Mitigation: byte-level `dataReplaced` is the universal fallback; structured ops are sugar layered on top.
- **PDA derivation axioms multiply.** Each program with PDAs (most of them) adds new axiomatized "this is a valid PDA derivation." Mitigation: a single `pdaValid` predicate parameterized by program + seeds + bump, axiomatized once.
- **QEDGen-side bridge complexity.** If the codegen needs to produce proofs in terms of `stepCpi`, that's QEDGen codegen surgery. Mitigation: keep `stepCpi` simple enough that the proof bodies are mostly `simp + decide`.
- **Anchor framework's transparent CPI wrappers.** `anchor-spl::token::transfer(ctx, amount)` wraps `invoke_signed`. The reference spec models the `invoke_signed` side; the framework-side conformance is QEDGen's concern, not formal-svm's.

## Decision points before implementation

Before writing v0.3.0-rc.0 code, the following decisions need explicit signoff:

1. **`AccountEffectKind` shape**: signed `lamportsDelta` + `dataReplaced` + `ownerReassigned` + `executableSet`. Or different?
2. **Structured vs. byte-level token data**: structured with axiomatized round-trip in v0.3.0, byte-level harness in v0.4.0+. Or different?
3. **`ErrorCode` shape**: flat enum, per-program constructors. Or hierarchical namespaces?
4. **`stepCpi` name**: keep, or rename?
5. **First-shipped program coverage**: System (full) + SPL Token transfer in Phase 1a, or just System transfer alone?

Once these land, Phase 1a is a ~1-session implementation against this design.
