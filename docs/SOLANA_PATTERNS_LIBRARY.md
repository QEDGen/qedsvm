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

## Why grounded primitives, not an abstract interface library (the Solana shape)

A reasonable instinct is to mirror Ethereum: an abstract verified library of
high-level interface invariants (the OpenZeppelin / ERC model), against which many
implementations are checked. That model rests on **fan-out**: one interface
(ERC-20), one reference implementation, thousands of contracts implementing the
same interface, so verifying "what the interface means" once amortizes over every
conformer, and the EVM's typed ABIs make "conforms to the interface" well-defined.

Solana breaks that assumption three ways:

1. **Composition is CPI-into-canonical, not implement-the-interface.** You do not
   write your own token program; you CPI to the one SPL Token program. For things
   that have a "standard," there is effectively a single implementation everyone
   depends on, not many conformers. No fan-out to amortize an abstract spec over.
2. **Accounts are untyped byte blobs.** There is no language-level ABI for account
   *contents*. Each program defines and enforces its own serialization and
   ownership. So "conforms to a shared state interface" is not even well-defined
   for most programs.
3. **The IDL is generated from the implementation.** The interface is downstream
   of the code, co-defined with it, not a contract the code is written against.

So an abstract interface-invariant library is aimed at a fan-out Solana mostly
lacks. The conclusion that falls out:

- **Prove the canonical primitive programs directly.** SPL Token, ATA, System,
  Stake, the loaders: one implementation the whole ecosystem rides on, the program
  *is* the standard, and a direct byte-level proof benefits everyone who CPIs into
  it. (This is the existing `AsmRefinesToken*` work.)
- **Put the reusable layer one level down, in the checks, not the interface.**
  Every program (canonical or bespoke) does owner / signer / PDA / discriminator /
  balance checks. *That* has universal fan-out. So the Solana-native analog of a
  "verified standard library" is the proven canonical programs plus a grounded
  vocabulary of the low-level checks they are built from. The library's role is
  "primitives the direct proofs compose from," not "an interface above them."

Two practical payoffs of this shape:

- **Partial guarantees before full correctness.** Fully proving a primitive program
  is a large proof; the check recognizers let us ship meaningful, composable partial
  assurances ("this path performs the owner check, the balance never underflows")
  well before full functional correctness.
- **The bespoke long tail is covered by the same vocabulary.** Custom programs have
  no shared interface to verify against, but they all use the same checks, so the
  grounded primitives are the one thing reusable across them.

Watch item: the emerging Token-2022 / SPL token interface (multiple token programs
sharing a common transfer surface) is the one place an ETH-style fan-out is
appearing. A thin shared transfer spec could pay off there. It is a handful of
programs, not thousands, so it is a watch item, not a reason to build the abstract
layer first.

## Architecture: checks-as-guards, with predicates as substrate

The security-relevant unit on Solana is not a state predicate but a GUARD: the
program reads a field, compares it, and FAULTS (does not perform the effect) when
the check is violated, on every path. The dominant exploit class is a missing or
wrong guard. So the library's center of gravity is Layer 3; Layers 1 and 2 are the
vocabulary the guards are stated and proven in.

(An earlier framing front-loaded the predicates and parked the guards as "future."
Re-evaluated against the Solana lens, that put the weight one rung too high:
predicates describe states, but the bug-relevant, reusable unit is the guard. A
predicate-only library documents what correct states look like while proving no
checks, which is the same one-rung-too-high mistake, one level down. The guards are
the product.)

- **L1 Predicates** (`Patterns/Predicates.lean`): field-level state predicates
  (`ownedByProgram`, `isSigner`, `balanceAtLeast`, `hasDiscriminator`, ...). Spec
  vocabulary; the easy, low-risk layer.
- **L2 Recognizers** (`Patterns/Recognizers.lean`): a bytecode idiom *refines* a
  predicate, proven SEMANTICALLY (the sequence *computes* the predicate), never by
  byte-matching. A discriminator check or pubkey-eq compiles to many sequences
  (inlined loop, `memcmp` syscall, unrolled); matching exact bytes is brittle and
  unsound. Reuse `account_agg` / `memBytesIs_segs` / `codecCoarse_eq_fine` and the
  `cuTripleWithinMem` obligations.
- **L3 Guards** (`Patterns/Guards.lean`): the product. A check is ENFORCED if, from
  a state where it is violated, the verified window FAULTS (typed `VmError`) instead
  of reaching the effect. Expressed over the `cuTripleFaultsWithin*` triples;
  all-paths domination builds on the dispatch/CFG substrate
  (`dispatch_routing_complete`, currently on a parked branch) incrementally.

### Requires vs enforces (the distinction that matters)

Two properties are easy to conflate, and the gap between them IS the bug class:

- **REQUIRES**: a refinement's precondition assumes the check passed. The proven
  `AsmRefinesToken*` arms are exactly this: they state the data transformation on
  the happy path and assume nothing faults. They carry NO check content.
- **ENFORCES**: the program itself diverts to a fault when the check is violated.
  This is the security property.

A missing check is precisely REQUIRES-without-ENFORCES: a path that reaches the
effect without the check. A library that only states predicates and refinement
preconditions documents correct states but proves no checks. The guards close that.

Canonical recipe for a guard: show the violated check ROUTES from the window entry
to the program's error handler (a `cuTripleWithinMem` to the error PC), then reuse
the handler's own fault spec (a `cuTripleFaultsWithin` from the error PC). The two
compose into `EnforcedFault` via `enforcedFault_of_routes_then_handler` (a thin
wrapper over `cuTripleWithinMem_seq_fault_pure`). The routing half is the
substantive, program-specific obligation; the handler-fault half is a generic,
reusable fact about the shared error exit.

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
  open item (below). CONFIRMED against the proven p_token bytecode: pinocchio reads
  these input-region offsets directly (no `AccountInfo` pointer-deref), e.g. the
  authority signer byte loads as `.ldx .byte .r0 .r1 0xa8`. Note the loads use
  *absolute* block offsets (the authority block is not the first), so a guard
  instantiates the block base for the specific account rather than assuming `+1`.

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

## Status

- **L1 Predicates**: implemented (`Patterns/Predicates.lean`), builds clean.
- **L2 Recognizers**: started (`Patterns/Recognizers.lean`). Balance bridge:
  `balanceAtLeast_of_amountCell` (core), `balanceAtLeast_weaken`,
  `balanceAtLeast_of_tokenAcctBalance` (the `tokenAcctBalance` atom that
  `AsmRefinesTokenTransfer` carries entails the same account with its `amount`
  conjunct weakened to `balanceAtLeast`). Depend on **no axioms**.
- **L3 Guards**: TWENTY-SIX full `EnforcedError` guards across FIVE p-token
  arms (Transfer 16, MintTo 5, Burn 2, TransferChecked 2, CloseAccount 1),
  all standard-axiom clean, all built the same way (violating fixture →
  diff_mollusk test → captured failing trace → qedlift error-path lift →
  `cuTripleWithinMem_seq_exit` composition; guard files generated mechanically
  from the lifted specs). Transfer arm:
  1. **Balance** (`BalanceGuardEnforced.lean`): insufficient balance HALTS with
     exit 1 (InsufficientFunds), token cells untouched.
  2. **Frozen source** (`FrozenGuardEnforced.lean`): exit 17 (AccountFrozen).
  3. **Frozen destination** (`DestFrozenGuardEnforced.lean`): the sibling one
     `jeq` later (pc 4012 vs 4011), exit 17.
  4. **Mint mismatch, all four limbs**
     (`MintMismatch{,Limb1,Limb2,Limb3}GuardEnforced.lean`): the
     pubkey-INEQUALITY guard, complete. The unrolled 4-limb mint compare
     (pc 4017-4028) has one diverge `jne` per limb (4019/4022/4025/4028); any
     two distinct mints first differ at exactly one limb, and each limb's
     path is a proven EnforcedError, exit 3 (MintMismatch).
  5. **Uninitialized src/dest** (`{Src,Dest}UninitGuardEnforced.lean`): state
     byte = 0 diverts at 4005/4008; exit = 10<<32
     (ProgramError::UninitializedAccount — builtins encode in the HIGH 32
     bits, unlike TokenError customs which exit with the small custom code).
  6. **Invalid state byte src/dest** (`{Src,Dest}BadStateGuardEnforced.lean`):
     state > 2 (not a valid AccountState tag — the account-shape /
     type-confusion class) diverts at 4004/4007; exit = 4<<32
     (ProgramError::InvalidAccountData).
  7. **Short instruction data** (`ShortIxGuardEnforced.lean`): ix data < 9
     bytes diverts at 3998 through the 312 hub; exit 12
     (TokenError::InvalidInstruction).
  8. **The authority tri-case**
     (`{OwnerNotSigner,DelegateNotSigner,OwnerMismatch}GuardEnforced.lean`):
     the honest signer/owner guard, un-parking the deferred item. The naive
     "not signer implies fault" claim is FALSE on this binary (the delegate
     path continues); the three legs state it honestly: owner ∧ ¬signer and
     delegate ∧ ¬signer halt with 8<<32
     (ProgramError::MissingRequiredSignature); a properly SIGNING stranger
     (neither owner nor delegate) halts with exit 4 (TokenError::OwnerMismatch
     — the canonical most-skipped check).
  9. **Delegated-amount allowance** (`DelegateInsufficientGuardEnforced.lean`):
     a signing delegate with allowance < amount halts with exit 1
     (InsufficientFunds) via the delegated_amount@121 cell — a distinct check
     and distinct cell from the source-balance guard.
  Fan-out arms (`PToken/{MintToArm,BurnArm,TransferCheckedArm,CloseAccountArm}/`):
  10. **MintTo supply overflow** (`MintToArm/SupplyOverflowGuardEnforced.lean`):
      exit 14 (TokenError::Overflow). THE load-bearing check: it is the
      invariant the absent Transfer dest-overflow check leans on, so both
      sides of the supply invariant are now in the catalog (the absent check
      pinned, the enforcing check proven).
  11. **MintTo fixed-supply** (exit 5), **mint-authority mismatch** (exit 4),
      **mint mismatch** (exit 3), **dest frozen** (exit 17).
  12. **Burn insufficient** (exit 1 — the balance guard's twin on the arm
      that decrements supply) and **Burn frozen** (exit 17).
  13. **TransferChecked decimals mismatch** (exit 18 — the check the *Checked
      family exists for) and **explicit-mint mismatch** (exit 3 — vs the
      provided mint account, distinct from Transfer's src-vs-dest compare).
  14. **CloseAccount nonzero balance** (exit 11, NonNativeHasBalance).
  **FINDING — the first REQUIRES-without-ENFORCES on a canonical program:**
  p-token does NOT enforce a destination-balance overflow check on Transfer.
  Where SPL Token uses `checked_add(...).ok_or(TokenError::Overflow)`, the
  p-token binary WRAPS the destination amount mod 2^64 (verified against
  mollusk: dest = u64::MAX-100 + 250 transfer succeeds on both engines with
  the dest balance at 149). The check is protected only by the global supply
  invariant (balances sum to supply ≤ u64::MAX, upheld by MintTo), not by the
  Transfer arm. Pinned as `p_token_transfer_dest_overflow_wraps_on_both` in
  diff_mollusk.rs so a future p-token that adds the check surfaces as a diff.
  This is exactly the gap class the library exists to expose: sound under an
  invariant that lives in a DIFFERENT arm.
  The routing-only half-guard (`H3dBalanceGuard.lean`,
  `p_token_balance_insufficient_routes_to_error`) predates and is subsumed by
  the full balance guard. `EnforcedFault` + `enforcedFault_of_routes_then_handler`
  remain the fault-channel mode (no p-token instance; pinocchio enforces via
  clean nonzero exits, hence `EnforcedError`).

## Catalog roadmap

Driven bottom-up: prove a guard on a proven arm, let it dictate the predicate /
recognizer shapes.

1. **SPL Token (in progress).** DONE: Transfer (16 guards), MintTo (5: supply
   overflow, fixed supply, authority mismatch, mint mismatch, dest frozen),
   Burn (2: insufficient, frozen), TransferChecked (2: decimals, explicit
   mint), CloseAccount (1: nonzero balance). Plus one pinned NON-guard
   (Transfer dest overflow wraps — see the finding above; its enforcing
   counterpart, MintTo supply overflow, is proven). Remaining candidates:
   - wrong data_len (≠ 165): NOT a simple flip — the 305 `jne` targets the 312
     generic account parser (slow path), not an error route; the failure
     surfaces later. Needs its own trace study.
   - deeper per-arm coverage: Burn authority tri-case + delegated-amount,
     TransferChecked frozen/balance legs, CloseAccount authority legs, the
     Approve/Revoke/SetAuthority/FreezeAccount/ThawAccount arms.
   - Burn supply-underflow side: balance ≤ supply invariant means the burn
     subtraction cannot underflow supply; worth a wrap-vs-check probe like
     the Transfer dest add (is the mint.supply -= amount checked?).
2. **Signer/owner DEFERRED, with reason.** The p_token signer check is NOT a clean
   guard: its proven non-signer branch *continues to the effect* (pinocchio's
   delegate-authority path, `H3fSignerExit`), so a naive "signer enforced" guard is
   false. An honest signer guard must model the delegate alternative and is
   materially deeper. p_token also performs no program-owner check (the runtime /
   caller owns that). So balance and frozen checks come first.
3. ATA, System program, Token-2022, common Anchor patterns.

Lib boundary: the guard *notion* lives in the SVM lib (`Patterns/Guards.lean`);
concrete guards reusing proven arms live in the Examples lib
(`examples/lean/PToken/...`), since Examples imports SVM, not the reverse.

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

- **Full `EnforcedFault` for the balance check**: compose the routing guard with a
  fault spec for the error handler at `h3dErrPc` (the shared `mov r0,err; ja; exit`
  exit, via `errorExit*` in `Terminating.lean`). Needs the handler CodeReq and a
  check of abort-vs-fault typing.
- CFG domination for L3 all-paths enforcement (build on `dispatch_routing_complete`,
  currently on the parked `dispatch-completeness` branch).
- An honest signer guard that models the pinocchio delegate-authority path.
- `Pubkey ↔ ByteArray` bridge, to give a `Pubkey`-typed `isPdaPubkey`
  (`SVM/Solana/Pda.lean:16` notes this is not yet built).
- Multi-account input-block locator (the `nonDupBlockSize` stride walk) if
  predicates need to address the Nth account rather than a caller-supplied base.
