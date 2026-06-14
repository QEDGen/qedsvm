# qedmeta — sidecar verification artifact (v0.1 draft)

## What it is

A small TOML file shipped alongside a compiled Solana program, hash-pinned
to its `.so`. The file carries everything a verifier needs to discharge a
proof obligation against the deployed binary: which entry points map to
which MIR intrinsics, the CU budget for each, the account layout, the
discriminator value, the dispatcher PCs, and the per-instruction CFG slice.

The file is **never embedded in the deployed binary**. On-chain bytes are
identical to a build that knows nothing about qedsvm. The sidecar lives
off-chain (GitHub release, IPFS, Arweave, a qedsvm registry).

Analogous to IDL, but for verification rather than client codegen.

## Why a sidecar

Rent on Solana is per-byte. Anything embedded in the deployed `.so`
costs deployers SOL for the lifetime of the program. Anchor's
`.solana.idl` section is the cautionary tale — projects routinely
strip it before deploy because of bloat (often 5-25% of program
size). qedmeta sidesteps that entire conversation: zero bytes added,
nothing to strip.

## Two production paths

qedmeta is the same format regardless of who emits it. Two emitters
exist:

### Compile-time emission (the canonical path) — qedgen

The expected production path. qedgen reads source-level annotations
(`#[qedgen::instruction(refines = "Mir.tokenTransfer", cu_budget = 76)]`
or equivalent), runs alongside `cargo build-sbf`, and emits the
sidecar from the *source* plus the linker's PC tables. The PCs in
the sidecar are exact (compiler knows them); the dispatcher and CFG
slice are derived from the build, not pattern-matched.

This is analogous to how Anchor emits its IDL from `#[program]`
annotations at build time.

The compile-time generator lives in the qedgen repo.

### Recovery fallback — qedrecover

For programs that *don't* use qedgen annotations (third-party
binaries, legacy code, programs whose source isn't accessible),
qedrecover scans the compiled `.so` plus an external IDL plus a
user-written overlay and produces the same qedmeta format
heuristically. PCs come from pattern-matching the dispatcher shape
in bytecode; the CFG slice comes from `solana_sbpf::Analysis`.

Recovery is fragile by design — codegen changes can break the
recogniser. But the brittleness is at build/sidecar-regeneration
time, not at verify time. A failing recovery is caught before the
sidecar ships, and the overlay can carry manual PC overrides as
escape hatches.

Both paths emit the same file. The verifier doesn't care which one
produced it.

## Verifier contract

A verifier consuming `(.so, .qedmeta)`:

1. Recomputes the SHA-256 of the `.so`; fails fast if it doesn't
   match `target.sha256` in the sidecar.
2. For each `[[instruction]]`, looks up `instruction.proofs.spec_module`
   + `.spec_theorem` in the Lean proof library.
3. Type-checks that theorem against the binary state at the recovered
   PCs (`dispatch_load_pc`, `arm_entry_pc`).
4. Verifies the CU budget claimed in `instruction.cu_budget` matches
   the CU bound proven by the theorem.

The verifier never re-runs recovery or re-derives PCs. It trusts the
sidecar's claims and proves the implication "if these PCs hold the
asserted shape, the program refines the intrinsic." The hash pin
keeps the trust well-founded: the sidecar is only valid against one
specific binary.

## Format reference

See `qedsvm-rs/tests/fixtures/p_token.qedmeta.toml` for a concrete
example. The schema (v0.1):

| Section | Purpose |
|---------|---------|
| `target` | Binary hash, program name/id, source provenance |
| `idl` | Hash-pin to the IDL the metadata was produced against (inline or external) |
| `[[instruction]]` | Per-instruction claim + recovered metadata + proof binding |
| `instruction.discriminator` | Discriminator value, width, format |
| `[[instruction.account]]` | One row per account in instruction-order |
| `instruction.recovered` | Build-time-frozen PCs and CFG slice |
| `[[instruction.idiom]]` | v0.2+: block-level idiom annotations (lever 4 from issue #11) |
| `[[instruction.tag]]` | v0.2+: happy/sad-path tagging from execution traces |
| `instruction.proofs` | Lean module/theorem that proves the claim |

Top-level fields:

| Field | Type | Description |
|-------|------|-------------|
| `schema_version` | int | Bumped on breaking changes. **v2** (issue #41): qedlift now CONSUMES `[instruction.recovered].arm_entry_pc` to seed/cross-check its walk instead of re-deriving the arm. v1 (or unset) sidecars still load — `recovered` is optional and its absence degrades to the disc-guided walk. A sidecar declaring a version newer than the consumer understands is rejected. |
| `spec_version` | string | Human-readable version tag (`"qedmeta/0.2"`) |

## Extension points reserved in v0.1

- **Idiom annotations**. The asm-side recogniser (lever 4 in the
  issue thread) shipped in qedrecover (`idioms.rs`) with a starter
  vocabulary: `u64_field_{increment,decrement}` (the balance-mutation
  triple), `error_propagation_check` (call whose r0 result is
  branch-tested), `read_discriminator` (the dispatch load). Tags are
  emitted as `idioms` in the recovered Lean metadata today; promoting
  them into `[[instruction.idiom]]` here is the remaining v0.2 step.

- **Happy/sad-path tags**. Empty `[[instruction.tag]]` array reserved
  for execution-trace-driven path classification. Each entry labels
  a block as `happy` / `error` / `shared` based on a mollusk trace.

Both are no-ops in v0.1 — readers ignore empty arrays. Schema is
forward-compatible with future field additions inside `instruction.*`
tables.

## Repo placement

This spec lives in qedsvm because both qedgen (compile-time) and
qedrecover (recovery-time) need to emit it. The qedgen-side
generator (the proc-macro / cargo plugin that reads source
annotations and produces qedmeta) belongs in the qedgen repo. The
verifier that consumes `(.so, .qedmeta)` lives in qedsvm.
