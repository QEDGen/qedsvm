# Refinement descriptor (the qedgen <-> qedsvm seam)

Status: **v3, prototype**. Single-field constant deltas (any positive literal) and single-field
parameter deltas with checked argument bindings are wired end to end; the schema is versioned so the surface can grow without
silent mis-consumption.

A refinement descriptor is the declarative obligation that crosses the seam between qedgen
(the producer, which lowers a `.qedspec` to it) and qedlift (the consumer, which discharges it
against the compiled bytes). It is the byte-level analogue of the spec-model obligations qedgen
already feeds Kani/proptest. The design rationale and ownership model are in
[`DEVEX_QEDSPEC_GAP.md`](./DEVEX_QEDSPEC_GAP.md) ("Separation of concerns").

This is a **producer/consumer contract**, modeled on `qedmeta.toml` (which qedrecover produces
and qedlift consumes): versioned, fail-closed, and neither tool depends on the other's
internals. The contract is the JSON shape below; qedlift's `RefinementDescriptor`
(`qedsvm-rs/qed-artifacts/src/lib.rs`) is the shared contract.

## Principle: the seam is name-level

The operation carries **named semantics** (which field a handler mutates, by what op,
and the property). It does **not** carry argument byte offsets. Offsets are *shape*, and shape is the
IDL's job: qedlift resolves the account layout from the IDL by `account` name through the same
`qed-analysis` parser the rest of the lift uses. The descriptor never carries qedspec syntax or
Lean tactic text either: qedlift *generates* the Lean from the descriptor.
Schema v3 additionally declares the input instance's account lengths and tracked
account index, from which the consumer derives serialized-input positions.

## Schema

```jsonc
{
  "schema_version": 1,          // contract version; see "Versioning" below
  "account": "vault",           // IDL account name; its shape is resolved from the IDL
  "handler": "increment",       // optional: qedspec handler, provenance only
  "mutated": "total",           // a field NAME (not an offset); resolved via the IDL
  "op": { "add_const": 1 }      // constant credit (v1; any positive literal k)
  // Bound runtime credit uses schema v3 + input_layout; see the example below.

  // OPTIONAL fallback for fixtures / sBPF specs with no IDL: an inline layout. When present,
  // the shape is taken from here instead of the IDL. Field kinds: "pubkey" | "u64" | "byte" |
  // "bytes" (with "width_bytes" for "bytes").
  // "layout": [ { "offset": 0, "kind": "u64", "name": "total" } ]
}
```

| Field | Required | Meaning |
|---|---|---|
| `schema_version` | no (default 0) | Contract version. `> DESCRIPTOR_SCHEMA_MAX` is refused fail-closed. |
| `account` | yes | IDL account name to resolve the shape from (or a label when `layout` is inline). |
| `handler` | for `add_param` | Selects the IDL instruction for parameter binding. Provenance only for `add_const`. It does not prove dispatch completeness. |
| `mutated` | yes | Name of the mutated field. Resolved to an offset/kind via the layout (IDL or inline). |
| `op` | yes | The mutation. `{ "add_const": k }` (k >= 1, schema v1+) or `{ "add_param": "name" }` (parsed since v2, bound refinement requires v3). |
| `layout` | no | Inline shape fallback when no IDL exists. Absent = resolve from the IDL by `account`. |
| `input_layout` | for `add_param` | Schema v3 aligned Solana input layout: `account_data_lengths` for every non-duplicate account in order, and `account_index` for the tracked account. |

Bound parameter example:

```json
{
  "schema_version": 3,
  "account": "vault",
  "handler": "deposit",
  "mutated": "total",
  "op": { "add_param": "amount" },
  "input_layout": { "account_data_lengths": [41], "account_index": 0 }
}
```

The IDL must define `deposit.arguments`, including a direct little-endian `u64`
argument named `amount`. Offsets include all preceding serialized arguments
(including a discriminator argument). Only fixed-width numbers, public keys,
fixed-count arrays, and fixed-size wrappers are supported before the parameter.
Unknown or variable-width prefixes, duplicate instruction/argument names, and
non-u64 parameters are rejected.

The input layout is an **explicit assumption**: the caller supplies a full aligned,
non-duplicate account layout. It is not inferred from a trace, and QEDSVM does not
prove runtime account counts or data lengths equal that declaration. Duplicate
accounts and variable layouts are outside this binding mode. The lift must start
at PC 0 with the initial r1 available as its input pointer.

For the example, account data starts at input+96, `total` at input+128, and
instruction data at input+10400. The emitter checks that the increment operand
is the initial u64 read at input+10400, and the write targets input+128. Account
codec fields are expressed relative to input r1, so `ensures` uses field offset
128. This binding is a front-end check against IDL/layout assumptions; Lean
checks the emitted concrete-address theorem.

## Consumer behavior (qedlift)

Invoke with `--descriptor <path>` (single-arm mode). When a descriptor is present it **wins
over `--arm-name`**, and the hardcoded `refine_registry` is bypassed entirely.

1. **Load + version-gate.** Refuse `schema_version > DESCRIPTOR_SCHEMA_MAX` (fail-closed).
2. **Resolve shape.** Inline `layout` if present, else `resolve_layout(sidecar, idl, account)`
   (the shared `qed-analysis` path). Pass the IDL with `--idl`.
3. **Soundness checks against the bytes** (the descriptor must not misdescribe the program):
   - the lift's mutated offset must equal the offset of the named `mutated` field;
   - the lift's observed delta must equal `op.add_const`.
   - for `add_param`, the operand's initial memory address must match the named
     argument's IDL offset within serialized instruction data; the destination
     must match the selected serialized account's field.
   Either mismatch -> no refinement is emitted (it refuses rather than emit a false statement).
4. **Emit.** Build the layout-general `AsmRefinesFieldUpdate` (own the mutated `u64`, frame the
   rest, reshape coarse->fine via `account_agg`/`codecCoarse_eq_fine`), plus the qedgen
   `ensures`-shape (`u64FieldAt off post = u64FieldAt off pre + k`) discharged by
   `qedsvm_discharge`. Output is `<Module>Refinement.lean`, sorry-free.

## Versioning

`DESCRIPTOR_SCHEMA_MAX` in `qed-artifacts` is the newest schema this qedlift understands. A newer
descriptor is refused, exactly like `load_qedmeta`: a newer schema may carry semantics this
consumer would silently mis-handle, so it fails closed. The qedsvm version pinned in the
consumer's lakefile is effectively the contract version; bump `schema_version` in lockstep with
the producer (qedgen) when the surface below changes.

Legacy v0-v2 descriptors still parse. Constant operations retain their behavior;
parameter refinements require v3, an IDL and `input_layout`. Older parameter
descriptors return `unsupported / missing_parameter_binding`, never `emitted`.

## Refinement outcomes

`LiftResult.refinement_outcome` is serializable and independent of raw lift success:

| Status | Meaning |
| --- | --- |
| `not_requested` | No descriptor or registry arm was requested. |
| `emitted` | The refinement module was generated; Lean has **not** been run by qedlift. |
| `rejected` | The requested obligation conflicts with the available layout or bytecode evidence. Includes a typed `reason` and diagnostic `message`. |
| `unsupported` | Required binding information or a supported emission shape is unavailable. Includes `reason` and `message`. |

The single-arm CLI writes `refinement outcome: {JSON}` to stderr. If a descriptor
was requested and its refinement was not emitted, it exits unsuccessfully before
writing/streaming artifacts. The library still returns the raw lift for inspection.
Consumers must require `emitted` **and** a successful Lean check of the generated
modules before calling a property verified. Existing output files from earlier
runs are not proof of success for a failed command.

## Scope and roadmap

In scope: a single mutated `u64` field credited by a positive constant (`add_const: k`, schema
v1) or a bound runtime parameter (`add_param: name`, schema v3), with multi-field framing of untouched
`pubkey` / `u64` / `byte` fields and whole-`bytes` framing as one opaque gap.

Not yet (will bump the schema): subtraction; multi-field writes; split-blob layouts in the
descriptor path (the registry path has it); quantified / conservation / liveness properties
(no byte-level path yet). Argument bindings currently support direct u64 reads
at fixed input-relative addresses. Dynamic pointer reconstruction and other
argument types require further support.

**Producer + driver:** the `qedgen descriptor` subcommand (qedgen repo,
`crates/qedgen/src/descriptor.rs`) emits this JSON from a real `.qedspec`, and `qedgen discharge`
chains the whole thing into one command (build descriptor -> shell out to `qedlift --descriptor`
-> verdict). The chain `.qedspec -> qedgen -> qedlift --descriptor -> proof` runs end to end and
reproduces the committed `VaultDescriptorRefinement.lean` byte-identically. What remains is
folding the per-handler verdict into qedgen's aggregate trust report and widening the op surface.

## Examples

Name-level (the principled form; shape from the IDL):

```jsonc
{ "schema_version": 1, "account": "vault", "handler": "increment",
  "mutated": "total", "op": { "add_const": 1 } }
```

Inline-layout fallback (no IDL, e.g. the degenerate `counter.so`):

```jsonc
{ "schema_version": 1, "account": "Counter", "handler": "increment",
  "mutated": "counter", "op": { "add_const": 1 },
  "layout": [ { "offset": 0, "kind": "u64", "name": "counter" } ] }
```

Worked fixtures: `qedsvm-rs/tests/fixtures/{vault,counter}.descriptor.json`, pinned by
`descriptor_refinement_is_mechanically_emitted` and `descriptor_rejects_newer_schema`.

## Whole-transition mode (#40)

`--transition --descriptor <json> --output-dir <dir>` lifts every PATH of the
program — one discovered `<stem>_<path>.pcs` trace per path, captured from
real runs beside the `.so` — and emits:

- one lift module per path, each carrying a mechanically-emitted
  `*_transition_path` corollary (`AsmRefinesTransitionPath`): the running
  triple composed with the shared `.exit` via `cuTripleWithinMem_seq_exit`,
  terminating with that path's exit code, the descriptor's tracked account
  codec going preFields → postFields (a preservation path has them equal,
  with cells outside the path's footprint framed through the lift);
- the bundle theorem (`<Stem>Transition.lean`): ONE statement covering every
  path under its branch guards, binders canonically renamed (tracked cells →
  descriptor field names, the `add_param` operand cell → the param name).

Parameter renaming is performed only for a validated v3 binding. Legacy guarded
fixtures still produce raw observed-transition bundles with unnamed operand
binders; these are not successful discharges of a named parameter obligation.
Transition bundling does not upgrade `refinement_outcome` or establish all-path coverage.

With a v3 `add_param` descriptor, every path uses the declared account-data base
and IDL argument location, including rejection paths that do not write the
account. A mutation must match the selected field and argument cells. Arithmetic
assumptions such as non-overflow stay inside the relevant path's implication;
they do not exclude overflow rejection from the bundle. Return paths support
pubkey fields whose aligned `u64` limbs are read but preserved. Unread limbs are
framed, so a mismatch can reject after reading only part of the key. Pubkey
mutations and partial-width reads fail closed; fault paths still require framed
pubkey fields.

`sbpfv3_vault_deposit.descriptor.json` exercises a 41-byte vault with owner,
total, and bump fields. Its four captured paths cover success, zero amount,
overflow, and an unknown discriminator. `VaultDepositTransitionWitness.lean`
instantiates all four checked branch proofs, including overflow at `u64::MAX`.

`sbpfv3_vault_authorized.descriptor.json` adds a checked two-account schema and
owner signature checks. Its 21 captured cases include a mismatch in each owner
limb, missing signature, malformed instruction/account shapes, and overflow.
`AuthorizedVaultTransitionWitness.lean` instantiates every captured branch.
`AuthorizedVaultCoverage.lean` proves termination and the classified vault
postcondition for all inputs satisfying its common `[41, 0]` layout, word bounds,
memory regions, and 64-CU execution precondition. This fixture-specific theorem
does not change the captured-path scope of transition bundles in general.

A path whose walk ends in a typed abort/panic fault (the `abort` /
`sol_panic_` syscalls) gets an `AsmRefinesTransitionFault` corollary instead
(`*_transition_fault`, composed via `cuTripleWithinMem_seq_fault_pure`):
typed `.abort` error channel, tracked codecs owned in the pre, no post (a
faulted instruction is rolled back wholesale). The bundle mixes obligation
kinds freely.

A path ending in an OOB syscall fault gets the `.accessViolation` variant:
the tail is the per-syscall `*_faults_oob` triple, frame_right-extended to
the prefix remainder and composed via the Mem-Mem `cuTripleWithinMem_seq_fault`
— the bundle conjunct's region requirement is `prefix rr ∧ region OOB`.

Fail-closed: blob fields, unsupported pubkey reads/mutations, call-local prefixes, and
cross-path binder conflicts skip emission with a stderr note. Worked
fixtures: `guarded_counter.descriptor.json` (+
`guarded_counter_{abort,success}.pcs`), the fault-path
`guarded_abort.descriptor.json` (+ `guarded_abort_{panic,success}.pcs`), and
the OOB-path `guarded_oob.descriptor.json` (+ `guarded_oob_{oob,success}.pcs`),
pinned by `guarded_{counter,abort,oob}_transition_is_mechanically_emitted`.

### Transition outcome (#70)

Transition mode writes one `transition outcome: {JSON}` line to stderr, also
when the run fails, so a caller gets a per-path verdict without parsing the
generated Lean:

```json
{"schema":1,"status":"emitted","bundle":"GuardedCounterTransition","paths":[
  {"label":"abort","module":"GuardedCounterAbort","status":"emitted","kind":"return","exit_code":1,"tracked_written":false},
  {"label":"success","module":"GuardedCounterSuccess","status":"emitted","kind":"return","exit_code":0,"tracked_written":true}]}
```

- `label` is the `<label>` of the `<stem>_<label>.pcs` trace.
- `kind` is `return` (with `exit_code` and whether the descriptor's tracked
  field was written) or `fault` (with `vm_error`: `abort` or
  `access_violation`). A spec rejection (`requires C else E`) is usually a
  `return` with a non-zero exit code and no tracked write, as on
  `guarded_counter`'s `abort` path above, not a `fault`.
- A path that is not emitted carries `status`, `reason` and `message`
  instead of a kind. The reason is the exact point where the transition
  emitter fell closed. `rejected` means the binary contradicts the
  descriptor (`mutation_mismatch`: a tracked field changes outside the
  descriptor op). `unsupported` means the shape is not wired:
  `missing_layout`, `unsupported_shape` (the message names the shape, such
  as a blob field or a path ending in a CPI invoke), `binder_conflict` (a
  framed field name collides with a lift binder), `trace_unreadable`,
  `lift_failed`, or `symbolic_exit_code` (a return whose exit code is not a
  constant).
- Every path is attempted. If any is not emitted, top-level `status` is
  `rejected` (some path was rejected) or `unsupported`, no bundle is
  written, and the command exits unsuccessfully. Run-level failures carry a
  top-level `reason`: `too_few_traces` (fewer than two traces) or
  `bundle_failed` (the message names the conflicting hypothesis).
- `schema` is bumped on any breaking change to this shape.

As with `refinement outcome`, `emitted` means generation succeeded; Lean must
still check the modules.
