# Refinement descriptor (the qedgen <-> qedsvm seam)

Status: **v1, prototype**. The single-field `+1` update class is wired end to end; the
schema is versioned so the surface can grow without silent mis-consumption.

A refinement descriptor is the declarative obligation that crosses the seam between qedgen
(the producer, which lowers a `.qedspec` to it) and qedlift (the consumer, which discharges it
against the compiled bytes). It is the byte-level analogue of the spec-model obligations qedgen
already feeds Kani/proptest. The design rationale and ownership model are in
[`DEVEX_QEDSPEC_GAP.md`](./DEVEX_QEDSPEC_GAP.md) ("Separation of concerns").

This is a **producer/consumer contract**, modeled on `qedmeta.toml` (which qedrecover produces
and qedlift consumes): versioned, fail-closed, and neither tool depends on the other's
internals. The contract is the JSON shape below; qedlift's `RefinementDescriptor`
(`qedsvm-rs/src/bin/qedlift/input.rs`) is the reference consumer.

## Principle: the seam is name-level

The descriptor carries **semantics only** (which named field a handler mutates, by what op,
and the property). It does **not** carry byte offsets. Offsets are *shape*, and shape is the
IDL's job: qedlift resolves the account layout from the IDL by `account` name through the same
`qed-analysis` parser the rest of the lift uses. The descriptor never carries qedspec syntax or
Lean tactic text either: qedlift *generates* the Lean from the descriptor.

## Schema (v1)

```jsonc
{
  "schema_version": 1,          // contract version; see "Versioning" below
  "account": "vault",           // IDL account name; its shape is resolved from the IDL
  "handler": "increment",       // optional: qedspec handler, provenance only
  "mutated": "total",           // a field NAME (not an offset); resolved via the IDL
  "op": { "add_const": 1 }      // the mutation; only add_const:1 is wired in v1

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
| `handler` | no | qedspec handler this obligation came from. Rendered in the proof's provenance comment; drives nothing. |
| `mutated` | yes | Name of the mutated field. Resolved to an offset/kind via the layout (IDL or inline). |
| `op` | yes | The mutation. v1: `{ "add_const": 1 }` only. |
| `layout` | no | Inline shape fallback when no IDL exists. Absent = resolve from the IDL by `account`. |

## Consumer behavior (qedlift)

Invoke with `--descriptor <path>` (single-arm mode). When a descriptor is present it **wins
over `--arm-name`**, and the hardcoded `refine_registry` is bypassed entirely.

1. **Load + version-gate.** Refuse `schema_version > DESCRIPTOR_SCHEMA_MAX` (fail-closed).
2. **Resolve shape.** Inline `layout` if present, else `resolve_layout(sidecar, idl, account)`
   (the shared `qed-analysis` path). Pass the IDL with `--idl`.
3. **Soundness checks against the bytes** (the descriptor must not misdescribe the program):
   - the lift's mutated offset must equal the offset of the named `mutated` field;
   - the lift's observed delta must equal `op.add_const`.
   Either mismatch -> no refinement is emitted (it refuses rather than emit a false statement).
4. **Emit.** Build the layout-general `AsmRefinesFieldUpdate` (own the mutated `u64`, frame the
   rest, reshape coarse->fine via `account_agg`/`codecCoarse_eq_fine`), plus the qedgen
   `ensures`-shape (`u64FieldAt off post = u64FieldAt off pre + k`) discharged by
   `qedsvm_discharge`. Output is `<Module>Refinement.lean`, sorry-free.

## Versioning

`DESCRIPTOR_SCHEMA_MAX` in `input.rs` is the newest schema this qedlift understands. A newer
descriptor is refused, exactly like `load_qedmeta`: a newer schema may carry semantics this
consumer would silently mis-handle, so it fails closed. The qedsvm version pinned in the
consumer's lakefile is effectively the contract version; bump `schema_version` in lockstep with
the producer (qedgen) when the surface below changes.

## v1 scope and roadmap

In scope (v1): single mutated `u64` field, `add_const: 1`, multi-field framing of untouched
`pubkey` / `u64` / `byte` fields, whole-`bytes` framing as one opaque gap.

Not yet (will bump the schema): deltas other than `+1`, subtraction, multi-field writes;
split-blob layouts in the descriptor path (the registry path has it); quantified / conservation
/ liveness properties (no byte-level path yet).

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
