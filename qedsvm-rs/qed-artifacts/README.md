# qed-artifacts

Shared, versioned file-format contracts for qedsvm's Rust proof tools.

The crate owns the Rust representations of:

- `qedmeta.toml`, produced by `qedrecover` and consumed by `qedlift`;
- qedsvm overlays and the Codama IDL subset used during recovery;
- refinement descriptors produced from specifications and consumed by `qedlift`.

Schema loaders fail closed when an artifact declares a version newer than the
consumer supports. Tool-specific analysis and Lean rendering stay in their own
crates; this crate contains contracts and validation only.

Compatibility is explicit through `SchemaCompatibility`:

| Version | Behavior |
| --- | --- |
| Missing / `0` | Accepted as historical unversioned input. |
| Older than current | Accepted as legacy input; fields introduced later use their documented defaults. |
| Current | Accepted with the complete current contract. |
| Newer than current | Rejected fail-closed with `ArtifactError::UnsupportedSchema`. |

Canonical v1, v2, and future-schema fixtures live in `tests/fixtures`. The
`qed-artifacts`, `qedrecover`, and `qedlift` test suites all consume those same
files so producer and consumer compatibility cannot drift independently.

Descriptor schema v3 adds `input_layout` (ordered non-duplicate account data
lengths and tracked account index). Together with the handler's Codama IDL this
lets qedlift bind a parameter to its serialized instruction-data address.
Legacy parameter descriptors still parse, but cannot emit a bound refinement.
See [the descriptor contract](../../docs/REFINEMENT_DESCRIPTOR.md).
