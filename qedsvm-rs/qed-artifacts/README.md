# qed-artifacts

Shared, versioned file-format contracts for qedsvm's Rust proof tools.

The crate owns the Rust representations of:

- `qedmeta.toml`, produced by `qedrecover` and consumed by `qedlift`;
- qedsvm overlays and the Codama IDL subset used during recovery;
- refinement descriptors produced from specifications and consumed by `qedlift`.

Schema loaders fail closed when an artifact declares a version newer than the
consumer supports. Tool-specific analysis and Lean rendering stay in their own
crates; this crate contains contracts and validation only.
