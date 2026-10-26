# Same-build debug concept map

`qed-analysis` reads source labels without Lean or program execution:

```sh
cd qedsvm-rs
cargo run -p qed-analysis --bin qed-concept-map -- \
  path/to/deployed.so path/to/unstripped.debug > program.concepts.json
```

The library entrypoint is
`qed_analysis::concept_map::ConceptMap::from_elf_bytes(deployed, debug)`.
`to_json()` emits deterministic, pretty-printed JSON. The CLI writes JSON only
on success, errors to stderr, and exits nonzero on failure.

Use the **same build's** stripped deployment artifact and unstripped ELF.
Extraction fails before producing labels unless their raw `.text` sections are
byte-identical and their sBPF versions agree. ELF64 little-endian EM_BPF and
EM_SBPF artifacts are accepted for the V0 and V3 versions currently modeled by
qedsvm. V0 uses the existing SBF split-address normalization; V3 retains its
full virtual addresses (including `.text` at `2^32`). Invalid/truncated instruction slots, malformed DWARF, and section read
errors fail extraction. The reader does not execute or verify instructions.

Build the deployment artifact itself with `[profile.release] debug = 2` and keep
its unstripped twin. `debug = 1` (limited) and `"line-tables-only"` do **not**
provide the types needed for member layouts and enum discriminants. Enabling
or changing debug information can change code generation; rebuilding a plain
release artifact with debug enabled is not a supported source of labels.
The committed full and limited fixture pairs are tested against their actual
platform-tools v1.57 outputs.

## JSON contract, version 1

- `schema_version`: `1`; reject unknown versions before consuming labels.
- `trust`: `"untrusted_debug_labels"`.
- `pc_convention`: `"logical_lddw_once"`. Every `range`/`ranges` value is a
  half-open `{start, end}` range in qedsvm's decoded instruction space, using
  `PcMap`. An `lddw` occupies one logical PC; its second slot is never a range
  boundary. The program-end boundary is the logical instruction count.
- `artifact`: SHA-256 of the entire `deployed` and `debug` input byte strings,
  SHA-256 of their common raw `.text`, text byte size, both text section virtual
  addresses, sBPF version, and logical instruction count. Recheck the deployed
  hash against the artifact being lifted. Keep this sidecar with its exact debug
  input if provenance is needed. A text hash alone is not deployment identity.
- `functions`: concrete subprograms and inline instances, each with a stable
  `id` (absolute `.debug_info` DIE offset), optional demangled `name`, `inlined`,
  nearest enclosing function `parent` ID, logical `ranges`, and optional inline
  `call_site` (`file`, `line`, `column`). Separate inline instances keep separate
  IDs even when their names match. Ranges need not be contiguous.
- `structures`: DIE `id`, optional source `name` and `byte_size`, and direct
  `members`. Each member includes optional `name`, constant `byte_offset`,
  `type_id`/`type_name`, `bit_size`, and `data_bit_offset`. A type reference may
  point to a non-exported base, array, pointer, or other type DIE; the sidecar is
  not a complete type graph. Duplicate source names are not merged.
- `enumerations`: DIE `id`, optional `name`, `byte_size`, underlying `signed`
  flag, and `variants` with optional `name` and decimal-string `value`.
  Decimal strings preserve negative and full-width unsigned 64-bit constants
  in JSON clients. These are source enum values, not inferred runtime return
  codes. Rust data-carrying/niche variant encodings are explicitly unsupported.
- `lines`: logical `range`, source `location`, and `inline_chains` of function
  IDs, outermost first. Line intervals split at function boundaries. Alternative
  overlapping chains remain separate; never concatenate them into one stack.
  Missing covering parents produce an `incomplete_inline_chain` diagnostic;
  the returned chain is explicitly partial.
  `call_site` on each inline function supplies the caller's location; the line
  table supplies the innermost location. No source files are read. Paths are
  DWARF strings and can be relative, remapped, or absent.
- `coverage`: availability of nonempty `debug_info`, `debug_line`, and observed
  struct/enum `type_entries`. These flags do not imply complete recovery.
- `diagnostics`: sorted, deduplicated `{code, entity, message}` records describing
  absent debug sections, missing types/names, unmapped ranges, unsupported
  offsets/variant encodings, and ambiguous coverage. Optional values are JSON
  `null`, never invented offsets, zero-valued discriminants, or fallback names.

Arrays follow deterministic DIE/line order (lines and diagnostics are sorted).
IDs are stable only for the exact debug artifact, not across rebuilds.

## Limits and trust boundary

Optimization can delete functions, members, lines, and enum variants. Missing
DWARF produces an explicitly partial sidecar; symbol-table guesses are not
substituted for source ranges. Abstract names are resolved through bounded
same-unit origin/specification references; cross-unit origin references can
leave a name absent. Separate/split DWARF files are not fetched. Nonconstant
member-location expressions are retained as unknown offsets, not evaluated.

A `structure_type` is **not evidence that it is an account**, nor that its memory
layout equals an account's serialized layout. A member offset is relative to
that source struct; DWARF alone does not connect it to the Solana input buffer,
a particular account index, or a deserializer's pointer. Similarly, source
functions are handler candidates, not proven dispatch instructions. Enum values
do not prove application error encodings. Any application-specific mapping
needs independent evidence and ambiguity handling in the consumer.

All labels and source paths are untrusted presentation proposals. Names do not
enter Lean proofs and must never establish a proof obligation or select a proof
success edge. Proofs continue to check the deployed bytecode independently.
This reader does not migrate any generators or implement issue #82.

## Fixture evidence

`debug_concepts_src` is a dependency-free `no_std` SBF program with a C-layout
`Account`, signed and unsigned error enums, nested `transfer`/`authorize` inline
frames, and two `lddw` instructions. Full debug recovers 48-byte `Account` member
offsets 0/32/40 and error values 7/42 and -3/5. Its 22 slots become 20 logical
instructions. A third pair exercises genuine high V3 text addresses. The `debug=1` twin retains line information and reports missing
type entries. This particular pair has identical full/limited deployment bytes;
that observation is not a code-generation stability guarantee.

Rebuild with `tests/fixtures/build-debug-concepts.sh`. The script uses the
cached pinned toolchain, disables global rustup override changes, checks each
new stripped/unstripped text pair through the reader, and refuses to overwrite
committed fixture bytes that drift. Toolchain and artifact hashes are recorded
in `tests/fixtures/debug_concepts_src/README.md`.
