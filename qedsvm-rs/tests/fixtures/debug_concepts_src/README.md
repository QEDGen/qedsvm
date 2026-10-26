# Debug concept-map fixture

A type-layout and inline-DWARF fixture; it is not a Solana account deserializer.
Do not infer account/input semantics from its `Account` source type.

Built on macOS with `cargo-build-sbf 4.3.0`, pinned `platform-tools v1.57`,
`rustc 1.95.0-dev (ae660768a 2026-08-17)`, architecture `v0`, release profile
`debug=2`, `strip=false`. The limited pair uses the same source with
`CARGO_PROFILE_RELEASE_DEBUG=1`. The V3 pair builds the same full-debug profile with `--arch v3`; its `.text`
starts at virtual address `0x100000000`, which must not undergo V0 address
unsplitting. The source profile deliberately defaults to
full debug: limited debug cannot supply the requested struct/enum DIEs.

Reproduce from repository root:

```sh
qedsvm-rs/tests/fixtures/build-debug-concepts.sh
```

SHA-256 of committed files:

| File | SHA-256 |
| --- | --- |
| `debug_concepts.so` | `59e62b350b40eb31f69fe5508f85e822c1ea1c66ace914828e97ca97071dbd08` |
| `debug_concepts.debug` | `3bcbe33a849d7aa1d824c069053bf9744cf5db4d25171803e84dc412e68c3840` |
| `debug_concepts_limited.so` | `59e62b350b40eb31f69fe5508f85e822c1ea1c66ace914828e97ca97071dbd08` |
| `debug_concepts_limited.debug` | `08ad4d80f77d5837851ad1b82fbe085d0e673dd591bbc31dda52e80f26ebaffa` |
| `debug_concepts_v3.so` | `1bf969899f21336caccaa9a3337a1b4920ce49bfbe686cb7970bb1806351fb6c` |
| `debug_concepts_v3.debug` | `79eb509333a7f43457a438a100447f1891c781f66e55afd874b63034b1cd2e9c` |

The three same-build `.text` pairs are independently checked by the reader tests.
A same-sized mutated deployment byte rejects the debug labels. `llvm-objdump`
shows entrypoint slots `[0,20)`, with `lddw` at 0 and 14, followed by
`signed_error` slots `[20,22)`; the expected logical ranges are `[0,18)` and
`[18,20)` respectively.
