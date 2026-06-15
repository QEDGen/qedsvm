# Lift coverage matrix: what an arbitrary `.so` + IDL gets you today

Date: 2026-06-05
Status: reference for the current lift/recover coverage
Verified against: `1df62c1` (`SVM/SBPF/SpecGen.lean`, `qedsvm-rs/src/bin/qedlift.rs`, `SVM/SBPF/ISA.lean`)
Related: [PIPELINE.md](PIPELINE.md), [API.md](API.md)

This is the honest boundary of the `.so` (+ Codama IDL, + trace) to machine-checked-proof
pipeline. The headline: the **raw lift to a Hoare triple is broad**, but the **mechanical
end-to-end story (raw triple to abstract refinement, no hand-written Lean) is narrow** and
gated on (a) a concrete execution trace and (b) the program fitting one of a handful of codec
shapes. This is not a general decompiler-verifier for an arbitrary binary yet, and the
boundaries are sharp.

A useful mental model is four independent axes. A program is only "fully mechanical" if it
clears all four: every instruction modeled, single happy path, only modeled syscalls, and a
registered codec shape.

## Legend

| Mark | Meaning |
| --- | --- |
| ✅ | Mechanical: lifts end-to-end with no hand-written Lean. |
| 🟡 | Triple-only / manual path: lifts the raw triple, but via the `sl_block_iter` manual-spec route or with no abstract-refinement meaning attached. |
| 🟠 | Hand-authored: needs new Lean (a MIR intrinsic + abstract triple + refinement predicate + the first per-program proof). |
| ❌ | Unmodeled in the proof layer. May still execute in the diff-tester against mollusk/agave (that is conformance, not a proof). |

## Axis 1: instruction semantics (raw lift)

Broad. The symbolic executor plus `SpecGen` cover the common compute opcodes. The real gaps
are few and named.

| Class | Status | Notes |
| --- | --- | --- |
| ALU64 imm+reg (`mov add sub mul and or xor lsh rsh arsh neg`) | ✅ | Full auto-dispatch via `sl_block_auto`. |
| ALU32 imm+reg (same ops, zero-extended) | ✅ | Same. |
| `div` / `mod` (64/32, imm+reg) | 🟡 | Modeled in the executor; carries a `divisor != 0` side hypothesis, so no `sl_block_auto` auto-dispatch. Rides the emitted `sl_block_iter` manual-spec path. |
| Loads `ldxb/h/w/dw`, `lddw` | ✅ | Width-specific value bounds surfaced as side conditions. |
| Stores, reg source `stxb/h/w/dw` | ✅ | |
| Stores, imm source `stb/sth/stw/stdw` | ✅ | Wired at `SpecGen.lean` via the `st{b,h,w,dw}_spec` wrappers. All four widths; the `sth`/ST_H_IMM gap closed 2026-06-10 (pinned by `halfword_store.so`: diff-test + lift). |
| Unconditional jump `ja` | ✅ | |
| Conditional jumps `jeq`/`jne`, imm src, not-taken | ✅ | Auto-dispatch at `SpecGen.lean:337-345`. |
| Conditional jumps, taken branch | 🟡 | Emitted via `sl_block_iter` (`use_block_iter` when any branch is taken or a call is present). |
| Conditional jumps, reg src or other ops (`jgt jlt jsgt jset` ...) | 🟡 | Specs exist in `Jump.lean`; no `sl_block_auto` dispatch (`SpecGen.lean:232` rejects non-imm src). Manual path only. |
| `call_local` + `exit` (nested return) | ✅ | Frame push/pop modeled; r6..r10 restored. |
| `callx` (indirect call) | 🟡 | Spec exists (`ControlFlow.lean`); no `SpecGen` dispatch. |
| Any other opcode | ❌ | Executor errors `opcode 0x.. not yet modelled`; Lean errors `SpecGen.lean:398`. |

**Failure mode is clean.** An unmodeled opcode stops `qedlift` before it emits, or fails Lean
elaboration. Nothing is silently lifted wrong.

## Axis 2: control flow

Single happy path only. The walker is a single-path symbolic executor, not a CFG analyzer.

| Shape | Status | Notes |
| --- | --- | --- |
| Straight-line block | ✅ | |
| Forward unconditional jump | ✅ | |
| Discriminator dispatch cascade (N-arm) | ✅ | One arm per invocation; the dispatcher is re-walked fresh per arm. Resolved by `--target-disc` or `--trace`. |
| Internal call / return | ✅ | |
| Loops (back-branch) | 🟡 → ❌ | No general support and no loop invariants. A trace gives bounded unrolling to the trace length only. A defaulted back-branch spins to `walk_cap` and errors. |
| Path merge / multi-arm-at-once | ❌ | No joins. No "these N arms cover the whole program" theorem; each arm is an independent triple. |

## Axis 3: syscalls (proof layer)

Narrow. This is the largest runtime-vs-lift divergence. The ISA enumerates ~40 syscalls
(`SVM/SBPF/ISA.lean`); the lift models 5.

| Syscall | Lift (proof) | Notes |
| --- | --- | --- |
| `sol_log_` | ✅ | `qedlift.rs:4261`. |
| `sol_memset_` | ✅ | 3-register shape (dst/fill/count), `qedlift.rs:4249`. |
| `sol_get_sysvar` (generic) | ✅ | Opaque return + CU bound, `qedlift.rs:4255`. Actual sysvar contents not modeled. |
| `sol_invoke_signed_rust` (CPI) | 🟡 | `qedlift.rs:4273`. Modeled as "r0 <- 0, envelope returns"; the callee's effects are NOT verified. |
| `sol_invoke_signed_c` (CPI) | 🟡 | `qedlift.rs:4279`. Same caveat. |
| Hashing (`sha256 sha512 keccak256 blake3 poseidon`) | ❌ | ISA only. |
| Curve ops (`secp256k1_recover`, `curve_*`, `alt_bn128_*`, `big_mod_exp`) | ❌ | ISA only. |
| PDA (`create_program_address`, `try_find_program_address`) | ❌ | ISA only. |
| Memory (`memcpy memmove memcmp`) | ❌ | ISA only. |
| Return data (`get_return_data`, `set_return_data`) | ❌ | ISA only. |
| Sysvar getters (`clock rent epoch_schedule` ...) | ❌ | ISA only; only the generic `sol_get_sysvar` is modeled. |
| Introspection (`remaining_compute_units`, `stack_height`, `sibling_instruction`) | ❌ | ISA only. |
| `sol_alloc_free_` (heap allocator) | ❌ | Deprecated; the heap is treated as ordinary `↦U64` memory instead (see the `HeapSL` predicates). |

A ❌ here means "no proof obligation", not "cannot run". The diff-tester executes the real
binary against mollusk/agave, so these syscalls run during conformance; they just have no
modeled meaning in the lifted theorem.

## Axis 4: refinement / codec (abstract meaning)

Narrow and IDL-gated. `CodecKind = { Token, Mint, Counter, Vault }` (`qedlift.rs:2868`). The
registry (`refine_registry`, `qedlift.rs:2876`) maps arm names to obligations:

| Arm name(s) | Obligation | Codec(s) | Status |
| --- | --- | --- | --- |
| `Transfer`, `TransferChecked` | `AsmRefinesTokenTransfer` | Token, Token | ✅ |
| `MintTo` | `AsmRefinesTokenMintTo` | Mint, Token | ✅ |
| `Burn` | `AsmRefinesTokenBurn` | Token, Mint | ✅ |
| `counterIncrement` | `AsmRefinesCounterIncrement` | Counter (single u64, coarse = fine) | ✅ |
| `VaultIncrement` | `AsmRefinesFieldUpdate` | Vault (layout-general field list) | ✅ |
| heap allocation | `<Module>_allocates` corollary | `heapBumpPtr` / `heapBlockU64` | ✅ |
| anything else | none | — | 🟠 |

The `Vault` / `AsmRefinesFieldUpdate` path is the genuinely layout-general one: any
`{Pubkey, u64, u8, blob}` field list is parsed from the Codama IDL (`parse_account_layout`)
into a `FieldVal` list and reshaped through `codecCoarse` / `account_agg`. Coverage:

- **Blob / option / enum / array fields** (`FieldKind::Bytes`): now mechanized. An untouched
  blob field is framed as a single opaque `.blob [.gap g]` (a free `ByteArray`, rendered
  `↦Bytes`); `account_agg` / `memBytesIs_segs` reshape it coarse to fine generically. Verified
  end-to-end by `Generated.VaultBlobRefinement` (sorry-free `lake build`, axiom-clean) and the
  `vault_blob_refinement_is_mechanically_emitted` pin test. The blob's byte size is not pinned
  in the obligation (the gap is universally quantified), so the theorem holds for any contents.
- **Non-constant deltas**: Counter and Vault both assume post = `NatAdd(InitMem, Const)`. A
  register-computed delta needs custom refinement.
- **Owned (handler-touched) bytes inside a blob**: the generic vault path only emits
  fully-framed blobs (a single `.gap`), not a mixed `[.byte, .gap, .u64, ...]` segment list. Two
  things to note. (1) For SPL token/mint this is already mechanized on the *token* path:
  `rest_segments` + `render_token_agg_module` discover the owned bytes of the `rest` region and
  emit the segment list, so the common touched-blob instance is covered. (2) The open gap is a
  *non-token* program that reads or writes scattered bytes inside an IDL-opaque field; the
  generic `account_agg` machinery already proves it (`memBytesIs_segs` over the mixed list), only
  the vault codegen does not yet discover owned bytes from the lift atoms and emit them. A
  read-only touched blob fits `AsmRefinesFieldUpdate` directly (pre == post for the blob); a
  written one makes the blob differ pre/post and shades into new state semantics.
- **New state semantics** (swap, deposit, anything not token/mint/+const-field): needs the full
  hand-authored stack: a `MirStmt` constructor + `runStep` clause + abstract triple + an
  `AsmRefines*` predicate + the first per-program proof.

## IDL consumption: derived vs fallback

The Codama IDL carries account layout only (field offsets, sizes, kinds). A TOML IDL carries
just discriminators for batch targeting, no layout, so it falls back to the hardcoded constants.

| Quantity | Derived from IDL | Fallback (when IDL absent / parse fails) |
| --- | --- | --- |
| Token rest-region start | `amount.offset + 8` | `72` |
| Token account size | `layout.size` | `165` |
| Mint supply offset | `supply.offset` | `36` |
| Mint rest offset | `supply.offset + 8` | `44` |
| Mint account size | `layout.size` | `82` |
| Vault field layout | fully IDL-driven `FieldVal` list | none: bails if IDL missing or account not found |

## Prerequisites for a non-trivial lift

1. **A concrete trace is effectively mandatory** beyond a single straight-line arm.
   Multi-arm dispatch needs `--target-disc` or `--trace` to choose the path, and
   syscall-vs-internal-call disambiguation only works in trace mode. In practice you need a
   runnable input fixture, not just the binary plus IDL. Capture is still manual (see
   PIPELINE.md seam 2).
2. **A Codama JSON IDL** for any layout-general (vault) or batch lift. Without it you are
   limited to the hardcoded token/mint/counter shapes.

## Bottom line: what an arbitrary program buys you

| Tier | Programs | Needs |
| --- | --- | --- |
| Fully mechanical, no hand Lean | SPL Transfer / TransferChecked / MintTo / Burn, Counter-increment, Vault `{pubkey,u64,u8,blob}` +const field update, heap-bump allocation | `.so` + trace; IDL for vault/batch |
| Raw triple only (no abstract meaning) | any straight-line / dispatch / bounded-trace arm over the modeled opcodes + 5 syscalls | `.so` + a concrete `--trace` |
| Needs hand-authoring | new intrinsic semantics, handler-touched bytes inside a blob, variable deltas, loops with invariants | new MIR intrinsic + triple + refinement + first proof |
| Not modeled at all | hashing, curves, PDA derivation, memcpy, return data, real CPI callee semantics, real sysvar contents | spec work in `SpecGen` + ISA |

Comprehensive and genuinely mechanical inside the token / mint / counter / vault / heap
envelope with a trace. Broad but trace-bound at the raw-triple level. Clearly bounded the
moment you hit a loop with an invariant, a real syscall (hash / curve / PDA / CPI), a
non-constant delta, or brand-new operation semantics.
