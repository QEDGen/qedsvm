# Coverage Boundary

Status: current lift/recover coverage
Related: [PIPELINE.md](PIPELINE.md), [API.md](API.md)

This document describes what the `.so + IDL + trace -> Lean proof` pipeline can verify. The raw Hoare-triple lift is broader than the fully mechanical abstract-refinement path. A program is fully mechanical only when it fits all required axes: modeled instructions, a single selected path, modeled syscalls, and a registered refinement/codec shape.

This is not a general verifier for arbitrary Solana binaries.

## Status Legend

| Status | Meaning |
| --- | --- |
| Mechanical | Emitted and checked without hand-written Lean for the supported shape. |
| Triple only | A raw `cuTripleWithinMem` theorem can be emitted, but no abstract refinement is attached. |
| Manual | Requires new Lean definitions, specs, or refinement code. |
| Unsupported | Not modeled in the proof layer. The program may still run in conformance tests. |

## Instruction Semantics

The symbolic executor and `SpecGen` cover common compute and memory instructions. Unsupported opcodes fail the lift or the Lean build.

| Class | Status | Notes |
| --- | --- | --- |
| ALU64 imm/reg: `mov add sub mul and or xor lsh rsh arsh neg` | Mechanical | Auto-dispatched through `sl_block_auto` where applicable. |
| ALU32 imm/reg: same operations, zero-extended | Mechanical | Same proof route as ALU64. |
| `div` / `mod` | Triple only | Modeled with a nonzero-divisor side condition; not fully auto-dispatched. |
| Loads: `ldxb`, `ldxh`, `ldxw`, `ldxdw`, `lddw` | Mechanical | Width-specific value bounds are surfaced as side conditions. |
| Stores, register source: `stxb`, `stxh`, `stxw`, `stxdw` | Mechanical |  |
| Stores, immediate source: `stb`, `sth`, `stw`, `stdw` | Mechanical |  |
| Unconditional jump `ja` | Mechanical |  |
| Conditional jumps, imm source, not taken | Mechanical | Auto-dispatched where supported by `SpecGen`. |
| Conditional jumps, taken branch | Triple only | Emitted through the iterative proof route. |
| Conditional jumps, register source or non-`jeq`/`jne` forms | Triple only | Specs exist for more jump forms than the automatic dispatcher handles. |
| `call_local` + `exit` | Mechanical | Models frame push/pop and callee return. |
| `callx` | Triple only | Spec exists, but codegen support is limited. |
| Other opcodes | Unsupported | Fail closed rather than emitting an unchecked theorem. |

## Control Flow

`qedlift` proves one selected path. It is not a whole-CFG verifier.

| Shape | Status | Notes |
| --- | --- | --- |
| Straight-line block | Mechanical |  |
| Forward unconditional jump | Mechanical |  |
| Discriminator dispatch cascade | Mechanical | One selected arm per lift, chosen by sidecar/targeting and optionally trace. |
| Internal call / return | Mechanical |  |
| Back-branch / loop | Triple only | A trace gives bounded unrolling for that concrete path only; no loop invariant is inferred. |
| Path merge / whole-program arm coverage | Unsupported | No theorem states that all possible arms or paths are covered. |

## Syscalls

The Lean ISA includes a broad syscall enum. The lift currently emits proof obligations for a narrower set.

| Syscall | Lift status | Notes |
| --- | --- | --- |
| `sol_log_` | Mechanical | Models the log call shape and CU bound used by generated lifts. |
| `sol_memset_` | Mechanical | Includes blob and split-cell shapes used by generated lifts. |
| `sol_get_sysvar` | Mechanical | Generic syscall plus the cell-shaped rent path used by generated lifts; not a full semantic model of every sysvar value. |
| `sol_invoke_signed_rust` | Terminal | The proof-facing CPI is the fail-closed `Cpi.exec` stub (audit C5), so an invoke ENDS the walk (`.unsupportedInstruction` typed-fault terminal); the lifted prefix's post owns the caller-side envelope cells (`cpiEnvelope`, see below). |
| `sol_invoke_signed_c` | Unsupported | Falls closed (no walker terminal registered for the C ABI yet). |
| `sol_sha256` | Mechanical | Single-slice success path: descriptor cells recover `(ptr, len)`, the digest is written to a framed `↦Bytes32` atom, `r0 := 0` (`call_sol_sha256_spec`). |
| Other hashing syscalls (`keccak256`, `blake3`) | Unsupported | No lifted proof obligation is emitted. |
| Curve/precompile syscalls | Unsupported (success) | No success triple. The OOB fault direction of `sol_secp256k1_recover` IS lifted as a `.accessViolation` `*_fault_correct` corollary (see Typed-Fault Corollaries). |
| `sol_create_program_address` | Mechanical | Single-seed success path (`call_sol_create_program_address_spec`); the off-curve case is a surfaced honest-conditional hypothesis, not a hidden assumption. |
| Other PDA syscalls (`sol_try_find_program_address`, multi-seed) | Unsupported | Same boundary. |
| `memcpy`, `memmove` | Mechanical | Two `↦Bytes` atoms (src readable, dst writable, disjoint); dst blob ← src, `r0 := 0` (`call_sol_mem{cpy,move}_spec`). |
| `memcmp` | Mechanical | Two `↦Bytes` inputs + a 4-byte `↦U32` output; result `memcmpResultU32 p1 p2 n` (`call_sol_memcmp_spec`). |
| `sol_set_return_data` | Mechanical | One `↦Bytes` input (`[r1, r1+r2)` readable, `r2 ≤ MAX_RETURN_DATA`) copied into the framed `↦ReturnData` atom; `r0 := 0` (`call_sol_set_return_data_spec`). |
| `sol_get_return_data` | Unsupported | Only the fault direction (`execGet_faults_oob`) is modeled; no success triple. |
| Dedicated sysvar getters | Unsupported (success) | Only the generic `sol_get_sysvar` success path is modeled. The OOB fault direction of `sol_get_clock_sysvar` IS lifted as a `.accessViolation` `*_fault_correct` corollary (see Typed-Fault Corollaries). |
| Introspection syscalls | Unsupported | Not emitted by `qedlift` as proof obligations. |
| `sol_alloc_free_` | Unsupported | Heap proofs use ordinary memory predicates instead. |

Unsupported here means "not verified by the lift", not "cannot execute". Diff tests can still run programs that use unverified runtime behavior.

## Typed-Fault Corollaries (termination)

When a lifted path terminates in a typed fault rather than a clean `exit`, the lift emits a `*_fault_correct` corollary of shape `cuTripleFaultsWithinMem … <VmError>`. This carries audit L1's typed fault channel (`exitCode = some e.toSentinel ∧ vmError = some e`), distinguishing a real VM fault from a clean exit that happens to return the same numeric sentinel. The corollary composes the running prefix (`<module>_lifted_spec`) with the terminal fault spec.

| Terminal | VmError | Status | Notes |
| --- | --- | --- | --- |
| `abort` / `sol_panic_` | `.abort` | Mechanical | Unconditional fault from any precondition; composed via `cuTripleWithinMem_seq_fault_pure` (`AbortCaller`). |
| OOB `sol_secp256k1_recover` | `.accessViolation` | Mechanical | Read-region guard (`containsRange r1 32 = false`); the prefix post is framed into the single-register fault-spec pre and composed via the Mem-aware `cuTripleWithinMem_seq_fault` (`OobSecp256k1`). |
| OOB `sol_get_clock_sysvar` | `.accessViolation` | Mechanical | Write-region guard (`containsWritable r1 40 = false`); single-atom prefix, fault spec applied directly (`OobClockSysvar`). |
| Other OOB syscalls | `.accessViolation` | Manual | Same recipe: a per-syscall `*_faults_oob` triple plus an emitter registry entry. Register-sized regions (e.g. `[r1, r1+r2)`) and a region register that is not the first post atom fall closed for now. |

OOB terminals are detected trace-side: a guarded syscall that does not return to `pc+1` on the trace is treated as the faulting terminal (static mode cannot distinguish success from fault).

## Abstract Refinement / Codec Coverage

Raw triples prove a selected bytecode path. Abstract refinements additionally connect that path to account-level state claims.

| Arm / shape | Predicate | Status |
| --- | --- | --- |
| SPL `Transfer` | `AsmRefinesFieldUpdates` (2 accounts) | Mechanical |
| SPL `TransferChecked` | `AsmRefinesFieldUpdates` (2 accounts) | Mechanical |
| SPL `MintTo` | `AsmRefinesFieldUpdates` (2 accounts) | Mechanical |
| SPL `Burn` | `AsmRefinesFieldUpdates` (2 accounts) | Mechanical |
| Counter increment | `AsmRefinesCounterIncrement` | Mechanical |
| Vault constant field update | `AsmRefinesFieldUpdate` | Mechanical |
| Whole-transition path (terminating, exit code + field pre→post/preservation) | `AsmRefinesTransitionPath` (#40) | Mechanical (`--transition`: discovered `<stem>_<path>.pcs` traces + descriptor → per-path `*_transition_path` corollaries + the bundle theorem; validated on `guarded_counter`) |
| Whole-transition FAULT path (typed abort/panic, codecs owned in the pre) | `AsmRefinesTransitionFault` (#40) | Mechanical (`*_transition_fault` via `cuTripleWithinMem_seq_fault_pure`; validated on `guarded_abort`, whose bundle mixes obligation kinds; OOB fault terminals fall closed) |
| Heap bump allocation | Heap corollary over `heapBumpPtr` / `heapBlock*` | Mechanical |
| SPL `CloseAccount` | Raw traced triple + generated balance-style corollary | Triple only |
| SPL `InitializeMint2` | Raw traced triple | Triple only |
| New operation semantics | New predicate/spec required | Manual |

Predicate selection can be **spec-driven**, not only registry-driven: a versioned, name-level `RefinementDescriptor` (`--descriptor`, see [REFINEMENT_DESCRIPTOR.md](REFINEMENT_DESCRIPTOR.md)) builds the layout-general `AsmRefinesFieldUpdate`, resolving field offsets from the IDL and bypassing the hardcoded 6-entry registry. Same proof, driven by a spec obligation rather than a Rust edit. The descriptor path covers a single-field `u64` credited by a positive constant (`add_const: k`) or a runtime parameter (`add_param: name`, the latter matched as `field += <runtime read>`); subtraction, multi-field writes, and split-blob layouts are not yet emitted on this path.

Input-region positions come from the loader-serialization offset algebra
(`SVM/Solana/InputLayout.lean`, #40 gap 3): `acctDataOff`/`acctFieldAddr`/
`instrDataOff` over the accounts' data lengths, decide-validated against the
diff-tested p_token lift anchors (`96`/`10600`/`21024`), with
`inputAccounts` stating transition accounts by account index. The CPI
envelope a caller hands `sol_invoke_signed` is `SVM/Solana/CpiEnvelope.lean`
(#40 gap 4): `cpiEnvelope` encodes the Rust-ABI `StableInstruction` cells and
`cpiEnvelope_reads` bridges a `holdsFor` witness to the runner's exact decode
reads. The per-call-site envelope theorem is worked END-TO-END on real
bytecode: `cpi_envelope_caller.so` (diff-tested CU-exact, invoking noop with
the callee program account passed — its instruction data sits at
`instrDataOff [0]`) lifts to a prefix ending AT the invoke, and
`CpiEnvelopeDemo.cpi_envelope_at_call_site` reshapes the prefix post into
`cpiEnvelope` — the invoke event stated against the binary. Remaining: the
32-byte pid byte-fold ↔ `pubkeyAt` limb bridge (ties `cpiEnvelope_reads` to
`cpiCallNextState`'s literal fold), and the C-ABI variant.

## Account Layouts

| Layout feature | Status | Notes |
| --- | --- | --- |
| SPL token account | Mechanical | Layout-general field list (mint/owner pubkeys, amount `u64`, split rest blob); no token-specific aggregation module (#25). |
| SPL mint account | Mechanical | Layout-general field list (preAuth blob with owned `.u64` segs, supply `u64`, rest blob); no mint-specific aggregation module (#25). |
| Counter account | Mechanical | Single `u64` field. |
| Vault-style field list | Mechanical | IDL-driven `{Pubkey, u64, u8, blob}` field lists through `codecCoarse` and `account_agg`. |
| Untouched blob fields | Mechanical | Framed as opaque `ByteArray` gaps. |
| Read-only owned bytes inside a blob | Mechanical for covered generated shapes | Split into byte/gap segments when the codegen recognizes the owned bytes. |
| Written bytes inside an otherwise opaque blob | Manual | Requires state semantics for how the blob changes. |
| Non-constant deltas | Manual | Existing counter/vault refinements assume constant addition. |

## IDL Requirements

Codama JSON IDLs carry discriminator and account-layout metadata. TOML IDLs are sufficient for simple batch targeting but do not provide layout-general account fields.

| Quantity | Codama JSON IDL | Fallback |
| --- | --- | --- |
| Instruction discriminator | Derived | Required for recovery/batch targeting. |
| Account roles | Derived | Required for account-aware sidecar metadata. |
| Token account layout | Derived | Hardcoded SPL token constants if layout is unavailable. |
| Mint account layout | Derived | Hardcoded SPL mint constants if layout is unavailable. |
| Vault/account field list | Derived | No fallback; lift bails without layout. |

## Practical Requirements

- A concrete trace is effectively required for branchy happy-path lifts.
- A runnable fixture is required to capture that trace.
- A Codama JSON IDL is required for layout-general account refinements.
- The emitted CU bound must be less than or equal to the sidecar budget.
- Generated Lean must pass `lake build`.

## Summary

| Tier | Programs | Requirements |
| --- | --- | --- |
| Fully mechanical abstract refinement | SPL Transfer / TransferChecked / MintTo / Burn, counter increment, vault constant field update, heap bump allocation | `.so`, sidecar metadata, trace when branchy, Codama IDL when layout is needed |
| Raw Hoare triple only | Selected paths over modeled instructions and modeled lift syscalls, including generated CloseAccount and InitializeMint2 traced lifts | `.so`, targeting metadata, concrete trace for branchy paths |
| Manual extension | New state semantics, loops with invariants, non-constant account deltas, unrecognized blob mutations | New Lean specs/refinement predicates/codegen |
| Unsupported by proof layer | Unmodeled opcodes or syscalls such as hashing, curve ops, PDA derivation, return-data reads, real CPI callee effects | New instruction/syscall specs and lift support |
