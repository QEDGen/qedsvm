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
| `sol_invoke_signed_rust` | Triple only | Modeled as an effect-free CPI envelope for the lifted caller path; callee effects are not verified by this theorem. |
| `sol_invoke_signed_c` | Triple only | Same CPI limitation as the Rust ABI form. |
| Hashing syscalls | Unsupported | ISA/runtime support may exist, but no lifted proof obligation is emitted. |
| Curve/precompile syscalls | Unsupported | Same boundary as hashing. |
| PDA syscalls | Unsupported | Same boundary as hashing. |
| `memcpy`, `memmove` | Mechanical | Two `↦Bytes` atoms (src readable, dst writable, disjoint); dst blob ← src, `r0 := 0` (`call_sol_mem{cpy,move}_spec`). |
| `memcmp` | Mechanical | Two `↦Bytes` inputs + a 4-byte `↦U32` output; result `memcmpResultU32 p1 p2 n` (`call_sol_memcmp_spec`). |
| `sol_set_return_data` | Mechanical | One `↦Bytes` input (`[r1, r1+r2)` readable, `r2 ≤ MAX_RETURN_DATA`) copied into the framed `↦ReturnData` atom; `r0 := 0` (`call_sol_set_return_data_spec`). |
| `sol_get_return_data` | Unsupported | Only the fault direction (`execGet_faults_oob`) is modeled; no success triple. |
| Dedicated sysvar getters | Unsupported | Only the generic `sol_get_sysvar` proof path is modeled by the lift. |
| Introspection syscalls | Unsupported | Not emitted by `qedlift` as proof obligations. |
| `sol_alloc_free_` | Unsupported | Heap proofs use ordinary memory predicates instead. |

Unsupported here means "not verified by the lift", not "cannot execute". Diff tests can still run programs that use unverified runtime behavior.

## Abstract Refinement / Codec Coverage

Raw triples prove a selected bytecode path. Abstract refinements additionally connect that path to account-level state claims.

| Arm / shape | Predicate | Status |
| --- | --- | --- |
| SPL `Transfer` | `AsmRefinesTokenTransfer` | Mechanical |
| SPL `TransferChecked` | `AsmRefinesTokenTransfer` | Mechanical |
| SPL `MintTo` | `AsmRefinesTokenMintTo` | Mechanical |
| SPL `Burn` | `AsmRefinesTokenBurn` | Mechanical |
| Counter increment | `AsmRefinesCounterIncrement` | Mechanical |
| Vault constant field update | `AsmRefinesFieldUpdate` | Mechanical |
| Heap bump allocation | Heap corollary over `heapBumpPtr` / `heapBlock*` | Mechanical |
| SPL `CloseAccount` | Raw traced triple + generated balance-style corollary | Triple only |
| SPL `InitializeMint2` | Raw traced triple | Triple only |
| New operation semantics | New predicate/spec required | Manual |

## Account Layouts

| Layout feature | Status | Notes |
| --- | --- | --- |
| SPL token account | Mechanical | Token amount and owned rest-region bytes are handled by token-specific aggregation. |
| SPL mint account | Mechanical | Mint supply and owned rest-region bytes are handled by mint-specific aggregation. |
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
