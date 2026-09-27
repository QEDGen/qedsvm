# sBPF V3 ISA conformance matrix

The normative inventory for this migration is `solana-sbpf 0.14.4`'s
`src/verifier.rs` (`RequisiteVerifier::verify`) with `SBPFVersion::V3` from
`src/program.rs`. A row lists opcode forms the verifier accepts, subject to
the restrictions below. Each `imm/reg` row represents two opcode forms.

| Component | Pinned version | Evidence |
| --- | --- | --- |
| `solana-sbpf` | 0.14.4 | `qedsvm-rs/Cargo.lock` |
| `mollusk-svm` / Agave | `0.12.1-agave-4.0` | `qedsvm-rs/Cargo.toml` |
| `cargo-build-sbf` | 4.3.0 | `qedsvm-rs/tests/fixtures/README.md` |
| platform-tools | 1.57 | `qedsvm-rs/tests/fixtures/README.md` |
| V3 fixtures | SHA-256 manifest, checked in CI | `qedsvm-rs/tests/fixtures/sbpfv3_fixtures.sha256` |

`Decode` = Lean decoding pin; `Execute` = Lean execution pin; `Diff` =
qedsvm/Mollusk comparison; `Lift` = checked selected-path proof.

The inventory is not transcribed by hand: `qedlift/tests/v3_opcode_matrix.rs`
enumerates all 256 opcodes against the pinned `RequisiteVerifier` for V3
(113 accepted) and fails unless every accepted opcode is either used by
`sbpfv3_isa_matrix.so` or is one of the two call forms with their own
fixtures. `sbpfv3_isa_matrix.so` (`tests/fixtures/build_sbpfv3_isa_matrix.py`)
runs every non-call form on one straight-line path over account data:
`sbpfv3_isa_matrix_matches_mollusk` compares its account bytes and compute
units with Mollusk, and `Generated.Sbpfv3IsaMatrixLifted` proves the whole
path (126 instructions, 44 conditional jumps with jointly satisfiable path
hypotheses, checked by its branch-satisfiability witness). `M` below marks
that shared evidence.

| V3 form | Opcodes | Decode | Execute | Diff | Lift |
| --- | --- | --- | --- | --- | --- |
| `LD_DW_IMM` | `18` | `V3DecodeTests` | `RunnerTests` | M | M |
| `LD_B/H/W/DW_REG` | `71/69/61/79` | `V3DecodeTests` | `RunnerTests` | M | M |
| `ST_B/H/W/DW_IMM` | `72/6a/62/7a` | `V3DecodeTests` | `RunnerTests` | M | M |
| `ST_B/H/W/DW_REG` | `73/6b/63/7b` | `V3DecodeTests` | `RunnerTests` | M | M |
| `ADD32`, `SUB32` imm/reg | `04/0c`, `14/1c` | `V3DecodeTests` | `RunnerTests` | M | M |
| `MUL32`, `DIV32` imm/reg | `24/2c`, `34/3c` | `V3DecodeTests` | `RunnerTests` | M | M |
| `OR32`, `AND32` imm/reg | `44/4c`, `54/5c` | `V3DecodeTests` | `RunnerTests` | M | M |
| `LSH32`, `RSH32` imm/reg | `64/6c`, `74/7c` | `V3DecodeTests` | `RunnerTests` | M | M |
| `NEG32`, `MOD32` imm/reg | `84`, `94/9c` | `V3DecodeTests` | `RunnerTests` | M | M |
| `XOR32`, `MOV32` imm/reg | `a4/ac`, `b4/bc` | `V3DecodeTests` | `RunnerTests` | M | M |
| `ARSH32` imm/reg | `c4/cc` | `V3DecodeTests` | `RunnerTests` | M | M |
| `LE`, `BE` | `d4/dc` | `V3DecodeTests` | `RunnerTests` | `sbpfv3_endian_widths_match_mollusk`, M | M |
| `ADD64`, `SUB64` imm/reg | `07/0f`, `17/1f` | `V3DecodeTests` | `RunnerTests` | M | M |
| `MUL64`, `DIV64` imm/reg | `27/2f`, `37/3f` | `V3DecodeTests` | `RunnerTests` | M | M |
| `OR64`, `AND64` imm/reg | `47/4f`, `57/5f` | `V3DecodeTests` | `RunnerTests` | M | M |
| `LSH64`, `RSH64` imm/reg | `67/6f`, `77/7f` | `V3DecodeTests` | `RunnerTests` | M | M |
| `NEG64`, `MOD64` imm/reg | `87`, `97/9f` | `V3DecodeTests` | `RunnerTests` | M | M |
| `XOR64`, `MOV64` imm/reg | `a7/af`, `b7/bf` | `V3DecodeTests` | `RunnerTests` | M | M |
| `ARSH64` imm/reg | `c7/cf` | `V3DecodeTests` | `RunnerTests` | M | M |
| `JEQ32`, `JGT32`, `JGE32` imm/reg | `16/1e`, `26/2e`, `36/3e` | `V3DecodeTests` | `RunnerTests` | `sbpfv3_jmp32_all_conditions_both_outcomes_match_mollusk`, M | M |
| `JSET32`, `JNE32`, `JSGT32`, `JSGE32` imm/reg | `46/4e`, `56/5e`, `66/6e`, `76/7e` | `V3DecodeTests` | `RunnerTests` | `sbpfv3_jmp32_all_conditions_both_outcomes_match_mollusk`, M | M |
| `JLT32`, `JLE32`, `JSLT32`, `JSLE32` imm/reg | `a6/ae`, `b6/be`, `c6/ce`, `d6/de` | `V3DecodeTests` | `RunnerTests` | `sbpfv3_jmp32_all_conditions_both_outcomes_match_mollusk`, M | M |
| `JA` | `05` | `V3DecodeTests` | `RunnerTests` | M | M |
| `JEQ64`, `JGT64`, `JGE64` imm/reg | `15/1d`, `25/2d`, `35/3d` | `V3DecodeTests` | `RunnerTests` | M | M |
| `JSET64`, `JNE64`, `JSGT64`, `JSGE64` imm/reg | `45/4d`, `55/5d`, `65/6d`, `75/7d` | `V3DecodeTests` | `RunnerTests` | M | M |
| `JLT64`, `JLE64`, `JSLT64`, `JSLE64` imm/reg | `a5/ad`, `b5/bd`, `c5/cd`, `d5/dd` | `V3DecodeTests` | `RunnerTests` | M | M |
| `CALL_IMM` static syscall/relative function | `85` | `ElfTests` | `RunnerTests` | `sbpfv3_static_path_matches_mollusk`, `sbpfv3_cpi_*` | `Sbpfv3CompiledAccountLifted`, `Sbpfv3CpiCaller*`, `Sbpfv3CpiWriter*` |
| `CALL_REG` (`callx`, destination nibble) | `8d` | `V3DecodeTests` | `RunnerTests` | `sbpfv3_callx_frame_and_return_match_mollusk` | `Sbpfv3CallxPathLifted` |
| `EXIT` | `95` | `V3DecodeTests` | `RunnerTests` | M | M |

Verifier rejection rules for V3:

| Rejected form | Pinned verifier rule | Lean pin |
| --- | --- | --- |
| Empty or non-eight-byte-multiple text | `NoProgram`, `ProgramLengthNotMultiple` | `V3DecodeTests` |
| Truncated `lddw` or nonzero continuation opcode | `LDDWCannotBeLast`, `IncompleteLDDW` | `V3DecodeTests` |
| Invalid source/destination register; write to `r10` | `check_registers` (`r10` is read-only in V3) | `V3DecodeTests` |
| `callx` target register `r10` or invalid nibble | `check_callx_register` requires `0..10` | `V3DecodeTests` |
| Immediate `DIV`/`MOD` by zero | `check_imm_nonzero` | `V3DecodeTests` |
| Immediate shift outside `[0,32)` or `[0,64)` | `check_imm_shift` | `V3DecodeTests` |
| `LE`/`BE` width outside 16/32/64 | `check_imm_endian` | `V3DecodeTests` |
| Branch outside code or into `lddw` continuation | `check_jmp_offset` | `V3DecodeTests` |
| V2-only opcode meanings | V3 guards and opcode aliases in `verify` | `V3DecodeTests` |

The V3 verifier keeps classic load/store classes and `lddw`, enables
JMP32 and both endian operations, and uses the `dst` nibble for `callx`.
It disables V2 PQR and the V2-only relocated load/store meanings. Some V2
opcode bytes alias valid V3 arithmetic or JMP32 instructions; they must be
decoded with V3 semantics, rather than blanket-rejected. `CALL_IMM`
uses the static syscall/relative-function interpretation. The matrix is
versioned against this exact implementation; a newer runtime needs a
deliberate review of every row.

## Agave 4.4 alignment

Checked 2026-09-27. Agave 4.4 is pre-release (`solana-program-runtime`
4.4.0-alpha.5) and pins `solana-sbpf =0.24.0`; no Mollusk release targets
Agave 4.4 yet (latest: `mollusk-svm` 0.15.1, and 0.15.0-agave-4.3.0-beta.0).
Comparing `solana-sbpf` 0.24.0 with the pinned 0.14.4 for V3:

| Area | Change | V3 effect |
| --- | --- | --- |
| `RequisiteVerifier` (on-chain) | New signature taking the syscall registry, unused; accepted opcodes and every rejection rule identical | none |
| `LocalVerifier` (new) | Client-side check run by `solana deploy`: rejects unknown static syscall hashes and `call` imm `-1` | none on chain; deploy-time only |
| `SBPFVersion` feature predicates, opcode constants, `MM_*` layout | identical | none |
| Interpreter | Refactors (call frames outside the VM, syscall callback type). `EXIT` from an internal call no longer range-checks the saved return PC, which is always a call site + 1 | error kind only, for programs that end in a call |
| Strict ELF loader | Debug-only symbol/section labelling removed; header and program-header validation identical | none |
| `Config` | `stack_frame_size` still 4096 by default (now overridable by `VM_STACK_FRAME_SIZE`); `allow_memory_region_zero` removed, region 0 always mapped (the previous default) | none at defaults |

No V3 semantic delta was found, so the Stage 1 pins stand. The final
Agave 4.4 conformance gate (rerunning `diff_mollusk` against an Agave 4.4
Mollusk) is **pending** until such a release exists; the migration is not
declared complete before it passes.
