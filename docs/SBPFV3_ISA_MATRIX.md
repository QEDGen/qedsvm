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
| compiled V3 fixture | SHA-256 `576074e54158e103ee42ac68ef86cd190091177b2304ff8df94f3da880b3f34c` | `qedsvm-rs/tests/fixtures/sbpfv3_compiled_account.so` |

`Decode` = Lean decoding pin; `Execute` = Lean execution pin; `Diff` =
qedsvm/Mollusk comparison; `Lift` = checked selected-path proof. A pending
cell is a migration gap, not evidence of support. Task 3 fills the decode
column, Task 4 the execution column, Task 5 the differential column, and
Stage 2 the lift column.

| V3 form | Opcodes | Decode | Execute | Diff | Lift |
| --- | --- | --- | --- | --- | --- |
| `LD_DW_IMM` | `18` | pending | pending | pending | pending |
| `LD_B/H/W/DW_REG` | `71/69/61/79` | pending | pending | pending | pending |
| `ST_B/H/W/DW_IMM` | `72/6a/62/7a` | pending | pending | pending | pending |
| `ST_B/H/W/DW_REG` | `73/6b/63/7b` | pending | pending | pending | pending |
| `ADD32`, `SUB32` imm/reg | `04/0c`, `14/1c` | pending | pending | pending | pending |
| `MUL32`, `DIV32` imm/reg | `24/2c`, `34/3c` | pending | pending | pending | pending |
| `OR32`, `AND32` imm/reg | `44/4c`, `54/5c` | pending | pending | pending | pending |
| `LSH32`, `RSH32` imm/reg | `64/6c`, `74/7c` | pending | pending | pending | pending |
| `NEG32`, `MOD32` imm/reg | `84`, `94/9c` | pending | pending | pending | pending |
| `XOR32`, `MOV32` imm/reg | `a4/ac`, `b4/bc` | pending | pending | pending | pending |
| `ARSH32` imm/reg | `c4/cc` | pending | pending | pending | pending |
| `LE`, `BE` | `d4/dc` | pending | pending | pending | pending |
| `ADD64`, `SUB64` imm/reg | `07/0f`, `17/1f` | pending | pending | pending | pending |
| `MUL64`, `DIV64` imm/reg | `27/2f`, `37/3f` | pending | pending | pending | pending |
| `OR64`, `AND64` imm/reg | `47/4f`, `57/5f` | pending | pending | pending | pending |
| `LSH64`, `RSH64` imm/reg | `67/6f`, `77/7f` | pending | pending | pending | pending |
| `NEG64`, `MOD64` imm/reg | `87`, `97/9f` | pending | pending | pending | pending |
| `XOR64`, `MOV64` imm/reg | `a7/af`, `b7/bf` | pending | pending | pending | pending |
| `ARSH64` imm/reg | `c7/cf` | pending | pending | pending | pending |
| `JEQ32`, `JGT32`, `JGE32` imm/reg | `16/1e`, `26/2e`, `36/3e` | pending | pending | pending | pending |
| `JSET32`, `JNE32`, `JSGT32`, `JSGE32` imm/reg | `46/4e`, `56/5e`, `66/6e`, `76/7e` | pending | pending | pending | pending |
| `JLT32`, `JLE32`, `JSLT32`, `JSLE32` imm/reg | `a6/ae`, `b6/be`, `c6/ce`, `d6/de` | pending | pending | pending | pending |
| `JA` | `05` | pending | pending | pending | pending |
| `JEQ64`, `JGT64`, `JGE64` imm/reg | `15/1d`, `25/2d`, `35/3d` | pending | pending | pending | pending |
| `JSET64`, `JNE64`, `JSGT64`, `JSGE64` imm/reg | `45/4d`, `55/5d`, `65/6d`, `75/7d` | pending | pending | pending | pending |
| `JLT64`, `JLE64`, `JSLT64`, `JSLE64` imm/reg | `a5/ad`, `b5/bd`, `c5/cd`, `d5/dd` | pending | pending | pending | pending |
| `CALL_IMM` static syscall/relative function | `85` | `ElfTests` | pending | pending | pending |
| `CALL_REG` (`callx`, destination nibble) | `8d` | `V3DecodeTests` | pending | pending | pending |
| `EXIT` | `95` | pending | pending | pending | pending |

Verifier rejection rules for V3:

| Rejected form | Pinned verifier rule | Lean pin |
| --- | --- | --- |
| Empty or non-eight-byte-multiple text | `NoProgram`, `ProgramLengthNotMultiple` | pending |
| Truncated `lddw` or nonzero continuation opcode | `LDDWCannotBeLast`, `IncompleteLDDW` | pending |
| Invalid source/destination register; write to `r10` | `check_registers` (`r10` is read-only in V3) | pending |
| `callx` target register `r10` or invalid nibble | `check_callx_register` requires `0..10` | pending |
| Immediate `DIV`/`MOD` by zero | `check_imm_nonzero` | pending |
| Immediate shift outside `[0,32)` or `[0,64)` | `check_imm_shift` | pending |
| `LE`/`BE` width outside 16/32/64 | `check_imm_endian` | pending |
| Branch outside code or into `lddw` continuation | `check_jmp_offset` | pending |
| V2 PQR, relocated memory opcodes, `HOR64_IMM` | V3 feature guards in `verify` | pending |

The V3 verifier keeps classic load/store classes and `lddw`, enables
JMP32 and both endian operations, and uses the `dst` nibble for `callx`.
It disables V2 PQR and the V2-only relocated load/store forms. `CALL_IMM`
uses the static syscall/relative-function interpretation. The matrix is
versioned against this exact implementation; a newer runtime needs a
deliberate review of every row.
