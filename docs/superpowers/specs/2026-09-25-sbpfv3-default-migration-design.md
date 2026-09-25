# sBPF v3 default migration

## Intent and success criterion

New Solana programs will target sBPF v3. qedsvm must treat V3 as the normal
verification input while continuing to execute and verify existing V0 binaries.
The migration is complete when a valid V3 ELF can pass the versioned loader,
decoder, and Lean interpreter for every V3 ISA instruction form. The
selected-path proof pipeline covers every non-syscall V3 form and the modeled
syscall effects. Proofs remain scoped to the selected path. A valid instruction
must never acquire V0 semantics by fallback.

The first foundation is PR #68: strict V3 ELF loading, static syscalls, relative
calls, JMP32 execution, and two generated account-byte path proofs. That PR's
documented lift exclusions are migration work, not the finished V3 boundary.

## Source of truth and version policy

The V3 opcode, verifier, call, stack, and ELF rules come from the pinned
`solana-sbpf` implementation and Solana's V3 SIMDs. Record the exact sbpf,
Mollusk/Agave, cargo-build-sbf, and platform-tools versions used by each
conformance fixture. Keep this matrix in the repository so a dependency upgrade
cannot silently redefine what “full V3” means. Before declaring the migration
complete, run the matrix against releases compatible with the V3 deployment
feature in Agave 4.4; review upstream deltas and update the matrix deliberately.

The currently checked-in source-built V3 fixture uses cargo-build-sbf 4.3.0
and platform-tools 1.57. New source fixtures use platform-tools 1.56 or newer
with `--arch v3`, and CI checks their ELF version. qedsvm reads `e_flags` from
each ELF. It does not guess the version from opcodes. V1, V2, and V4 remain
explicitly unsupported in the Lean proof pipeline until separately designed.

## Stage 1: complete V3 loading and execution

Keep a versioned program-image boundary shared by the Rust analysis frontend
and Lean ELF runner. V3 uses strict program headers, section headers are not
required, and no V0 relocation logic is applied. V0 retains its current loader
and execution path. Invalid ELF structures and unsupported versions fail before
execution or proof generation.

Build an explicit opcode inventory from the pinned V3 verifier. For every valid
V3 instruction form, the Lean decoder produces the matching instruction and
the interpreter implements its runtime behavior. This includes all JMP32
conditions and operand forms, V3 call and callx encodings, function boundaries,
fixed frame behavior, and the V3 arithmetic and sign-extension rules. Invalid
forms are rejected with an identifiable load or decode error; an unsupported
instruction cannot be represented as a successful no-op. Version-dependent
behavior is passed explicitly to execution where the decoded instruction alone
does not determine it.

Conformance tests compare the same source-built ELF under qedsvm and Mollusk.
The test set covers every opcode form, boundary cases for signed and 32-bit
values, taken and untaken jumps, direct and indirect calls, return/frame
behavior, invalid jump/call targets, memory effects, exit state, and compute
units. Small hand-assembled ELFs supplement source-built programs for forms
the compiler rarely emits. Existing V0 fixtures remain green.

## Stage 2: selected-path proofs and V3-first workflow

`qedlift` and `qedrecover` consume the version read by `ProgramImage`; they do
not have a V0 default on an ELF-based path. Complete symbolic path semantics
and Lean instruction specifications for every non-syscall V3 ISA form,
including all JMP32 variants and callx. A trace may select an indirect call
target, but the generated theorem must state and prove the register/target
condition; a trace alone is not a proof. Unsupported syscall effects and CPI
behavior produce typed diagnostics, with no theorem emitted for a fabricated
effect.

Every generated V3 proof pins the complete ELF, its V3 version, the loaded
text, and the walked instruction decodes. Its path theorem includes the actual
branch and call conditions, memory pre/postconditions, and compute accounting.
Large-program shared-text mode preserves those pins once in a reusable module.
The CLI and Rust API report unsupported proof obligations by category and PC,
so a user can distinguish an invalid binary from a valid V3 path beyond the
modeled syscall or refinement boundary.

New examples, fixture builds, quick starts, and CI smoke tests use V3 source
programs and an explicit V3 build command. Raw-byte APIs require a version or
use a clearly named V0 compatibility wrapper. Existing V0 fixtures and proof
artifacts continue to build. No migration rewrites deployed V0 binaries.

## Acceptance gates

1. The repository has a checked opcode matrix against the pinned V3 verifier.
   Every valid instruction form has decode and execution coverage. Every
   non-syscall form, plus calls to modeled syscalls, has selected-path proof
   coverage; every invalid form is rejected rather than interpreted as V0.
2. Strict V3 ELF acceptance and rejection agree with the pinned runtime on the
   conformance corpus, including sectionless binaries and malformed headers.
3. Source-built V3 programs with all jump families, direct and indirect calls,
   memory effects, and modeled syscalls produce sorry-free Lean path theorems.
   Representative guarded account updates agree with Mollusk on exit, account
   bytes, logs, and compute units for both sides of each guard.
4. New-program documentation and smoke tests use V3 by default. V0 regression
   tests and generated examples remain green. Unsupported syscall/CPI proof
   cases fail with typed diagnostics and no proof artifact.
5. CI builds the Lean library and examples, runs Rust tests and strict Clippy,
   checks formatting, and runs the V3 differential suite. Fixture provenance
   and the tested runtime/toolchain version matrix are recorded.

## Delivery and boundaries

Implement the stages in order. Stage 1 is independently reviewable as a V3
execution/conformance release; Stage 2 adds proof parity and changes the
new-program workflow. PR #68 remains a truthful selected-path foundation and
does not claim full migration. The final V3-first release waits for both stages
and their acceptance gates.

This project does not activate a cluster feature gate, deploy programs, infer
loop invariants, prove all program paths, or promise proof coverage for every
Solana syscall, CPI, and abstract account refinement. Those remain separately
scoped verification features.

## References

- [Solana sBPFv3 rollout](https://solana.com/es/upgrades/sbpfv3-programs)
- [SIMD-0178: static syscalls](https://github.com/solana-foundation/solana-improvement-documents/blob/main/proposals/0178-static-syscalls.md)
- [SIMD-0189: strict ELF headers](https://github.com/solana-foundation/solana-improvement-documents/blob/main/proposals/0189-sbpf-stricter-elf-headers.md)
- [SIMD-0377: eBPF ISA compatibility](https://github.com/solana-foundation/solana-improvement-documents/blob/main/proposals/0377-ebpf-isa-compatibility.md)
- [SIMD-0500: V3 minimum for new deployments](https://github.com/solana-foundation/solana-improvement-documents/blob/main/proposals/0500-disable-deployment-of-sbpf-v0-v1-v2.md)
- [Anza sBPF bytecode reference](https://github.com/anza-xyz/sbpf/blob/main/doc/bytecode.md)
