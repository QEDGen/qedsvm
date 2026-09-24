# sBPF v3 verification support

## Goal

Accept an sBPF v3 ELF, execute it in the Lean reference VM, lift a selected path into a Lean-checked theorem, and compare the same binary against the pinned Solana runtime. Keep the existing V0 behavior available for deployed legacy programs. An unsupported v3 instruction or ELF shape must produce an explicit failure, never a V0 interpretation.

## Version boundary

Read `e_flags` before decoding any instruction. Represent the sBPF version as a value passed through ELF loading, byte decoding, execution, and proof generation. Generated theorems must pin both the `.text` bytes and the version that determines their interpretation. Rust `ProgramImage` must expose the version returned by `solana-sbpf`; qedlift and qedrecover must not infer it from opcode patterns. V1, V2, and V4 remain unsupported by the Lean proof path until implemented, even though the Rust dependency can load them.

## ELF loading

V0 continues through the existing section-header and relocation loader. V3 uses its strict program headers: an optional read-only segment and a required executable bytecode segment. Validate segment bounds, addresses, entry point, alignment, and the absence of runtime relocations as required by the pinned upstream loader. The Lean runner maps the read-only segment at its declared VM address and the executable segment at the program address. The version-specific loader returns text bytes, entry slot, mapped read-only bytes, and function metadata. It does not silently fall back to V0 section names.

## Instructions and calls

V3 retains the ordinary load/store and `lddw` encodings but adds the 32-bit conditional jump class. The ISA must distinguish a 32-bit comparison from a 64-bit comparison. V3 `call` opcode `0x85` uses its source field: zero denotes a syscall hash, one denotes a relative internal call. V3 `callx` reads the destination register. The Lean decoder, Rust renderer, and symbolic walk use the same version-specific interpretation. V3 functions use the runtime's frame behavior; any program that uses an unmodeled frame operation fails closed.

## Proof and conformance boundary

The first shipped proof target is a small v3 program that executes at least one static syscall, one 32-bit branch, and one internal call, plus a guarded state update. A proof of its selected path must compile without `sorry`, and an execution fixture must match Mollusk on exit, account bytes, logs, and compute units. Malformed headers, unsupported versions, unknown syscalls, and unsupported opcodes must be rejected. The existing V0 examples and differential suite remain green.

## Scope limits

This project targets the qedsvm verification pipeline. It does not activate cluster feature gates, change the on-chain loader, or promise all v3 programs are dischargeable. Unsupported syscalls and instructions remain explicit limitations. The toolchain used to create permanent fixtures must be at least platform-tools v1.53 and cargo-build-sbf v4.2.0; v1.56 is preferred. Existing upstream v3 ELF fixtures can bootstrap decoder work before that upgrade.
