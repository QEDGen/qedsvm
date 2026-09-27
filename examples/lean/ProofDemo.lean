import Generated.Sbpfv3CompiledAccountLifted
import ByteIncrement

/-!
# Proof demo

Entry point: `lake build ProofDemo`. A green build = a binary proved to meet its spec (no `sorry`).

The default demo is sBPF v3: `Generated/Sbpfv3CompiledAccountLifted.lean` is emitted by
`qedlift` from `qedsvm-rs/tests/fixtures/sbpfv3_compiled_account.so` (built with
`cargo-build-sbf --arch v3`) and a captured path trace. It pins the complete V3 ELF, decodes
every walked instruction with V3 semantics, and proves the selected path's account-byte
update, including a JMP32 branch, a relative call and a static syscall.

`ByteIncrement.lean` is the legacy V0 example (4-insn ldx+add64+stx+exit end-to-end); V0 is
deprecated and receives no new coverage.
-/
