import ByteIncrement

/-!
# Proof demo

`ByteIncrement.lean` chains a 4-instruction sBPF program
(`ldx + add64 + stx + exit`) into a single end-to-end theorem:
`Runner.run` on the raw 32 bytes produces a halted state, the witness
satisfies the separation-logic spec, and the exit code reflects the
witness's `r0`.

This file is the demo entry point: a successful `lake build ProofDemo`
is the claim that a binary has been proved to meet its spec, with no
`sorry` and no proof obligation.

Run:    `lake build ProofDemo`

The theorem itself lives in `examples/lean/ByteIncrement.lean`.
-/
