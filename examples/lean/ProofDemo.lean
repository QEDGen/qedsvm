import ByteIncrement

/-!
# Proof demo: the trust base, in numbers

`ByteIncrement.lean` chains a 4-instruction sBPF program
(`ldx + add64 + stx + exit`) into a single end-to-end theorem:
`Runner.run` on the raw 32 bytes produces a halted state, the witness
satisfies the separation-logic spec, and the exit code reflects the
witness's `r0`.

This file does two things visible in the build output:

  1. **`#check byteIncrement_run_terminates`** asserts the theorem
     has the type we claim. No `sorry`, no proof obligation.
  2. **`#print axioms byteIncrement_run_terminates`** prints the
     trust base for this proof: every axiom transitively reachable
     from the theorem.

Run:    `lake build ProofDemo`
        Build output includes `#check` type and `#print axioms` list.

Crypto-using proofs additionally land on the 21 trust statements in
`SVM/SBPF/CryptoTrust.lean` (declared with `axiom`). The byte-increment
chain uses no crypto, so its axiom list is the Lean kernel only.
-/

open SVM SVM.SBPF Examples.ByteIncrement

-- The witness theorem chains raw bytes → decoded array → executeFn
-- agreement → Hoare-triple discharge → Runner.run terminates with
-- the spec's postcondition holding.
#check @byteIncrement_run_terminates

-- The trust base: every axiom this proof rests on, transitively.
#print axioms byteIncrement_run_terminates
