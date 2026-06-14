import SVM.SBPF.InstructionSpecs.Syscalls.ReturnData

namespace SVM.SBPF

/-! ## Syscall: `sol_create_program_address` — H6 region check

`Pda.execCreate` now routes the program_id `[r3,32)`, the seed descriptor
array `[r1, r2·16)` + each seed slice, and the 32-byte output `[r4,32)`
through the region guards (`State.guardRead` / `guardedCommit`), so an
out-of-region (or non-writable output) access traps with a typed
`accessViolation` (`Pda.execCreate_faults_oob`).

The two SL success triples that used to live here
(`call_create_program_address_n0_spec`, `call_create_program_address_n1_spec`)
and the PDA derivation macros that composed them (`pda_n0_macro_spec`,
`pda_n0_macro_executeFn`, `pda_n1_macro_spec`, `pda_n1_macro_executeFn`,
`pda_n1_stack_macro_spec`, `pda_n1_stack_macro_executeFn` in `Macros.lean`)
reduced `execCreate` to `commitOptional` and proved the output buffer was
written with the derived PDA. Under H6 that success path now requires the
output / program_id / seed slices to fall in valid regions (else the syscall
traps), so the unconditional triples no longer hold as stated. They were
UNCONSUMED (no lift composed them; the macro chain bottomed out unused, its
intended reuse for the crypto success paths superseded by the `*_faults_oob`
fault lemmas), so they are retired in favour of `Pda.execCreate_faults_oob`
rather than re-derived as `cuTripleWithinMem` region-conditional triples.
See docs/SOUNDNESS_AUDIT_* (H6). -/

end SVM.SBPF
