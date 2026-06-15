import SVM.SBPF.InstructionSpecs.Syscalls.ReturnData

namespace SVM.SBPF

/-! ## Syscall: `sol_create_program_address` — H6 region check

`Pda.execCreate` routes program_id, the seed descriptor array + each seed slice,
and the output through the region guards, so an out-of-region (or non-writable
output) access traps with a typed `accessViolation` (`Pda.execCreate_faults_oob`).

The old SL success triples and the PDA-derivation macros composing them now fail
under H6 (the slices must fall in valid regions). Being UNCONSUMED, they are
retired in favour of `Pda.execCreate_faults_oob`. SOUNDNESS_AUDIT (H6). -/

end SVM.SBPF
