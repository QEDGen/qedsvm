import SVM.SBPF.InstructionSpecs.Syscalls.Mem

namespace SVM.SBPF

open Memory

/-! ## Sysvar getters — H6 note

All six sysvar-getter success specs were retired once each output write gained a
`guardWrite` region check (H6 stage 4a/4c): the unconditional success triples
became false (the write can fault) and had no consumers. Fault direction pinned
model-side by `Sysvar.{zeroFillR1,execRent,execEpochSchedule}_faults_oob` and
cross-engine by `oob_clock_sysvar.so`. -/

end SVM.SBPF
