import SVM.SBPF.InstructionSpecs.Syscalls.Mem

namespace SVM.SBPF

open Memory

/-! ## Sysvar getters — H6 note

All six sysvar-getter success specs (`call_sol_get_{clock,rent,epoch_schedule,
last_restart_slot,fees,epoch_rewards}_sysvar_spec`) were retired once each output
write gained a `guardWrite` region check (H6 stage 4a/4c): the prior
unconditional success triples became false (the write can now fault) and had no
consumers. The fault direction is pinned model-side by
`Sysvar.zeroFillR1_faults_oob` / `Sysvar.execRent_faults_oob` /
`Sysvar.execEpochSchedule_faults_oob`, and cross-engine by the
`oob_clock_sysvar.so` diff fixture. -/

end SVM.SBPF
