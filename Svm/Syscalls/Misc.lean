-- Miscellaneous syscalls that don't fit elsewhere:
--   `sol_alloc_free_`           (deprecated; modern programs ship their own allocator)
--   `sol_remaining_compute_units` (opaque to our model)
--   `sol_get_stack_height`      (top-level = depth 1 — we don't model CPI)
--   `sol_get_processed_sibling_instruction` (we don't track sibling instrs)
--   `sol_get_sysvar`            (generic sysvar lookup — base cost only)
--   `.unknown _`                (any imm hash that doesn't match a known syscall)

import Svm.SBPF.Machine

namespace Svm.SBPF
namespace Misc

/-- Default CU charge for these (`sysvar_base_cost / syscall_base_cost = 100`). -/
def cu : Nat := 100

/-- `sol_alloc_free_`: deprecated. Returns 0 unconditionally. -/
@[simp] def execAllocFree (s : State) : State :=
  { s with regs := s.regs.set .r0 0 }

/-- `sol_remaining_compute_units`: opaque to our model. The program
    sees r0 unchanged (an "opaque runtime value"). -/
@[simp] def execRemainingComputeUnits (s : State) : State := s

/-- `sol_get_stack_height`: top-level invocation depth = 1. -/
@[simp] def execGetStackHeight (s : State) : State :=
  { s with regs := s.regs.set .r0 1 }

/-- `sol_get_processed_sibling_instruction`: we don't track siblings.
    Return 0. -/
@[simp] def execProcessedSibling (s : State) : State :=
  { s with regs := s.regs.set .r0 0 }

/-- `sol_get_sysvar` (generic lookup): return 0 (success, no data
    surfaced — the per-sysvar getters are the modeled path). -/
@[simp] def execGetSysvar (s : State) : State :=
  { s with regs := s.regs.set .r0 0 }

/-- Unknown syscall hash. Agave aborts with `UnknownSyscall`; we
    return 0 so programs that test against an opaque hash don't
    spuriously fail. -/
@[simp] def execUnknown (s : State) : State :=
  { s with regs := s.regs.set .r0 0 }

end Misc
end Svm.SBPF
