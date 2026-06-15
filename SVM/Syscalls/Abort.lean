-- Abort/panic syscalls. Both terminate with `ProgramFailedToComplete`;
-- `sol_panic_` additionally logs the caller-supplied message.

import SVM.SBPF.Machine

namespace SVM.SBPF
namespace Abort

/-- Both abort/panic charge `syscall_base_cost = 100` before failing. -/
def cu : Nat := 100

/-- `abort`: no args; sets exitCode/vmError to the abort sentinel. -/
@[simp] def execAbort (s : State) : State :=
  { s with exitCode := some ERR_ABORT, vmError := some .abort }

/-- `sol_panic_(file_ptr, file_len, line, column)` — agave's `SyscallPanic`.
    r1/r2 point at the source FILE name (not a user message). Only the abort
    is load-bearing and matches agave; agave doesn't log the file and charges
    `len` CU, we push the bytes and charge flat (error path, never
    diff-compared). See docs/SOUNDNESS_AUDIT_* (M10). -/
@[simp] def execPanic (s : State) : State :=
  let ptr := s.regs.r1
  let len := s.regs.r2
  { s with exitCode := some ERR_ABORT, vmError := some .abort
           log      := s.log.push (readBytes s.mem ptr len) }

end Abort
end SVM.SBPF
