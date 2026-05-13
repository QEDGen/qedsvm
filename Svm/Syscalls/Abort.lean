-- Abort/panic syscalls. Both terminate execution with
-- `ProgramFailedToComplete`; `sol_panic_` additionally logs the
-- caller-supplied message.

import Svm.SBPF.Machine

namespace Svm.SBPF
namespace Abort

/-- Both abort/panic charge `syscall_base_cost = 100` before failing. -/
def cu : Nat := 100

/-- `abort`: no args. Sets `exitCode := some ERR_ABORT`. -/
@[simp] def execAbort (s : State) : State :=
  { s with exitCode := some ERR_ABORT }

/-- `sol_panic_(msgPtr, msgLen, filePtr, fileLen, line)`. Logs the
    message bytes (file/line dropped — they're for diagnostics, not
    state) and sets `exitCode := some ERR_ABORT`. -/
@[simp] def execPanic (s : State) : State :=
  let ptr := s.regs.r1
  let len := s.regs.r2
  { s with exitCode := some ERR_ABORT
           log      := s.log.push (readBytes s.mem ptr len) }

end Abort
end Svm.SBPF
