-- Abort/panic syscalls. Both terminate execution with
-- `ProgramFailedToComplete`; `sol_panic_` additionally logs the
-- caller-supplied message.

import SVM.SBPF.Machine

namespace SVM.SBPF
namespace Abort

/-- Both abort/panic charge `syscall_base_cost = 100` before failing. -/
def cu : Nat := 100

/-- `abort`: no args. Sets `exitCode := some ERR_ABORT, vmError := some .abort`. -/
@[simp] def execAbort (s : State) : State :=
  { s with exitCode := some ERR_ABORT, vmError := some .abort }

/-- `sol_panic_(file_ptr, file_len, line, column)` — agave's `SyscallPanic`
    (4 args; r1/r2 point at the source FILE name, not a user message;
    line/column in r3/r4 are diagnostics). Only the abort
    (`exitCode := ERR_ABORT`) is load-bearing and matches agave. Agave
    does not write the file to the program log and charges `len` CU; we
    approximate by pushing the bytes and charging a flat CU (panic is an
    error path, never diff-compared). See docs/SOUNDNESS_AUDIT_* (M10). -/
@[simp] def execPanic (s : State) : State :=
  let ptr := s.regs.r1
  let len := s.regs.r2
  { s with exitCode := some ERR_ABORT, vmError := some .abort
           log      := s.log.push (readBytes s.mem ptr len) }

end Abort
end SVM.SBPF
