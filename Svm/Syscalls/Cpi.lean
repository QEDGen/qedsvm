-- Cross-Program Invocation syscalls: `sol_invoke_signed` (Rust ABI)
-- and `sol_invoke_signed_c` (C ABI). We don't model CPI yet; both
-- return 0 (success) so the calling program continues — programs
-- that actually rely on the result of a CPI will diverge from real
-- agave behavior.

import Svm.SBPF.Machine

namespace Svm.SBPF
namespace Cpi

/-- `DEFAULT_INVOCATION_COST` from agave. -/
def cu : Nat := 946

/-- Stub: both ABI variants do the same thing here — set r0 = 0. -/
@[simp] def exec (s : State) : State :=
  { s with regs := s.regs.set .r0 0 }

end Cpi
end Svm.SBPF
