-- Cross-Program Invocation syscalls: `sol_invoke_signed` (Rust ABI)
-- and `sol_invoke_signed_c` (C ABI).
--
-- This is the PROOF-FACING stub used by `step` / `executeFn`. It fails
-- closed: a real CPI mutates callee account state, sets return data,
-- enforces privilege/signer/depth rules, and can fail (aborting the
-- caller). None of that is modeled here, so rather than return success
-- with zero effects (which would let a proof conclude "invoke
-- succeeded, all account memory unchanged" — false of essentially every
-- on-chain CPI) we abort. The diff-testing runner uses a separate,
-- richer CPI model (`Runner.cpiCallNextState`, reached via
-- `executeFnCpiWithFuel`) that intercepts CPI before `step`, so this
-- stub does not affect conformance testing. See docs/SOUNDNESS_AUDIT_*
-- (C4); a full proof-side CPI model is tracked as a design item (C5).

import SVM.SBPF.Machine

namespace SVM.SBPF
namespace Cpi

/-- `DEFAULT_INVOCATION_COST` from agave. -/
def cu : Nat := 946

/-- Fail closed: the proof-facing CPI is not modeled, so refuse to run
    rather than fabricate a successful, no-effect invoke. -/
@[simp] def exec (s : State) : State :=
  { s with exitCode := some ERR_UNSUPPORTED_INSTRUCTION }

end Cpi
end SVM.SBPF
