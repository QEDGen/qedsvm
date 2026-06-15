-- CPI syscalls: `sol_invoke_signed` (Rust ABI) / `sol_invoke_signed_c` (C ABI).
--
-- PROOF-FACING stub used by `step`/`executeFn`. Fails closed: a real CPI
-- mutates callee state, sets return data, and can abort the caller, none of
-- which is modeled. Returning success-with-no-effects would let a proof
-- conclude "invoke succeeded, all account memory unchanged" (false of nearly
-- every on-chain CPI), so we abort. Diff-testing uses the richer
-- `Runner.cpiCallNextState` (via `executeFnCpiWithFuel`), which intercepts CPI
-- before `step`, so this stub doesn't affect conformance. See
-- docs/SOUNDNESS_AUDIT_* (C4); full proof-side CPI model is C5.

import SVM.SBPF.Machine

namespace SVM.SBPF
namespace Cpi

/-- `INVOKE_UNITS_COST_SIMD_0339` (execution_budget.rs:23). Diff baseline is
    mollusk under `all_enabled()`, which activates SIMD-0339, so the cost is
    946 — NOT the pre-SIMD-0339 `DEFAULT_INVOCATION_COST = 1000`. Pinned by
    the CPI diff fixtures' CU-exact assertions (audit M6). -/
def cu : Nat := 946

/-- Fail closed: the proof-facing CPI is not modeled, so refuse to run
    rather than fabricate a successful, no-effect invoke. -/
@[simp] def exec (s : State) : State :=
  { s with exitCode := some ERR_UNSUPPORTED_INSTRUCTION, vmError := some .unsupportedInstruction }

end Cpi
end SVM.SBPF
