-- CPI syscalls: `sol_invoke_signed` (Rust ABI) / `sol_invoke_signed_c` (C ABI).
--
-- `CalleeResult` / `applyResult` are the compositional proof-facing semantics:
-- a successful invocation commits proposed account memory, while every error
-- rolls it back to the caller's pre-invocation memory. Logs, return data, the
-- error code in r0, and compute usage cross the invocation boundary in either
-- case. `Runner.cpiCallNextState` uses this same commit function.
--
-- The parameter-free `exec` used by the ordinary `step`/`executeFn` remains a
-- closed-world fallback: without a callee semantics it cannot fabricate a
-- result, so it fails closed. Proofs of CPI callers should supply a callee
-- relation through `Transitions` and reason about `applyResult`.

import SVM.SBPF.Machine

namespace SVM.SBPF
namespace Cpi

/-- `INVOKE_UNITS_COST_SIMD_0339` (execution_budget.rs:23). Diff baseline is
    mollusk under `all_enabled()`, which activates SIMD-0339, so the cost is
    946 — NOT the pre-SIMD-0339 `DEFAULT_INVOCATION_COST = 1000`. Pinned by
    the CPI diff fixtures' CU-exact assertions (audit M6). -/
def cu : Nat := 946

/-- Observable result of executing one CPI callee. `mem` is the callee's
    proposed caller-memory write-back. It is committed exactly when `code = 0`.
    A nonzero code therefore cannot smuggle partial account mutations across
    the invocation boundary. Return data and logs remain observable on both
    paths, matching the transaction-scoped runtime channels. -/
structure CalleeResult where
  code : Nat
  mem : Memory.Mem
  log : Array ByteArray
  returnData : ByteArray
  returnDataProgId : ByteArray
  cuConsumed : Nat

/-- Commit a callee result into its caller.

    This is the compositional CPI transaction boundary shared by proofs and the
    executable runner:
    * `code = 0`: commit account-memory write-back;
    * `code ≠ 0`: roll every account mutation back to `s.mem`;
    * both paths propagate r0, logs, return data, and callee CU consumption;
    * caller-local control state and VM-fault state remain owned by the caller.

    `pc` advances here because the runner intercepts CPI before ordinary
    `step`; the usual closed-world `exec` below is still a syscall body and is
    advanced/charged by `step`. -/
@[simp] def applyResult (s : State) (r : CalleeResult) : State :=
  { s with regs := s.regs.set .r0 r.code
           mem := if r.code = 0 then r.mem else s.mem
           pc := s.pc + 1
           log := r.log
           returnData := r.returnData
           returnDataProgId := r.returnDataProgId
           cuConsumed := s.cuConsumed + cu + r.cuConsumed }

/-- A callee semantics is a relation, rather than a function, so a proof may
    abstract over another verified program, a native-program specification, or
    a nondeterministic environment contract without adding an oracle to
    `State`. -/
abbrev CalleeSemantics := State → CalleeResult → Prop

/-- Relational CPI transition induced by a callee specification. -/
def Transitions (callee : CalleeSemantics) (before after : State) : Prop :=
  ∃ result, callee before result ∧ after = applyResult before result

@[simp] theorem applyResult_r0 (s : State) (r : CalleeResult) :
    (applyResult s r).regs.r0 = r.code := by
  rfl

@[simp] theorem applyResult_mem_success (s : State) (r : CalleeResult)
    (h : r.code = 0) : (applyResult s r).mem = r.mem := by
  simp [applyResult, h]

@[simp] theorem applyResult_mem_failure (s : State) (r : CalleeResult)
    (h : r.code ≠ 0) : (applyResult s r).mem = s.mem := by
  simp [applyResult, h]

@[simp] theorem applyResult_returnData (s : State) (r : CalleeResult) :
    (applyResult s r).returnData = r.returnData := by
  rfl

@[simp] theorem applyResult_returnDataProgId (s : State) (r : CalleeResult) :
    (applyResult s r).returnDataProgId = r.returnDataProgId := by
  rfl

@[simp] theorem applyResult_exitCode (s : State) (r : CalleeResult) :
    (applyResult s r).exitCode = s.exitCode := by
  rfl

@[simp] theorem applyResult_vmError (s : State) (r : CalleeResult) :
    (applyResult s r).vmError = s.vmError := by
  rfl

/-- A successful nested invocation may contribute to the outer callee's
    proposed memory, but an outer error rolls the entire proposal back to the
    original caller state. This is the key transactional composition law. -/
theorem outer_failure_rolls_back_nested_success
    (caller calleeStart : State) (inner outer : CalleeResult)
    (hInner : inner.code = 0) (hOuter : outer.code ≠ 0)
    (hOuterMem : outer.mem = (applyResult calleeStart inner).mem) :
    (applyResult caller outer).mem = caller.mem ∧
      (applyResult calleeStart inner).mem = inner.mem ∧
      outer.mem = inner.mem := by
  constructor
  · exact applyResult_mem_failure caller outer hOuter
  · constructor
    · exact applyResult_mem_success calleeStart inner hInner
    · rw [hOuterMem, applyResult_mem_success calleeStart inner hInner]

/-- Successful nesting exposes the outer callee's final account state and
    return data to its caller. -/
theorem outer_success_commits_nested_result
    (caller calleeStart : State) (inner outer : CalleeResult)
    (hInner : inner.code = 0) (hOuter : outer.code = 0)
    (hOuterMem : outer.mem = (applyResult calleeStart inner).mem) :
    (applyResult caller outer).mem = inner.mem ∧
      (applyResult caller outer).returnData = outer.returnData := by
  constructor
  · rw [applyResult_mem_success caller outer hOuter, hOuterMem,
      applyResult_mem_success calleeStart inner hInner]
  · rfl

/-- Fail-closed fallback for ordinary execution without a supplied callee
    semantics. This must never become success-with-no-effects. -/
@[simp] def exec (s : State) : State :=
  { s with exitCode := some ERR_UNSUPPORTED_INSTRUCTION, vmError := some .unsupportedInstruction }

end Cpi
end SVM.SBPF
