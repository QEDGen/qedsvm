-- What a run returned: one observable for proofs, the FFI and differential tests (#94).

import SVM.SBPF.Machine

/-! # Run outcome

A halted `State` says what the run returned through three fields: the
`exitCode` sentinel (`none` = out of CU), the typed `vmError`, and
`cuConsumed`, which can overshoot the budget by the last instruction's cost.
`Outcome.ofState` reads them once:

- `exitCode = some r0`, `vmError = none`: the program exited, `.ok r0`.
- `vmError = some e`: the VM faulted, `.fault e`. The `exitCode` sentinel is
  `e.toSentinel`.
- `exitCode = none`: `.cuExceeded`. The runner only stops a live state when
  it is over budget: its fuel is the budget, and every step charges at least
  1 CU.

CU used is clamped to the budget: agave drains the meter to exactly the
budget on `ComputeBudgetExceeded`, and the clamp is the identity on every
in-budget run.

`Outcome.consensus` keeps what the chain records. Agave folds every fault
kind, and a non-zero exit, into a failed transaction that still pays for its
CU; only a zero exit commits the input region and return data. -/

namespace SVM.SBPF

/-- What a run returned. `input` is the input region after the run. -/
inductive Outcome
  | ok (r0 cuUsed : Nat) (input returnData : ByteArray)
  | fault (e : VmError) (cuUsed : Nat)
  | cuExceeded
  deriving Inhabited

/-- What consensus sees of a run. -/
inductive ConsensusOutcome
  | success (cuUsed : Nat) (input returnData : ByteArray)
  | failed (cuUsed : Nat)
  deriving Inhabited

/-- CU used, clamped to the budget. -/
def State.cuUsed (s : State) (budget : Nat) : Nat := min s.cuConsumed budget

/-- The outcome of a halted state whose input region is `inputLen` bytes at
    `INPUT_START`. -/
def Outcome.ofState (s : State) (inputLen budget : Nat) : Outcome :=
  match s.exitCode, s.vmError with
  | none, _ => .cuExceeded
  | some _, some e => .fault e (s.cuUsed budget)
  | some r0, none =>
    .ok r0 (s.cuUsed budget) (readBytes s.mem Memory.INPUT_START inputLen) s.returnData

/-- CU used, as the chain charges it. -/
def Outcome.cuUsed (budget : Nat) : Outcome → Nat
  | .ok _ cu _ _ | .fault _ cu => cu
  | .cuExceeded => budget

def Outcome.consensus (budget : Nat) : Outcome → ConsensusOutcome
  | .ok 0 cu input rd => .success cu input rd
  | o => .failed (o.cuUsed budget)

/-! ## Reading an outcome back -/

@[simp] theorem Outcome.ofState_cuExceeded_iff (s : State) (inputLen budget : Nat) :
    Outcome.ofState s inputLen budget = .cuExceeded ↔ s.exitCode = none := by
  unfold Outcome.ofState
  split <;> simp_all

theorem Outcome.ofState_fault_iff (s : State) (inputLen budget : Nat) (e : VmError)
    (cu : Nat) :
    Outcome.ofState s inputLen budget = .fault e cu ↔
      s.exitCode.isSome ∧ s.vmError = some e ∧ cu = s.cuUsed budget := by
  unfold Outcome.ofState
  split <;> simp_all [eq_comm]

theorem Outcome.ofState_ok_iff (s : State) (inputLen budget r0 cu : Nat)
    (input rd : ByteArray) :
    Outcome.ofState s inputLen budget = .ok r0 cu input rd ↔
      s.exitCode = some r0 ∧ s.vmError = none ∧ cu = s.cuUsed budget ∧
        input = readBytes s.mem Memory.INPUT_START inputLen ∧ rd = s.returnData := by
  unfold Outcome.ofState
  split <;> simp_all [eq_comm]

/-- A clean exit with `r0`: the outcome is `.ok r0 …`. -/
theorem Outcome.ofState_of_exit (s : State) (inputLen budget r0 : Nat)
    (h_exit : s.exitCode = some r0) (h_clean : s.vmError = none) :
    Outcome.ofState s inputLen budget =
      .ok r0 (s.cuUsed budget) (readBytes s.mem Memory.INPUT_START inputLen) s.returnData := by
  simp [Outcome.ofState, h_exit, h_clean]

/-- A fault `e`: the outcome is `.fault e …`. -/
theorem Outcome.ofState_of_fault (s : State) (inputLen budget code : Nat) (e : VmError)
    (h_exit : s.exitCode = some code) (h_fault : s.vmError = some e) :
    Outcome.ofState s inputLen budget = .fault e (s.cuUsed budget) := by
  simp [Outcome.ofState, h_exit, h_fault]

/-- Only a zero exit succeeds on chain. -/
theorem Outcome.consensus_success_iff (o : Outcome) (budget cu : Nat) (input rd : ByteArray) :
    o.consensus budget = .success cu input rd ↔ o = .ok 0 cu input rd := by
  unfold Outcome.consensus
  split <;> simp_all

end SVM.SBPF
