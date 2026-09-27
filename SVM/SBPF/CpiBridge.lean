/-
  CPI bridge: extend a lifted prefix that ends AT an invoke across the CPI
  transition itself.

  Ordinary `step` treats an invoke as the fail-closed `Cpi.exec`, so a lifted
  caller path stops at the call site. The bridge keeps that prefix triple and
  adds the relational CPI step: for ANY callee behaviour admitted by a
  `Cpi.CalleeSemantics`, the state right after the invoke is described by
  `Cpi.Outcome` — success commits the callee's proposed memory, failure rolls
  it back, and r0, logs, return data and compute usage cross the boundary.
  `Runner.cpiCallNextState` commits through the same `Cpi.applyResult`.

  The bridge says nothing about caller instructions after the invoke; a
  suffix triple from `invokePc + 1` composes on top of `Cpi.Outcome`.
-/

import SVM.SBPF.CPSSpec
import SVM.Syscalls.Cpi

namespace SVM.SBPF
namespace Cpi

/-- Observable effect of one CPI transition from the invoke state `sI` to
    `s'`, for some callee result `r` the contract admits. -/
def Outcome (callee : CalleeSemantics) (sI s' : State) : Prop :=
  ∃ r, callee sI r ∧
    s'.pc = sI.pc + 1 ∧
    s'.regs.r0 = r.code ∧
    (∀ reg, reg ≠ .r0 → s'.regs.get reg = sI.regs.get reg) ∧
    s'.callStack = sI.callStack ∧
    s'.regions = sI.regions ∧
    s'.exitCode = sI.exitCode ∧
    (r.code = 0 → s'.mem = r.mem) ∧
    (r.code ≠ 0 → s'.mem = sI.mem) ∧
    s'.log = r.log ∧
    s'.returnData = r.returnData ∧
    s'.returnDataProgId = r.returnDataProgId ∧
    s'.cuConsumed = sI.cuConsumed + cu + r.cuConsumed

/-- Every `Transitions` step has the `Outcome` shape. -/
theorem transition_facts {callee : CalleeSemantics} {sI s' : State}
    (h : Transitions callee sI s') : Outcome callee sI s' := by
  obtain ⟨r, hr, rfl⟩ := h
  refine ⟨r, hr, rfl, rfl, ?_, rfl, rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · intro reg hreg
    cases reg <;> first | exact absurd rfl hreg | rfl
  · intro hcode; simp [applyResult, hcode]
  · intro hcode; simp [applyResult, hcode]

/-- The bridge statement: a prefix run from `entry` reaches the invoke at
    `invokePc` in state `Q ** R`, the instruction there is the CPI syscall
    `sc`, and every CPI transition the callee contract admits from that state
    has the `Outcome` shape. Mirrors `cuTripleWithinMem`'s argument order. -/
def cpiBridgeWithinMem (N nCu entry invokePc : Nat) (cr : CodeReq)
    (P Q : Assertion) (rr : Memory.RegionTable → Prop) (sc : Syscall)
    (callee : CalleeSemantics) : Prop :=
  ∀ (R : Assertion), R.pcFree →
  ∀ (fetch : Nat → Option Insn),
    (cr.union (CodeReq.singleton invokePc (.call sc))).SatisfiedBy fetch →
  ∀ (s : State), (P ** R).holdsFor s → s.pc = entry → s.exitCode = none →
    s.cuConsumed + N + nCu ≤ s.cuBudget → rr s.regions →
    ∃ k, k ≤ N ∧
      (executeFn fetch s k).pc = invokePc ∧
      fetch invokePc = some (.call sc) ∧
      (executeFn fetch s k).exitCode = none ∧
      (executeFn fetch s k).cuConsumed ≤ s.cuConsumed + N + nCu ∧
      (Q ** R).holdsFor (executeFn fetch s k) ∧
      ∀ s', Transitions callee (executeFn fetch s k) s' →
        Outcome callee (executeFn fetch s k) s'

/-- Bridge a lifted prefix that ends at an invoke across the CPI transition,
    for any callee contract. `hFresh` (the prefix does not itself pin
    `invokePc`) ties the transition to the decoded CPI instruction. -/
theorem cuTripleWithinMem_cpi_bridge
    {N nCu entry invokePc : Nat} {cr : CodeReq} {P Q : Assertion}
    {rr : Memory.RegionTable → Prop}
    (h : cuTripleWithinMem N nCu entry invokePc cr P Q rr)
    (hFresh : cr invokePc = none) (sc : Syscall) (callee : CalleeSemantics) :
    cpiBridgeWithinMem N nCu entry invokePc cr P Q rr sc callee := by
  intro R hR fetch hcr s hPre hpc hex hbud hrr
  have hInv : fetch invokePc = some (.call sc) := by
    apply hcr invokePc
    show (match cr invokePc with | some i => some i | none => _) = _
    rw [hFresh]
    exact CodeReq.singleton_self
  obtain ⟨k, hk, hPc, hEx, hCu, hPost⟩ :=
    h R hR fetch (CodeReq.SatisfiedBy_of_union_left hcr) s hPre hpc hex hbud hrr
  exact ⟨k, hk, hPc, hInv, hEx, hCu, hPost, fun _ hT => transition_facts hT⟩

end Cpi
end SVM.SBPF
