/-
  Fail-closed reachability: from a state, no run ever halts cleanly with exit code 0. The
  rules compose along straight-line code (`failsClosed_step`), through any internal call
  without a spec of the callee (`failsClosed_call`, via `callee_returns_or_faults`), and
  from a bounded triple run at a raised budget (`failsClosed_of_raised`, via budget
  monotonicity), so an error tail's proof needs only the callee that computes its code.
-/
import SVM.SBPF.CalleeReturn
import SVM.SBPF.BudgetMono

namespace SVM.SBPF

/-- No run from `s` reports success: every halt with exit code 0 carries a typed fault. -/
def FailsClosed (fetch : Nat → Option Insn) (s : State) : Prop :=
  ∀ n, (executeFn fetch s n).exitCode = some 0 → (executeFn fetch s n).vmError.isSome

theorem failsClosed_halted (fetch : Nat → Option Insn) (s : State) (c : Nat)
    (hc : s.exitCode = some c) (h : c = 0 → s.vmError.isSome) : FailsClosed fetch s := by
  intro n
  rw [executeFn_halted fetch s n c hc]
  intro h0
  exact h (Option.some.inj (hc.symm.trans h0))

/-- Fail-closed is backward-closed under a step (an over-budget stall never halts). -/
theorem failsClosed_step (fetch : Nat → Option Insn) (s : State) (insn : Insn)
    (h0 : s.exitCode = none) (hf : fetch s.pc = some insn)
    (h : FailsClosed fetch (chargeCu (step insn s))) : FailsClosed fetch s := by
  intro n
  cases n with
  | zero => rw [executeFn_zero, h0]; intro hz; cases hz
  | succ n =>
    by_cases hover : s.cuConsumed > s.cuBudget
    · rw [executeFn_overBudget fetch s _ h0 hover, h0]; intro hz; cases hz
    · rw [executeFn_step fetch s n insn h0 (Nat.le_of_not_lt hover) hf]
      exact h n

/-- A state inside a callee (frame `F0` on top of `outer`) fails closed if every return to
    `F0.retPc` does: until the callee pops `F0`, no run halts cleanly. -/
theorem failsClosed_inCallee (fetch : Nat → Option Insn) (v : State) (F0 : CallFrame)
    (outer : List CallFrame) (h0 : v.exitCode = none) (hcs : v.callStack = F0 :: outer)
    (hret : ∀ u : State, u.callStack = outer → u.pc = F0.retPc → u.exitCode = none →
      FailsClosed fetch u) :
    FailsClosed fetch v := by
  intro n
  rcases callee_returns_or_faults fetch F0 outer n v [] h0 hcs with
    ⟨_, _, hnc⟩ | ⟨j, u, _, hu1, hu2, _, _, _, _, _, hu8, hu9⟩
  · intro hz
    rcases hnc with h | h
    · rw [h] at hz; cases hz
    · exact h
  · rw [hu9]
    exact hret u hu1 hu2 hu8 (n - j)

/-- **Callee-agnostic call rule.** A `call_local` fails closed if every state back at the
    return PC with the caller's stack does; nothing about the callee is assumed. -/
theorem failsClosed_call (fetch : Nat → Option Insn) (s : State) (target : Nat)
    (h0 : s.exitCode = none) (hf : fetch s.pc = some (.call_local target))
    (hret : ∀ u : State, u.callStack = s.callStack → u.pc = s.pc + 1 → u.exitCode = none →
      FailsClosed fetch u) :
    FailsClosed fetch s := by
  apply failsClosed_step fetch s _ h0 hf
  simp only [step]
  split
  · exact failsClosed_halted fetch _ ERR_CALL_DEPTH_EXCEEDED rfl (fun _ => rfl)
  · exact failsClosed_inCallee fetch _ _ s.callStack h0 rfl hret

/-- **Raised-budget rule.** On budget-oblivious code, if the run from `s` with some larger
    budget halts with a nonzero code, then `s` fails closed at its own budget: any halt at
    the real budget is also a halt at the raised one, and a run halts at most once. -/
theorem failsClosed_of_raised (fetch : Nat → Option Insn) (hob : BudgetOblivious fetch)
    (s : State) (B : Nat) (hB : s.cuBudget ≤ B) (k c : Nat)
    (hk : (executeFn fetch { s with cuBudget := B } k).exitCode = some c) (hc : c ≠ 0) :
    FailsClosed fetch s := by
  intro n hn
  exfalso
  have hmono := executeFn_withBudget fetch hob n s B hB (by rw [hn]; rfl)
  have hn' : (executeFn fetch { s with cuBudget := B } n).exitCode = some 0 := by
    rw [hmono]; exact hn
  rcases executeFn_exitCode_determined fetch _ n 0 hn' k with h | h <;> rw [hk] at h
  · cases h
  · exact hc (Option.some.inj h)

/-- Not control flow: the instruction either faults or falls through to the next PC. -/
def Insn.isStraight : Insn → Bool
  | .jeq .. | .jne .. | .jgt .. | .jge .. | .jlt .. | .jle .. | .jsgt .. | .jsge .. | .jslt ..
  | .jsle .. | .jset .. | .jmp32 .. | .ja .. | .call .. | .call_local .. | .callx .. | .exit => false
  | _ => true

/-- A straight-line step from a running state faults or advances one PC, stack unchanged. -/
theorem step_straight (insn : Insn) (s : State) (hs : insn.isStraight = true)
    (h0 : s.exitCode = none) :
    ((step insn s).exitCode = none ∧ (step insn s).pc = s.pc + 1 ∧
        (step insn s).callStack = s.callStack) ∨
      (∃ c, (step insn s).exitCode = some c ∧ (step insn s).vmError.isSome) := by
  cases insn <;> simp [Insn.isStraight] at hs <;> simp only [step] <;> (try split) <;>
    simp [h0]

/-- Straight-line code from `s.pc` for `k` instructions. -/
def StraightRun (fetch : Nat → Option Insn) (pc k : Nat) : Prop :=
  ∀ i < k, ∃ insn, fetch (pc + i) = some insn ∧ insn.isStraight = true

/-- **Straight-line rule.** Across `k` straight-line instructions every step faults or falls
    through, so `s` fails closed if every state `k` PCs on (same stack, running) does. -/
theorem failsClosed_straight (fetch : Nat → Option Insn) :
    ∀ (k : Nat) (s : State), s.exitCode = none → StraightRun fetch s.pc k →
      (∀ u : State, u.pc = s.pc + k → u.exitCode = none → u.callStack = s.callStack →
        FailsClosed fetch u) →
      FailsClosed fetch s := by
  intro k
  induction k with
  | zero => intro s h0 _ hk; exact hk s rfl h0 rfl
  | succ k ih =>
    intro s h0 hrun hk
    obtain ⟨insn, hf, hs⟩ := hrun 0 (by omega)
    apply failsClosed_step fetch s insn h0 hf
    rcases step_straight insn s hs h0 with ⟨h0', hpc', hcs'⟩ | ⟨c, hc, hv⟩
    · refine ih (chargeCu (step insn s)) h0' (fun i hi => ?_) (fun u hu h0u hcsu => ?_)
      · obtain ⟨insn', hf', hs'⟩ := hrun (i + 1) (by omega)
        refine ⟨insn', ?_, hs'⟩
        show fetch ((step insn s).pc + i) = _
        rw [hpc', show s.pc + 1 + i = s.pc + (i + 1) by omega]
        exact hf'
      · exact hk u (by rw [hu]; show (step insn s).pc + k = _; rw [hpc']; omega) h0u
          (by rw [hcsu]; exact hcs')
    · exact failsClosed_halted fetch _ c hc (fun _ => hv)

/-- **Call-entry rule.** A `call_local` fails closed if its target does (with any stack): the
    push either succeeds or faults on the depth limit. Use this to follow a call whose
    callee is known not to return. -/
theorem failsClosed_enter (fetch : Nat → Option Insn) (s : State) (target : Nat)
    (h0 : s.exitCode = none) (hf : fetch s.pc = some (.call_local target))
    (hk : ∀ u : State, u.pc = target → u.exitCode = none → FailsClosed fetch u) :
    FailsClosed fetch s := by
  apply failsClosed_step fetch s _ h0 hf
  simp only [step]
  split
  · exact failsClosed_halted fetch _ ERR_CALL_DEPTH_EXCEEDED rfl (fun _ => rfl)
  · exact hk _ rfl h0

/-- `sol_panic_` aborts with a typed fault. -/
theorem failsClosed_panic (fetch : Nat → Option Insn) (s : State) (h0 : s.exitCode = none)
    (hf : fetch s.pc = some (.call .sol_panic_)) : FailsClosed fetch s :=
  failsClosed_step fetch s _ h0 hf (failsClosed_halted fetch _ ERR_ABORT rfl (fun _ => rfl))

end SVM.SBPF
