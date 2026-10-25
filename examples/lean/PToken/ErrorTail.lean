/-
  p_token's shared error tail never reports success. Every error path of the entrypoint
  funnels into PCs 3536-3542:

    3536 mov64 r1, r6        3539 mov64 r1, r6
    3537 mov64 r2, r9        3540 mov64 r2, r9
    3538 call_local 6864     3541 call_local 116
                             3542 exit

  The logger call at 3538 is crossed with the callee-agnostic rule (`failsClosed_call`): no
  spec of fn 6864 is needed, only that whatever it does, it either faults or returns to 3539.
  From 3539 the code is fn 116 (`error_convert_spec`), whose result `convVal` is never 0
  (`convVal_ne_zero`), and two `exit`s. `failsClosed_of_raised` runs that bounded path at a
  raised budget and transfers the halt back, so the theorem holds at every budget.

  `error_tail_fails_closed`: from 3536 with an empty call stack, every run that halts with
  exit code 0 has a typed fault. Pins tie `TailCode` to the real `.text` (`ErrorTailPins`).
-/
import SVM.SBPF.FailClosed
import SVM.SBPF.CodecRead
import PToken.ErrorConvert

namespace Examples.PTokenErrorTail

open SVM.SBPF Examples.PTokenErrorConvert

/-- fn 116's code requirement (prologue + decision tree). -/
def convCr : CodeReq :=
  (((CodeReq.singleton 116 (.mov64 .r0 (.reg .r2))).union
    (CodeReq.singleton 117 (.lsh64 .r1 (.imm 32)))).union
    (CodeReq.singleton 118 (.rsh64 .r1 (.imm 32)))).union crTree

/-- The instructions the tail runs, as `fetch` must serve them. -/
structure TailCode (fetch : Nat → Option Insn) : Prop where
  i3536 : fetch 3536 = some (.mov64 .r1 (.reg .r6))
  i3537 : fetch 3537 = some (.mov64 .r2 (.reg .r9))
  i3538 : fetch 3538 = some (.call_local 6864)
  i3539 : fetch 3539 = some (.mov64 .r1 (.reg .r6))
  i3540 : fetch 3540 = some (.mov64 .r2 (.reg .r9))
  i3541 : fetch 3541 = some (.call_local 116)
  i3542 : fetch 3542 = some .exit
  i197 : fetch 197 = some .exit
  conv : convCr.SatisfiedBy fetch

/-- fn 116's precondition, framed with the call stack, holds of any state at its own values. -/
theorem holdsFor_conv_pre (s : State) :
    (((.r0 ↦ᵣ s.regs.get .r0) ** (.r1 ↦ᵣ s.regs.get .r1) ** (.r2 ↦ᵣ s.regs.get .r2)) **
      callStackIs s.callStack).holdsFor s := by
  refine ⟨((PartialState.singletonReg .r0 (s.regs.get .r0)).union
      ((PartialState.singletonReg .r1 (s.regs.get .r1)).union
        (PartialState.singletonReg .r2 (s.regs.get .r2)))).union
      (PartialState.singletonCallStack s.callStack), ?_,
    _, _, ?_, rfl, ⟨_, _, ?_, rfl, rfl, _, _, ?_, rfl, rfl, rfl⟩, rfl⟩
  · exact
      { regs := fun r v h => by
          cases r <;> simp [PartialState.union, PartialState.singletonReg,
            PartialState.singletonCallStack] at h <;> subst h <;> rfl
        mem := fun a v h => by
          simp [PartialState.union, PartialState.singletonReg,
            PartialState.singletonCallStack] at h
        pc := fun v h => by
          simp [PartialState.union, PartialState.singletonReg,
            PartialState.singletonCallStack] at h
        returnData := fun rd h => by
          simp [PartialState.union, PartialState.singletonReg,
            PartialState.singletonCallStack] at h
        callStack := fun cs h => by
          simp [PartialState.union, PartialState.singletonReg,
            PartialState.singletonCallStack] at h
          exact h }
  · exact ⟨fun _ => Or.inr rfl, fun _ => Or.inr rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  · exact ⟨fun r => by cases r <;> simp [PartialState.union, PartialState.singletonReg],
      fun _ => Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  · exact ⟨fun r => by cases r <;> simp [PartialState.singletonReg],
      fun _ => Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

/-- Read `r0` and the call stack back out of fn 116's framed post. -/
theorem conv_post {z : State} {cv a b : Nat} {cs : List CallFrame}
    (h : (((.r0 ↦ᵣ cv) ** (.r1 ↦ᵣ a) ** (.r2 ↦ᵣ b)) ** callStackIs cs).holdsFor z) :
    z.regs.get .r0 = cv ∧ z.callStack = cs := by
  constructor
  · obtain ⟨hp, hc, hpred⟩ := holdsFor_sepConj_left (holdsFor_sepConj_left h)
    exact hc.regs .r0 cv (hpred ▸ PartialState.singletonReg_regs_self)
  · obtain ⟨hp, hc, hpred⟩ := holdsFor_sepConj_right h
    refine hc.callStack cs ?_
    rw [show hp = PartialState.singletonCallStack cs from hpred]
    exact PartialState.singletonCallStack_callStack_self

/-- From 3539 with an empty call stack: fn 116 then the two `exit`s, so every halt carries
    `convVal ≠ 0` or a fault. -/
theorem tail3539_fails_closed (fetch : Nat → Option Insn) (hc : TailCode fetch)
    (hob : BudgetOblivious fetch) (u : State) (hpc : u.pc = 3539) (hcs : u.callStack = [])
    (h0 : u.exitCode = none) : FailsClosed fetch u := by
  let B := u.cuConsumed + u.cuBudget + 20
  let u' : State := { u with cuBudget := B }
  -- 3539, 3540: two moves; 3541: the call into fn 116.
  let s1 := chargeCu (step (.mov64 .r1 (.reg .r6)) u')
  let s2 := chargeCu (step (.mov64 .r2 (.reg .r9)) s1)
  let w := chargeCu (step (.call_local 116) s2)
  have hs1 : s1.pc = 3540 ∧ s1.exitCode = none ∧ s1.callStack = [] ∧
      s1.cuConsumed = u.cuConsumed + 1 ∧ s1.cuBudget = B := by
    simp [s1, u', step, hpc, h0, hcs]
  have hs2 : s2.pc = 3541 ∧ s2.exitCode = none ∧ s2.callStack = [] ∧
      s2.cuConsumed = u.cuConsumed + 2 ∧ s2.cuBudget = B := by
    simp [s2, step, hs1]
  have hw : w.pc = 116 ∧ w.exitCode = none ∧ w.cuConsumed = u.cuConsumed + 3 ∧
      w.cuBudget = B ∧ ∃ F : CallFrame, w.callStack = [F] ∧ F.retPc = 3542 := by
    simp [w, step, hs2, MAX_CALL_DEPTH]
  obtain ⟨hwpc, hw0, hwcu, hwB, F, hwcs, hFret⟩ := hw
  have hpre3 : ∀ m, executeFn fetch u' (m + 3) = executeFn fetch w m := by
    intro m
    rw [show m + 3 = (m + 2) + 1 from rfl,
      executeFn_step fetch u' (m + 2) _ h0 (by simp [u', B]; omega) (by show fetch u.pc = _; rw [hpc]; exact hc.i3539),
      show m + 2 = (m + 1) + 1 from rfl,
      executeFn_step fetch s1 (m + 1) _ hs1.2.1 (by rw [hs1.2.2.2.1, hs1.2.2.2.2]; omega)
        (by rw [hs1.1]; exact hc.i3540),
      executeFn_step fetch s2 m _ hs2.2.1 (by rw [hs2.2.2.2.1, hs2.2.2.2.2]; omega)
        (by rw [hs2.1]; exact hc.i3541)]
  -- fn 116, framed with the call stack.
  obtain ⟨k1, hk1, hzpc, hz0, hzcu, hzQ⟩ :=
    error_convert_spec (w.regs.get .r0) (w.regs.get .r1) (w.regs.get .r2)
      (callStackIs w.callStack) (pcFree_callStackIs _) fetch hc.conv w (holdsFor_conv_pre w)
      hwpc hw0 (by rw [hwcu, hwB]; omega)
  generalize hz : executeFn fetch w k1 = z at hzpc hz0 hzcu hzQ
  obtain ⟨hzr0, hzcs⟩ := conv_post hzQ
  rw [hwcs] at hzcs
  -- 197: `exit` pops fn 116's frame back to 3542; 3542: `exit` on the empty stack.
  let z1 := chargeCu (step .exit z)
  have hz1 : z1.pc = 3542 ∧ z1.exitCode = none ∧ z1.callStack = [] ∧
      z1.regs.get .r0 = z.regs.get .r0 ∧ z1.cuConsumed = z.cuConsumed + 1 ∧
      z1.cuBudget = B := by
    have hzB : z.cuBudget = B := by rw [← hz, executeFn_preserves_cuBudget, hwB]
    simp only [z1, step, hzcs, chargeCu]
    refine ⟨hFret, hz0, ?_, ?_, ?_, hzB⟩ <;> first | trivial | rfl | (cases F; rfl)
  have hzB : z.cuBudget = B := by rw [← hz, executeFn_preserves_cuBudget, hwB]
  have hrun : executeFn fetch u' (k1 + 2 + 3) = executeFn fetch z1 1 := by
    rw [hpre3, executeFn_compose, hz, show (2 : Nat) = 1 + 1 from rfl,
      executeFn_step fetch z 1 _ hz0 (by rw [hzB]; omega) (by rw [hzpc]; exact hc.i197)]
  refine failsClosed_of_raised fetch hob u B (by simp only [B]; omega) (k1 + 2 + 3)
    (convVal (w.regs.get .r2) (variant32 (w.regs.get .r1))) ?_ (convVal_ne_zero _ _)
  show (executeFn fetch u' (k1 + 2 + 3)).exitCode = _
  rw [hrun, show (1 : Nat) = 0 + 1 from rfl,
    executeFn_step fetch z1 0 _ hz1.2.1 (by rw [hz1.2.2.2.2.1, hz1.2.2.2.2.2]; omega)
      (by rw [hz1.1]; exact hc.i3542), executeFn_zero]
  simp only [chargeCu, step, hz1.2.2.1]
  rw [hz1.2.2.2.1, hzr0]

/-- **The error tail fails closed.** From the tail's entry (3536) with an empty call stack,
    no run of p_token halts with exit code 0 unless it carries a typed fault. The logger
    call at 3538 needs no spec. -/
theorem error_tail_fails_closed (fetch : Nat → Option Insn) (hc : TailCode fetch)
    (hob : BudgetOblivious fetch) (s : State) (hpc : s.pc = 3536) (hcs : s.callStack = [])
    (h0 : s.exitCode = none) : FailsClosed fetch s := by
  apply failsClosed_step fetch s _ h0 (by rw [hpc]; exact hc.i3536)
  have h1 : (chargeCu (step (.mov64 .r1 (.reg .r6)) s)).pc = 3537 := by simp [step, hpc]
  apply failsClosed_step fetch _ _ (by simp [step, h0]) (by rw [h1]; exact hc.i3537)
  have h2 : (chargeCu (step (.mov64 .r2 (.reg .r9))
      (chargeCu (step (.mov64 .r1 (.reg .r6)) s)))).pc = 3538 := by simp [step, hpc]
  apply failsClosed_call fetch _ 6864 (by simp [step, h0]) (by rw [h2]; exact hc.i3538)
  intro u hucs hupc hu0
  exact tail3539_fails_closed fetch hc hob u (by rw [hupc, h2]) (by rw [hucs]; simp [step, hcs])
    hu0

end Examples.PTokenErrorTail
