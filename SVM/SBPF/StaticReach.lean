/-
  Static reachability is sound for real runs. A program's top-level code (empty call stack)
  only moves along a static successor relation in which an internal call is summarized as
  falling through to its return PC (`callee_returns_or_faults`: a callee faults, never halts
  cleanly, or returns there). So a run that starts at top level in a PC set closed under
  that relation stays in it at top level, unless it first visits a designated stop set.

  A call into a function proved never to return (`NoReturn`, e.g. a panic helper) has no
  static successor, so the code after a panic site is not treated as reachable.

  Uses: with an empty stop set, a top-level run never reaches a PC outside a closed set
  (e.g. the PCs that cannot statically reach some edge). With a stop set `{g}`, a run that
  reaches a PC outside the set reachable from the entry while avoiding `g` must have
  visited `g` (`g` dominates it). Closedness is a Bool check over the decoded program.
-/
import SVM.SBPF.FailClosed

namespace SVM.SBPF

/-- Static successors of the instruction at `pc`, with internal calls summarized as returning
    to `pc + 1`. `exit` and `callx` have none (`callx` is rejected by `ClosedExcept`). -/
def staticSucc (pc : Nat) : Insn → List Nat
  | .jeq _ _ t | .jne _ _ t | .jgt _ _ t | .jge _ _ t | .jlt _ _ t | .jle _ _ t
  | .jsgt _ _ t | .jsge _ _ t | .jslt _ _ t | .jsle _ _ t | .jset _ _ t
  | .jmp32 _ _ _ t => [t, pc + 1]
  | .ja t => [t]
  | .exit | .callx _ => []
  | _ => [pc + 1]

/-- `staticSucc`, except that a call into a `noret` target (a function that never returns to
    its caller, `NoReturn`) has no successor. -/
def callSucc (noret : Nat → Bool) (pc : Nat) : Insn → List Nat
  | .call_local t => if noret t then [] else [pc + 1]
  | insn => staticSucc pc insn

theorem callSucc_of_not_call (noret : Nat → Bool) (pc : Nat) (insn : Insn)
    (h : ∀ t, insn ≠ .call_local t) : callSucc noret pc insn = staticSucc pc insn := by
  cases insn <;> first | rfl | exact absurd rfl (h _)

/-- `R` is closed under `callSucc noret`, except at the stop set `G`, and contains no `callx`. -/
def ClosedExcept (fetch : Nat → Option Insn) (noret : Nat → Bool) (R G : Nat → Bool) : Prop :=
  ∀ pc, R pc = true → G pc = false → ∀ insn, fetch pc = some insn →
    (∀ reg, insn ≠ .callx reg) ∧ ∀ q ∈ callSucc noret pc insn, R q = true

/-- A top-level step other than a call stays at top level and moves to a static successor,
    or stays put (faults and the final `exit` leave the PC unchanged). -/
theorem step_static (insn : Insn) (s : State) (hcs : s.callStack = [])
    (hnc : ∀ t, insn ≠ .call_local t) (hnx : ∀ reg, insn ≠ .callx reg) :
    (step insn s).callStack = [] ∧
      ((step insn s).pc = s.pc ∨ (step insn s).pc ∈ staticSucc s.pc insn) := by
  cases insn
  case call sc =>
    simp only [step]
    exact ⟨(execSyscall_callStack sc s).trans hcs, Or.inr (by simp [staticSucc])⟩
  case call_local t => exact absurd rfl (hnc t)
  case callx reg => exact absurd rfl (hnx reg)
  case exit => simp [step, hcs]
  all_goals simp only [step, staticSucc] <;> (repeat' split) <;> simp [hcs]

/-- **Static reachability is sound at top level.** From a top-level state at a PC in `R`
    (closed except at `G`), every later top-level state is at a PC in `R`, unless the run
    first visited a top-level state at a PC in `G`, from which the rest of the run continues. -/
theorem reach_until (fetch : Nat → Option Insn) (noret : Nat → Bool)
    (hNR : ∀ t, noret t = true → NoReturn fetch t) (R G : Nat → Bool)
    (hR : ClosedExcept fetch noret R G) :
    ∀ (n : Nat) (s : State), R s.pc = true → s.callStack = [] →
      (executeFn fetch s n).callStack = [] →
      R (executeFn fetch s n).pc = true ∨
      ∃ j w, j ≤ n ∧ w.callStack = [] ∧ G w.pc = true ∧ w.exitCode = none ∧
        w = executeFn fetch s j ∧ executeFn fetch s n = executeFn fetch w (n - j) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro s hRs hcs hend
  cases n with
  | zero => exact Or.inl (by simpa using hRs)
  | succ n =>
  cases h0 : s.exitCode with
  | some c => rw [executeFn_halted fetch s _ c h0]; exact Or.inl hRs
  | none =>
  by_cases hG : G s.pc = true
  · exact Or.inr ⟨0, s, by omega, hcs, hG, h0, rfl, rfl⟩
  have hG' : G s.pc = false := by simpa using hG
  by_cases hover : s.cuConsumed ≥ s.cuBudget
  · rw [executeFn_overBudget fetch s _ h0 hover]; exact Or.inl hRs
  have hle : s.cuConsumed < s.cuBudget := Nat.lt_of_not_le hover
  cases hf : fetch s.pc with
  | none =>
    have hbad : executeFn fetch s (n + 1)
        = { s with exitCode := some ERR_INVALID_PC, vmError := some .invalidPc } := by
      simp [executeFn, h0, hf, Nat.not_le.mpr hle]
    rw [hbad]; exact Or.inl hRs
  | some insn =>
  obtain ⟨hnx, hsucc⟩ := hR s.pc hRs hG' insn hf
  have hlift : ∀ (u : State), R u.pc = true → u.callStack = [] → ∀ m, m < n + 1 →
      u = executeFn fetch s (n + 1 - m) →
      executeFn fetch s (n + 1) = executeFn fetch u m →
      R (executeFn fetch s (n + 1)).pc = true ∨
      ∃ j w, j ≤ n + 1 ∧ w.callStack = [] ∧ G w.pc = true ∧ w.exitCode = none ∧
        w = executeFn fetch s j ∧ executeFn fetch s (n + 1) = executeFn fetch w (n + 1 - j) := by
    intro u hRu hcsu m hm hu heq
    rw [heq] at hend ⊢
    rcases ih m hm u hRu hcsu hend with h | ⟨j, w, hj, h1, h2, h3, hw, h4⟩
    · exact Or.inl h
    · refine Or.inr ⟨(n + 1 - m) + j, w, by omega, h1, h2, h3, ?_, ?_⟩
      · rw [hw, hu, ← executeFn_compose]
      · rw [h4]; congr 1; omega
  by_cases hch : chargeExceeds insn s = true
  · -- failed syscall charge (#93): stops where it stands
    rw [executeFn_chargeExceeds fetch s n insn h0 hle hf hch]
    obtain ⟨c, hc⟩ := chargeOnly_eq insn s
    rw [hc]; exact Or.inl hRs
  have hch : chargeExceeds insn s = false := by simpa using hch
  rw [executeFn_step fetch s n insn h0 hle hf hch] at hend
  by_cases hcl : ∃ t, insn = .call_local t
  · obtain ⟨t, rfl⟩ := hcl
    by_cases hdepth : s.callStack.length + 1 ≥ MAX_CALL_DEPTH
    · -- depth fault: halted where it stands
      have hstep : step (.call_local t) s =
          { s with exitCode := some ERR_CALL_DEPTH_EXCEEDED,
                   vmError := some .callDepthExceeded } := by
        simp only [step]; rw [if_pos hdepth]
      rw [executeFn_step fetch s n _ h0 hle hf, hstep, executeFn_halted fetch _ _ _ rfl]
      exact Or.inl hRs
    · let F0 : CallFrame :=
        { retPc := s.pc + 1, savedR6 := s.regs.r6, savedR7 := s.regs.r7,
          savedR8 := s.regs.r8, savedR9 := s.regs.r9, savedR10 := s.regs.r10 }
      let v := chargeCu (step (.call_local t) s)
      have hv0 : v.exitCode = none := by simp [v, step, hdepth, h0]
      have hvcs : v.callStack = [] ++ F0 :: [] := by
        show (step (.call_local t) s).callStack = _
        simp only [step, if_neg hdepth]; rw [hcs]; rfl
      by_cases hnr : noret t = true
      · -- a call into a function that never returns: no later top-level state
        obtain ⟨ys, hys⟩ := hNR t hnr v F0 [] (by simp [v, step, hdepth]) hvcs hv0 n
        rw [hys] at hend; simp at hend
      have hret : s.pc + 1 ∈ callSucc noret s.pc (.call_local t) := by simp [callSucc, hnr]
      rcases callee_returns_or_faults fetch F0 [] n v [] hv0 hvcs with
        ⟨ys', hcs', _⟩ | ⟨j, u, hj, hu1, hu2, -, -, -, -, -, hu8, hu', hu9⟩
      · rw [hcs'] at hend; simp at hend
      · refine hlift u (by rw [hu2]; exact hsucc _ hret) hu1 (n - j) (by omega) ?_ ?_
        · rw [hu', show n + 1 - (n - j) = j + 1 by omega,
            executeFn_step fetch s j _ h0 hle hf]
        · rw [executeFn_step fetch s n _ h0 hle hf]
          exact hu9
  · have hnc : ∀ t, insn ≠ .call_local t := fun t h => hcl ⟨t, h⟩
    obtain ⟨hcs', hpc'⟩ := step_static insn s hcs hnc hnx
    refine hlift (chargeCu (step insn s)) ?_ hcs' n (by omega) ?_
      (executeFn_step fetch s n insn h0 hle hf hch)
    rotate_left
    · rw [show n + 1 - n = 0 + 1 by omega, executeFn_step fetch s 0 insn h0 hle hf hch,
        executeFn_zero]
    rcases hpc' with h | h
    · show R (step insn s).pc = true; rw [h]; exact hRs
    · exact hsucc _ (by rw [callSucc_of_not_call noret _ insn hnc]; exact h)

/-- A top-level run never leaves a closed set (`reach_until` with an empty stop set). -/
theorem never_leaves (fetch : Nat → Option Insn) (noret : Nat → Bool)
    (hNR : ∀ t, noret t = true → NoReturn fetch t) (N : Nat → Bool)
    (hN : ClosedExcept fetch noret N (fun _ => false)) (w : State) (hNw : N w.pc = true)
    (hcs : w.callStack = []) (m : Nat) (hend : (executeFn fetch w m).callStack = []) :
    N (executeFn fetch w m).pc = true := by
  rcases reach_until fetch noret hNR N _ hN m w hNw hcs hend with h | ⟨_, _, _, _, hG, _⟩
  · exact h
  · cases hG

/-- **Guard necessity.** Let `N` be closed and exclude the target PC `e` (e.g. every PC that
    cannot statically reach `e`). A top-level run from `w` that later stands at `e` at top
    level took a step at `w` that did not land in `N`. Unfolding `step` at a conditional
    jump turns this into the branch condition on `w`'s registers. -/
theorem guard_toward (fetch : Nat → Option Insn) (noret : Nat → Bool)
    (hNR : ∀ t, noret t = true → NoReturn fetch t) (N : Nat → Bool)
    (hN : ClosedExcept fetch noret N (fun _ => false)) (e : Nat) (he : N e = false)
    (w : State) (hcs : w.callStack = []) (h0 : w.exitCode = none) (insn : Insn)
    (hf : fetch w.pc = some insn) (hnc : ∀ t, insn ≠ .call_local t)
    (hnx : ∀ reg, insn ≠ .callx reg) (hne : w.pc ≠ e) (m : Nat)
    (hend : (executeFn fetch w m).callStack = [] ∧ (executeFn fetch w m).pc = e) :
    N (step insn w).pc = false := by
  cases hstep : N (step insn w).pc with
  | false => rfl
  | true =>
  exfalso
  cases m with
  | zero => exact hne (by simpa using hend.2)
  | succ k =>
  by_cases hover : w.cuConsumed ≥ w.cuBudget
  · rw [executeFn_overBudget fetch w _ h0 hover] at hend; exact hne hend.2
  have hle := Nat.lt_of_not_le hover
  by_cases hch : chargeExceeds insn w = true
  · rw [executeFn_chargeExceeds fetch w k insn h0 hle hf hch] at hend
    obtain ⟨c, hc⟩ := chargeOnly_eq insn w
    rw [hc] at hend; exact hne hend.2
  have hch : chargeExceeds insn w = false := by simpa using hch
  rw [executeFn_step fetch w k insn h0 hle hf hch] at hend
  have hcs' := (step_static insn w hcs hnc hnx).1
  have := never_leaves fetch noret hNR N hN (chargeCu (step insn w)) hstep hcs' k hend.1
  rw [hend.2, he] at this
  cases this

/-- **Dominance.** If `R` is reachable from the entry while avoiding the stop set `G` (closed
    except at `G`) and excludes `e`, every top-level run from the entry that stands at `e` at
    top level visited a PC in `G` at top level, running, after some `j` steps. -/
theorem visits_before (fetch : Nat → Option Insn) (noret : Nat → Bool)
    (hNR : ∀ t, noret t = true → NoReturn fetch t) (R G : Nat → Bool)
    (hR : ClosedExcept fetch noret R G) (s : State) (hRs : R s.pc = true) (hcs : s.callStack = [])
    (e n : Nat) (he : R e = false)
    (hend : (executeFn fetch s n).callStack = [] ∧ (executeFn fetch s n).pc = e) :
    ∃ j, j ≤ n ∧ (executeFn fetch s j).callStack = [] ∧ G (executeFn fetch s j).pc = true ∧
      (executeFn fetch s j).exitCode = none ∧
      executeFn fetch s n = executeFn fetch (executeFn fetch s j) (n - j) := by
  rcases reach_until fetch noret hNR R G hR n s hRs hcs hend.1 with h | ⟨j, w, hj, h1, h2, h3, hw, h4⟩
  · rw [hend.2, he] at h; cases h
  · subst hw; exact ⟨j, hj, h1, h2, h3, h4⟩

end SVM.SBPF
