/-
  A generic no-return check (solana-skills#450). A witness lists the steps of one or more
  panic chains: straight-line runs, local calls and the final `sol_panic_` call. The check
  accepts the steps in order, and each step may continue only at the PC of a step accepted
  before it. So every accepted PC reaches the panic call without a return, and
  `noRetCheck_sound` turns the check into `NoReturn` for every head. The witness comes from
  an untrusted analysis (`qed_analysis::discover::noreturn`); only this check is trusted.
-/
import SVM.SBPF.FailClosed
import SVM.SBPF.PathCond

namespace SVM.SBPF

/-- One step of a panic chain. -/
inductive NoRetStep where
  /-- `len` straight-line instructions from `pc`, continuing at `pc + len`. -/
  | straight (pc len : Nat)
  /-- `call_local target` at `pc`, continuing at `target`. -/
  | callLocal (pc target : Nat)
  /-- A conditional jump at `pc` to `target`. Both `target` and `pc + 1` continue. -/
  | branch (pc target : Nat)
  /-- `call sol_panic_` at `pc`. The chain ends here. -/
  | panicCall (pc : Nat)
  deriving Repr, DecidableEq

def NoRetStep.pc : NoRetStep → Nat
  | .straight pc _ => pc
  | .callLocal pc _ => pc
  | .branch pc _ => pc
  | .panicCall pc => pc

/-- The helpers claimed never to return, and the steps that show it. -/
structure NoRetWitness where
  heads : List Nat
  steps : List NoRetStep
  deriving Repr

/-- Bool form of `StraightRun`. -/
def straightRunCheck (fetch : Nat → Option Insn) (pc k : Nat) : Bool :=
  (List.range k).all fun i => match fetch (pc + i) with
    | some insn => insn.isStraight
    | none => false

theorem straightRun_of_straightRunCheck (fetch : Nat → Option Insn) (pc k : Nat)
    (h : straightRunCheck fetch pc k = true) : StraightRun fetch pc k := by
  intro i hi
  have := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  revert this
  cases fetch (pc + i) with
  | none => intro h; cases h
  | some insn => intro h; exact ⟨insn, rfl, h⟩

/-- One step is sound given the PCs accepted before it (`done`). -/
def NoRetStep.ok (fetch : Nat → Option Insn) (done : List Nat) : NoRetStep → Bool
  | .straight pc len => straightRunCheck fetch pc len && done.contains (pc + len)
  | .callLocal pc t => decide (fetch pc = some (.call_local t)) && done.contains t
  | .branch pc t => (match fetch pc with
      | some insn => insn.jumpTarget? == some t
      | none => false) && done.contains t && done.contains (pc + 1)
  | .panicCall pc => decide (fetch pc = some (.call .sol_panic_))

/-- A conditional jump only moves the PC. -/
theorem step_jump_frame (insn : Insn) (t : Nat) (h : insn.jumpTarget? = some t) (s : State) :
    (step insn s).callStack = s.callStack ∧ (step insn s).exitCode = s.exitCode := by
  cases insn <;> simp [Insn.jumpTarget?] at h <;> simp only [step] <;> (try split) <;> simp

def noRetStepsOk (fetch : Nat → Option Insn) : List Nat → List NoRetStep → Bool
  | _, [] => true
  | done, st :: rest => st.ok fetch done && noRetStepsOk fetch (st.pc :: done) rest

def noRetCheck (fetch : Nat → Option Insn) (w : NoRetWitness) : Bool :=
  noRetStepsOk fetch [] w.steps && w.heads.all fun h => (w.steps.map NoRetStep.pc).contains h

/-- Every run that starts at `pc` keeps its starting stack at the bottom. -/
def StaysFrom (fetch : Nat → Option Insn) (pc : Nat) : Prop :=
  ∀ (base : List CallFrame) (s : State), s.pc = pc → s.exitCode = none →
    (∃ ys, s.callStack = ys ++ base) → StaysAbove fetch base s

theorem NoRetStep.ok_sound (fetch : Nat → Option Insn) (done : List Nat)
    (hdone : ∀ p ∈ done, StaysFrom fetch p) (st : NoRetStep) (h : st.ok fetch done = true) :
    StaysFrom fetch st.pc := by
  intro base s hpc h0 hcs
  cases st with
  | straight pc len =>
    simp only [NoRetStep.ok, Bool.and_eq_true, List.contains_iff_mem] at h
    simp only [NoRetStep.pc] at hpc
    exact staysAbove_straight fetch base len s h0 hcs
      (by rw [hpc]; exact straightRun_of_straightRunCheck _ _ _ h.1) fun u hu h0u hcsu =>
        hdone _ h.2 base u (by rw [hu, hpc]) h0u (by rw [hcsu]; exact hcs)
  | callLocal pc t =>
    simp only [NoRetStep.ok, Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at h
    simp only [NoRetStep.pc] at hpc
    exact staysAbove_enter fetch base s t h0 hcs (by rw [hpc]; exact h.1) fun u hu h0u hcsu =>
      hdone _ h.2 base u hu h0u hcsu
  | branch pc t =>
    simp only [NoRetStep.ok, Bool.and_eq_true, List.contains_iff_mem] at h
    simp only [NoRetStep.pc] at hpc
    obtain ⟨⟨hj, ht⟩, hn⟩ := h
    cases hf : fetch pc with
    | none => rw [hf] at hj; cases hj
    | some insn =>
      rw [hf] at hj
      have hj : insn.jumpTarget? = some t := by simpa using hj
      apply staysAbove_step fetch base s insn h0 (by rw [hpc]; exact hf) hcs
      obtain ⟨hcs', h0'⟩ := step_jump_frame insn t hj s
      have hu : ∃ ys, (chargeCu (step insn s)).callStack = ys ++ base := by
        show ∃ ys, (step insn s).callStack = ys ++ base
        rw [hcs']; exact hcs
      have h0u : (chargeCu (step insn s)).exitCode = none := by
        show (step insn s).exitCode = none
        rw [h0']; exact h0
      rcases step_jump_pc insn t hj s with hp | hp
      · exact hdone t ht base _ (by show (step insn s).pc = t; exact hp) h0u hu
      · exact hdone (pc + 1) hn base _ (by show (step insn s).pc = pc + 1; rw [hp, hpc]) h0u hu
  | panicCall pc =>
    simp only [NoRetStep.ok, decide_eq_true_eq] at h
    simp only [NoRetStep.pc] at hpc
    exact staysAbove_panic fetch base s h0 hcs (by rw [hpc]; exact h)

theorem noRetStepsOk_sound (fetch : Nat → Option Insn) :
    ∀ (steps : List NoRetStep) (done : List Nat), (∀ p ∈ done, StaysFrom fetch p) →
      noRetStepsOk fetch done steps = true → ∀ st ∈ steps, StaysFrom fetch st.pc := by
  intro steps
  induction steps with
  | nil => intro _ _ _ st hst; cases hst
  | cons st rest ih =>
    intro done hdone h
    simp only [noRetStepsOk, Bool.and_eq_true] at h
    have hst := NoRetStep.ok_sound fetch done hdone st h.1
    have hdone' : ∀ p ∈ st.pc :: done, StaysFrom fetch p := by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hst
      · exact hdone p hp
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hst
    · exact ih _ hdone' h.2 x hx

/-- **The check is sound.** Every head of an accepted witness never returns. -/
theorem noRetCheck_sound (fetch : Nat → Option Insn) (w : NoRetWitness)
    (h : noRetCheck fetch w = true) : ∀ t ∈ w.heads, NoReturn fetch t := by
  simp only [noRetCheck, Bool.and_eq_true] at h
  intro t ht s F0 outer hpc hcs h0
  have hmem := List.all_eq_true.mp h.2 t ht
  simp only [List.contains_iff_mem, List.mem_map] at hmem
  obtain ⟨st, hst, rfl⟩ := hmem
  exact noRetStepsOk_sound fetch w.steps [] (fun _ hp => by cases hp) h.1 st hst
    (F0 :: outer) s hpc h0 ⟨[], by simp [hcs]⟩

end SVM.SBPF
