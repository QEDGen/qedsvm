/-
  Callee-agnostic return: whatever an internal callee does, a run started inside it either is
  still inside it, has halted with a typed fault, or has passed through the caller's return
  point with the caller's callee-saved registers (r6-r10) restored from the call frame.

  sBPF keeps the caller's r6-r10 in the `CallFrame` that `call_local` pushes; the callee can
  only push and pop frames above it, and `exit` restores them when it pops that frame. So the
  caller's view after a call needs no spec of the callee: every syscall fails closed
  (`execSyscall_failsClosed`), so every halt other than a top-level `exit` sets `vmError`.
  This is what lets a fail-closed error tail be proven through a logging call without
  specifying the logger.
-/
import SVM.SBPF.Execute
import SVM.SBPF.Bounded

namespace SVM.SBPF

/-- Not halted with a clean exit code: still running, or halted with a typed fault. -/
def NoCleanHalt (s : State) : Prop := s.exitCode = none ∨ s.vmError.isSome

/-- A syscall fails closed when, from a running state, it never produces a clean halt. -/
def SyscallFailsClosed (sc : Syscall) : Prop :=
  ∀ s : State, s.exitCode = none → NoCleanHalt (execSyscall sc s)

/-- `t` (a state reached from `s0`) kept `s0`'s exit code or carries a typed fault. -/
def ExitOrFault (s0 t : State) : Prop := t.exitCode = s0.exitCode ∨ t.vmError.isSome

theorem State.guardRead_of_k {P : State → Prop} (s : State) (addr len : Nat)
    (k : State → State) (hf : P s.accessFault) (hk : P (k s)) : P (s.guardRead addr len k) := by
  simp only [State.guardRead]; split
  · exact hk
  · exact hf

theorem State.guardWrite_of_k {P : State → Prop} (s : State) (addr len : Nat)
    (k : State → State) (hf : P s.accessFault) (hk : P (k s)) : P (s.guardWrite addr len k) := by
  simp only [State.guardWrite]; split
  · exact hk
  · exact hf

theorem State.guardSlices_of_k {P : State → Prop} (s : State) (descsAddr count : Nat)
    (k : State → State) (hf : P s.accessFault) (hk : P (k s)) :
    P (s.guardSlices descsAddr count k) := by
  rcases s.guardSlices_eq descsAddr count k with h | h <;> rw [h]
  · exact hf
  · exact hk

/-- Peel a guard chain on `s0`: faults set `vmError`, continuations are record updates that
    keep the exit code. -/
macro "exit_or_fault" : tactic => `(tactic|
  repeat first
    | exact Or.inl rfl
    | exact Or.inr rfl
    | apply State.guardRead_of_k (P := ExitOrFault _)
    | apply State.guardWrite_of_k (P := ExitOrFault _)
    | apply State.guardSlices_of_k (P := ExitOrFault _)
    | split)

theorem State.hashWrite_exitOrFault (s : State) (outPtr outLen inPtr inN : Nat)
    (digest : ByteArray) : ExitOrFault s (s.hashWrite outPtr outLen inPtr inN digest) := by
  simp only [State.hashWrite]; exit_or_fault

theorem State.guardedCommit_exitOrFault (s : State) (outPtr outLen inPtr inN : Nat)
    (result : Option ByteArray) :
    ExitOrFault s (s.guardedCommit outPtr outLen inPtr inN result) := by
  simp only [State.guardedCommit]
  exit_or_fault
  cases result <;> exact Or.inl rfl

theorem Pda.execTryFind_exitOrFault (s : State) : ExitOrFault s (Pda.execTryFind s) := by
  simp only [Pda.execTryFind]; exit_or_fault

theorem Sysvar.execRent_exitOrFault (s : State) : ExitOrFault s (Sysvar.execRent s) := by
  simp only [Sysvar.execRent]; exit_or_fault

theorem Sysvar.execEpochSchedule_exitOrFault (s : State) :
    ExitOrFault s (Sysvar.execEpochSchedule s) := by
  simp only [Sysvar.execEpochSchedule]; exit_or_fault

theorem Logging.execLogData_exitOrFault (s : State) : ExitOrFault s (Logging.execLogData s) := by
  simp only [Logging.execLogData]; exit_or_fault

/-- Every syscall either leaves the exit code alone or sets the typed fault channel (L1: each
    syscall abort writes `vmError` alongside its sentinel). -/
theorem execSyscall_exitCode_or_fault (sc : Syscall) (s : State) :
    ExitOrFault s (execSyscall sc s) := by
  unfold ExitOrFault
  cases sc <;> simp [execSyscall, commitOptional] <;> (repeat' split) <;>
    first
    | simp
    | exact State.hashWrite_exitOrFault s _ _ _ _ _
    | exact State.guardedCommit_exitOrFault s _ _ _ _ _
    | exact Pda.execTryFind_exitOrFault s
    | exact Sysvar.execRent_exitOrFault s
    | exact Sysvar.execEpochSchedule_exitOrFault s
    | exact Logging.execLogData_exitOrFault s

/-- Every modeled syscall fails closed. -/
theorem execSyscall_failsClosed (sc : Syscall) : SyscallFailsClosed sc := by
  intro s h0
  rcases execSyscall_exitCode_or_fault sc s with h | h
  · exact Or.inl (h.trans h0)
  · exact Or.inr h

theorem execCallx_noCleanHalt (reg : Reg) (s : State) (h0 : s.exitCode = none) :
    NoCleanHalt (execCallx reg s) := by
  unfold execCallx NoCleanHalt
  split
  · exact Or.inr rfl
  · split
    · exact Or.inr rfl
    · split
      · exact Or.inr rfl
      · exact Or.inl h0

/-- One step from a running state with a non-empty call stack never halts cleanly (`exit`
    only halts on an empty stack; every other halt is a typed fault). -/
theorem step_noCleanHalt (insn : Insn) (s : State) (h0 : s.exitCode = none)
    (hcs : s.callStack ≠ []) :
    NoCleanHalt (step insn s) := by
  cases insn with
  | call sc =>
    rcases execSyscall_failsClosed sc s h0 with h | h
    · exact Or.inl (by simpa [step] using h)
    · exact Or.inr (by simpa [step] using h)
  | callx reg => simpa [step] using execCallx_noCleanHalt reg s h0
  | exit =>
    unfold NoCleanHalt
    cases hc : s.callStack with
    | nil => exact absurd hc hcs
    | cons f rest => left; simp [step, hc, h0]
  | call_local target =>
    unfold NoCleanHalt; simp only [step]; split
    · exact Or.inr rfl
    · exact Or.inl h0
  | _ =>
    unfold NoCleanHalt
    simp only [step]
    first
    | exact Or.inl h0
    | (split
       · first | exact Or.inl h0 | exact Or.inr rfl
       · first | exact Or.inl h0 | exact Or.inr rfl)

/-- A step changes the call stack only by pushing or popping its top frame, so a stack of the
    form `ys ++ F0 :: outer` keeps that form unless the step is the `exit` that pops `F0`. -/
theorem step_callStack_above (insn : Insn) (s : State) (F0 : CallFrame) (outer : List CallFrame)
    (ys : List CallFrame) (hcs : s.callStack = ys ++ F0 :: outer)
    (hret : ¬ (insn = .exit ∧ ys = [])) :
    ∃ ys', (step insn s).callStack = ys' ++ F0 :: outer := by
  cases insn with
  | call sc => exact ⟨ys, (execSyscall_callStack sc s).trans hcs⟩
  | call_local target =>
    simp only [step]; split
    · exact ⟨ys, hcs⟩
    · exact ⟨_ :: ys, congrArg (List.cons _) hcs⟩
  | callx reg =>
    simp only [step, execCallx]
    split
    · exact ⟨ys, hcs⟩
    · split
      · exact ⟨ys, hcs⟩
      · split
        · exact ⟨ys, hcs⟩
        · exact ⟨_ :: ys, congrArg (List.cons _) hcs⟩
  | exit =>
    cases ys with
    | nil => exact absurd ⟨rfl, rfl⟩ hret
    | cons y ys' => exact ⟨ys', by simp [step, hcs]⟩
  | _ =>
    simp only [step]
    first
    | exact ⟨ys, hcs⟩
    | (split <;> exact ⟨ys, hcs⟩)

/-- **Callee-agnostic return.** Run any number of steps from a state inside a callee (its
    stack is `ys ++ F0 :: outer`, `F0` the caller's frame). Either the run is still above `F0`
    and has not halted cleanly, or it passed through a state `u`, reached after `j` steps, that
    is back at the caller's return PC with `F0`'s saved r6-r10, the caller's stack `outer`, and
    no halt; `u` is the run's own state after `j` steps and the rest of the run continues
    from it. Nothing is assumed about the code. -/
theorem callee_returns_or_faults (fetch : Nat → Option Insn) (F0 : CallFrame)
    (outer : List CallFrame) :
    ∀ (k : Nat) (s : State) (ys : List CallFrame),
      s.exitCode = none → s.callStack = ys ++ F0 :: outer →
      (∃ ys', (executeFn fetch s k).callStack = ys' ++ F0 :: outer ∧
          NoCleanHalt (executeFn fetch s k)) ∨
      (∃ j u, j ≤ k ∧ u.callStack = outer ∧ u.pc = F0.retPc ∧
          u.regs.r6 = F0.savedR6 ∧ u.regs.r7 = F0.savedR7 ∧ u.regs.r8 = F0.savedR8 ∧
          u.regs.r9 = F0.savedR9 ∧ u.regs.r10 = F0.savedR10 ∧ u.exitCode = none ∧
          u = executeFn fetch s j ∧ executeFn fetch s k = executeFn fetch u (k - j)) := by
  intro k
  induction k with
  | zero =>
    intro s ys h0 hcs
    exact Or.inl ⟨ys, by simpa using hcs, Or.inl (by simpa using h0)⟩
  | succ k ih =>
    intro s ys h0 hcs
    by_cases hover : s.cuConsumed ≥ s.cuBudget
    · rw [executeFn_overBudget fetch s (k + 1) h0 hover]
      exact Or.inl ⟨ys, hcs, Or.inl h0⟩
    have hle : s.cuConsumed < s.cuBudget := Nat.lt_of_not_le hover
    cases hf : fetch s.pc with
    | none =>
      have hbad : executeFn fetch s (k + 1)
          = { s with exitCode := some ERR_INVALID_PC, vmError := some .invalidPc } := by
        simp [executeFn, h0, hf, Nat.not_le.mpr hle]
      rw [hbad]
      exact Or.inl ⟨ys, hcs, Or.inr rfl⟩
    | some insn =>
      by_cases hch : chargeExceeds insn s = true
      · -- failed syscall charge (#93): live, over budget, same call stack
        rw [executeFn_chargeExceeds fetch s k insn h0 hle hf hch]
        obtain ⟨c, hc⟩ := chargeOnly_eq insn s
        rw [hc]; exact Or.inl ⟨ys, hcs, Or.inl h0⟩
      have hch : chargeExceeds insn s = false := by simpa using hch
      rw [executeFn_step fetch s k insn h0 hle hf hch]
      by_cases hr : insn = .exit ∧ ys = []
      · obtain ⟨rfl, rfl⟩ := hr
        right
        refine ⟨1, chargeCu (step .exit s), by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals first
          | (show _ = executeFn fetch s (0 + 1)
             rw [executeFn_step fetch s 0 _ h0 hle hf, executeFn_zero])
          | simp [step, hcs, h0]
      · obtain ⟨ys', hcs'⟩ := step_callStack_above insn s F0 outer ys hcs hr
        have hne : s.callStack ≠ [] := by simp [hcs]
        have hnc := step_noCleanHalt insn s h0 hne
        have hcs'' : (chargeCu (step insn s)).callStack = ys' ++ F0 :: outer := hcs'
        have hnc' : NoCleanHalt (chargeCu (step insn s)) := hnc
        cases hex : (chargeCu (step insn s)).exitCode with
        | some c =>
          rw [executeFn_halted fetch _ k c hex]
          exact Or.inl ⟨ys', hcs'', hnc'⟩
        | none =>
          rcases ih (chargeCu (step insn s)) ys' hex hcs'' with h | ⟨j, u, hj, hu⟩
          · exact Or.inl h
          · refine Or.inr ⟨j + 1, u, by omega, ?_⟩
            obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, hu', h9⟩ := hu
            exact ⟨h1, h2, h3, h4, h5, h6, h7, h8,
              by rw [hu', executeFn_step fetch s j insn h0 hle hf hch],
              by rw [h9]; congr 1; omega⟩

/-- Once a run halts, its exit code is fixed: every run from `u` either has not halted yet or
    halted with that same code. -/
theorem executeFn_exitCode_determined (fetch : Nat → Option Insn) (u : State) (n : Nat)
    (e : Nat) (hn : (executeFn fetch u n).exitCode = some e) (m : Nat) :
    (executeFn fetch u m).exitCode = none ∨ (executeFn fetch u m).exitCode = some e := by
  by_cases hmn : m ≤ n
  · have hsplit := executeFn_compose fetch u m (n - m)
    rw [show m + (n - m) = n from by omega] at hsplit
    cases hm : (executeFn fetch u m).exitCode with
    | none => exact Or.inl rfl
    | some c =>
      rw [hsplit, executeFn_halted fetch _ _ c hm] at hn
      exact Or.inr (hm.symm.trans hn)
  · have hsplit := executeFn_compose fetch u n (m - n)
    rw [show n + (m - n) = m from by omega, executeFn_halted fetch _ _ e hn] at hsplit
    exact Or.inr (by rw [hsplit]; exact hn)

end SVM.SBPF
