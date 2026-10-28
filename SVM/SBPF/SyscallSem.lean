-- sBPF execution with the syscalls as a parameter (#95).

import SVM.SBPF.Execute

/-! # Syscall semantics as a parameter

`step` hard-wires the syscalls: its `.call sc` arm runs `execSyscall` and
charges `syscallCu`, and the crypto syscalls reach Rust through `@[extern]`.
`stepWith S` and `executeFnWith S` take the syscalls as a parameter `S`;
every other instruction is `step`'s.

- `SyscallSem.builtin` is today's behaviour:
  `executeFnWith .builtin = executeFn` (`executeFnWith_builtin`).
- Two semantics that agree on the syscalls a program contains run it the
  same (`executeFnWith_congr`). A program with no syscall runs the same under
  every `S` (`executeFnWith_eq_of_noSyscall`), so a proof about `executeFn`
  for it holds for every `S`.
- A proof that does reach a syscall states what it needs of `S` as a
  hypothesis (a contract on `S.exec` and `S.cu`) instead of unfolding the
  FFI-backed body. That keeps trusted crypto (`CryptoTrust`) out of it.

`executeFn` and `step` stay as they are, so existing proofs and the runner
are unchanged. -/

namespace SVM.SBPF

/-- What a syscall does and what it costs. The charge is checked before the
    effect runs (#93), so the two are separate fields. -/
structure SyscallSem where
  /-- The syscall's CU charge, on top of the instruction's baseline 1 CU. -/
  cu   : Syscall → State → Nat
  /-- The syscall's effect. `callWith` advances `pc` and adds `cu`. -/
  exec : Syscall → State → State

/-- qedsvm's syscalls, the ones `step` runs. -/
def SyscallSem.builtin : SyscallSem := ⟨syscallCu, execSyscall⟩

/-- A syscall instruction under `S`: `step`'s `.call` arm, with `S` in place of
    `execSyscall` and `syscallCu`. -/
@[simp] def callWith (S : SyscallSem) (sc : Syscall) (s : State) : State :=
  let s' := S.exec sc s
  { s' with pc := s.pc + 1, cuConsumed := s'.cuConsumed + S.cu sc s }

/-- `step` with the syscalls taken from `S`. -/
@[simp] def stepWith (S : SyscallSem) (insn : Insn) (s : State) : State :=
  match insn with
  | .call sc => callWith S sc s
  | _ => step insn s

/-- `chargeExceeds` with the charge taken from `S`. -/
@[simp] def chargeExceedsWith (S : SyscallSem) (insn : Insn) (s : State) : Bool :=
  match insn with
  | .call sc => sc.chargesFirst && decide (s.cuBudget < s.cuConsumed + 1 + S.cu sc s)
  | _ => false

/-- `chargeOnly` with the charge taken from `S`. -/
@[simp] def chargeOnlyWith (S : SyscallSem) (insn : Insn) (s : State) : State :=
  match insn with
  | .call sc => { s with cuConsumed := s.cuConsumed + 1 + S.cu sc s }
  | _ => chargeCu s

/-- `executeFn` with the syscalls taken from `S`. -/
def executeFnWith (S : SyscallSem) (fetch : Nat → Option Insn) (s : State) (fuel : Nat) :
    State :=
  match fuel with
  | 0 => s
  | fuel' + 1 =>
    match s.exitCode with
    | some _ => s
    | none =>
      if s.cuConsumed ≥ s.cuBudget then s
      else match fetch s.pc with
      | none => { s with exitCode := some ERR_INVALID_PC, vmError := some .invalidPc }
      | some insn =>
        if chargeExceedsWith S insn s then chargeOnlyWith S insn s
        else executeFnWith S fetch (chargeCu (stepWith S insn s)) fuel'

/-! ## `builtin` is `step` -/

theorem callWith_builtin (sc : Syscall) (s : State) :
    callWith .builtin sc s = step (.call sc) s := rfl

theorem stepWith_builtin (insn : Insn) (s : State) :
    stepWith .builtin insn s = step insn s := by
  cases insn <;> rfl

theorem chargeExceedsWith_builtin (insn : Insn) (s : State) :
    chargeExceedsWith .builtin insn s = chargeExceeds insn s := by
  cases insn <;> rfl

theorem chargeOnlyWith_builtin (insn : Insn) (s : State) :
    chargeOnlyWith .builtin insn s = chargeOnly insn s := by
  cases insn <;> rfl

theorem executeFnWith_builtin (fetch : Nat → Option Insn) (s : State) (n : Nat) :
    executeFnWith .builtin fetch s n = executeFn fetch s n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    cases hec : s.exitCode with
    | some _ => simp only [executeFnWith, executeFn, hec]
    | none =>
      by_cases hb : s.cuConsumed ≥ s.cuBudget
      · simp only [executeFnWith, executeFn, hec, if_pos hb]
      · cases hf : fetch s.pc with
        | none => simp only [executeFnWith, executeFn, hec, if_neg hb, hf]
        | some insn =>
          simp only [executeFnWith, executeFn, hec, if_neg hb, hf, stepWith_builtin,
            chargeExceedsWith_builtin, chargeOnlyWith_builtin, ih]

/-! ## Only the syscalls a program contains matter -/

/-- An instruction that is not a syscall runs as `step` runs it, under any `S`. -/
theorem stepWith_of_not_call (S : SyscallSem) (insn : Insn) (s : State)
    (h : ∀ sc, insn ≠ .call sc) : stepWith S insn s = step insn s := by
  cases insn <;> first | rfl | exact absurd rfl (h _)

/-- `S` and `S'` agree on every syscall `fetch` contains. -/
def SyscallSem.AgreeOn (S S' : SyscallSem) (fetch : Nat → Option Insn) : Prop :=
  ∀ pc sc, fetch pc = some (.call sc) → S.cu sc = S'.cu sc ∧ S.exec sc = S'.exec sc

/-- Two semantics that agree on the syscalls a program contains run it the same. -/
theorem executeFnWith_congr {S S' : SyscallSem} {fetch : Nat → Option Insn}
    (h : S.AgreeOn S' fetch) (s : State) (n : Nat) :
    executeFnWith S fetch s n = executeFnWith S' fetch s n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [executeFnWith]
    split
    · rfl
    · split
      · rfl
      · cases hf : fetch s.pc with
        | none => rfl
        | some insn =>
          have key : chargeExceedsWith S insn s = chargeExceedsWith S' insn s ∧
              chargeOnlyWith S insn s = chargeOnlyWith S' insn s ∧
              stepWith S insn s = stepWith S' insn s := by
            cases insn with
            | call sc =>
              obtain ⟨hc, he⟩ := h _ _ hf
              simp [hc, he]
            | _ => exact ⟨rfl, rfl, rfl⟩
          simp only [key.1, key.2.1, key.2.2, ih]

/-- A semantics that agrees with `builtin` on the syscalls a program contains
    runs it as `executeFn` does, so a proof about `executeFn` carries over. -/
theorem executeFnWith_eq_executeFn {S : SyscallSem} {fetch : Nat → Option Insn}
    (h : S.AgreeOn .builtin fetch) (s : State) (n : Nat) :
    executeFnWith S fetch s n = executeFn fetch s n :=
  (executeFnWith_congr h s n).trans (executeFnWith_builtin fetch s n)

/-- A program with no syscall runs as `executeFn` runs it, under every `S`. -/
theorem executeFnWith_eq_of_noSyscall (S : SyscallSem) {fetch : Nat → Option Insn}
    (h : ∀ pc sc, fetch pc ≠ some (.call sc)) (s : State) (n : Nat) :
    executeFnWith S fetch s n = executeFn fetch s n :=
  executeFnWith_eq_executeFn (fun pc sc hf => absurd hf (h pc sc)) s n

/-! ## Stepping lemmas, for any `S` -/

@[simp] theorem executeFnWith_zero (S : SyscallSem) (fetch : Nat → Option Insn) (s : State) :
    executeFnWith S fetch s 0 = s := rfl

@[simp] theorem executeFnWith_halted (S : SyscallSem) (fetch : Nat → Option Insn) (s : State)
    (n : Nat) (code : Nat) (h : s.exitCode = some code) :
    executeFnWith S fetch s n = s := by
  cases n with
  | zero => rfl
  | succ n => simp [executeFnWith, h]

theorem executeFnWith_overBudget (S : SyscallSem) (fetch : Nat → Option Insn) (s : State)
    (n : Nat) (h_run : s.exitCode = none) (h_over : s.cuConsumed ≥ s.cuBudget) :
    executeFnWith S fetch s n = s := by
  cases n with
  | zero => rfl
  | succ n => simp [executeFnWith, h_run, if_pos h_over]

/-- The charge of a syscall that fits the budget does not exceed it. -/
theorem chargeExceedsWith_call_false (S : SyscallSem) (sc : Syscall) (s : State)
    (h : s.cuConsumed + 1 + S.cu sc s ≤ s.cuBudget) :
    chargeExceedsWith S (.call sc) s = false := by
  have : ¬ s.cuBudget < s.cuConsumed + 1 + S.cu sc s := by omega
  simp [chargeExceedsWith, this]

theorem executeFnWith_step (S : SyscallSem) (fetch : Nat → Option Insn) (s : State) (n : Nat)
    (insn : Insn) (h_running : s.exitCode = none) (h_budget : s.cuConsumed < s.cuBudget)
    (h_fetch : fetch s.pc = some insn)
    (h_charge : chargeExceedsWith S insn s = false := by
      first | rfl | exact chargeExceedsWith_call_false _ _ _ (by omega)) :
    executeFnWith S fetch s (n + 1) = executeFnWith S fetch (chargeCu (stepWith S insn s)) n := by
  simp only [executeFnWith, h_running, h_fetch, Nat.not_le.mpr h_budget, if_false, h_charge,
    Bool.false_eq_true]

/-- A syscall whose charge exceeds the remaining budget is charged and not run. -/
theorem executeFnWith_chargeExceeds (S : SyscallSem) (fetch : Nat → Option Insn) (s : State)
    (n : Nat) (insn : Insn) (h_running : s.exitCode = none)
    (h_budget : s.cuConsumed < s.cuBudget) (h_fetch : fetch s.pc = some insn)
    (h_charge : chargeExceedsWith S insn s = true) :
    executeFnWith S fetch s (n + 1) = chargeOnlyWith S insn s := by
  simp only [executeFnWith, h_running, h_fetch, Nat.not_le.mpr h_budget, if_false, h_charge,
    if_true]

theorem chargeOnlyWith_overBudget (S : SyscallSem) (insn : Insn) (s : State)
    (h_charge : chargeExceedsWith S insn s = true) :
    (chargeOnlyWith S insn s).cuConsumed ≥ (chargeOnlyWith S insn s).cuBudget := by
  cases insn <;> simp_all
  omega

/-- Running `n + m` steps is running `n`, then `m`. -/
theorem executeFnWith_compose (S : SyscallSem) (fetch : Nat → Option Insn) (s : State)
    (n m : Nat) :
    executeFnWith S fetch s (n + m) = executeFnWith S fetch (executeFnWith S fetch s n) m := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    cases h_ec : s.exitCode with
    | some code =>
      rw [executeFnWith_halted S fetch s (n + 1 + m) code h_ec,
          executeFnWith_halted S fetch s (n + 1) code h_ec,
          executeFnWith_halted S fetch s m code h_ec]
    | none =>
      by_cases h_over : s.cuConsumed ≥ s.cuBudget
      · rw [executeFnWith_overBudget S fetch s (n + 1 + m) h_ec h_over,
            executeFnWith_overBudget S fetch s (n + 1) h_ec h_over,
            executeFnWith_overBudget S fetch s m h_ec h_over]
      · have h_le : s.cuConsumed < s.cuBudget := Nat.lt_of_not_le h_over
        rw [show n + 1 + m = (n + m) + 1 from by omega]
        cases h_f : fetch s.pc with
        | none =>
          have hbad : ∀ k, executeFnWith S fetch s (k + 1) =
              { s with exitCode := some ERR_INVALID_PC, vmError := some .invalidPc } := by
            intro k; simp [executeFnWith, h_ec, h_f, Nat.not_le.mpr h_le]
          rw [hbad (n + m), hbad n, executeFnWith_halted S fetch _ m ERR_INVALID_PC rfl]
        | some insn =>
          cases h_ch : chargeExceedsWith S insn s with
          | true =>
            have hco : (chargeOnlyWith S insn s).exitCode = none := by
              cases insn <;> simp [h_ec]
            rw [executeFnWith_chargeExceeds S fetch s (n + m) insn h_ec h_le h_f h_ch,
                executeFnWith_chargeExceeds S fetch s n insn h_ec h_le h_f h_ch,
                executeFnWith_overBudget S fetch _ m hco (chargeOnlyWith_overBudget S insn s h_ch)]
          | false =>
            rw [executeFnWith_step S fetch s (n + m) insn h_ec h_le h_f h_ch,
                executeFnWith_step S fetch s n insn h_ec h_le h_f h_ch]
            exact ih _

end SVM.SBPF
