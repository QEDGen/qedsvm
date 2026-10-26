/-
  Budget monotonicity: raising the CU budget never changes how a run halts, as long as the
  code never executes a syscall that reads the budget (`sol_log_compute_units_`,
  `sol_remaining_compute_units`).

  Bounded triples (`cuTripleWithin`) only speak about runs whose remaining budget covers
  their worst-case step count; a run with less budget may still take a shorter path to the
  same halt. This lemma lets a fail-closed argument run the triple at a raised budget and
  transfer every halt back.
-/
import SVM.SBPF.Execute

namespace SVM.SBPF

/-- Syscalls whose result depends on `cuBudget`. -/
def Syscall.readsBudget : Syscall → Bool
  | .sol_log_compute_units_ | .sol_remaining_compute_units => true
  | _ => false

theorem State.guardRead_withBudget (s : State) (B addr len : Nat) (k : State → State)
    (hk : k { s with cuBudget := B } = { k s with cuBudget := B }) :
    ({ s with cuBudget := B } : State).guardRead addr len k
      = { s.guardRead addr len k with cuBudget := B } := by
  simp only [State.guardRead]; split <;> simp_all

theorem State.guardWrite_withBudget (s : State) (B addr len : Nat) (k : State → State)
    (hk : k { s with cuBudget := B } = { k s with cuBudget := B }) :
    ({ s with cuBudget := B } : State).guardWrite addr len k
      = { s.guardWrite addr len k with cuBudget := B } := by
  simp only [State.guardWrite]; split <;> simp_all

/-- The descriptor walk's fold, with its address/length readers abstracted so neither the
    elaborator nor the kernel unfolds `readU64` while matching. -/
theorem foldr_guardRead_withBudget (A L : Memory.Mem → Nat → Nat) (k : State → State)
    (l : List Nat) (s : State) (B : Nat)
    (hk : k { s with cuBudget := B } = { k s with cuBudget := B }) :
    List.foldr (fun i (kont : State → State) (s' : State) =>
        s'.guardRead (A s'.mem i) (L s'.mem i) kont) k l { s with cuBudget := B }
      = { List.foldr (fun i (kont : State → State) (s' : State) =>
            s'.guardRead (A s'.mem i) (L s'.mem i) kont) k l s with cuBudget := B } := by
  induction l with
  | nil => exact hk
  | cons i t ih => exact State.guardRead_withBudget s B (A s.mem i) (L s.mem i) _ ih

theorem State.guardSlices_withBudget (s : State) (B descsAddr count : Nat) (k : State → State)
    (hk : k { s with cuBudget := B } = { k s with cuBudget := B }) :
    ({ s with cuBudget := B } : State).guardSlices descsAddr count k
      = { s.guardSlices descsAddr count k with cuBudget := B } :=
  foldr_guardRead_withBudget (fun m i => Memory.readU64 m (descsAddr + i * 16))
    (fun m i => Memory.readU64 m (descsAddr + i * 16 + 8)) k (List.range count) s B hk

/-- Peel a guard chain on both sides of a budget-commutation goal. -/
macro "budget_comm" : tactic => `(tactic|
  repeat first
    | rfl
    | refine State.guardRead_withBudget _ _ _ _ _ ?_
    | refine State.guardWrite_withBudget _ _ _ _ _ ?_
    | refine State.guardSlices_withBudget _ _ _ _ _ ?_)

theorem State.hashWrite_withBudget (s : State) (B outPtr outLen inPtr inN : Nat)
    (digest : ByteArray) :
    ({ s with cuBudget := B } : State).hashWrite outPtr outLen inPtr inN digest
      = { s.hashWrite outPtr outLen inPtr inN digest with cuBudget := B } := by
  simp only [State.hashWrite]; budget_comm

theorem State.guardedCommit_withBudget (s : State) (B outPtr outLen inPtr inN : Nat)
    (result : Option ByteArray) :
    ({ s with cuBudget := B } : State).guardedCommit outPtr outLen inPtr inN result
      = { s.guardedCommit outPtr outLen inPtr inN result with cuBudget := B } := by
  simp only [State.guardedCommit]; budget_comm
  cases result <;> rfl

theorem Sysvar.execRent_withBudget (s : State) (B : Nat) :
    Sysvar.execRent { s with cuBudget := B } = { Sysvar.execRent s with cuBudget := B } := by
  simp only [Sysvar.execRent]; budget_comm

theorem Sysvar.execEpochSchedule_withBudget (s : State) (B : Nat) :
    Sysvar.execEpochSchedule { s with cuBudget := B }
      = { Sysvar.execEpochSchedule s with cuBudget := B } := by
  simp only [Sysvar.execEpochSchedule]; budget_comm

theorem Logging.execLogData_withBudget (s : State) (B : Nat) :
    Logging.execLogData { s with cuBudget := B } = { Logging.execLogData s with cuBudget := B } := by
  simp only [Logging.execLogData]; budget_comm

theorem Pda.execTryFind_withBudget (s : State) (B : Nat) :
    Pda.execTryFind { s with cuBudget := B } = { Pda.execTryFind s with cuBudget := B } := by
  simp only [Pda.execTryFind]; budget_comm
  dsimp only
  split <;> budget_comm

/-- Every syscall that doesn't read the budget commutes with changing it. -/
theorem execSyscall_withBudget (sc : Syscall) (s : State) (B : Nat)
    (h : sc.readsBudget = false) :
    execSyscall sc { s with cuBudget := B } = { execSyscall sc s with cuBudget := B } := by
  cases sc
  case sol_sha256 | sol_sha512 | sol_keccak256 | sol_blake3 =>
    simp only [execSyscall, Sha256.exec, Sha512.exec, Keccak256.exec, Blake3.exec]
    exact State.hashWrite_withBudget s B _ _ _ _ _
  case sol_poseidon =>
    simp only [execSyscall, Poseidon.exec]
    exact State.guardedCommit_withBudget s B _ _ _ _ _
  case sol_create_program_address =>
    simp only [execSyscall, Pda.execCreate]
    refine State.guardRead_withBudget _ _ _ _ _ ?_
    dsimp only
    exact State.guardedCommit_withBudget s B _ _ _ _ _
  case sol_try_find_program_address => exact Pda.execTryFind_withBudget s B
  case sol_get_rent_sysvar => exact Sysvar.execRent_withBudget s B
  case sol_get_epoch_schedule_sysvar => exact Sysvar.execEpochSchedule_withBudget s B
  case sol_log_data => exact Logging.execLogData_withBudget s B
  all_goals simp [Syscall.readsBudget] at h
  all_goals simp [execSyscall, commitOptional] <;> (repeat' split) <;> simp_all

theorem syscallCu_withBudget (sc : Syscall) (s : State) (B : Nat) :
    syscallCu sc { s with cuBudget := B } = syscallCu sc s := by
  cases sc <;>
    simp [syscallCu, Logging.cuLog, Pda.cuTryFind, Sysvar.cuGetSysvar, Sha256.cu, Sha512.cu,
      Keccak256.cu, Blake3.cu, Poseidon.cu, MemOps.cu, Curve25519.cuValidatePoint,
      Curve25519.cuGroupOp, Curve25519.cuMSM, AltBn128.cuGroupOp, AltBn128.cuCompression,
      BigModExp.cu, ReturnData.cuGet, ReturnData.cuSet]

theorem callxTarget_withBudget (s : State) (B : Nat) (reg : Reg) :
    callxTarget { s with cuBudget := B } reg = callxTarget s reg := rfl

/-- A step that doesn't run a budget-reading syscall commutes with changing the budget. -/
theorem step_withBudget (insn : Insn) (s : State) (B : Nat)
    (h : ∀ sc, insn = .call sc → sc.readsBudget = false) :
    step insn { s with cuBudget := B } = { step insn s with cuBudget := B } := by
  cases insn
  case call sc =>
    simp only [step]
    rw [execSyscall_withBudget sc s B (h sc rfl), syscallCu_withBudget]
  all_goals (simp only [step, execCallx, callxTarget_withBudget]; try dsimp only)
  all_goals (repeat' split) <;> first | rfl | simp_all

/-- The code at `fetch` never runs a budget-reading syscall. -/
def BudgetOblivious (fetch : Nat → Option Insn) : Prop :=
  ∀ a sc, fetch a = some (.call sc) → sc.readsBudget = false

/-- **Budget monotonicity.** On budget-oblivious code, a run that halts within `n` steps
    halts identically (same exit code, fault, and every other field) with any larger
    budget. -/
theorem executeFn_withBudget (fetch : Nat → Option Insn) (hob : BudgetOblivious fetch) :
    ∀ (n : Nat) (s : State) (B : Nat), s.cuBudget ≤ B →
      (executeFn fetch s n).exitCode.isSome →
      executeFn fetch { s with cuBudget := B } n = { executeFn fetch s n with cuBudget := B } := by
  intro n
  induction n with
  | zero => intro s B _ _; rfl
  | succ n ih =>
    intro s B hB hhalt
    by_cases hsome : ∃ c, s.exitCode = some c
    · obtain ⟨c, hc⟩ := hsome
      rw [executeFn_halted fetch s _ c hc,
          executeFn_halted fetch { s with cuBudget := B } _ c hc]
    have h0 : s.exitCode = none := by
      cases h : s.exitCode with
      | none => rfl
      | some c => exact absurd ⟨c, h⟩ hsome
    by_cases hover : s.cuConsumed ≥ s.cuBudget
    · rw [executeFn_overBudget fetch s _ h0 hover, h0] at hhalt
      exact absurd hhalt (by decide)
    have hle : s.cuConsumed < s.cuBudget := Nat.lt_of_not_le hover
    have hleB : ({ s with cuBudget := B } : State).cuConsumed
        < ({ s with cuBudget := B } : State).cuBudget := Nat.lt_of_lt_of_le hle hB
    cases hf : fetch s.pc with
    | none =>
      simp [executeFn, h0, hf, Nat.not_le.mpr hle, Nat.not_le.mpr hleB]
    | some insn =>
      rw [executeFn_step fetch s n insn h0 hle hf] at hhalt ⊢
      rw [executeFn_step fetch { s with cuBudget := B } n insn h0 hleB hf,
          step_withBudget insn s B (fun sc h => hob s.pc sc (h ▸ hf))]
      exact ih (chargeCu (step insn s)) B (by rw [chargeCu, step_preserves_cuBudget]; exact hB) hhalt

end SVM.SBPF
