-- Tests for `SyscallSem` (#95): proofs that hold for any syscall semantics.

import SVM.SBPF.SyscallSem

namespace SVM.SBPF.SyscallSemTests

open SVM.SBPF

/-! ## A syscall, through its contract

`call sol_sha256; mov64 r0, 0; exit`. The proof holds for every `S` whose
`sol_sha256` meets the contract below; it never unfolds `Sha256.exec`, whose
hash is Rust behind `@[extern]`. -/

def hashThenExit : Nat → Option Insn
  | 0 => some (.call .sol_sha256)
  | 1 => some (.mov64 .r0 (.imm 0))
  | 2 => some .exit
  | _ => none

/-- What the proof needs of `sol_sha256`: it does not fault, push a frame or
    move the CU meter. -/
def HashContract (S : SyscallSem) (s : State) : Prop :=
  let s' := S.exec .sol_sha256 s
  s'.exitCode = none ∧ s'.callStack = [] ∧
    s'.cuConsumed = s.cuConsumed ∧ s'.cuBudget = s.cuBudget

theorem hashThenExit_exits (S : SyscallSem) (s : State)
    (h_pc : s.pc = 0) (h_run : s.exitCode = none)
    (h_contract : HashContract S s)
    (h_bud : s.cuConsumed + 3 + S.cu .sol_sha256 s ≤ s.cuBudget) :
    (executeFnWith S hashThenExit s 3).exitCode = some 0 := by
  obtain ⟨h_ec, h_cs, h_cu, h_cb⟩ := h_contract
  rw [executeFnWith_step S _ s 2 (.call .sol_sha256) h_run (by omega)
    (by simp [hashThenExit, h_pc]) (chargeExceedsWith_call_false _ _ _ (by omega))]
  rw [executeFnWith_step S _ _ 1 (.mov64 .r0 (.imm 0)) (by simpa using h_ec)
    (by simp [h_cu, h_cb]; omega) (by simp [hashThenExit, h_pc])]
  rw [executeFnWith_step S _ _ 0 .exit (by simpa using h_ec)
    (by simp [h_cu, h_cb]; omega) (by simp [hashThenExit, h_pc])]
  simp [h_cs]

/-- The builtin `sol_sha256` charges what `syscallCu` says. -/
example (s : State) : SyscallSem.builtin.cu .sol_sha256 s = syscallCu .sol_sha256 s := rfl

/-! ## No syscall: a proof about `executeFn` holds for every `S` -/

def addThenExit : Nat → Option Insn
  | 0 => some (.mov64 .r0 (.imm 3))
  | 1 => some (.add64 .r0 (.imm 4))
  | 2 => some .exit
  | _ => none

theorem addThenExit_noSyscall : ∀ pc sc, addThenExit pc ≠ some (.call sc) := by
  intro pc sc h
  match pc, h with
  | 0, h | 1, h | 2, h | _ + 3, h => simp [addThenExit] at h

theorem addThenExit_exits (s : State) (h_pc : s.pc = 0) (h_run : s.exitCode = none)
    (h_cs : s.callStack = []) (h_bud : s.cuConsumed + 3 ≤ s.cuBudget) :
    (executeFn addThenExit s 3).exitCode = some 7 := by
  rw [executeFn_step _ s 2 (.mov64 .r0 (.imm 3)) h_run (by omega) (by simp [addThenExit, h_pc])]
  rw [executeFn_step _ _ 1 (.add64 .r0 (.imm 4)) (by simpa using h_run)
    (by simp; omega) (by simp [addThenExit, h_pc])]
  rw [executeFn_step _ _ 0 .exit (by simpa using h_run)
    (by simp; omega) (by simp [addThenExit, h_pc])]
  simp [h_cs, RegFile.get, RegFile.set, resolveSrc, toU64, U64_MODULUS]

/-- The same fact under any syscall semantics, with no new proof. -/
theorem addThenExit_exits_any (S : SyscallSem) (s : State) (h_pc : s.pc = 0)
    (h_run : s.exitCode = none) (h_cs : s.callStack = [])
    (h_bud : s.cuConsumed + 3 ≤ s.cuBudget) :
    (executeFnWith S addThenExit s 3).exitCode = some 7 := by
  rw [executeFnWith_eq_of_noSyscall S addThenExit_noSyscall]
  exact addThenExit_exits s h_pc h_run h_cs h_bud

end SVM.SBPF.SyscallSemTests
