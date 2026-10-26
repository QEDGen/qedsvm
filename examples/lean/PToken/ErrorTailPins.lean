/-
  End-to-end instantiation of `error_tail_fails_closed` on p_token's real program: the
  decoded `.text` serves the tail's instructions and fn 116's tree (`TailCode`), and contains
  no budget-reading syscall (`BudgetOblivious`). Both are checked in-kernel by
  `native_decide` over the decoded program. Kept separate so the standard-axiom module does
  not pull in `native_decide` or the 100 KB text literal.
-/
import PToken.ErrorTail
import SVM.SBPF.Runner
import Generated.PTokenText

namespace Examples.PTokenErrorTail

open SVM.SBPF Examples.Lifted

/-- p_token's `.text`, decoded the way the runner loads it. -/
@[irreducible] def ptokenInsns : Option (Array Insn) := Decode.decodeProgramV0 PTokenText PTokenFnRegistry

/-- Bounded check that `fetch` honors every pin of `cr` below `N`. -/
def crCheck (cr : CodeReq) (fetch : Nat → Option Insn) (N : Nat) : Bool :=
  (List.range N).all fun a => match cr a with
    | none => true
    | some i => decide (fetch a = some i)

theorem SatisfiedBy_of_crCheck (cr : CodeReq) (fetch : Nat → Option Insn) (N : Nat)
    (hdom : ∀ a, N ≤ a → cr a = none) (h : crCheck cr fetch N = true) : cr.SatisfiedBy fetch := by
  intro a i hi
  by_cases ha : a < N
  · have := List.all_eq_true.mp h a (List.mem_range.mpr ha)
    rw [hi] at this
    simpa using this
  · rw [hdom a (Nat.le_of_not_lt ha)] at hi
    cases hi

/-- No instruction is a budget-reading syscall. -/
def obliviousCheck (insns : Array Insn) : Bool :=
  insns.all fun i => match i with
    | .call sc => !sc.readsBudget
    | _ => true

theorem budgetOblivious_of_check (insns : Array Insn) (h : obliviousCheck insns = true) :
    BudgetOblivious (Runner.fetchFromArray insns) := by
  intro a sc hf
  unfold Runner.fetchFromArray at hf
  split at hf
  · rename_i ha
    injection hf with hi
    have := Array.all_eq_true.mp h a ha
    rw [hi] at this
    simpa using this
  · cases hf

/-- fn 116's code lives below PC 197. -/
theorem convCr_dom : ∀ a, 197 ≤ a → convCr a = none := by
  intro a ha
  simp (disch := omega) only [convCr, Examples.PTokenErrorConvert.crTree, CodeReq.union,
    CodeReq.singleton, CodeReq.empty, if_neg]

/-- Everything `error_tail_fails_closed` needs of a decoded program, as one Bool. -/
def tailCheckOn (insns : Array Insn) : Bool :=
  let f := Runner.fetchFromArray insns
  obliviousCheck insns && crCheck convCr f 197 &&
    decide (f 3536 = some (.mov64 .r1 (.reg .r6))) &&
    decide (f 3537 = some (.mov64 .r2 (.reg .r9))) &&
    decide (f 3538 = some (.call_local 6864)) &&
    decide (f 3539 = some (.mov64 .r1 (.reg .r6))) &&
    decide (f 3540 = some (.mov64 .r2 (.reg .r9))) &&
    decide (f 3541 = some (.call_local 116)) &&
    decide (f 3542 = some .exit) &&
    decide (f 197 = some .exit)

/-- Soundness of the check, over an abstract program. -/
theorem tailCheckOn_sound (insns : Array Insn) (h : tailCheckOn insns = true) :
    TailCode (Runner.fetchFromArray insns) ∧ BudgetOblivious (Runner.fetchFromArray insns) := by
  simp only [tailCheckOn, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hob, hconv⟩, h3536⟩, h3537⟩, h3538⟩, h3539⟩, h3540⟩, h3541⟩, h3542⟩, h197⟩ := h
  exact ⟨⟨h3536, h3537, h3538, h3539, h3540, h3541, h3542, h197,
    SatisfiedBy_of_crCheck _ _ _ convCr_dom hconv⟩, budgetOblivious_of_check _ hob⟩

/-- The check on p_token's decoded `.text`. -/
def tailCheck : Bool := ptokenInsns.all tailCheckOn

/-- Decoding succeeds and the check passes. -/
theorem tailCheck_ok : ptokenInsns.isSome = true ∧ tailCheck = true := by native_decide

/-- **p_token's error tail fails closed, on the real program.** p_token's `.text` decodes, and
    runs of the decoded program from the tail's entry (3536) with an empty call stack never
    halt with exit code 0 unless they carry a typed fault. -/
theorem ptoken_error_tail_fails_closed :
    ptokenInsns.isSome = true ∧
      ∀ insns, ptokenInsns = some insns →
        ∀ s : State, s.pc = 3536 → s.callStack = [] → s.exitCode = none →
          FailsClosed (Runner.fetchFromArray insns) s := by
  refine ⟨tailCheck_ok.1, fun insns hp s hpc hcs h0 => ?_⟩
  have h := tailCheck_ok.2
  rw [tailCheck, hp, Option.all_some] at h
  obtain ⟨hc, hob⟩ := tailCheckOn_sound insns h
  exact error_tail_fails_closed _ hc hob s hpc hcs h0

end Examples.PTokenErrorTail
