/-
  End-to-end instantiation of `panic_sites_fail_closed` on p_token's real program: the
  decoded `.text` serves the panic chain (`PanicCode`), checked in-kernel by `native_decide`.
-/
import PToken.PanicChain
import PToken.ErrorTailPins

namespace Examples.PTokenPanicChain

open SVM.SBPF Examples.PTokenErrorTail

/-- Bool form of `StraightRun`. -/
def straightCheck (fetch : Nat → Option Insn) (pc k : Nat) : Bool :=
  (List.range k).all fun i => match fetch (pc + i) with
    | some insn => insn.isStraight
    | none => false

theorem straightRun_of_check (fetch : Nat → Option Insn) (pc k : Nat)
    (h : straightCheck fetch pc k = true) : StraightRun fetch pc k := by
  intro i hi
  have := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  revert this
  cases fetch (pc + i) with
  | none => intro h; cases h
  | some insn => intro h; exact ⟨insn, rfl, h⟩

/-- Everything `panic_sites_fail_closed` needs of a decoded program, as one Bool. -/
def panicCheckOn (insns : Array Insn) : Bool :=
  let f := Runner.fetchFromArray insns
  decide (f 11177 = some (.call_local 11618)) && straightCheck f 11618 22 &&
    decide (f 11640 = some (.call_local 10862)) && straightCheck f 10881 22 &&
    decide (f 10903 = some (.call_local 10862)) && straightCheck f 10862 5 &&
    decide (f 10867 = some (.call_local 10823)) && straightCheck f 10823 6 &&
    decide (f 10829 = some (.call .sol_panic_)) &&
    panicSites.all fun site =>
      decide (f site = some (.call_local 11177)) || decide (f site = some (.call_local 10881))

theorem panicCheckOn_sound (insns : Array Insn) (h : panicCheckOn insns = true) :
    PanicCode (Runner.fetchFromArray insns) := by
  simp only [panicCheckOn, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h11177, r11618⟩, h11640⟩, r10881⟩, h10903⟩, r10862⟩, h10867⟩, r10823⟩,
    h10829⟩, hsites⟩ := h
  refine ⟨h11177, straightRun_of_check _ _ _ r11618, h11640, straightRun_of_check _ _ _ r10881,
    h10903, straightRun_of_check _ _ _ r10862, h10867, straightRun_of_check _ _ _ r10823, h10829,
    fun site hsite => ?_⟩
  have := List.all_eq_true.mp hsites site hsite
  simpa only [Bool.or_eq_true, decide_eq_true_eq] using this

/-- The check on p_token's decoded `.text`. -/
def panicCheck : Bool := ptokenInsns.all panicCheckOn

theorem panicCheck_ok : panicCheck = true := by native_decide

/-- **p_token's panic sites abort, on the real program.** From any of the 12 sites, with any
    call stack, runs of the decoded `.text` never halt with exit code 0 unless they carry a
    typed fault. -/
theorem ptoken_panic_sites_fail_closed :
    ∀ insns, ptokenInsns = some insns →
      ∀ site ∈ panicSites, ∀ s : State, s.pc = site → s.exitCode = none →
        FailsClosed (Runner.fetchFromArray insns) s := by
  intro insns hp site hsite s hpc h0
  have h := panicCheck_ok
  rw [panicCheck, hp, Option.all_some] at h
  exact panic_sites_fail_closed _ (panicCheckOn_sound insns h) site hsite s hpc h0

end Examples.PTokenPanicChain
