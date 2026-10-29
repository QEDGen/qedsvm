/-
  Regression for the generic no-return checker (solana-skills#450): the witness that
  `qed_analysis::discover::noreturn` emits for p_token proves the same fact as the
  hand-written `panic_helpers_noReturn`, with no p_token-specific proof.
-/
import SVM.SBPF.NoReturnCheck
import PToken.ErrorTailPins

namespace Examples.PTokenNoReturnGeneric

open SVM.SBPF Examples.PTokenErrorTail

/-- Emitted by `qed-discover` for `tests/fixtures/p_token.so`. -/
def ptNoRetWitness : NoRetWitness :=
  { heads := [10823, 10858, 10862, 10868, 10881, 11177, 11618]
    steps := [.panicCall 10829, .straight 10823 6, .callLocal 10867 10823, .straight 10862 5, .callLocal 10880 10862, .straight 10868 12, .callLocal 10861 10868, .straight 10858 3, .callLocal 10903 10862, .straight 10881 22, .callLocal 11640 10862, .straight 11618 22, .callLocal 11177 11618] }

theorem ptNoRetWitness_ok : ptokenInsns.all (fun insns =>
    noRetCheck (Runner.fetchFromArray insns) ptNoRetWitness) = true := by
  native_decide

theorem ptNoret_generic (insns : Array Insn) (hp : ptokenInsns = some insns) :
    ∀ t, (t == 11177 || t == 10881) = true → NoReturn (Runner.fetchFromArray insns) t := by
  have h := ptNoRetWitness_ok
  rw [hp, Option.all_some] at h
  intro t ht
  apply noRetCheck_sound _ _ h
  simp only [Bool.or_eq_true, beq_iff_eq] at ht
  rcases ht with rfl | rfl <;> simp [ptNoRetWitness]

end Examples.PTokenNoReturnGeneric
