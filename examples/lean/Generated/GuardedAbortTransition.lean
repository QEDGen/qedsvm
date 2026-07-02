/-
  Whole-transition bundle for guarded_abort (#40 gap 1). MECHANICALLY EMITTED
  by qedlift from the per-path trace-guided lifts (one discovered
  `guarded_abort_<path>.pcs` trace per path) + the refinement descriptor. ONE
  statement covering every path: under each path's branch guards the program
  TERMINATES with that path's exit code (or FAULTS with its typed error) and
  the tracked account codec transitions accordingly (preservation and fault
  paths hold it fixed).
-/

import Generated.GuardedAbortPanicLifted
import Generated.GuardedAbortSuccessLifted

namespace Examples.GuardedAbortTransition

open SVM SVM.SBPF SVM.SBPF.Memory SVM.Solana.Abstract

theorem guarded_abort_transition
    (baseAddr amount vR2Old counter nCuAbort vR3Old vR0Old : Nat)
    (hamount_lt : amount < 2 ^ 64)
    (hCuAbort : ∀ s : State,
        (step (.call .abort) s).cuConsumed ≤ s.cuConsumed + nCuAbort)
    (hcounter_lt : counter < 2 ^ 64)
    (h_noovf0 : counter + amount < 2 ^ 64) :
    (amount = toU64 0 →
      SVM.Solana.Abstract.AsmRefinesTransitionFault
      ((((CodeReq.singleton 0 (.ldx .dword .r2 .r1 0)).union
        (CodeReq.singleton 1 (.jeq .r2 (.imm (0)) 7)))).union
        (CodeReq.singleton 7 (.call .abort)))
      (2 + 1) (0 + nCuAbort) 0
      (fun rt => rt.containsRange (effectiveAddr baseAddr 0) 8 = true)
      (.abort)
      [(baseAddr,
        [(8, .u64 counter)],
        [(8, .u64 counter)])]
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 amount) **
      (.r2 ↦ᵣ vR2Old))) ∧
    (amount ≠ toU64 0 →
      SVM.Solana.Abstract.AsmRefinesTransitionPath
      ((((((((CodeReq.singleton 0 (.ldx .dword .r2 .r1 0)).union
        (CodeReq.singleton 1 (.jeq .r2 (.imm (0)) 7))).union
        (CodeReq.singleton 2 (.ldx .dword .r3 .r1 8))).union
        (CodeReq.singleton 3 (.add64 .r3 (.reg .r2)))).union
        (CodeReq.singleton 4 (.stx .dword .r1 8 .r3))).union
        (CodeReq.singleton 5 (.mov64 .r0 (.imm (0)))))).union
        (CodeReq.singleton 6 .exit))
      (6 + 1) (0) 0
      (fun rt => ((rt.containsRange (effectiveAddr baseAddr 0) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 8) 8 = true) ∧
                  rt.containsWritable (effectiveAddr baseAddr 8) 8 = true)
      (toU64 0)
      [(baseAddr,
        [(8, .u64 counter)],
        [(8, .u64 (counter + amount))])]
      (((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 amount) **
      (.r2 ↦ᵣ vR2Old) **
      (.r3 ↦ᵣ vR3Old) **
      (.r0 ↦ᵣ vR0Old)) **
       callStackIs [])
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 amount) **
      (.r2 ↦ᵣ amount) **
      (.r3 ↦ᵣ wrapAdd counter amount))) :=
  ⟨fun hg0 =>
      Examples.Lifted.GuardedAbortPanic.GuardedAbortPanic_transition_fault baseAddr amount vR2Old hamount_lt hg0 counter nCuAbort hCuAbort,
   fun hg0 =>
      Examples.Lifted.GuardedAbortSuccess.GuardedAbortSuccess_transition_path baseAddr amount vR2Old counter vR3Old vR0Old hamount_lt hcounter_lt hg0 h_noovf0⟩

end Examples.GuardedAbortTransition
