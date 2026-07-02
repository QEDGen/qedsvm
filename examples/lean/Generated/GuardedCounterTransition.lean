/-
  Whole-transition bundle for guarded_counter (#40 gap 1). MECHANICALLY EMITTED
  by qedlift from the per-path trace-guided lifts (one discovered
  `guarded_counter_<path>.pcs` trace per path) + the refinement descriptor. ONE
  statement covering every path: under each path's branch guards the program
  TERMINATES with that path's exit code and the tracked account codec
  transitions accordingly (preservation paths have preFields = postFields).
-/

import Generated.GuardedCounterAbortLifted
import Generated.GuardedCounterSuccessLifted

namespace Examples.GuardedCounterTransition

open SVM SVM.SBPF SVM.SBPF.Memory SVM.Solana.Abstract

theorem guarded_counter_transition
    (baseAddr amount vR2Old vR0Old counter vR3Old : Nat)
    (hamount_lt : amount < 2 ^ 64)
    (hcounter_lt : counter < 2 ^ 64)
    (h_noovf0 : counter + amount < 2 ^ 64) :
    (amount = toU64 0 →
      SVM.Solana.Abstract.AsmRefinesTransitionPath
      (((((CodeReq.singleton 0 (.ldx .dword .r2 .r1 0)).union
        (CodeReq.singleton 1 (.jeq .r2 (.imm (0)) 7))).union
        (CodeReq.singleton 7 (.mov64 .r0 (.imm (1)))))).union
        (CodeReq.singleton 8 .exit))
      (3 + 1) (0) 0
      (fun rt => rt.containsRange (effectiveAddr baseAddr 0) 8 = true)
      (toU64 1)
      [(baseAddr,
        [(8, .u64 counter)],
        [(8, .u64 counter)])]
      (((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 amount) **
      (.r2 ↦ᵣ vR2Old) **
      (.r0 ↦ᵣ vR0Old)) **
       callStackIs [])
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 amount) **
      (.r2 ↦ᵣ amount))) ∧
    (amount ≠ toU64 0 →
      SVM.Solana.Abstract.AsmRefinesTransitionPath
      (((((((((CodeReq.singleton 0 (.ldx .dword .r2 .r1 0)).union
        (CodeReq.singleton 1 (.jeq .r2 (.imm (0)) 7))).union
        (CodeReq.singleton 2 (.ldx .dword .r3 .r1 8))).union
        (CodeReq.singleton 3 (.add64 .r3 (.reg .r2)))).union
        (CodeReq.singleton 4 (.stx .dword .r1 8 .r3))).union
        (CodeReq.singleton 5 (.mov64 .r0 (.imm (0))))).union
        (CodeReq.singleton 6 (.ja 8)))).union
        (CodeReq.singleton 8 .exit))
      (7 + 1) (0) 0
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
      Examples.Lifted.GuardedCounterAbort.GuardedCounterAbort_transition_path baseAddr amount vR2Old vR0Old hamount_lt hg0 counter,
   fun hg0 =>
      Examples.Lifted.GuardedCounterSuccess.GuardedCounterSuccess_transition_path baseAddr amount vR2Old counter vR3Old vR0Old hamount_lt hcounter_lt hg0 h_noovf0⟩

end Examples.GuardedCounterTransition
