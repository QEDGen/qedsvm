/-
  Whole-transition obligation, worked end-to-end on real bytecode (#40 gap 1).

  `guarded_counter.so` denotes the transition
      `if amount = 0 then abort 1 else counter += amount; return 0`.
  Its refinement decomposes per path, each discharged from a trace-guided
  qedlift running triple (`Generated.GuardedCounter{Success,Abort}Lifted`)
  composed with the shared `.exit` at pc 8 via `cuTripleWithinMem_seq_exit`:

  * SUCCESS (`amount ≠ 0`): exits with code 0, the tracked account codec
    carrying `counter + amount`;
  * ABORT (`amount = 0`): exits with code 1, the tracked account codec
    UNCHANGED — preservation is syntactic (`preFields = postFields`); the
    counter cell is never in the abort path's footprint, so it is framed
    through the lift and owned by the codec in the obligation.

  `guarded_counter_transition` bundles both paths into the single
  statement shape qedgen's per-arm conformance denotes.
-/

import SVM.SBPF.Tactic.SL
import SVM.Solana.Abstract.Transition
import Generated.GuardedCounterSuccessLifted
import Generated.GuardedCounterAbortLifted

namespace Examples.GuardedCounterTransition

open SVM SVM.SBPF SVM.SBPF.Memory SVM.Solana.Abstract
open Examples.Lifted.GuardedCounterSuccess Examples.Lifted.GuardedCounterAbort

/-- The guarded counter's tracked layout: `amount` arg at offset 0,
    `counter` field at offset 8. -/
def gcFields (amount counter : Nat) : List (Nat × FieldVal) :=
  [(0, .u64 amount), (8, .u64 counter)]

set_option maxHeartbeats 800000 in
/-- SUCCESS path: under the guard `amount ≠ 0`, the program terminates with
    exit code 0 and the account codec carries the credited counter. -/
theorem guarded_counter_success_path
    (baseAddr amount counter vR2Old vR3Old vR0Old : Nat)
    (h_amount_lt : amount < 2 ^ 64)
    (h_counter_lt : counter < 2 ^ 64)
    (h_guard : amount ≠ toU64 0)
    (h_noovf : counter + amount < 2 ^ 64) :
    AsmRefinesTransitionPath
      ((((((((CodeReq.singleton 0 (.ldx .dword .r2 .r1 0)).union
        (CodeReq.singleton 1 (.jeq .r2 (.imm (0)) 7))).union
        (CodeReq.singleton 2 (.ldx .dword .r3 .r1 8))).union
        (CodeReq.singleton 3 (.add64 .r3 (.reg .r2)))).union
        (CodeReq.singleton 4 (.stx .dword .r1 8 .r3))).union
        (CodeReq.singleton 5 (.mov64 .r0 (.imm (0))))).union
        (CodeReq.singleton 6 (.ja 8))).union
        (CodeReq.singleton 8 .exit))
      (7 + 1) 0 0
      (fun rt => ((rt.containsRange (effectiveAddr baseAddr 0) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 8) 8 = true) ∧
                  rt.containsWritable (effectiveAddr baseAddr 8) 8 = true)
      (toU64 0)
      [(baseAddr, gcFields amount counter, gcFields amount (counter + amount))]
      ((.r1 ↦ᵣ baseAddr) ** (.r2 ↦ᵣ vR2Old) ** (.r3 ↦ᵣ vR3Old) **
       (.r0 ↦ᵣ vR0Old) ** callStackIs [])
      ((.r1 ↦ᵣ baseAddr) ** (.r2 ↦ᵣ amount) **
       (.r3 ↦ᵣ wrapAdd counter amount)) := by
  unfold AsmRefinesTransitionPath
  simp only [codecsPre, codecsPost, gcFields, codecCoarse, FieldVal.coarse,
             sepConj_emp_right_eq, Nat.add_zero]
  refine cuTripleWithinMem_seq_exit ?_ ?_
  · repeat' apply CodeReq.Disjoint_union_left
    all_goals exact CodeReq.singleton_disjoint_singleton _ _ (by decide)
  · rw [← wrapAdd_of_lt h_noovf]
    have framed := cuTripleWithinMem_frame_right (callStackIs [])
      (pcFree_callStackIs _)
      (GuardedCounterSuccess_lifted_spec baseAddr amount vR2Old counter
        vR3Old vR0Old h_amount_lt h_counter_lt h_guard)
    sl_exact framed

set_option maxHeartbeats 800000 in
/-- ABORT path: under the failed guard `amount = 0`, the program terminates
    with exit code 1 and the account codec UNCHANGED (the counter cell is
    outside the path's footprint — framed through the lift). -/
theorem guarded_counter_abort_path
    (baseAddr amount counter vR2Old vR0Old : Nat)
    (h_amount_lt : amount < 2 ^ 64)
    (h_guard : amount = toU64 0) :
    AsmRefinesTransitionPath
      ((((CodeReq.singleton 0 (.ldx .dword .r2 .r1 0)).union
        (CodeReq.singleton 1 (.jeq .r2 (.imm (0)) 7))).union
        (CodeReq.singleton 7 (.mov64 .r0 (.imm (1))))).union
        (CodeReq.singleton 8 .exit))
      (3 + 1) 0 0
      (fun rt => rt.containsRange (effectiveAddr baseAddr 0) 8 = true)
      (toU64 1)
      [(baseAddr, gcFields amount counter, gcFields amount counter)]
      ((.r1 ↦ᵣ baseAddr) ** (.r2 ↦ᵣ vR2Old) ** (.r0 ↦ᵣ vR0Old) **
       callStackIs [])
      ((.r1 ↦ᵣ baseAddr) ** (.r2 ↦ᵣ amount)) := by
  unfold AsmRefinesTransitionPath
  simp only [codecsPre, codecsPost, gcFields, codecCoarse, FieldVal.coarse,
             sepConj_emp_right_eq, Nat.add_zero]
  refine cuTripleWithinMem_seq_exit ?_ ?_
  · repeat' apply CodeReq.Disjoint_union_left
    all_goals exact CodeReq.singleton_disjoint_singleton _ _ (by decide)
  · have framed := cuTripleWithinMem_frame_right
      ((effectiveAddr baseAddr 8 ↦U64 counter) ** callStackIs [])
      (by sl_pcfree)
      (GuardedCounterAbort_lifted_spec baseAddr amount vR2Old vR0Old
        h_amount_lt h_guard)
    sl_exact framed

/-- The WHOLE transition (#40 gap 1): one statement covering every path —
    the Lean analogue of qedgen's per-arm conformance shape. Under each
    path's guard, the program terminates with that path's exit code and the
    tracked account codec transitions accordingly (abort: unchanged). -/
theorem guarded_counter_transition
    (baseAddr amount counter vR2Old vR3Old vR0Old : Nat)
    (h_amount_lt : amount < 2 ^ 64)
    (h_counter_lt : counter < 2 ^ 64) :
    (amount ≠ toU64 0 → counter + amount < 2 ^ 64 →
      AsmRefinesTransitionPath
        ((((((((CodeReq.singleton 0 (.ldx .dword .r2 .r1 0)).union
          (CodeReq.singleton 1 (.jeq .r2 (.imm (0)) 7))).union
          (CodeReq.singleton 2 (.ldx .dword .r3 .r1 8))).union
          (CodeReq.singleton 3 (.add64 .r3 (.reg .r2)))).union
          (CodeReq.singleton 4 (.stx .dword .r1 8 .r3))).union
          (CodeReq.singleton 5 (.mov64 .r0 (.imm (0))))).union
          (CodeReq.singleton 6 (.ja 8))).union
          (CodeReq.singleton 8 .exit))
        (7 + 1) 0 0
        (fun rt => ((rt.containsRange (effectiveAddr baseAddr 0) 8 = true) ∧
                    rt.containsRange (effectiveAddr baseAddr 8) 8 = true) ∧
                    rt.containsWritable (effectiveAddr baseAddr 8) 8 = true)
        (toU64 0)
        [(baseAddr, gcFields amount counter,
          gcFields amount (counter + amount))]
        ((.r1 ↦ᵣ baseAddr) ** (.r2 ↦ᵣ vR2Old) ** (.r3 ↦ᵣ vR3Old) **
         (.r0 ↦ᵣ vR0Old) ** callStackIs [])
        ((.r1 ↦ᵣ baseAddr) ** (.r2 ↦ᵣ amount) **
         (.r3 ↦ᵣ wrapAdd counter amount))) ∧
    (amount = toU64 0 →
      AsmRefinesTransitionPath
        ((((CodeReq.singleton 0 (.ldx .dword .r2 .r1 0)).union
          (CodeReq.singleton 1 (.jeq .r2 (.imm (0)) 7))).union
          (CodeReq.singleton 7 (.mov64 .r0 (.imm (1))))).union
          (CodeReq.singleton 8 .exit))
        (3 + 1) 0 0
        (fun rt => rt.containsRange (effectiveAddr baseAddr 0) 8 = true)
        (toU64 1)
        [(baseAddr, gcFields amount counter, gcFields amount counter)]
        ((.r1 ↦ᵣ baseAddr) ** (.r2 ↦ᵣ vR2Old) ** (.r0 ↦ᵣ vR0Old) **
         callStackIs [])
        ((.r1 ↦ᵣ baseAddr) ** (.r2 ↦ᵣ amount))) :=
  ⟨fun h_guard h_noovf =>
      guarded_counter_success_path baseAddr amount counter vR2Old vR3Old
        vR0Old h_amount_lt h_counter_lt h_guard h_noovf,
   fun h_guard =>
      guarded_counter_abort_path baseAddr amount counter vR2Old vR0Old
        h_amount_lt h_guard⟩

end Examples.GuardedCounterTransition
