/-
  The `heap_alloc` program's Hoare triple, restated via the heap-allocator
  SL predicates (`SVM/SBPF/HeapSL.lean`). Where `HeapAllocLifted` owns raw
  `↦U64` cells at fixed heap addresses, this reads as a clean allocation
  claim: the bump slot moves from its old position to the block address
  `0x30007ff0`, and the allocated block ends holding 42. Derived from the
  mechanically-lifted triple — the predicates fold in definitionally.
-/

import Generated.HeapAllocLifted
import SVM.SBPF.HeapSL

namespace Examples.HeapAllocSpec
open SVM SVM.SBPF SVM.SBPF.Memory
open Examples.Lifted.HeapAlloc

/-- `heap_alloc`, stated over the allocator predicates: `heapBumpPtr` (the
    bump slot at `MM_HEAP_START`) advances from `oldMemD_0` to the block
    pointer `0x30007ff0`, and `heapBlockU64` (the freshly allocated block,
    initially `oldMemD_1`) ends holding `42`. -/
theorem HeapAlloc_allocates
    (baseAddr oldMemD_0 vR2Old oldMemD_1 vR0Old : Nat)
    (holdMemD_0_lt : oldMemD_0 < 2 ^ 64)
    (hReloadLt_5 : toU64 42 % 2 ^ (8 * 8) < 2 ^ 64)
    : cuTripleWithinMem 7 0 0 7
      ((((((((CodeReq.singleton 0 (.lddw .r1 (12884901888))).union
        (CodeReq.singleton 1 (.ldx .dword .r2 .r1 0))).union
        (CodeReq.singleton 2 (.lddw .r2 (12884934640)))).union
        (CodeReq.singleton 3 (.stx .dword .r1 0 .r2))).union
        (CodeReq.singleton 4 (.st .dword .r2 0 (42)))).union
        (CodeReq.singleton 5 (.ldx .dword .r1 .r2 0))).union
        (CodeReq.singleton 6 (.mov64 .r0 (.imm (0))))))
      ((.r1 ↦ᵣ baseAddr) **
      (heapBumpPtr oldMemD_0) **
      (.r2 ↦ᵣ vR2Old) **
      (heapBlockU64 (toU64 12884934640) oldMemD_1) **
      (.r0 ↦ᵣ vR0Old))
      ((.r1 ↦ᵣ toU64 42 % 2 ^ (8 * 8)) **
      (heapBumpPtr (toU64 12884934640)) **
      (.r2 ↦ᵣ toU64 12884934640) **
      (heapBlockU64 (toU64 12884934640) (toU64 42 % 2 ^ (8 * 8))) **
      (.r0 ↦ᵣ toU64 0))
      (fun rt => (((rt.containsRange (effectiveAddr (toU64 12884901888) 0) 8 = true) ∧
                  rt.containsWritable (effectiveAddr (toU64 12884901888) 0) 8 = true) ∧
                  rt.containsWritable (effectiveAddr (toU64 12884934640) 0) 8 = true) ∧
                  rt.containsRange (effectiveAddr (toU64 12884934640) 0) 8 = true) := by
  simp only [heapBumpPtr, heapBlockU64]
  exact HeapAlloc_lifted_spec baseAddr oldMemD_0 vR2Old oldMemD_1 vR0Old
    holdMemD_0_lt hReloadLt_5

end Examples.HeapAllocSpec
