/-
  Separation-logic predicates for the SVM program heap (the embedded bump
  allocator). A heap-allocating program's lift owns raw `↦U64` / `↦Bytes`
  cells at fixed heap addresses (`MM_HEAP_START` and the allocated block);
  these predicates name the allocator state so a lifted triple reads as
  "the bump pointer moved, a block now holds X" rather than bare memory
  cells. They are thin wrappers over `memU64Is` / `memBytesIs`, so a
  lifted spec folds into them definitionally (no proof obligation).

  See `examples/lean/HeapAllocSpec.lean` for the worked re-statement of
  the `heap_alloc` lift via these predicates.
-/

import SVM.SBPF.SepLogic
import SVM.SBPF.Memory

namespace SVM.SBPF

open Memory

/-- The embedded bump allocator keeps its current position in the `u64`
    slot at the start of the heap region (`MM_HEAP_START` = 0x300000000).
    `heapBumpPtr p` asserts that slot holds pointer `p`. -/
def heapBumpPtr (p : Nat) : Assertion := memU64Is HEAP_START p

/-- A `u64`-sized allocated heap block at `addr` holding value `v`. -/
def heapBlockU64 (addr v : Nat) : Assertion := memU64Is addr v

/-- An allocated heap block of `bs.size` bytes at `addr`. -/
def heapBlock (addr : Nat) (bs : ByteArray) : Assertion := memBytesIs addr bs

@[simp] theorem heapBumpPtr_eq (p : Nat) :
    heapBumpPtr p = memU64Is HEAP_START p := rfl

@[simp] theorem heapBlockU64_eq (addr v : Nat) :
    heapBlockU64 addr v = memU64Is addr v := rfl

@[simp] theorem heapBlock_eq (addr : Nat) (bs : ByteArray) :
    heapBlock addr bs = memBytesIs addr bs := rfl

end SVM.SBPF
