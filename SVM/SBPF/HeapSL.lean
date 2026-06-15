/-
  Separation-logic predicates for the SVM program heap (the embedded bump
  allocator). These name the allocator state so a lifted triple reads as "the
  bump pointer moved, a block now holds X" rather than bare memory cells. Thin
  wrappers over `memU64Is` / `memBytesIs`, so a lifted spec folds into them
  definitionally (no proof obligation). Worked re-statement of the `heap_alloc`
  lift: `examples/lean/HeapAllocSpec.lean`.
-/

import SVM.SBPF.SepLogic
import SVM.SBPF.Memory

namespace SVM.SBPF

open Memory

/-- The bump pointer lives in the `u64` slot at `HEAP_START` (= 0x300000000);
    `heapBumpPtr p` asserts that slot holds `p`. -/
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
