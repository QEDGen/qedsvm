/-
  Per-instruction separation-logic Hoare triples for sBPF + shared helpers.

  Each spec is `cuTripleWithin 1 0 pc (pc + 1) (CodeReq.singleton pc insn) P Q`:
  one CU per instruction (this layer; true CU pricing scales later), a CodeReq
  pinning the instruction at `pc`, and an SL pre/post over the read/written
  resources.
-/

import SVM.SBPF.CPSSpec

namespace SVM.SBPF

open Memory

/-! ## Helpers shared across syscall specs -/

/-- `ByteArray` of `N` zero bytes. -/
def zerosByteArray (N : Nat) : ByteArray :=
  ⟨Array.replicate N (0 : UInt8)⟩

@[simp] theorem zerosByteArray_size (N : Nat) :
    (zerosByteArray N).size = N := by
  show (Array.replicate N (0 : UInt8)).size = N
  exact Array.size_replicate

theorem zerosByteArray_get! (N i : Nat) (hi : i < N) :
    (zerosByteArray N).get! i = (0 : UInt8) := by
  show (Array.replicate N (0 : UInt8))[i]! = 0
  rw [getElem!_pos _ _ (by rw [Array.size_replicate]; exact hi)]
  exact Array.getElem_replicate _

/-- `Mem.read` on a coerced bare `Nat → Nat` equals the function applied:
    closure-style writes (`Sysvar.zeroFillR1` / `ReturnData.execGet`) make a
    `Mem` of form `↑(fun a => ...)` whose reads fall through `default` (empty
    overlay). -/
theorem Mem_read_default (f : Nat → Nat) (a : Nat) :
    ({ default := f } : Memory.Mem).read a = f a := by
  unfold Memory.Mem.read
  simp


end SVM.SBPF
