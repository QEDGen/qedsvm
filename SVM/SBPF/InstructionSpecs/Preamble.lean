/-
  Per-instruction separation-logic Hoare triples for sBPF.

  Each spec is `cuTripleWithin 1 pc (pc + 1) (CodeReq.singleton pc insn) P Q`:
  one compute unit per instruction (in this layer — true CU pricing will
  scale this in a later phase), code requirement pinning the instruction at
  `pc`, and a separation-logic pre/post over the resources the instruction
  reads and writes.

  This file currently proves only the simplest cases — pure-ALU 64-bit moves
  — from first principles, as a methodology proof-of-concept. The pattern
  generalizes via to-be-built `generic_*_spec` helpers (Phase A / B).
-/

import SVM.SBPF.CPSSpec

namespace SVM.SBPF

open Memory

/-! ## Helpers shared across syscall specs.

Hoisted to the top of the file so they're in scope for every spec below. -/

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

/-- Bridge lemma: `Mem.read` on a coerced bare `Nat → Nat` function
    equals the function applied. The closure-style memory writes in
    `Sysvar.zeroFillR1` / `ReturnData.execGet` produce a `Mem` of the
    form `↑(fun a => ...)`, so reads fall through `default` (the
    HashMap overlay is empty). -/
theorem Mem_read_default (f : Nat → Nat) (a : Nat) :
    ({ default := f } : Memory.Mem).read a = f a := by
  unfold Memory.Mem.read
  simp


end SVM.SBPF
