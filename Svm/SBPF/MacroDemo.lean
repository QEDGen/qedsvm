/-
  First multi-instruction macro proof.

  Demonstrates the verified-macro-assembler methodology end-to-end:
  per-instruction Hoare triples (`mov64_imm_spec`) compose via the
  bounded-triple sequencing rule (`cuTripleWithin_seq`) and explicit
  frame rules (`cuTripleWithin_frame_right/left`) to produce a single
  triple for the whole macro, with a verified CU bound of 2.

  This is the killer demonstration: it proves the methodology actually
  composes, which is what separates a verified macro assembler from a
  collection of per-instruction specs.
-/

import Svm.SBPF.InstructionSpecs

namespace Svm.SBPF

/-! ## Disjointness helper for singleton code requirements -/

theorem CodeReq.singleton_disjoint_singleton {a b : Nat} (i j : Insn) (h : a ≠ b) :
    (CodeReq.singleton a i).Disjoint (CodeReq.singleton b j) := by
  intro x
  unfold CodeReq.singleton
  by_cases hxa : x = a
  · right
    have hxb : x ≠ b := hxa ▸ h
    simp [hxb]
  · left; simp [hxa]

/-! ## Two-mov macro

The sBPF macro:

```
  pc=0:  mov64 r1, 7
  pc=1:  mov64 r2, 8
```

Spec: starting from any initial values for r1 and r2, after 2 compute
units, r1 holds 7 and r2 holds 8. -/

theorem two_mov_macro_spec (vOld1 vOld2 : Nat) :
    cuTripleWithin 2 0 2
      ((CodeReq.singleton 0 (.mov64 .r1 (.imm 7))).union
       (CodeReq.singleton 1 (.mov64 .r2 (.imm 8))))
      ((.r1 ↦ᵣ vOld1) ** (.r2 ↦ᵣ vOld2))
      ((.r1 ↦ᵣ toU64 7) ** (.r2 ↦ᵣ toU64 8)) := by
  -- Step 1 (pc=0): per-instruction spec for `mov64 r1, 7`.
  have h1_base : cuTripleWithin 1 0 1
      (CodeReq.singleton 0 (.mov64 .r1 (.imm 7)))
      (.r1 ↦ᵣ vOld1)
      (.r1 ↦ᵣ toU64 7) :=
    mov64_imm_spec .r1 7 vOld1 0 (by decide)
  -- Frame in r2's old value (pcFree side condition discharged automatically).
  have h1 :=
    cuTripleWithin_frame_right (.r2 ↦ᵣ vOld2) (pcFree_regIs _ _) h1_base
  -- Step 2 (pc=1): per-instruction spec for `mov64 r2, 8`.
  have h2_base : cuTripleWithin 1 1 2
      (CodeReq.singleton 1 (.mov64 .r2 (.imm 8)))
      (.r2 ↦ᵣ vOld2)
      (.r2 ↦ᵣ toU64 8) :=
    mov64_imm_spec .r2 8 vOld2 1 (by decide)
  -- Frame in r1's already-set value on the left.
  have h2 :=
    cuTripleWithin_frame_left (.r1 ↦ᵣ toU64 7) (pcFree_regIs _ _) h2_base
  -- Disjointness of the two singleton code requirements (different PCs).
  have hd := CodeReq.singleton_disjoint_singleton
    (.mov64 .r1 (.imm 7)) (.mov64 .r2 (.imm 8)) (by decide : (0 : Nat) ≠ 1)
  -- Sequential composition: 1 + 1 = 2 CU, code reqs union.
  exact cuTripleWithin_seq hd h1 h2

/-! ## Computation macro: `r1 := 10 + 5`

A two-instruction macro that performs actual arithmetic:

```
  pc=0:  mov64 r1, 10
  pc=1:  add64 r1, 5
```

After 2 compute units, r1 holds `wrapAdd (toU64 10) (toU64 5) = 15`.
Both instructions are framed onto the singleton `(.r1 ↦ᵣ vOld)`; no
auxiliary register needed. The intermediate value is `toU64 10` —
threaded through the composition via the seq rule's intermediate
assertion. -/

theorem add_constants_macro_spec (vOld : Nat) :
    cuTripleWithin 2 0 2
      ((CodeReq.singleton 0 (.mov64 .r1 (.imm 10))).union
       (CodeReq.singleton 1 (.add64 .r1 (.imm 5))))
      (.r1 ↦ᵣ vOld)
      (.r1 ↦ᵣ wrapAdd (toU64 10) (toU64 5)) := by
  have h1 : cuTripleWithin 1 0 1
      (CodeReq.singleton 0 (.mov64 .r1 (.imm 10)))
      (.r1 ↦ᵣ vOld)
      (.r1 ↦ᵣ toU64 10) :=
    mov64_imm_spec .r1 10 vOld 0 (by decide)
  have h2 : cuTripleWithin 1 1 2
      (CodeReq.singleton 1 (.add64 .r1 (.imm 5)))
      (.r1 ↦ᵣ toU64 10)
      (.r1 ↦ᵣ wrapAdd (toU64 10) (toU64 5)) :=
    add64_imm_spec .r1 5 (toU64 10) 1 (by decide)
  have hd := CodeReq.singleton_disjoint_singleton
    (.mov64 .r1 (.imm 10)) (.add64 .r1 (.imm 5)) (by decide : (0 : Nat) ≠ 1)
  exact cuTripleWithin_seq hd h1 h2

end Svm.SBPF
