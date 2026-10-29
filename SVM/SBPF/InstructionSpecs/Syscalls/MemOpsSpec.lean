import SVM.SBPF.InstructionSpecs.Preamble

/-! # Functional memop specs (#103)

The state after each memop body (`MemOps.exec*`) for general lengths, under
region, overlap and alignment conditions on its argument registers, and the
first-difference characterization of memcmp. Alias-agnostic: `moveMem` reads
the original memory, so an overlapping memmove is exact. The separation-logic
triples in `Mem.lean` and `MemOpsGeneral.lean` are proved from these.

CU is agave's `mem_op_consume`: `max(10, n / 250)` (`MemOps.cu_of_lt`,
`MemOps.cu_of_ge`), charged before the body, so a fault keeps it. -/

namespace SVM.SBPF

open Memory

/-! ## CU -/

theorem MemOps.cu_of_lt (s : State) (h : s.regs.r3 < 2750) : MemOps.cu s = 10 := by
  simp only [MemOps.cu, Nat.max]; omega

theorem MemOps.cu_of_ge (s : State) (h : 2750 ≤ s.regs.r3) :
    MemOps.cu s = s.regs.r3 / 250 := by
  simp only [MemOps.cu, Nat.max]; omega

/-! ## Overlap -/

/-- agave's overlap check is exactly range disjointness. -/
theorem MemOps.nonoverlapping_iff (src dst n : Nat) :
    MemOps.nonoverlapping src dst n = true ↔ src + n ≤ dst ∨ dst + n ≤ src := by
  unfold MemOps.nonoverlapping
  split <;> simp only [decide_eq_true_eq] <;> omega

/-! ## `moveMem` -/

theorem MemOps.moveMem_in (m : Mem) (dst src n i : Nat) (hi : i < n) :
    MemOps.moveMem m dst src n (dst + i) = m (src + i) % 256 := by
  unfold MemOps.moveMem
  rw [Mem_read_default, if_pos ⟨Nat.le_add_right _ _, by omega⟩,
    show dst + i - dst = i by omega]

theorem MemOps.moveMem_out (m : Mem) (dst src n a : Nat) (h : a < dst ∨ dst + n ≤ a) :
    MemOps.moveMem m dst src n a = m a := by
  unfold MemOps.moveMem
  rw [Mem_read_default, if_neg (by omega)]

/-! ## Functional specs: memmove and memcpy -/

/-- The memmove body when both slices are in region (or `n = 0`). -/
theorem MemOps.execMove_ok (s : State)
    (hsrc : s.regs.r3 = 0 ∨ s.regions.containsRange s.regs.r2 s.regs.r3 = true)
    (hdst : s.regs.r3 = 0 ∨ s.regions.containsWritable s.regs.r1 s.regs.r3 = true) :
    MemOps.execMove s =
      { s with regs := s.regs.set .r0 0,
               mem := MemOps.moveMem s.mem s.regs.r1 s.regs.r2 s.regs.r3 } := by
  simp only [MemOps.execMove, State.guardRead, State.guardWrite]
  rw [if_pos hsrc, if_pos hdst]

/-- Either nonempty slice out of region faults; which one is checked first is
    unobservable. -/
theorem MemOps.execMove_fault (s : State) (hn : s.regs.r3 ≠ 0)
    (h : s.regions.containsRange s.regs.r2 s.regs.r3 = false ∨
         s.regions.containsWritable s.regs.r1 s.regs.r3 = false) :
    MemOps.execMove s = s.accessFault := by
  simp only [MemOps.execMove, State.guardRead, State.guardWrite]
  by_cases hs : s.regions.containsRange s.regs.r2 s.regs.r3 = true
  · rw [if_pos (Or.inr hs)]
    have hd : s.regions.containsWritable s.regs.r1 s.regs.r3 = false := by
      rcases h with h | h
      · rw [hs] at h; nomatch h
      · exact h
    rw [if_neg (by simp [hn, hd])]
  · rw [if_neg (by simp [hn, hs])]

theorem MemOps.execCopy_ok (s : State)
    (hno : MemOps.nonoverlapping s.regs.r2 s.regs.r1 s.regs.r3 = true) :
    MemOps.execCopy s = MemOps.execMove s := by
  unfold MemOps.execCopy; rw [if_pos hno]

/-- An overlapping memcpy faults before either pointer is translated. -/
theorem MemOps.execCopy_overlap (s : State)
    (hov : MemOps.nonoverlapping s.regs.r2 s.regs.r1 s.regs.r3 = false) :
    MemOps.execCopy s =
      { s with exitCode := some ERR_COPY_OVERLAPPING, vmError := some .copyOverlapping } := by
  unfold MemOps.execCopy; rw [if_neg (by simp [hov])]

/-! ## Functional specs: memset -/

theorem MemOps.execSet_ok (s : State)
    (hdst : s.regs.r3 = 0 ∨ s.regions.containsWritable s.regs.r1 s.regs.r3 = true) :
    MemOps.execSet s =
      { s with regs := s.regs.set .r0 0,
               mem := (fun a => if a ≥ s.regs.r1 ∧ a - s.regs.r1 < s.regs.r3
                         then s.regs.r2 % 256 else s.mem a : Nat → Nat) } := by
  simp only [MemOps.execSet, State.guardWrite]
  rw [if_pos hdst]

theorem MemOps.execSet_fault (s : State) (hn : s.regs.r3 ≠ 0)
    (h : s.regions.containsWritable s.regs.r1 s.regs.r3 = false) :
    MemOps.execSet s = s.accessFault := by
  simp only [MemOps.execSet, State.guardWrite]
  rw [if_neg (by simp [hn, h])]

/-! ## Functional specs: memcmp -/

/-- The sign-carrying difference at the first index where `a` and `b` differ
    among `0 .. n-1`, else `0`. Both memcmp folds are instances. -/
def MemOps.firstDiff (a b : Nat → Nat) (n : Nat) : Int :=
  (List.range n).foldl (fun acc i => if acc ≠ 0 then acc else (a i : Int) - (b i : Int)) 0

/-- Two's-complement u32 encoding of memcmp's `i32` result. -/
def MemOps.cmpU32 (c : Int) : Nat := if c ≥ 0 then c.toNat else U32_MODULUS - (-c).toNat

/-- The comparison `execCmp` computes over memory. -/
def MemOps.cmpMem (m : Mem) (p1 p2 n : Nat) : Int :=
  MemOps.firstDiff (fun i => m (p1 + i) % 256) (fun i => m (p2 + i) % 256) n

/-- memcmp with both inputs in region, a writable and 4-aligned result. -/
theorem MemOps.execCmp_ok (s : State)
    (h1 : s.regs.r3 = 0 ∨ s.regions.containsRange s.regs.r1 s.regs.r3 = true)
    (h2 : s.regs.r3 = 0 ∨ s.regions.containsRange s.regs.r2 s.regs.r3 = true)
    (hout : s.regions.containsWritable s.regs.r4 4 = true)
    (halign : s.regs.r4 % 4 = 0) :
    MemOps.execCmp s =
      { s with regs := s.regs.set .r0 0,
               mem := writeU32 s.mem s.regs.r4
                 (MemOps.cmpU32 (MemOps.cmpMem s.mem s.regs.r1 s.regs.r2 s.regs.r3)) } := by
  simp only [MemOps.execCmp, State.guardRead, State.guardWrite]
  rw [if_pos h1, if_pos h2, if_pos (Or.inr hout), if_neg (not_not_intro halign)]
  rfl

theorem MemOps.execCmp_fault (s : State)
    (h : (s.regs.r3 ≠ 0 ∧ s.regions.containsRange s.regs.r1 s.regs.r3 = false) ∨
         (s.regs.r3 ≠ 0 ∧ s.regions.containsRange s.regs.r2 s.regs.r3 = false) ∨
         s.regions.containsWritable s.regs.r4 4 = false) :
    MemOps.execCmp s = s.accessFault := by
  simp only [MemOps.execCmp, State.guardRead, State.guardWrite]
  by_cases g1 : s.regs.r3 = 0 ∨ s.regions.containsRange s.regs.r1 s.regs.r3 = true
  · rw [if_pos g1]
    by_cases g2 : s.regs.r3 = 0 ∨ s.regions.containsRange s.regs.r2 s.regs.r3 = true
    · rw [if_pos g2]
      have g3 : ¬ ((4 : Nat) = 0 ∨ s.regions.containsWritable s.regs.r4 4 = true) := by
        rcases h with ⟨hn, h⟩ | ⟨hn, h⟩ | h
        · rcases g1 with g | g
          · exact absurd g hn
          · rw [g] at h; nomatch h
        · rcases g2 with g | g
          · exact absurd g hn
          · rw [g] at h; nomatch h
        · simp [h]
      rw [if_neg g3]
    · rw [if_neg g2]
  · rw [if_neg g1]

/-- A writable but unaligned result faults after the region checks. -/
theorem MemOps.execCmp_unaligned (s : State)
    (h1 : s.regs.r3 = 0 ∨ s.regions.containsRange s.regs.r1 s.regs.r3 = true)
    (h2 : s.regs.r3 = 0 ∨ s.regions.containsRange s.regs.r2 s.regs.r3 = true)
    (hout : s.regions.containsWritable s.regs.r4 4 = true)
    (halign : s.regs.r4 % 4 ≠ 0) :
    MemOps.execCmp s =
      { s with exitCode := some ERR_UNALIGNED_POINTER, vmError := some .unalignedPointer } := by
  simp only [MemOps.execCmp, State.guardRead, State.guardWrite]
  rw [if_pos h1, if_pos h2, if_pos (Or.inr hout), if_pos halign]

/-! ## memcmp is a lexicographic comparison on the first difference -/

private theorem firstDiff_foldl_stable (a b : Nat → Nat) (l : List Nat) (acc : Int)
    (h : acc ≠ 0) :
    l.foldl (fun acc i => if acc ≠ 0 then acc else (a i : Int) - (b i : Int)) acc = acc := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons, if_pos h]; exact ih

/-- Equal on the whole prefix: the result is `0`. -/
theorem MemOps.firstDiff_eq_zero (a b : Nat → Nat) (n : Nat)
    (h : ∀ j, j < n → a j = b j) : MemOps.firstDiff a b n = 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    unfold MemOps.firstDiff at ih ⊢
    rw [List.range_succ, List.foldl_append, ih (fun j hj => h j (by omega))]
    simp only [List.foldl_cons, List.foldl_nil, ne_eq, not_true_eq_false, if_false,
      h k (by omega), Int.sub_self]

/-- The first differing index `i < n` decides the result: `a i - b i`. -/
theorem MemOps.firstDiff_eq_of_first (a b : Nat → Nat) (n i : Nat) (hin : i < n)
    (hpre : ∀ j, j < i → a j = b j) (hne : a i ≠ b i) :
    MemOps.firstDiff a b n = (a i : Int) - (b i : Int) := by
  have hd : (a i : Int) - (b i : Int) ≠ 0 := by omega
  have hi : MemOps.firstDiff a b (i + 1) = (a i : Int) - (b i : Int) := by
    unfold MemOps.firstDiff
    rw [List.range_succ, List.foldl_append]
    have h0 := MemOps.firstDiff_eq_zero a b i hpre
    unfold MemOps.firstDiff at h0
    rw [h0]
    simp only [List.foldl_cons, List.foldl_nil, ne_eq, not_true_eq_false, if_false]
  obtain ⟨k, rfl⟩ : ∃ k, n = i + 1 + k := ⟨n - (i + 1), by omega⟩
  unfold MemOps.firstDiff at hi ⊢
  rw [List.range_add, List.foldl_append, hi]
  exact firstDiff_foldl_stable a b _ _ hd

end SVM.SBPF
