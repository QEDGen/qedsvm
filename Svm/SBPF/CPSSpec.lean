/-
  Bounded Hoare triples for sBPF code.

  Following Jensen/Benton/Kennedy (POPL 2013, PPDP 2013) and the
  EvmAsm.Rv64.CPSSpec adaptation in Verified-zkEVM/evm-asm.

  The primary specification form is `cuTripleWithin N entry exit cr P Q`:

    For every pc-free frame R and every `fetch` satisfying the code
    requirement `cr`, starting from any state where (P ** R) holds,
    pc = entry, and exitCode = none, there exists k ≤ N such that
    `executeFn fetch s k` ends with pc = exit, exitCode = none, and
    (Q ** R) holds.

  The step bound `N` doubles as a verified compute-unit budget. Compose
  two triples and the bounds add; a whole program's CU bound is the sum
  of its macros' bounds. This is the link from Solana's transaction CU
  cap to a Lean-checked static analysis.

  Frame rule is baked into the definition (universal R). Triples therefore
  only describe the resources their code actually reads or writes.
-/

import Svm.SBPF.SepLogic

namespace Svm.SBPF

/-! ## CodeReq — persistent code-layout side condition

A `CodeReq` is a partial map from program-counter values to instructions.
It is *persistent* (not consumed) — every execution under the triple is
quantified over a `fetch` that satisfies the layout. -/

abbrev CodeReq := Nat → Option Insn

namespace CodeReq

/-- The empty code requirement. -/
def empty : CodeReq := fun _ => none

/-- A code requirement consisting of a single (address, instruction) pair. -/
def singleton (a : Nat) (i : Insn) : CodeReq :=
  fun a' => if a' = a then some i else none

/-- A fetch function satisfies a code requirement when every address the
    requirement pins down is honored by the fetch. -/
def SatisfiedBy (cr : CodeReq) (fetch : Nat → Option Insn) : Prop :=
  ∀ a i, cr a = some i → fetch a = some i

/-- Union of two code requirements (left-biased). -/
def union (cr1 cr2 : CodeReq) : CodeReq :=
  fun a => match cr1 a with | some i => some i | none => cr2 a

/-- Two requirements are disjoint when they never pin the same address. -/
def Disjoint (cr1 cr2 : CodeReq) : Prop :=
  ∀ a, cr1 a = none ∨ cr2 a = none

theorem singleton_satisfied {cr : CodeReq} {fetch : Nat → Option Insn} {a : Nat} {i : Insn}
    (hcr : cr.SatisfiedBy fetch) (hpin : cr a = some i) : fetch a = some i :=
  hcr a i hpin

theorem singleton_self {a : Nat} {i : Insn} :
    (CodeReq.singleton a i) a = some i := by
  unfold singleton; simp

theorem SatisfiedBy_singleton {fetch : Nat → Option Insn} {a : Nat} {i : Insn} :
    (singleton a i).SatisfiedBy fetch ↔ fetch a = some i := by
  unfold SatisfiedBy singleton
  constructor
  · intro h; exact h a i (by simp)
  · intro h a' i' hpin
    by_cases hae : a' = a
    · simp [hae] at hpin; rw [hae, ← hpin]; exact h
    · simp [hae] at hpin

/-- If a fetch satisfies a union of code requirements, it satisfies each
    requirement individually. -/
theorem SatisfiedBy_of_union_left {cr1 cr2 : CodeReq} {fetch : Nat → Option Insn}
    (h : (cr1.union cr2).SatisfiedBy fetch) : cr1.SatisfiedBy fetch := by
  intro a i hpin
  apply h a i
  show (match cr1 a with | some i => some i | none => cr2 a) = some i
  rw [hpin]

theorem SatisfiedBy_of_union_right {cr1 cr2 : CodeReq} {fetch : Nat → Option Insn}
    (hd : cr1.Disjoint cr2) (h : (cr1.union cr2).SatisfiedBy fetch) :
    cr2.SatisfiedBy fetch := by
  intro a i hpin
  apply h a i
  rcases hd a with hl | hr
  · show (match cr1 a with | some i => some i | none => cr2 a) = some i
    rw [hl, hpin]
  · rw [hr] at hpin; nomatch hpin

end CodeReq

/-! ## Bounded CPS-style triple -/

/-- `cuTripleWithin N entry exit_ cr P Q`:

    For every pc-free frame `R` and every instruction-fetch function
    `fetch` honoring the code requirement `cr`, starting from a state
    where `P ** R` holds, the program counter equals `entry`, and the
    machine is running (exitCode = none), execution reaches in at most
    `N` steps a state where the program counter equals `exit_`, the
    machine is still running, and `Q ** R` holds.

    Frame rule is built in (universal R, R must be pc-free).
    The bound `N` is a verified compute-unit budget. -/
def cuTripleWithin (nSteps : Nat) (entry exit_ : Nat) (cr : CodeReq)
    (P Q : Assertion) : Prop :=
  ∀ (R : Assertion), R.pcFree →
  ∀ (fetch : Nat → Option Insn), cr.SatisfiedBy fetch →
  ∀ (s : State), (P ** R).holdsFor s → s.pc = entry → s.exitCode = none →
    ∃ k, k ≤ nSteps ∧
      (executeFn fetch s k).pc = exit_ ∧
      (executeFn fetch s k).exitCode = none ∧
      (Q ** R).holdsFor (executeFn fetch s k)

/-! ## Structural rules -/

/-- Rule of consequence: strengthen the precondition, weaken the
    postcondition, keep the step bound. -/
theorem cuTripleWithin_weaken {nSteps : Nat} {entry exit_ : Nat} {cr : CodeReq}
    {P P' Q Q' : Assertion}
    (hpre  : ∀ h, P' h → P h)
    (hpost : ∀ h, Q h → Q' h)
    (h : cuTripleWithin nSteps entry exit_ cr P Q) :
    cuTripleWithin nSteps entry exit_ cr P' Q' := by
  intro R hR fetch hcr s hP'R hpc hex
  have hPR : (P ** R).holdsFor s := by
    obtain ⟨hp, hcompat, h1, h2, hd, hu, hP'1, hR2⟩ := hP'R
    exact ⟨hp, hcompat, h1, h2, hd, hu, hpre h1 hP'1, hR2⟩
  obtain ⟨k, hk, hpc', hex', hQR⟩ := h R hR fetch hcr s hPR hpc hex
  refine ⟨k, hk, hpc', hex', ?_⟩
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hQ1, hR2⟩ := hQR
  exact ⟨hp, hcompat, h1, h2, hd, hu, hpost h1 hQ1, hR2⟩

/-- Monotonicity in the step bound: a triple with bound `N` is also a
    triple with bound `N' ≥ N`. -/
theorem cuTripleWithin_mono_nSteps {nSteps nSteps' : Nat} {entry exit_ : Nat}
    {cr : CodeReq} {P Q : Assertion}
    (hle : nSteps ≤ nSteps')
    (h : cuTripleWithin nSteps entry exit_ cr P Q) :
    cuTripleWithin nSteps' entry exit_ cr P Q := by
  intro R hR fetch hcr s hPR hpc hex
  obtain ⟨k, hk, hpc', hex', hQR⟩ := h R hR fetch hcr s hPR hpc hex
  exact ⟨k, Nat.le_trans hk hle, hpc', hex', hQR⟩

/-- Zero-step triple: if `P ⇒ Q` pointwise and entry = exit_, the triple
    holds with bound 0. -/
theorem cuTripleWithin_refl {entry : Nat} {P Q : Assertion}
    (h : ∀ hp, P hp → Q hp) :
    cuTripleWithin 0 entry entry CodeReq.empty P Q := by
  intro R _ _ _ s hPR hpc hex
  refine ⟨0, Nat.le_refl 0, ?_, ?_, ?_⟩
  · simp [hpc]
  · simp [hex]
  · simp only [executeFn]
    obtain ⟨hp, hcompat, h1, h2, hd, hu, hP1, hR2⟩ := hPR
    exact ⟨hp, hcompat, h1, h2, hd, hu, h h1 hP1, hR2⟩

/-- Sequential composition: chain two triples with the intermediate
    assertion / PC matching, union the code requirements (disjoint), and
    sum the compute-unit bounds.

    This is the core machinery for verifying multi-instruction macros. -/
theorem cuTripleWithin_seq {N1 N2 : Nat} {pc1 pc2 pc3 : Nat} {cr1 cr2 : CodeReq}
    (hd : cr1.Disjoint cr2)
    {P Q R : Assertion}
    (h1 : cuTripleWithin N1 pc1 pc2 cr1 P Q)
    (h2 : cuTripleWithin N2 pc2 pc3 cr2 Q R) :
    cuTripleWithin (N1 + N2) pc1 pc3 (cr1.union cr2) P R := by
  intro F hF fetch hcr s hPF hpc hex
  have hcr1 := CodeReq.SatisfiedBy_of_union_left hcr
  have hcr2 := CodeReq.SatisfiedBy_of_union_right hd hcr
  obtain ⟨k1, hk1, hpc_mid, hex_mid, hQF⟩ := h1 F hF fetch hcr1 s hPF hpc hex
  obtain ⟨k2, hk2, hpc_end, hex_end, hRF⟩ :=
    h2 F hF fetch hcr2 (executeFn fetch s k1) hQF hpc_mid hex_mid
  refine ⟨k1 + k2, Nat.add_le_add hk1 hk2, ?_, ?_, ?_⟩
  · rw [executeFn_compose]; exact hpc_end
  · rw [executeFn_compose]; exact hex_end
  · rw [executeFn_compose]; exact hRF

/-- Explicit frame rule (right): adding a pc-free assertion `F` to both
    sides of a triple preserves it. Derived from the universal `R`
    quantification in the triple definition by re-associating
    `(P ** F) ** R = P ** (F ** R)`. -/
theorem cuTripleWithin_frame_right (F : Assertion) (hF : F.pcFree)
    {N : Nat} {pc1 pc2 : Nat} {cr : CodeReq} {P Q : Assertion}
    (h : cuTripleWithin N pc1 pc2 cr P Q) :
    cuTripleWithin N pc1 pc2 cr (P ** F) (Q ** F) := by
  intro R hR fetch hcr s hPFR hpc hex
  have hFR_pcfree : (F ** R).pcFree := pcFree_sepConj hF hR
  have hP_FR : (P ** (F ** R)).holdsFor s := holdsFor_sepConj_assoc.mp hPFR
  obtain ⟨k, hk, hpc', hex', hQFR⟩ :=
    h (F ** R) hFR_pcfree fetch hcr s hP_FR hpc hex
  refine ⟨k, hk, hpc', hex', ?_⟩
  exact holdsFor_sepConj_assoc.mpr hQFR

/-- Explicit frame rule (left): adding a pc-free assertion `F` on the
    left of a triple preserves it. Derived from `frame_right` via
    `sepConj_comm`. -/
theorem cuTripleWithin_frame_left (F : Assertion) (hF : F.pcFree)
    {N : Nat} {pc1 pc2 : Nat} {cr : CodeReq} {P Q : Assertion}
    (h : cuTripleWithin N pc1 pc2 cr P Q) :
    cuTripleWithin N pc1 pc2 cr (F ** P) (F ** Q) :=
  cuTripleWithin_weaken
    (fun hp hFP => (sepConj_comm hp).mp hFP)
    (fun hp hQF => (sepConj_comm hp).mp hQF)
    (cuTripleWithin_frame_right F hF h)

end Svm.SBPF
