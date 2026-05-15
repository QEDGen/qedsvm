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

/-- Two singleton CodeReqs are Disjoint when their addresses differ. -/
theorem singleton_disjoint_singleton {a b : Nat} (i j : Insn) (h : a ≠ b) :
    (CodeReq.singleton a i).Disjoint (CodeReq.singleton b j) := by
  intro x
  unfold CodeReq.singleton
  by_cases hxa : x = a
  · right
    have hxb : x ≠ b := hxa ▸ h
    simp [hxb]
  · left; simp [hxa]

/-- Disjointness lifts through union on the left. -/
theorem Disjoint_union_left {cr1 cr2 cr3 : CodeReq}
    (h1 : cr1.Disjoint cr3) (h2 : cr2.Disjoint cr3) :
    (cr1.union cr2).Disjoint cr3 := by
  intro a
  rcases h1 a with h_cr1 | h_cr3
  · rcases h2 a with h_cr2 | h_cr3'
    · left
      show (match cr1 a with | some i => some i | none => cr2 a) = none
      rw [h_cr1, h_cr2]
    · right; exact h_cr3'
  · right; exact h_cr3

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

/-! ## Memory-aware triple

`cuTripleWithinMem` extends `cuTripleWithin` with a persistent side
condition on `s.regions`. Memory ops (ldx/st/stx) need this because
`step` traps to `ERR_ACCESS_VIOLATION` when the accessed range isn't
covered by the region table — that check is a property of `s` (not
something an assertion can own from `PartialState`), so it lives
alongside `CodeReq` as a separate persistent input.

`s.regions` is never mutated by `step` (see
`executeFn_preserves_regions`), so once `rr` holds at entry it holds
throughout the macro — composition just conjuncts. -/

def cuTripleWithinMem (nSteps : Nat) (entry exit_ : Nat) (cr : CodeReq)
    (P Q : Assertion) (rr : Memory.RegionTable → Prop) : Prop :=
  ∀ (R : Assertion), R.pcFree →
  ∀ (fetch : Nat → Option Insn), cr.SatisfiedBy fetch →
  ∀ (s : State), (P ** R).holdsFor s → s.pc = entry → s.exitCode = none →
    rr s.regions →
    ∃ k, k ≤ nSteps ∧
      (executeFn fetch s k).pc = exit_ ∧
      (executeFn fetch s k).exitCode = none ∧
      (Q ** R).holdsFor (executeFn fetch s k)

/-- Every non-memory triple is also a memory triple with no region
    requirement. Lets ALU/jump specs compose with memory specs. -/
theorem cuTripleWithin.toMem {nSteps entry exit_ : Nat} {cr : CodeReq}
    {P Q : Assertion}
    (h : cuTripleWithin nSteps entry exit_ cr P Q) :
    cuTripleWithinMem nSteps entry exit_ cr P Q (fun _ => True) := by
  intro R hR fetch hcr s hPR hpc hex _
  exact h R hR fetch hcr s hPR hpc hex

/-- Sequential composition for memory triples: bound sums, code reqs
    union, region conditions conjunct. Uses `executeFn_preserves_regions`
    to carry `rr2` past the first segment. -/
theorem cuTripleWithinMem_seq {N1 N2 : Nat} {pc1 pc2 pc3 : Nat}
    {cr1 cr2 : CodeReq} (hd : cr1.Disjoint cr2)
    {P Q R : Assertion} {rr1 rr2 : Memory.RegionTable → Prop}
    (h1 : cuTripleWithinMem N1 pc1 pc2 cr1 P Q rr1)
    (h2 : cuTripleWithinMem N2 pc2 pc3 cr2 Q R rr2) :
    cuTripleWithinMem (N1 + N2) pc1 pc3 (cr1.union cr2) P R
      (fun rt => rr1 rt ∧ rr2 rt) := by
  intro F hF fetch hcr s hPF hpc hex h_reg
  obtain ⟨hreg1, hreg2⟩ := h_reg
  have hcr1 := CodeReq.SatisfiedBy_of_union_left hcr
  have hcr2 := CodeReq.SatisfiedBy_of_union_right hd hcr
  obtain ⟨k1, hk1, hpc_mid, hex_mid, hQF⟩ :=
    h1 F hF fetch hcr1 s hPF hpc hex hreg1
  have h_reg_mid : rr2 (executeFn fetch s k1).regions := by
    rw [executeFn_preserves_regions]; exact hreg2
  obtain ⟨k2, hk2, hpc_end, hex_end, hRF⟩ :=
    h2 F hF fetch hcr2 (executeFn fetch s k1) hQF hpc_mid hex_mid h_reg_mid
  refine ⟨k1 + k2, Nat.add_le_add hk1 hk2, ?_, ?_, ?_⟩
  · rw [executeFn_compose]; exact hpc_end
  · rw [executeFn_compose]; exact hex_end
  · rw [executeFn_compose]; exact hRF

/-- Frame rule for memory triples (right). -/
theorem cuTripleWithinMem_frame_right (F : Assertion) (hF : F.pcFree)
    {N : Nat} {pc1 pc2 : Nat} {cr : CodeReq} {P Q : Assertion}
    {rr : Memory.RegionTable → Prop}
    (h : cuTripleWithinMem N pc1 pc2 cr P Q rr) :
    cuTripleWithinMem N pc1 pc2 cr (P ** F) (Q ** F) rr := by
  intro R hR fetch hcr s hPFR hpc hex h_reg
  have hFR_pcfree : (F ** R).pcFree := pcFree_sepConj hF hR
  have hP_FR : (P ** (F ** R)).holdsFor s := holdsFor_sepConj_assoc.mp hPFR
  obtain ⟨k, hk, hpc', hex', hQFR⟩ :=
    h (F ** R) hFR_pcfree fetch hcr s hP_FR hpc hex h_reg
  refine ⟨k, hk, hpc', hex', ?_⟩
  exact holdsFor_sepConj_assoc.mpr hQFR

/-- Rule of consequence for memory triples: strengthen the pre, weaken
    the post, and strengthen `rr` (caller's stronger region claim implies
    the spec's weaker one). -/
theorem cuTripleWithinMem_weaken {nSteps : Nat} {entry exit_ : Nat} {cr : CodeReq}
    {P P' Q Q' : Assertion} {rr rr' : Memory.RegionTable → Prop}
    (hpre  : ∀ h, P' h → P h)
    (hpost : ∀ h, Q h → Q' h)
    (h_rr  : ∀ rt, rr' rt → rr rt)
    (h : cuTripleWithinMem nSteps entry exit_ cr P Q rr) :
    cuTripleWithinMem nSteps entry exit_ cr P' Q' rr' := by
  intro R hR fetch hcr s hP'R hpc hex h_reg'
  have hPR : (P ** R).holdsFor s := by
    obtain ⟨hp, hcompat, h1, h2, hd, hu, hP'1, hR2⟩ := hP'R
    exact ⟨hp, hcompat, h1, h2, hd, hu, hpre h1 hP'1, hR2⟩
  obtain ⟨k, hk, hpc', hex', hQR⟩ :=
    h R hR fetch hcr s hPR hpc hex (h_rr _ h_reg')
  refine ⟨k, hk, hpc', hex', ?_⟩
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hQ1, hR2⟩ := hQR
  exact ⟨hp, hcompat, h1, h2, hd, hu, hpost h1 hQ1, hR2⟩

/-- Memory + pure composition: chain a memory triple with a pure triple
    (lifted via `.toMem`), keeping only the memory triple's region
    requirement. Without this, `cuTripleWithinMem_seq` would add a
    trivial `True` conjunct to the chain's `rr` for every pure step. -/
theorem cuTripleWithinMem_seq_pure_right {N1 N2 : Nat} {pc1 pc2 pc3 : Nat}
    {cr1 cr2 : CodeReq} (hd : cr1.Disjoint cr2)
    {P Q R : Assertion} {rr : Memory.RegionTable → Prop}
    (h1 : cuTripleWithinMem N1 pc1 pc2 cr1 P Q rr)
    (h2 : cuTripleWithin N2 pc2 pc3 cr2 Q R) :
    cuTripleWithinMem (N1 + N2) pc1 pc3 (cr1.union cr2) P R rr :=
  cuTripleWithinMem_weaken (fun _ x => x) (fun _ x => x)
    (fun _ x => And.intro x True.intro)
    (cuTripleWithinMem_seq hd h1 h2.toMem)

/-- Pure + memory composition: chain a pure triple (lifted via `.toMem`)
    with a memory triple, keeping only the memory triple's region
    requirement. Mirror of `cuTripleWithinMem_seq_pure_right`. -/
theorem cuTripleWithinMem_seq_pure_left {N1 N2 : Nat} {pc1 pc2 pc3 : Nat}
    {cr1 cr2 : CodeReq} (hd : cr1.Disjoint cr2)
    {P Q R : Assertion} {rr : Memory.RegionTable → Prop}
    (h1 : cuTripleWithin N1 pc1 pc2 cr1 P Q)
    (h2 : cuTripleWithinMem N2 pc2 pc3 cr2 Q R rr) :
    cuTripleWithinMem (N1 + N2) pc1 pc3 (cr1.union cr2) P R rr :=
  cuTripleWithinMem_weaken (fun _ x => x) (fun _ x => x)
    (fun _ x => And.intro True.intro x)
    (cuTripleWithinMem_seq hd h1.toMem h2)

/-- Frame rule for memory triples (left). -/
theorem cuTripleWithinMem_frame_left (F : Assertion) (hF : F.pcFree)
    {N : Nat} {pc1 pc2 : Nat} {cr : CodeReq} {P Q : Assertion}
    {rr : Memory.RegionTable → Prop}
    (h : cuTripleWithinMem N pc1 pc2 cr P Q rr) :
    cuTripleWithinMem N pc1 pc2 cr (F ** P) (F ** Q) rr := by
  intro R hR fetch hcr s hPFR hpc hex h_reg
  -- F ** P ** R → P ** F ** R via comm; apply frame_right; then swap back.
  have h' := cuTripleWithinMem_frame_right F hF h
  -- h' : cuTripleWithinMem N pc1 pc2 cr (P ** F) (Q ** F) rr
  have hPFR' : ((P ** F) ** R).holdsFor s := by
    have : ((F ** P) ** R).holdsFor s ↔ ((P ** F) ** R).holdsFor s :=
      holdsFor_iff_pointwise (fun h => by
        constructor
        · rintro ⟨h1, h2, hd, hu, hFP, hRsat⟩
          exact ⟨h1, h2, hd, hu, (sepConj_comm h1).mp hFP, hRsat⟩
        · rintro ⟨h1, h2, hd, hu, hPF, hRsat⟩
          exact ⟨h1, h2, hd, hu, (sepConj_comm h1).mp hPF, hRsat⟩)
    exact this.mp hPFR
  obtain ⟨k, hk, hpc', hex', hQFR⟩ := h' R hR fetch hcr s hPFR' hpc hex h_reg
  refine ⟨k, hk, hpc', hex', ?_⟩
  have : ((Q ** F) ** R).holdsFor (executeFn fetch s k) ↔
         ((F ** Q) ** R).holdsFor (executeFn fetch s k) :=
    holdsFor_iff_pointwise (fun h => by
      constructor
      · rintro ⟨h1, h2, hd, hu, hQF, hRsat⟩
        exact ⟨h1, h2, hd, hu, (sepConj_comm h1).mp hQF, hRsat⟩
      · rintro ⟨h1, h2, hd, hu, hFQ, hRsat⟩
        exact ⟨h1, h2, hd, hu, (sepConj_comm h1).mp hFQ, hRsat⟩)
  exact this.mp hQFR

/-! ## Reshape wrappers for `**` permutations

Specializations of `_weaken` that take a pointwise iff instead of a
one-directional implication. The elab-level permutation builder in
`SLTactic.lean` (`sl_block_iter`) emits iffs by construction; these
wrappers let the caller plug the iff directly without manually packaging
its `.mp` direction. -/

/-- Reshape the post of a triple via a pointwise iff `Q ↔ Q'`. Takes
    the iff in OLD ↔ NEW orientation (so the chain's existing post is
    on the left). -/
theorem cuTripleWithin_reshape_post {N pc1 pc2 : Nat} {cr : CodeReq}
    {P Q Q' : Assertion}
    (iff_post : ∀ h, Q h ↔ Q' h)
    (h : cuTripleWithin N pc1 pc2 cr P Q) :
    cuTripleWithin N pc1 pc2 cr P Q' :=
  cuTripleWithin_weaken (fun _ x => x) (fun hp hQ => (iff_post hp).mp hQ) h

/-- Reshape the pre of a triple via a pointwise iff `P ↔ P'`. Takes
    the iff in OLD ↔ NEW orientation (chain's existing pre on the
    left). The lemma applies `.mpr` to convert the new pre `P'` back
    into the old `P` needed by `weaken`. -/
theorem cuTripleWithin_reshape_pre {N pc1 pc2 : Nat} {cr : CodeReq}
    {P P' Q : Assertion}
    (iff_pre : ∀ h, P h ↔ P' h)
    (h : cuTripleWithin N pc1 pc2 cr P Q) :
    cuTripleWithin N pc1 pc2 cr P' Q :=
  cuTripleWithin_weaken (fun hp hP' => (iff_pre hp).mpr hP') (fun _ x => x) h

theorem cuTripleWithinMem_reshape_post {N pc1 pc2 : Nat} {cr : CodeReq}
    {P Q Q' : Assertion} {rr : Memory.RegionTable → Prop}
    (iff_post : ∀ h, Q h ↔ Q' h)
    (h : cuTripleWithinMem N pc1 pc2 cr P Q rr) :
    cuTripleWithinMem N pc1 pc2 cr P Q' rr :=
  cuTripleWithinMem_weaken (fun _ x => x) (fun hp hQ => (iff_post hp).mp hQ)
    (fun _ x => x) h

theorem cuTripleWithinMem_reshape_pre {N pc1 pc2 : Nat} {cr : CodeReq}
    {P P' Q : Assertion} {rr : Memory.RegionTable → Prop}
    (iff_pre : ∀ h, P h ↔ P' h)
    (h : cuTripleWithinMem N pc1 pc2 cr P Q rr) :
    cuTripleWithinMem N pc1 pc2 cr P' Q rr :=
  cuTripleWithinMem_weaken (fun hp hP' => (iff_pre hp).mpr hP') (fun _ x => x)
    (fun _ x => x) h

/-! ## SL ↔ WP bridge — concrete-execution corollary

`cuTripleWithinMem N entry exit_ cr P Q rr` is universally quantified over
`fetch` and a pc-free frame `R`. Specializing `R := emp` collapses the
triple to a concrete statement about `executeFn`: given any specific
`fetch` honoring `cr`, any state where `P` holds with `pc = entry` and
the region requirement met, running ≤ N steps lands at `pc = exit_` with
`Q` holding.

This is the link between the two methodologies in this repo:

- **SL track** (`cuTripleWithin{,Mem}` + `Svm.SBPF.SLTactic`) is
  compositional. Per-instruction specs live in `InstructionSpecs.lean`;
  the `seq` + frame rules sum CU bounds, union code requirements, and
  preserve disjoint resources. Use SL when building a *library* of
  reusable macro specs whose users don't know the surrounding program.

- **WP track** (`Svm.SBPF.WPTactic.wp_exec`) is concrete-execution.
  Given a fixed compiled program (concrete `fetch`) and a concrete fuel
  bound, `wp_exec` unfolds `executeFn` step-by-step and discharges the
  resulting goal. Use WP when proving a *specific compiled program*
  satisfies a closed property (terminates with a given exitCode).

`cuTripleWithinMem.toExec` lets an SL spec downgrade to a WP-style fact
about `executeFn`. A macro library proven in the SL discipline becomes
directly usable inside a `wp_exec`-style proof of an end-to-end program:
the SL macro yields `executeFn fetch s k = s'` for some `k ≤ CU-bound`,
and the surrounding `wp_exec` proof composes its before/after segments
around that k-step jump. -/

/-- Bridge: a `cuTripleWithinMem` triple specializes to a concrete fact
    on `executeFn`. The pc-free frame `R` is instantiated to `emp`, so
    `P` and `Q` need not be sepConj'd with anything at the use site. -/
theorem cuTripleWithinMem.toExec {N entry exit_ : Nat} {cr : CodeReq}
    {P Q : Assertion} {rr : Memory.RegionTable → Prop}
    (h : cuTripleWithinMem N entry exit_ cr P Q rr)
    {fetch : Nat → Option Insn} (hcr : cr.SatisfiedBy fetch)
    {s : State} (hP : P.holdsFor s) (hpc : s.pc = entry)
    (hex : s.exitCode = none) (h_reg : rr s.regions) :
    ∃ k, k ≤ N ∧
      (executeFn fetch s k).pc = exit_ ∧
      (executeFn fetch s k).exitCode = none ∧
      Q.holdsFor (executeFn fetch s k) := by
  have hP_emp : (P ** emp).holdsFor s :=
    (holdsFor_iff_pointwise sepConj_emp_right).mpr hP
  obtain ⟨k, hk, hpc', hex', hQ_emp⟩ :=
    h emp pcFree_emp fetch hcr s hP_emp hpc hex h_reg
  refine ⟨k, hk, hpc', hex', ?_⟩
  exact (holdsFor_iff_pointwise sepConj_emp_right).mp hQ_emp

/-- Bridge for non-memory triples: convenience wrapper that routes
    through `cuTripleWithin.toMem` and discharges the trivial region
    requirement. -/
theorem cuTripleWithin.toExec {N entry exit_ : Nat} {cr : CodeReq}
    {P Q : Assertion}
    (h : cuTripleWithin N entry exit_ cr P Q)
    {fetch : Nat → Option Insn} (hcr : cr.SatisfiedBy fetch)
    {s : State} (hP : P.holdsFor s) (hpc : s.pc = entry)
    (hex : s.exitCode = none) :
    ∃ k, k ≤ N ∧
      (executeFn fetch s k).pc = exit_ ∧
      (executeFn fetch s k).exitCode = none ∧
      Q.holdsFor (executeFn fetch s k) :=
  h.toMem.toExec hcr hP hpc hex trivial

end Svm.SBPF
