/-
  Bounded Hoare triples for sBPF code, after Jensen/Benton/Kennedy (POPL
  2013, PPDP 2013) and the EvmAsm.Rv64.CPSSpec adaptation in
  Verified-zkEVM/evm-asm. Primary form: `cuTripleWithin nSteps nCu entry
  exit cr P Q` (see the def docstring).

  The bound is TWO indices: `nSteps` counts instructions (each charges 1
  baseline CU into `cuConsumed` — H5 total metering), `nCu` upper-bounds
  the syscall surcharge; total agave-CU = `nSteps + nCu` (`nCu = 0` for
  non-syscall code). Composing adds both bounds.

  The budget side-condition (`cuConsumed + nSteps + nCu ≤ cuBudget`) is
  what makes the triple sound against the VM's fail-closed budget halt:
  `executeFn` stops (OutOfBudget) once `cuConsumed > cuBudget`, so
  "reaches exit still running" only holds when the window provably fits.
  `_seq` splits the budget via `executeFn_preserves_cuBudget`.

  Frame rule is baked in (universal R), so triples describe only the
  resources their code reads or writes.
-/

import SVM.SBPF.SepLogic

namespace SVM.SBPF

/-! ## CodeReq — persistent code-layout side condition: a partial pc →
instruction map, never consumed (every execution is quantified over a
`fetch` satisfying it). -/

abbrev CodeReq := Nat → Option Insn

namespace CodeReq

/-- The empty code requirement. -/
def empty : CodeReq := fun _ => none

/-- A code requirement consisting of a single (address, instruction) pair. -/
def singleton (a : Nat) (i : Insn) : CodeReq :=
  fun a' => if a' = a then some i else none

/-- A fetch satisfies a `CodeReq` when it honors every address the req pins. -/
def SatisfiedBy (cr : CodeReq) (fetch : Nat → Option Insn) : Prop :=
  ∀ a i, cr a = some i → fetch a = some i

/-- Union of two code requirements (left-biased). -/
def union (cr1 cr2 : CodeReq) : CodeReq :=
  fun a => match cr1 a with | some i => some i | none => cr2 a

/-- Two requirements are disjoint when they never pin the same address. -/
def Disjoint (cr1 cr2 : CodeReq) : Prop :=
  ∀ a, cr1 a = none ∨ cr2 a = none

/-- Helper for `fromList`: left-folds `(pc, insn)` pairs into `acc ∪ s₁ ∪ …`.
    Separate def so the shape matches the hand-written
    `(((s₀.union s₁).union s₂)…)` form, preserving `isDefEq` against the
    chain `sl_block_iter` builds. -/
def fromListAux : CodeReq → List (Nat × Insn) → CodeReq
  | acc, [] => acc
  | acc, (a, i) :: rest => fromListAux (acc.union (singleton a i)) rest

/-- Build a `CodeReq` from `(pc, insn)` pairs, in the same left-folded
    `singleton ∪ …` shape as the hand-written arm-file chains (so `unfold`
    sees identical Expr structure). See `cr![ … ]` for the literal form. -/
def fromList : List (Nat × Insn) → CodeReq
  | [] => empty
  | (a, i) :: rest => fromListAux (singleton a i) rest

/-! ### Reduction lemmas for `fromList` — it reduces by `rfl`; these let
`simp only [...]` drive the reduction where named rewrites beat `unfold`. -/

theorem fromListAux_nil (acc : CodeReq) : fromListAux acc [] = acc := rfl

theorem fromListAux_cons (acc : CodeReq) (a : Nat) (i : Insn)
    (rest : List (Nat × Insn)) :
    fromListAux acc ((a, i) :: rest) =
      fromListAux (acc.union (singleton a i)) rest := rfl

theorem fromList_nil : fromList [] = empty := rfl

theorem fromList_cons (a : Nat) (i : Insn) (rest : List (Nat × Insn)) :
    fromList ((a, i) :: rest) = fromListAux (singleton a i) rest := rfl

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

/-- `Disjoint` is symmetric. -/
theorem Disjoint_comm {cr1 cr2 : CodeReq} (h : cr1.Disjoint cr2) :
    cr2.Disjoint cr1 := by
  intro a; exact (h a).symm

/-- Disjointness lifts through union on the right (mirror of
    `Disjoint_union_left` via `Disjoint_comm`). -/
theorem Disjoint_union_right {cr1 cr2 cr3 : CodeReq}
    (h1 : cr1.Disjoint cr2) (h2 : cr1.Disjoint cr3) :
    cr1.Disjoint (cr2.union cr3) :=
  Disjoint_comm (Disjoint_union_left (Disjoint_comm h1) (Disjoint_comm h2))

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

/-! ## `cr![ pc ↦ ins, … ]` builder notation

Sugar for `CodeReq.fromList`, expanding to a left-folded
`singleton ∪ singleton ∪ …` chain that matches the hand-written arm-file
CR shape (so `isDefEq` against `sl_block_iter`-built chains is preserved).
Empty `cr![]` → `CodeReq.empty`. -/

/-- Single item of a `cr!` list: `pc ↦ ins`. -/
syntax crItem := term:65 " ↦ " term:65

/-- `cr![ pc₀ ↦ ins₀, … ]` — left-folded union of `CodeReq.singleton`s. -/
syntax (name := crListNotation) "cr![" crItem,* "]" : term

open Lean in
/-- Helper: extract `(pc, ins)` from one `crItem` syntax node. -/
private def crItemParts : TSyntax `SVM.SBPF.crItem → MacroM (TSyntax `term × TSyntax `term)
  | `(crItem| $pc ↦ $ins) => return (pc, ins)
  | stx => Macro.throwErrorAt stx "cr!: expected `pc ↦ ins`"

open Lean in
macro_rules
  | `(cr![ $items:crItem,* ]) => do
    let items := items.getElems
    if h : items.size = 0 then
      `(CodeReq.empty)
    else
      let (pc0, ins0) ← crItemParts items[0]
      let mut acc : TSyntax `term ← `(CodeReq.singleton $pc0 $ins0)
      for hk : k in [1:items.size] do
        let (pc, ins) ← crItemParts items[k]
        acc ← `(($acc).union (CodeReq.singleton $pc $ins))
      return acc

/-- Sanity: `cr!` produces the hand-written union chain's exact shape (rfl). -/
private example :
    cr![ 0 ↦ (Insn.ldx .byte .r2 .r1 0),
         1 ↦ (Insn.jeq .r2 (.imm 3) 7) ]
    =
    ((CodeReq.singleton 0 (.ldx .byte .r2 .r1 0)).union
       (CodeReq.singleton 1 (.jeq .r2 (.imm 3) 7))) := rfl

/-- Sanity: `CodeReq.fromList` reduces by `rfl` to the same chain. -/
private example :
    CodeReq.fromList [(0, Insn.ldx .byte .r2 .r1 0),
                      (1, Insn.jeq .r2 (.imm 3) 7)]
    =
    ((CodeReq.singleton 0 (.ldx .byte .r2 .r1 0)).union
       (CodeReq.singleton 1 (.jeq .r2 (.imm 3) 7))) := rfl

/-- Sanity: `cr!` agrees with `fromList` on the literal-list form. -/
private example :
    cr![ 0 ↦ (Insn.ldx .byte .r2 .r1 0),
         1 ↦ (Insn.jeq .r2 (.imm 3) 7) ]
    =
    CodeReq.fromList [(0, .ldx .byte .r2 .r1 0),
                      (1, .jeq .r2 (.imm 3) 7)] := rfl

/-! ## Bounded CPS-style triple -/

/-- `cuTripleWithin nSteps nCu entry exit_ cr P Q`: for every pc-free frame
    `R` and `fetch` honoring `cr`, from any state with `P ** R`, `pc = entry`,
    running, execution reaches in ≤ `nSteps` steps a running state with
    `pc = exit_`, `cuConsumed` up by ≤ `nSteps + nCu`, and `Q ** R`.

    Frame rule built in (universal pc-free R). Total agave-CU = `nSteps`
    (instructions) + `nCu` (syscall surcharge). -/
def cuTripleWithin (nSteps nCu : Nat) (entry exit_ : Nat) (cr : CodeReq)
    (P Q : Assertion) : Prop :=
  ∀ (R : Assertion), R.pcFree →
  ∀ (fetch : Nat → Option Insn), cr.SatisfiedBy fetch →
  ∀ (s : State), (P ** R).holdsFor s → s.pc = entry → s.exitCode = none →
    s.cuConsumed + nSteps + nCu ≤ s.cuBudget →
    ∃ k, k ≤ nSteps ∧
      (executeFn fetch s k).pc = exit_ ∧
      (executeFn fetch s k).exitCode = none ∧
      (executeFn fetch s k).cuConsumed ≤ s.cuConsumed + nSteps + nCu ∧
      (Q ** R).holdsFor (executeFn fetch s k)

/-! ## Structural rules -/

/-- Rule of consequence: strengthen the precondition, weaken the
    postcondition, keep both bounds. -/
theorem cuTripleWithin_weaken {nSteps nCu : Nat} {entry exit_ : Nat} {cr : CodeReq}
    {P P' Q Q' : Assertion}
    (hpre  : ∀ h, P' h → P h)
    (hpost : ∀ h, Q h → Q' h)
    (h : cuTripleWithin nSteps nCu entry exit_ cr P Q) :
    cuTripleWithin nSteps nCu entry exit_ cr P' Q' := by
  intro R hR fetch hcr s hP'R hpc hex hbud
  have hPR : (P ** R).holdsFor s := by
    obtain ⟨hp, hcompat, h1, h2, hd, hu, hP'1, hR2⟩ := hP'R
    exact ⟨hp, hcompat, h1, h2, hd, hu, hpre h1 hP'1, hR2⟩
  obtain ⟨k, hk, hpc', hex', hcu, hQR⟩ := h R hR fetch hcr s hPR hpc hex hbud
  refine ⟨k, hk, hpc', hex', hcu, ?_⟩
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hQ1, hR2⟩ := hQR
  exact ⟨hp, hcompat, h1, h2, hd, hu, hpost h1 hQ1, hR2⟩

/-- Monotonicity in the step bound: a triple with bound `N` is also a
    triple with bound `N' ≥ N`. -/
theorem cuTripleWithin_mono_nSteps {nSteps nSteps' nCu : Nat} {entry exit_ : Nat}
    {cr : CodeReq} {P Q : Assertion}
    (hle : nSteps ≤ nSteps')
    (h : cuTripleWithin nSteps nCu entry exit_ cr P Q) :
    cuTripleWithin nSteps' nCu entry exit_ cr P Q := by
  intro R hR fetch hcr s hPR hpc hex hbud
  obtain ⟨k, hk, hpc', hex', hcu, hQR⟩ := h R hR fetch hcr s hPR hpc hex (by omega)
  exact ⟨k, Nat.le_trans hk hle, hpc', hex', by omega, hQR⟩

/-- Monotonicity in the syscall-CU bound: a triple with surcharge bound
    `M` is also one with bound `M' ≥ M`. -/
theorem cuTripleWithin_mono_nCu {nSteps nCu nCu' : Nat} {entry exit_ : Nat}
    {cr : CodeReq} {P Q : Assertion}
    (hle : nCu ≤ nCu')
    (h : cuTripleWithin nSteps nCu entry exit_ cr P Q) :
    cuTripleWithin nSteps nCu' entry exit_ cr P Q := by
  intro R hR fetch hcr s hPR hpc hex hbud
  obtain ⟨k, hk, hpc', hex', hcu, hQR⟩ := h R hR fetch hcr s hPR hpc hex (by omega)
  exact ⟨k, hk, hpc', hex', by omega, hQR⟩

/-- Cast `nSteps`/`nCu`/`exit_` to defeq Nat exprs. Used by `sl_block_iter`
    to coerce the chain's `(… + …)` bounds back to closed form (e.g.
    `1+1+1+1 → 4`); equalities discharged by `omega`/`decide` at use sites. -/
theorem cuTripleWithin_cast {nSteps nSteps' nCu nCu' entry exit_ exit_' : Nat}
    {cr : CodeReq} {P Q : Assertion}
    (hN : nSteps = nSteps') (hM : nCu = nCu') (hE : exit_ = exit_')
    (h : cuTripleWithin nSteps nCu entry exit_ cr P Q) :
    cuTripleWithin nSteps' nCu' entry exit_' cr P Q := by
  subst hN; subst hM; subst hE; exact h

/-- Zero-step triple: if `P ⇒ Q` pointwise and entry = exit_, the triple
    holds with bound 0 / 0. -/
theorem cuTripleWithin_refl {entry : Nat} {P Q : Assertion}
    (h : ∀ hp, P hp → Q hp) :
    cuTripleWithin 0 0 entry entry CodeReq.empty P Q := by
  intro R _ _ _ s hPR hpc hex _
  refine ⟨0, Nat.le_refl 0, ?_, ?_, ?_, ?_⟩
  · simp [hpc]
  · simp [hex]
  · simp [executeFn]
  · simp only [executeFn]
    obtain ⟨hp, hcompat, h1, h2, hd, hu, hP1, hR2⟩ := hPR
    exact ⟨hp, hcompat, h1, h2, hd, hu, h h1 hP1, hR2⟩

/-- Sequential composition: chain two triples (matching intermediate
    assertion + PC), disjoint-union the code reqs, sum both bounds. Core
    machinery for multi-instruction macros. -/
theorem cuTripleWithin_seq {N1 N2 M1 M2 : Nat} {pc1 pc2 pc3 : Nat}
    {cr1 cr2 : CodeReq}
    (hd : cr1.Disjoint cr2)
    {P Q R : Assertion}
    (h1 : cuTripleWithin N1 M1 pc1 pc2 cr1 P Q)
    (h2 : cuTripleWithin N2 M2 pc2 pc3 cr2 Q R) :
    cuTripleWithin (N1 + N2) (M1 + M2) pc1 pc3 (cr1.union cr2) P R := by
  intro F hF fetch hcr s hPF hpc hex hbud
  have hcr1 := CodeReq.SatisfiedBy_of_union_left hcr
  have hcr2 := CodeReq.SatisfiedBy_of_union_right hd hcr
  obtain ⟨k1, hk1, hpc_mid, hex_mid, hcu1, hQF⟩ :=
    h1 F hF fetch hcr1 s hPF hpc hex (by omega)
  -- Budget split (H5): midpoint budget unchanged, cuConsumed grew ≤ N1+M1,
  -- so the remainder N2+M2 still fits.
  have hbud_mid : (executeFn fetch s k1).cuConsumed + N2 + M2
      ≤ (executeFn fetch s k1).cuBudget := by
    rw [executeFn_preserves_cuBudget]; omega
  obtain ⟨k2, hk2, hpc_end, hex_end, hcu2, hRF⟩ :=
    h2 F hF fetch hcr2 (executeFn fetch s k1) hQF hpc_mid hex_mid hbud_mid
  refine ⟨k1 + k2, Nat.add_le_add hk1 hk2, ?_, ?_, ?_, ?_⟩
  · rw [executeFn_compose]; exact hpc_end
  · rw [executeFn_compose]; exact hex_end
  · -- Chain cuConsumed through the midpoint.
    rw [executeFn_compose]
    have := hcu2
    omega
  · rw [executeFn_compose]; exact hRF

/-- Frame rule (right): adding pc-free `F` to both sides. Derived from the
    universal `R` via re-association `(P ** F) ** R = P ** (F ** R)`. -/
theorem cuTripleWithin_frame_right (F : Assertion) (hF : F.pcFree)
    {N M : Nat} {pc1 pc2 : Nat} {cr : CodeReq} {P Q : Assertion}
    (h : cuTripleWithin N M pc1 pc2 cr P Q) :
    cuTripleWithin N M pc1 pc2 cr (P ** F) (Q ** F) := by
  intro R hR fetch hcr s hPFR hpc hex hbud
  have hFR_pcfree : (F ** R).pcFree := pcFree_sepConj hF hR
  have hP_FR : (P ** (F ** R)).holdsFor s := holdsFor_sepConj_assoc.mp hPFR
  obtain ⟨k, hk, hpc', hex', hcu, hQFR⟩ :=
    h (F ** R) hFR_pcfree fetch hcr s hP_FR hpc hex hbud
  refine ⟨k, hk, hpc', hex', hcu, ?_⟩
  exact holdsFor_sepConj_assoc.mpr hQFR

/-- Frame rule (left): adding pc-free `F` on the left. Via `frame_right` +
    `sepConj_comm`. -/
theorem cuTripleWithin_frame_left (F : Assertion) (hF : F.pcFree)
    {N M : Nat} {pc1 pc2 : Nat} {cr : CodeReq} {P Q : Assertion}
    (h : cuTripleWithin N M pc1 pc2 cr P Q) :
    cuTripleWithin N M pc1 pc2 cr (F ** P) (F ** Q) :=
  cuTripleWithin_weaken
    (fun hp hFP => (sepConj_comm hp).mp hFP)
    (fun hp hQF => (sepConj_comm hp).mp hQF)
    (cuTripleWithin_frame_right F hF h)

/-- Widen an `emp`/`emp` triple to any pc-free `F` as pre/post. Such triples
    (e.g. `ja_spec`) require/change nothing, so they reuse at any state `F`.
    Lets `sl_block_iter`/`sl_branch` auto-frame `ja_spec`-style steps without
    a manual `frame_right + sepConj_emp_left`. -/
theorem cuTripleWithin_widen_emp (F : Assertion) (hF : F.pcFree)
    {N M : Nat} {pc1 pc2 : Nat} {cr : CodeReq}
    (h : cuTripleWithin N M pc1 pc2 cr emp emp) :
    cuTripleWithin N M pc1 pc2 cr F F := by
  have := cuTripleWithin_frame_right F hF h
  apply cuTripleWithin_weaken
    (fun hp hPP => (sepConj_emp_left hp).mpr hPP)
    (fun hp hQQ => (sepConj_emp_left hp).mp hQQ) this

/-! ## Memory-aware triple

`cuTripleWithinMem` adds a persistent `s.regions` side condition. Memory
ops (ldx/st/stx) need it because `step` traps to `ERR_ACCESS_VIOLATION`
when the range isn't region-covered — a property of `s`, not ownable by a
`PartialState` assertion, so it sits alongside `CodeReq` as a separate
input. `s.regions` is never mutated (`executeFn_preserves_regions`), so
`rr` holds throughout once true at entry; composition just conjuncts. -/

def cuTripleWithinMem (nSteps nCu : Nat) (entry exit_ : Nat) (cr : CodeReq)
    (P Q : Assertion) (rr : Memory.RegionTable → Prop) : Prop :=
  ∀ (R : Assertion), R.pcFree →
  ∀ (fetch : Nat → Option Insn), cr.SatisfiedBy fetch →
  ∀ (s : State), (P ** R).holdsFor s → s.pc = entry → s.exitCode = none →
    s.cuConsumed + nSteps + nCu ≤ s.cuBudget →
    rr s.regions →
    ∃ k, k ≤ nSteps ∧
      (executeFn fetch s k).pc = exit_ ∧
      (executeFn fetch s k).exitCode = none ∧
      (executeFn fetch s k).cuConsumed ≤ s.cuConsumed + nSteps + nCu ∧
      (Q ** R).holdsFor (executeFn fetch s k)

/-- A non-memory triple is a memory triple with no region requirement, so
    ALU/jump specs compose with memory specs. -/
theorem cuTripleWithin.toMem {nSteps nCu entry exit_ : Nat} {cr : CodeReq}
    {P Q : Assertion}
    (h : cuTripleWithin nSteps nCu entry exit_ cr P Q) :
    cuTripleWithinMem nSteps nCu entry exit_ cr P Q (fun _ => True) := by
  intro R hR fetch hcr s hPR hpc hex hbud _
  exact h R hR fetch hcr s hPR hpc hex hbud

/-- Sequential composition for memory triples: bounds sum, code reqs union,
    region conditions conjunct (`executeFn_preserves_regions` carries `rr2`). -/
theorem cuTripleWithinMem_seq {N1 N2 M1 M2 : Nat} {pc1 pc2 pc3 : Nat}
    {cr1 cr2 : CodeReq} (hd : cr1.Disjoint cr2)
    {P Q R : Assertion} {rr1 rr2 : Memory.RegionTable → Prop}
    (h1 : cuTripleWithinMem N1 M1 pc1 pc2 cr1 P Q rr1)
    (h2 : cuTripleWithinMem N2 M2 pc2 pc3 cr2 Q R rr2) :
    cuTripleWithinMem (N1 + N2) (M1 + M2) pc1 pc3 (cr1.union cr2) P R
      (fun rt => rr1 rt ∧ rr2 rt) := by
  intro F hF fetch hcr s hPF hpc hex hbud h_reg
  obtain ⟨hreg1, hreg2⟩ := h_reg
  have hcr1 := CodeReq.SatisfiedBy_of_union_left hcr
  have hcr2 := CodeReq.SatisfiedBy_of_union_right hd hcr
  obtain ⟨k1, hk1, hpc_mid, hex_mid, hcu1, hQF⟩ :=
    h1 F hF fetch hcr1 s hPF hpc hex (by omega) hreg1
  have h_reg_mid : rr2 (executeFn fetch s k1).regions := by
    rw [executeFn_preserves_regions]; exact hreg2
  have hbud_mid : (executeFn fetch s k1).cuConsumed + N2 + M2
      ≤ (executeFn fetch s k1).cuBudget := by
    rw [executeFn_preserves_cuBudget]; omega
  obtain ⟨k2, hk2, hpc_end, hex_end, hcu2, hRF⟩ :=
    h2 F hF fetch hcr2 (executeFn fetch s k1) hQF hpc_mid hex_mid hbud_mid h_reg_mid
  refine ⟨k1 + k2, Nat.add_le_add hk1 hk2, ?_, ?_, ?_, ?_⟩
  · rw [executeFn_compose]; exact hpc_end
  · rw [executeFn_compose]; exact hex_end
  · rw [executeFn_compose]; omega
  · rw [executeFn_compose]; exact hRF

/-- Frame rule for memory triples (right). -/
theorem cuTripleWithinMem_frame_right (F : Assertion) (hF : F.pcFree)
    {N M : Nat} {pc1 pc2 : Nat} {cr : CodeReq} {P Q : Assertion}
    {rr : Memory.RegionTable → Prop}
    (h : cuTripleWithinMem N M pc1 pc2 cr P Q rr) :
    cuTripleWithinMem N M pc1 pc2 cr (P ** F) (Q ** F) rr := by
  intro R hR fetch hcr s hPFR hpc hex hbud h_reg
  have hFR_pcfree : (F ** R).pcFree := pcFree_sepConj hF hR
  have hP_FR : (P ** (F ** R)).holdsFor s := holdsFor_sepConj_assoc.mp hPFR
  obtain ⟨k, hk, hpc', hex', hcu, hQFR⟩ :=
    h (F ** R) hFR_pcfree fetch hcr s hP_FR hpc hex hbud h_reg
  refine ⟨k, hk, hpc', hex', hcu, ?_⟩
  exact holdsFor_sepConj_assoc.mpr hQFR

/-- Memory variant of `cuTripleWithin_cast`. -/
theorem cuTripleWithinMem_cast {nSteps nSteps' nCu nCu' entry exit_ exit_' : Nat}
    {cr : CodeReq} {P Q : Assertion} {rr : Memory.RegionTable → Prop}
    (hN : nSteps = nSteps') (hM : nCu = nCu') (hE : exit_ = exit_')
    (h : cuTripleWithinMem nSteps nCu entry exit_ cr P Q rr) :
    cuTripleWithinMem nSteps' nCu' entry exit_' cr P Q rr := by
  subst hN; subst hM; subst hE; exact h

/-- Rule of consequence for memory triples: strengthen pre, weaken post,
    strengthen `rr` (caller's stronger region claim ⇒ the spec's weaker one). -/
theorem cuTripleWithinMem_weaken {nSteps nCu : Nat} {entry exit_ : Nat}
    {cr : CodeReq}
    {P P' Q Q' : Assertion} {rr rr' : Memory.RegionTable → Prop}
    (hpre  : ∀ h, P' h → P h)
    (hpost : ∀ h, Q h → Q' h)
    (h_rr  : ∀ rt, rr' rt → rr rt)
    (h : cuTripleWithinMem nSteps nCu entry exit_ cr P Q rr) :
    cuTripleWithinMem nSteps nCu entry exit_ cr P' Q' rr' := by
  intro R hR fetch hcr s hP'R hpc hex hbud h_reg'
  have hPR : (P ** R).holdsFor s := by
    obtain ⟨hp, hcompat, h1, h2, hd, hu, hP'1, hR2⟩ := hP'R
    exact ⟨hp, hcompat, h1, h2, hd, hu, hpre h1 hP'1, hR2⟩
  obtain ⟨k, hk, hpc', hex', hcu, hQR⟩ :=
    h R hR fetch hcr s hPR hpc hex hbud (h_rr _ h_reg')
  refine ⟨k, hk, hpc', hex', hcu, ?_⟩
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hQ1, hR2⟩ := hQR
  exact ⟨hp, hcompat, h1, h2, hd, hu, hpost h1 hQ1, hR2⟩

/-- Memory + pure composition, keeping only the memory triple's `rr`.
    Without this, `_seq` would add a trivial `True` conjunct per pure step. -/
theorem cuTripleWithinMem_seq_pure_right {N1 N2 M1 M2 : Nat}
    {pc1 pc2 pc3 : Nat}
    {cr1 cr2 : CodeReq} (hd : cr1.Disjoint cr2)
    {P Q R : Assertion} {rr : Memory.RegionTable → Prop}
    (h1 : cuTripleWithinMem N1 M1 pc1 pc2 cr1 P Q rr)
    (h2 : cuTripleWithin N2 M2 pc2 pc3 cr2 Q R) :
    cuTripleWithinMem (N1 + N2) (M1 + M2) pc1 pc3 (cr1.union cr2) P R rr :=
  cuTripleWithinMem_weaken (fun _ x => x) (fun _ x => x)
    (fun _ x => And.intro x True.intro)
    (cuTripleWithinMem_seq hd h1 h2.toMem)

/-- Pure + memory composition, keeping only the memory triple's `rr`.
    Mirror of `cuTripleWithinMem_seq_pure_right`. -/
theorem cuTripleWithinMem_seq_pure_left {N1 N2 M1 M2 : Nat}
    {pc1 pc2 pc3 : Nat}
    {cr1 cr2 : CodeReq} (hd : cr1.Disjoint cr2)
    {P Q R : Assertion} {rr : Memory.RegionTable → Prop}
    (h1 : cuTripleWithin N1 M1 pc1 pc2 cr1 P Q)
    (h2 : cuTripleWithinMem N2 M2 pc2 pc3 cr2 Q R rr) :
    cuTripleWithinMem (N1 + N2) (M1 + M2) pc1 pc3 (cr1.union cr2) P R rr :=
  cuTripleWithinMem_weaken (fun _ x => x) (fun _ x => x)
    (fun _ x => And.intro True.intro x)
    (cuTripleWithinMem_seq hd h1.toMem h2)

/-- Frame rule for memory triples (left). -/
theorem cuTripleWithinMem_frame_left (F : Assertion) (hF : F.pcFree)
    {N M : Nat} {pc1 pc2 : Nat} {cr : CodeReq} {P Q : Assertion}
    {rr : Memory.RegionTable → Prop}
    (h : cuTripleWithinMem N M pc1 pc2 cr P Q rr) :
    cuTripleWithinMem N M pc1 pc2 cr (F ** P) (F ** Q) rr := by
  intro R hR fetch hcr s hPFR hpc hex hbud h_reg
  -- F ** P ** R → P ** F ** R via comm; frame_right; swap back.
  have h' := cuTripleWithinMem_frame_right F hF h
  have hPFR' : ((P ** F) ** R).holdsFor s := by
    have : ((F ** P) ** R).holdsFor s ↔ ((P ** F) ** R).holdsFor s :=
      holdsFor_iff_pointwise (fun h => by
        constructor
        · rintro ⟨h1, h2, hd, hu, hFP, hRsat⟩
          exact ⟨h1, h2, hd, hu, (sepConj_comm h1).mp hFP, hRsat⟩
        · rintro ⟨h1, h2, hd, hu, hPF, hRsat⟩
          exact ⟨h1, h2, hd, hu, (sepConj_comm h1).mp hPF, hRsat⟩)
    exact this.mp hPFR
  obtain ⟨k, hk, hpc', hex', hcu, hQFR⟩ :=
    h' R hR fetch hcr s hPFR' hpc hex hbud h_reg
  refine ⟨k, hk, hpc', hex', hcu, ?_⟩
  have : ((Q ** F) ** R).holdsFor (executeFn fetch s k) ↔
         ((F ** Q) ** R).holdsFor (executeFn fetch s k) :=
    holdsFor_iff_pointwise (fun h => by
      constructor
      · rintro ⟨h1, h2, hd, hu, hQF, hRsat⟩
        exact ⟨h1, h2, hd, hu, (sepConj_comm h1).mp hQF, hRsat⟩
      · rintro ⟨h1, h2, hd, hu, hFQ, hRsat⟩
        exact ⟨h1, h2, hd, hu, (sepConj_comm h1).mp hFQ, hRsat⟩)
  exact this.mp hQFR

/-! ## Reshape wrappers for `**` permutations — `_weaken` specializations
taking a pointwise iff (not a one-way implication). `sl_block_iter` emits
iffs by construction, so the caller plugs them without packaging `.mp`. -/

/-- Reshape the post via a pointwise iff `Q ↔ Q'` (OLD ↔ NEW orientation,
    chain's existing post on the left). -/
theorem cuTripleWithin_reshape_post {N M pc1 pc2 : Nat} {cr : CodeReq}
    {P Q Q' : Assertion}
    (iff_post : ∀ h, Q h ↔ Q' h)
    (h : cuTripleWithin N M pc1 pc2 cr P Q) :
    cuTripleWithin N M pc1 pc2 cr P Q' :=
  cuTripleWithin_weaken (fun _ x => x) (fun hp hQ => (iff_post hp).mp hQ) h

/-- Reshape the pre via a pointwise iff `P ↔ P'` (OLD ↔ NEW orientation);
    `.mpr` converts the new pre `P'` back to the old `P` for `weaken`. -/
theorem cuTripleWithin_reshape_pre {N M pc1 pc2 : Nat} {cr : CodeReq}
    {P P' Q : Assertion}
    (iff_pre : ∀ h, P h ↔ P' h)
    (h : cuTripleWithin N M pc1 pc2 cr P Q) :
    cuTripleWithin N M pc1 pc2 cr P' Q :=
  cuTripleWithin_weaken (fun hp hP' => (iff_pre hp).mpr hP') (fun _ x => x) h

theorem cuTripleWithinMem_reshape_post {N M pc1 pc2 : Nat} {cr : CodeReq}
    {P Q Q' : Assertion} {rr : Memory.RegionTable → Prop}
    (iff_post : ∀ h, Q h ↔ Q' h)
    (h : cuTripleWithinMem N M pc1 pc2 cr P Q rr) :
    cuTripleWithinMem N M pc1 pc2 cr P Q' rr :=
  cuTripleWithinMem_weaken (fun _ x => x) (fun hp hQ => (iff_post hp).mp hQ)
    (fun _ x => x) h

theorem cuTripleWithinMem_reshape_pre {N M pc1 pc2 : Nat} {cr : CodeReq}
    {P P' Q : Assertion} {rr : Memory.RegionTable → Prop}
    (iff_pre : ∀ h, P h ↔ P' h)
    (h : cuTripleWithinMem N M pc1 pc2 cr P Q rr) :
    cuTripleWithinMem N M pc1 pc2 cr P' Q rr :=
  cuTripleWithinMem_weaken (fun hp hP' => (iff_pre hp).mpr hP') (fun _ x => x)
    (fun _ x => x) h

/-! ## Branching triple — two-target form

`cuTripleWithinBranch`: like `cuTripleWithin` but the exit PC is one of
two depending on a Decidable `cond` at entry; post `Q` is the same on
both branches (jcond only moves the PC). Structural support mirrors
`cuTripleWithin`'s; the key combinator `cuTripleWithinBranch_join`
composes a branch with two follow-up chains landing at a common `pcJoin`,
producing a `cuTripleWithin` whose post is `(if cond then Rt else Rf)`.
Foundation for non-trivial control flow (discriminant dispatch, error
paths). -/

def cuTripleWithinBranch (nSteps nCu : Nat) (entry exitT exitF : Nat)
    (cond : Prop) [Decidable cond] (cr : CodeReq)
    (P Q : Assertion) : Prop :=
  ∀ (R : Assertion), R.pcFree →
  ∀ (fetch : Nat → Option Insn), cr.SatisfiedBy fetch →
  ∀ (s : State), (P ** R).holdsFor s → s.pc = entry → s.exitCode = none →
    s.cuConsumed + nSteps + nCu ≤ s.cuBudget →
    ∃ k, k ≤ nSteps ∧
      (executeFn fetch s k).pc = (if cond then exitT else exitF) ∧
      (executeFn fetch s k).exitCode = none ∧
      (executeFn fetch s k).cuConsumed ≤ s.cuConsumed + nSteps + nCu ∧
      (Q ** R).holdsFor (executeFn fetch s k)

/-- Bridge: a `cuTripleWithin` with an `if cond then pcT else pcF` exit
    (the shape jcond specs produce) lifts into the branch family. -/
theorem cuTripleWithin.toBranch {N M : Nat} {pc pcT pcF : Nat} {cr : CodeReq}
    {P Q : Assertion} {cond : Prop} [Decidable cond]
    (h : cuTripleWithin N M pc (if cond then pcT else pcF) cr P Q) :
    cuTripleWithinBranch N M pc pcT pcF cond cr P Q := by
  intro R hR fetch hcr s hPR hpc hex hbud
  exact h R hR fetch hcr s hPR hpc hex hbud

/-- Frame rule (right) for the branch triple: adding pc-free `F` to both
    sides. -/
theorem cuTripleWithinBranch_frame_right (F : Assertion) (hF : F.pcFree)
    {N M : Nat} {pc pcT pcF : Nat} {cr : CodeReq} {P Q : Assertion}
    {cond : Prop} [Decidable cond]
    (h : cuTripleWithinBranch N M pc pcT pcF cond cr P Q) :
    cuTripleWithinBranch N M pc pcT pcF cond cr (P ** F) (Q ** F) := by
  intro R hR fetch hcr s hPFR hpc hex hbud
  have hFR_pcfree : (F ** R).pcFree := pcFree_sepConj hF hR
  have hP_FR : (P ** (F ** R)).holdsFor s := holdsFor_sepConj_assoc.mp hPFR
  obtain ⟨k, hk, hpc', hex', hcu, hQFR⟩ :=
    h (F ** R) hFR_pcfree fetch hcr s hP_FR hpc hex hbud
  refine ⟨k, hk, hpc', hex', hcu, ?_⟩
  exact holdsFor_sepConj_assoc.mpr hQFR

/-- Rule of consequence for the branch triple: strengthen pre, weaken post
    (same Q on both branches), keep bounds + exit PCs + `cond`. -/
theorem cuTripleWithinBranch_weaken {N M : Nat} {pc pcT pcF : Nat}
    {cr : CodeReq}
    {P P' Q Q' : Assertion} {cond : Prop} [Decidable cond]
    (hpre  : ∀ h, P' h → P h)
    (hpost : ∀ h, Q h → Q' h)
    (h : cuTripleWithinBranch N M pc pcT pcF cond cr P Q) :
    cuTripleWithinBranch N M pc pcT pcF cond cr P' Q' := by
  intro R hR fetch hcr s hP'R hpc hex hbud
  have hPR : (P ** R).holdsFor s := by
    obtain ⟨hp, hcompat, h1, h2, hd, hu, hP'1, hR2⟩ := hP'R
    exact ⟨hp, hcompat, h1, h2, hd, hu, hpre h1 hP'1, hR2⟩
  obtain ⟨k, hk, hpc', hex', hcu, hQR⟩ := h R hR fetch hcr s hPR hpc hex hbud
  refine ⟨k, hk, hpc', hex', hcu, ?_⟩
  obtain ⟨hp, hcompat, h1, h2, hd, hu, hQ1, hR2⟩ := hQR
  exact ⟨hp, hcompat, h1, h2, hd, hu, hpost h1 hQ1, hR2⟩

/-- Frame rule (left) for the branch triple. Derived from frame_right
    via `sepConj_comm` weakens. -/
theorem cuTripleWithinBranch_frame_left (F : Assertion) (hF : F.pcFree)
    {N M : Nat} {pc pcT pcF : Nat} {cr : CodeReq} {P Q : Assertion}
    {cond : Prop} [Decidable cond]
    (h : cuTripleWithinBranch N M pc pcT pcF cond cr P Q) :
    cuTripleWithinBranch N M pc pcT pcF cond cr (F ** P) (F ** Q) :=
  cuTripleWithinBranch_weaken
    (fun hp hFP => (sepConj_comm hp).mp hFP)
    (fun hp hQF => (sepConj_comm hp).mp hQF)
    (cuTripleWithinBranch_frame_right F hF h)

/-- Branch composition (join rule): a branch triple plus two follow-up
    chains landing at a common `pcJoin`, disjoint code reqs, yields a
    `cuTripleWithin` from entry to `pcJoin` with post `(if cond then Rt
    else Rf)`. Bounds `N0 + max NT NF` / `M0 + max MT MF`: `max` because
    one branch is taken but `cond` is unknown statically. Union
    `(crBr ∪ crT) ∪ crF` left-folded to match `sl_block_iter`'s shape. -/
theorem cuTripleWithinBranch_join {N0 NT NF M0 MT MF : Nat}
    {pc0 pcT pcF pcJoin : Nat}
    {crBr crT crF : CodeReq}
    (hd_brT : crBr.Disjoint crT) (hd_brF : crBr.Disjoint crF)
    (hd_TF : crT.Disjoint crF)
    {cond : Prop} [Decidable cond]
    {P Q Rt Rf : Assertion}
    (h_br : cuTripleWithinBranch N0 M0 pc0 pcT pcF cond crBr P Q)
    (h_T : cuTripleWithin NT MT pcT pcJoin crT Q Rt)
    (h_F : cuTripleWithin NF MF pcF pcJoin crF Q Rf) :
    cuTripleWithin (N0 + max NT NF) (M0 + max MT MF) pc0 pcJoin
      ((crBr.union crT).union crF)
      P (if cond then Rt else Rf) := by
  intro R hRfree fetch hcr s hPR hpc hex hbud
  -- max facts surfaced for omega (it doesn't reason about `max`).
  have hmaxNT := Nat.le_max_left NT NF
  have hmaxNF := Nat.le_max_right NT NF
  have hmaxMT := Nat.le_max_left MT MF
  have hmaxMF := Nat.le_max_right MT MF
  -- Split the union: fetch satisfies crBr, crT, crF individually.
  have hcr_brT : (crBr.union crT).SatisfiedBy fetch :=
    CodeReq.SatisfiedBy_of_union_left hcr
  have hcr_F : crF.SatisfiedBy fetch := by
    apply CodeReq.SatisfiedBy_of_union_right _ hcr
    exact CodeReq.Disjoint_union_left hd_brF hd_TF
  have hcr_br : crBr.SatisfiedBy fetch :=
    CodeReq.SatisfiedBy_of_union_left hcr_brT
  have hcr_T : crT.SatisfiedBy fetch :=
    CodeReq.SatisfiedBy_of_union_right hd_brT hcr_brT
  -- Step 1: run the branch.
  obtain ⟨k0, hk0, hpc_mid, hex_mid, hcu0, hQR⟩ :=
    h_br R hRfree fetch hcr_br s hPR hpc hex (by omega)
  -- Budget left for either follow-up chain (H5).
  have hbud_mid : ∀ n m, n ≤ max NT NF → m ≤ max MT MF →
      (executeFn fetch s k0).cuConsumed + n + m
        ≤ (executeFn fetch s k0).cuBudget := by
    intro n m hn hm
    rw [executeFn_preserves_cuBudget]; omega
  -- Step 2: run the appropriate follow-up branch.
  by_cases hcond : cond
  · -- True branch: pc_mid = pcT.
    have hpc_mid' : (executeFn fetch s k0).pc = pcT := by
      rw [hpc_mid]; simp [hcond]
    obtain ⟨k1, hk1, hpc_end, hex_end, hcu1, hRtR⟩ :=
      h_T R hRfree fetch hcr_T (executeFn fetch s k0) hQR hpc_mid' hex_mid
        (hbud_mid NT MT hmaxNT hmaxMT)
    refine ⟨k0 + k1, ?_, ?_, ?_, ?_, ?_⟩
    ·
      apply Nat.add_le_add hk0
      exact Nat.le_trans hk1 (Nat.le_max_left NT NF)
    · rw [executeFn_compose]; exact hpc_end
    · rw [executeFn_compose]; exact hex_end
    · rw [executeFn_compose]; omega
    · rw [executeFn_compose]
      simp only [hcond, if_true]
      exact hRtR
  · -- False branch: pc_mid = pcF.
    have hpc_mid' : (executeFn fetch s k0).pc = pcF := by
      rw [hpc_mid]; simp [hcond]
    obtain ⟨k1, hk1, hpc_end, hex_end, hcu1, hRfR⟩ :=
      h_F R hRfree fetch hcr_F (executeFn fetch s k0) hQR hpc_mid' hex_mid
        (hbud_mid NF MF hmaxNF hmaxMF)
    refine ⟨k0 + k1, ?_, ?_, ?_, ?_, ?_⟩
    · apply Nat.add_le_add hk0
      exact Nat.le_trans hk1 (Nat.le_max_right NT NF)
    · rw [executeFn_compose]; exact hpc_end
    · rw [executeFn_compose]; exact hex_end
    · rw [executeFn_compose]; omega
    · rw [executeFn_compose]
      simp only [hcond, if_false]
      exact hRfR

/-- `cuTripleWithinBranch_join` specialized to both branches reaching the
    same post `Rjoin`, eliminating the `if cond then Rt else Rf`. -/
theorem cuTripleWithinBranch_join_uniform {N0 NT NF M0 MT MF : Nat}
    {pc0 pcT pcF pcJoin : Nat}
    {crBr crT crF : CodeReq}
    (hd_brT : crBr.Disjoint crT) (hd_brF : crBr.Disjoint crF)
    (hd_TF : crT.Disjoint crF)
    {cond : Prop} [Decidable cond]
    {P Q Rjoin : Assertion}
    (h_br : cuTripleWithinBranch N0 M0 pc0 pcT pcF cond crBr P Q)
    (h_T : cuTripleWithin NT MT pcT pcJoin crT Q Rjoin)
    (h_F : cuTripleWithin NF MF pcF pcJoin crF Q Rjoin) :
    cuTripleWithin (N0 + max NT NF) (M0 + max MT MF) pc0 pcJoin
      ((crBr.union crT).union crF)
      P Rjoin := by
  have h := cuTripleWithinBranch_join hd_brT hd_brF hd_TF h_br h_T h_F
  apply cuTripleWithin_weaken (fun _ x => x) ?_ h
  intro hp hpost
  by_cases hcond : cond <;> simp [hcond] at hpost <;> exact hpost

/-! ## SL ↔ WP bridge — concrete-execution corollary

Specializing the triple's universal `R := emp` collapses it to a concrete
`executeFn` statement, linking the two repo methodologies:
- **SL** (`cuTripleWithin{,Mem}` + `Tactic.SL`): compositional macro
  library; `seq`/frame rules sum CU bounds, union code reqs, preserve
  disjoint resources. Used when callers don't know the surrounding program.
- **WP** (`Tactic.WP.wp_exec`): concrete-execution; unfolds `executeFn`
  step-by-step over a fixed `fetch`. Used to prove a specific compiled
  program satisfies a closed property.
`.toExec` downgrades an SL spec to a WP-style `executeFn fetch s k = s'`
fact a `wp_exec` proof composes its segments around. -/

/-- Bridge: a `cuTripleWithinMem` triple specializes to a concrete
    `executeFn` fact (`R := emp`, so no sepConj at the use site). Exposes
    both bounds. -/
theorem cuTripleWithinMem.toExec {N M entry exit_ : Nat} {cr : CodeReq}
    {P Q : Assertion} {rr : Memory.RegionTable → Prop}
    (h : cuTripleWithinMem N M entry exit_ cr P Q rr)
    {fetch : Nat → Option Insn} (hcr : cr.SatisfiedBy fetch)
    {s : State} (hP : P.holdsFor s) (hpc : s.pc = entry)
    (hex : s.exitCode = none)
    (hbud : s.cuConsumed + N + M ≤ s.cuBudget)
    (h_reg : rr s.regions) :
    ∃ k, k ≤ N ∧
      (executeFn fetch s k).pc = exit_ ∧
      (executeFn fetch s k).exitCode = none ∧
      (executeFn fetch s k).cuConsumed ≤ s.cuConsumed + N + M ∧
      Q.holdsFor (executeFn fetch s k) := by
  have hP_emp : (P ** emp).holdsFor s :=
    (holdsFor_iff_pointwise sepConj_emp_right).mpr hP
  obtain ⟨k, hk, hpc', hex', hcu, hQ_emp⟩ :=
    h emp pcFree_emp fetch hcr s hP_emp hpc hex hbud h_reg
  refine ⟨k, hk, hpc', hex', hcu, ?_⟩
  exact (holdsFor_iff_pointwise sepConj_emp_right).mp hQ_emp

/-- Bridge for non-memory triples: routes through `.toMem` and discharges
    the trivial region requirement. -/
theorem cuTripleWithin.toExec {N M entry exit_ : Nat} {cr : CodeReq}
    {P Q : Assertion}
    (h : cuTripleWithin N M entry exit_ cr P Q)
    {fetch : Nat → Option Insn} (hcr : cr.SatisfiedBy fetch)
    {s : State} (hP : P.holdsFor s) (hpc : s.pc = entry)
    (hex : s.exitCode = none)
    (hbud : s.cuConsumed + N + M ≤ s.cuBudget) :
    ∃ k, k ≤ N ∧
      (executeFn fetch s k).pc = exit_ ∧
      (executeFn fetch s k).exitCode = none ∧
      (executeFn fetch s k).cuConsumed ≤ s.cuConsumed + N + M ∧
      Q.holdsFor (executeFn fetch s k) :=
  h.toMem.toExec hcr hP hpc hex hbud trivial

/-! ## Terminating triple — abort / panic / success-exit

`cuTripleWithin` requires `exitCode = none` post, so it can't express an
intentional abort. `cuTripleAbortsWithin` is the dual: within `nSteps`,
execution reaches `exitCode = some errCode`, with NO post on the partial
state (once aborted, the only content is the exit code). Unlocks
`exit`/`sol_panic_`/`abort` and, by sequencing, error-path `require`
patterns `P{c₁}Q ∧ Q{c₂}aborts → P{c₁;c₂}aborts`. -/

/-- `cuTripleAbortsWithin nSteps nCu entry cr P errCode`: for every pc-free
    frame `R` and `fetch` honoring `cr`, from a running state with `P ** R`
    and `pc = entry`, execution reaches in ≤ `nSteps` a state with
    `exitCode = some errCode` and `cuConsumed` up by ≤ `nSteps + nCu`. Frame
    built in; no post on the partial state. -/
def cuTripleAbortsWithin (nSteps nCu : Nat) (entry : Nat) (cr : CodeReq)
    (P : Assertion) (errCode : Nat) : Prop :=
  ∀ (R : Assertion), R.pcFree →
  ∀ (fetch : Nat → Option Insn), cr.SatisfiedBy fetch →
  ∀ (s : State), (P ** R).holdsFor s → s.pc = entry → s.exitCode = none →
    s.cuConsumed + nSteps + nCu ≤ s.cuBudget →
    ∃ k, k ≤ nSteps ∧
      (executeFn fetch s k).exitCode = some errCode ∧
      (executeFn fetch s k).cuConsumed ≤ s.cuConsumed + nSteps + nCu

/-- Rule of consequence (pre-weakening) for aborting triples (no post). -/
theorem cuTripleAbortsWithin_weaken {nSteps nCu : Nat} {entry : Nat}
    {cr : CodeReq}
    {P P' : Assertion} {errCode : Nat}
    (hpre : ∀ h, P' h → P h)
    (h : cuTripleAbortsWithin nSteps nCu entry cr P errCode) :
    cuTripleAbortsWithin nSteps nCu entry cr P' errCode := by
  intro R hR fetch hcr s hP'R hpc hex hbud
  have hPR : (P ** R).holdsFor s := by
    obtain ⟨hp, hcompat, h1, h2, hd, hu, hP'1, hR2⟩ := hP'R
    exact ⟨hp, hcompat, h1, h2, hd, hu, hpre h1 hP'1, hR2⟩
  exact h R hR fetch hcr s hPR hpc hex hbud

/-- Monotonicity in the step bound: an aborting triple with bound `N` is
    also one with bound `N' ≥ N`. -/
theorem cuTripleAbortsWithin_mono_nSteps {nSteps nSteps' nCu : Nat}
    {entry : Nat}
    {cr : CodeReq} {P : Assertion} {errCode : Nat}
    (hle : nSteps ≤ nSteps')
    (h : cuTripleAbortsWithin nSteps nCu entry cr P errCode) :
    cuTripleAbortsWithin nSteps' nCu entry cr P errCode := by
  intro R hR fetch hcr s hPR hpc hex hbud
  obtain ⟨k, hk, hex', hcu⟩ := h R hR fetch hcr s hPR hpc hex (by omega)
  exact ⟨k, Nat.le_trans hk hle, hex', by omega⟩

/-! ## Typed-fault triples (`cuTripleFaultsWithin`)

After L1, every fault site sets `State.vmError := some e` (the typed
channel distinguishing a real VM fault from a program-returned sentinel of
the same numeric value). This strengthens the abort triple to pin
`exitCode = some e.toSentinel` AND `vmError = some e`, forgetting back to
`cuTripleAbortsWithin` via `_toAborts` so existing abort-consumers still
compose. -/
def cuTripleFaultsWithin (nSteps nCu : Nat) (entry : Nat) (cr : CodeReq)
    (P : Assertion) (e : VmError) : Prop :=
  ∀ (R : Assertion), R.pcFree →
  ∀ (fetch : Nat → Option Insn), cr.SatisfiedBy fetch →
  ∀ (s : State), (P ** R).holdsFor s → s.pc = entry → s.exitCode = none →
    s.cuConsumed + nSteps + nCu ≤ s.cuBudget →
    ∃ k, k ≤ nSteps ∧
      (executeFn fetch s k).exitCode = some e.toSentinel ∧
      (executeFn fetch s k).vmError = some e ∧
      (executeFn fetch s k).cuConsumed ≤ s.cuConsumed + nSteps + nCu

/-- Forget the `vmError` conjunct: a fault triple is an abort triple at
    `e.toSentinel`, back-filling existing abort-consumers without re-proving. -/
theorem cuTripleFaultsWithin_toAborts {nSteps nCu : Nat} {entry : Nat}
    {cr : CodeReq} {P : Assertion} {e : VmError}
    (h : cuTripleFaultsWithin nSteps nCu entry cr P e) :
    cuTripleAbortsWithin nSteps nCu entry cr P e.toSentinel := by
  intro R hR fetch hcr s hPR hpc hex hbud
  obtain ⟨k, hk, hexit, _, hcu⟩ := h R hR fetch hcr s hPR hpc hex hbud
  exact ⟨k, hk, hexit, hcu⟩

/-- Rule of consequence (pre-weakening) for faulting triples. -/
theorem cuTripleFaultsWithin_weaken {nSteps nCu : Nat} {entry : Nat}
    {cr : CodeReq} {P P' : Assertion} {e : VmError}
    (hpre : ∀ h, P' h → P h)
    (h : cuTripleFaultsWithin nSteps nCu entry cr P e) :
    cuTripleFaultsWithin nSteps nCu entry cr P' e := by
  intro R hR fetch hcr s hP'R hpc hex hbud
  have hPR : (P ** R).holdsFor s := by
    obtain ⟨hp, hcompat, h1, h2, hd, hu, hP'1, hR2⟩ := hP'R
    exact ⟨hp, hcompat, h1, h2, hd, hu, hpre h1 hP'1, hR2⟩
  exact h R hR fetch hcr s hPR hpc hex hbud

/-- Monotonicity in the step bound for faulting triples. -/
theorem cuTripleFaultsWithin_mono_nSteps {nSteps nSteps' nCu : Nat}
    {entry : Nat} {cr : CodeReq} {P : Assertion} {e : VmError}
    (hle : nSteps ≤ nSteps')
    (h : cuTripleFaultsWithin nSteps nCu entry cr P e) :
    cuTripleFaultsWithin nSteps' nCu entry cr P e := by
  intro R hR fetch hcr s hPR hpc hex hbud
  obtain ⟨k, hk, hexit, hvm, hcu⟩ := h R hR fetch hcr s hPR hpc hex (by omega)
  exact ⟨k, Nat.le_trans hk hle, hexit, hvm, by omega⟩

/-- Sequencing into a typed fault: `P{c₁}Q` chained with `Q{c₂}faults e`
    yields `P{c₁;c₂}faults e`. `vmError`-carrying analog of
    `cuTripleAbortsWithin_seq_abort`. -/
theorem cuTripleFaultsWithin_seq_fault {N1 N2 M1 M2 : Nat} {pc1 pc2 : Nat}
    {cr1 cr2 : CodeReq}
    (hd : cr1.Disjoint cr2)
    {P Q : Assertion} {e : VmError}
    (h1 : cuTripleWithin N1 M1 pc1 pc2 cr1 P Q)
    (h2 : cuTripleFaultsWithin N2 M2 pc2 cr2 Q e) :
    cuTripleFaultsWithin (N1 + N2) (M1 + M2) pc1 (cr1.union cr2) P e := by
  intro F hF fetch hcr s hPF hpc hex hbud
  have hcr1 := CodeReq.SatisfiedBy_of_union_left hcr
  have hcr2 := CodeReq.SatisfiedBy_of_union_right hd hcr
  obtain ⟨k1, hk1, hpc_mid, hex_mid, hcu1, hQF⟩ :=
    h1 F hF fetch hcr1 s hPF hpc hex (by omega)
  have hbud_mid : (executeFn fetch s k1).cuConsumed + N2 + M2
      ≤ (executeFn fetch s k1).cuBudget := by
    rw [executeFn_preserves_cuBudget]; omega
  obtain ⟨k2, hk2, hex_end, hvm_end, hcu2⟩ :=
    h2 F hF fetch hcr2 (executeFn fetch s k1) hQF hpc_mid hex_mid hbud_mid
  refine ⟨k1 + k2, Nat.add_le_add hk1 hk2, ?_, ?_, ?_⟩
  · rw [executeFn_compose]; exact hex_end
  · rw [executeFn_compose]; exact hvm_end
  · rw [executeFn_compose]; omega

/-- Sequencing into abort: `P{c₁}Q` chained with `Q{c₂}aborts` yields
    `P{c₁;c₂}aborts`, bounds summing, code reqs disjoint-union. Like
    `cuTripleWithin_seq` but the tail aborts (no post-state): lets a
    discriminant-decode prefix dispatch to an `abort`/`sol_panic_` block. -/
theorem cuTripleAbortsWithin_seq_abort {N1 N2 M1 M2 : Nat} {pc1 pc2 : Nat}
    {cr1 cr2 : CodeReq}
    (hd : cr1.Disjoint cr2)
    {P Q : Assertion} {errCode : Nat}
    (h1 : cuTripleWithin N1 M1 pc1 pc2 cr1 P Q)
    (h2 : cuTripleAbortsWithin N2 M2 pc2 cr2 Q errCode) :
    cuTripleAbortsWithin (N1 + N2) (M1 + M2) pc1 (cr1.union cr2) P errCode := by
  intro F hF fetch hcr s hPF hpc hex hbud
  have hcr1 := CodeReq.SatisfiedBy_of_union_left hcr
  have hcr2 := CodeReq.SatisfiedBy_of_union_right hd hcr
  obtain ⟨k1, hk1, hpc_mid, hex_mid, hcu1, hQF⟩ :=
    h1 F hF fetch hcr1 s hPF hpc hex (by omega)
  have hbud_mid : (executeFn fetch s k1).cuConsumed + N2 + M2
      ≤ (executeFn fetch s k1).cuBudget := by
    rw [executeFn_preserves_cuBudget]; omega
  obtain ⟨k2, hk2, hex_end, hcu2⟩ :=
    h2 F hF fetch hcr2 (executeFn fetch s k1) hQF hpc_mid hex_mid hbud_mid
  refine ⟨k1 + k2, Nat.add_le_add hk1 hk2, ?_, ?_⟩
  · rw [executeFn_compose]; exact hex_end
  · rw [executeFn_compose]; omega

/-- Frame rule (right) for aborting triples: add pc-free `F` to the pre
    (no post, so only the pre is reshaped). -/
theorem cuTripleAbortsWithin_frame_right (F : Assertion) (hF : F.pcFree)
    {N M : Nat} {pc : Nat} {cr : CodeReq} {P : Assertion} {errCode : Nat}
    (h : cuTripleAbortsWithin N M pc cr P errCode) :
    cuTripleAbortsWithin N M pc cr (P ** F) errCode := by
  intro R hR fetch hcr s hPFR hpc hex hbud
  have hFR_pcfree : (F ** R).pcFree := pcFree_sepConj hF hR
  have hP_FR : (P ** (F ** R)).holdsFor s := holdsFor_sepConj_assoc.mp hPFR
  exact h (F ** R) hFR_pcfree fetch hcr s hP_FR hpc hex hbud

/-- Frame rule (left) for aborting triples. -/
theorem cuTripleAbortsWithin_frame_left (F : Assertion) (hF : F.pcFree)
    {N M : Nat} {pc : Nat} {cr : CodeReq} {P : Assertion} {errCode : Nat}
    (h : cuTripleAbortsWithin N M pc cr P errCode) :
    cuTripleAbortsWithin N M pc cr (F ** P) errCode :=
  cuTripleAbortsWithin_weaken
    (fun hp hFP => (sepConj_comm hp).mp hFP)
    (cuTripleAbortsWithin_frame_right F hF h)

/-! ## Memory-aware aborting triple

`cuTripleAbortsWithinMem` adds a persistent `rr` on `s.regions` (as
`cuTripleWithinMem` does to `cuTripleWithin`): the shape from sequencing a
memory-laden prefix into a terminating tail (`.exit`/`.call .abort`/
`.call .sol_panic_`). `rr` is discharged single-point at entry (`s.regions`
never mutated; nothing to re-establish after abort). -/

def cuTripleAbortsWithinMem (nSteps nCu : Nat) (entry : Nat) (cr : CodeReq)
    (P : Assertion) (rr : Memory.RegionTable → Prop) (errCode : Nat) : Prop :=
  ∀ (R : Assertion), R.pcFree →
  ∀ (fetch : Nat → Option Insn), cr.SatisfiedBy fetch →
  ∀ (s : State), (P ** R).holdsFor s → s.pc = entry → s.exitCode = none →
    s.cuConsumed + nSteps + nCu ≤ s.cuBudget →
    rr s.regions →
    ∃ k, k ≤ nSteps ∧
      (executeFn fetch s k).exitCode = some errCode ∧
      (executeFn fetch s k).cuConsumed ≤ s.cuConsumed + nSteps + nCu

/-- A non-memory aborting triple is a memory one with no region requirement,
    so pure abort specs compose with memory-laden prefixes. -/
theorem cuTripleAbortsWithin.toMem {nSteps nCu entry : Nat} {cr : CodeReq}
    {P : Assertion} {errCode : Nat}
    (h : cuTripleAbortsWithin nSteps nCu entry cr P errCode) :
    cuTripleAbortsWithinMem nSteps nCu entry cr P (fun _ => True) errCode := by
  intro R hR fetch hcr s hPR hpc hex hbud _
  exact h R hR fetch hcr s hPR hpc hex hbud

/-- Memory-aware sequencing into abort: `P{c₁}Q` chained with a Mem-aware
    `Q{c₂}aborts` yields a Mem-aware `P{c₁;c₂}aborts`, bounds summing, code
    reqs union, regions conjunct (mirrors `cuTripleWithinMem_seq`). Common
    use: a long memory-laden prefix terminated by `.exit`/`.call .abort`. -/
theorem cuTripleWithinMem_seq_abort {N1 N2 M1 M2 : Nat} {pc1 pc2 : Nat}
    {cr1 cr2 : CodeReq} (hd : cr1.Disjoint cr2)
    {P Q : Assertion} {rr1 rr2 : Memory.RegionTable → Prop}
    {errCode : Nat}
    (h1 : cuTripleWithinMem N1 M1 pc1 pc2 cr1 P Q rr1)
    (h2 : cuTripleAbortsWithinMem N2 M2 pc2 cr2 Q rr2 errCode) :
    cuTripleAbortsWithinMem (N1 + N2) (M1 + M2) pc1 (cr1.union cr2) P
      (fun rt => rr1 rt ∧ rr2 rt) errCode := by
  intro F hF fetch hcr s hPF hpc hex hbud h_reg
  obtain ⟨hreg1, hreg2⟩ := h_reg
  have hcr1 := CodeReq.SatisfiedBy_of_union_left hcr
  have hcr2 := CodeReq.SatisfiedBy_of_union_right hd hcr
  obtain ⟨k1, hk1, hpc_mid, hex_mid, hcu1, hQF⟩ :=
    h1 F hF fetch hcr1 s hPF hpc hex (by omega) hreg1
  have h_reg_mid : rr2 (executeFn fetch s k1).regions := by
    rw [executeFn_preserves_regions]; exact hreg2
  have hbud_mid : (executeFn fetch s k1).cuConsumed + N2 + M2
      ≤ (executeFn fetch s k1).cuBudget := by
    rw [executeFn_preserves_cuBudget]; omega
  obtain ⟨k2, hk2, hex_end, hcu2⟩ :=
    h2 F hF fetch hcr2 (executeFn fetch s k1) hQF hpc_mid hex_mid hbud_mid
      h_reg_mid
  refine ⟨k1 + k2, Nat.add_le_add hk1 hk2, ?_, ?_⟩
  · rw [executeFn_compose]; exact hex_end
  · rw [executeFn_compose]; omega

/-- Rule of consequence for memory-aware aborting triples: strengthen pre
    and `rr` (no post to weaken). -/
theorem cuTripleAbortsWithinMem_weaken {nSteps nCu : Nat} {entry : Nat}
    {cr : CodeReq}
    {P P' : Assertion} {rr rr' : Memory.RegionTable → Prop} {errCode : Nat}
    (hpre : ∀ h, P' h → P h)
    (h_rr  : ∀ rt, rr' rt → rr rt)
    (h : cuTripleAbortsWithinMem nSteps nCu entry cr P rr errCode) :
    cuTripleAbortsWithinMem nSteps nCu entry cr P' rr' errCode := by
  intro R hR fetch hcr s hP'R hpc hex hbud h_reg'
  have hPR : (P ** R).holdsFor s := by
    obtain ⟨hp, hcompat, h1, h2, hd, hu, hP'1, hR2⟩ := hP'R
    exact ⟨hp, hcompat, h1, h2, hd, hu, hpre h1 hP'1, hR2⟩
  exact h R hR fetch hcr s hPR hpc hex hbud (h_rr _ h_reg')

/-- Variant where the abort tail is non-Mem (commonly `.exit`): lift the
    tail via `.toMem`, route through the Mem seq, keep only the prefix's
    `rr` (the tail's lifted `True` collapses). -/
theorem cuTripleWithinMem_seq_abort_pure {N1 N2 M1 M2 : Nat}
    {pc1 pc2 : Nat}
    {cr1 cr2 : CodeReq} (hd : cr1.Disjoint cr2)
    {P Q : Assertion} {rr1 : Memory.RegionTable → Prop} {errCode : Nat}
    (h1 : cuTripleWithinMem N1 M1 pc1 pc2 cr1 P Q rr1)
    (h2 : cuTripleAbortsWithin N2 M2 pc2 cr2 Q errCode) :
    cuTripleAbortsWithinMem (N1 + N2) (M1 + M2) pc1 (cr1.union cr2) P
      rr1 errCode := by
  have h := cuTripleWithinMem_seq_abort hd h1 h2.toMem
  intro F hF fetch hcr s hPF hpc hex hbud h_reg
  exact h F hF fetch hcr s hPF hpc hex hbud ⟨h_reg, trivial⟩

/-! ## Memory-aware TYPED-FAULT triples (`cuTripleFaultsWithinMem`)

The `vmError`-carrying analog of `cuTripleAbortsWithinMem`: a memory-laden
prefix terminated by a typed fault (`.call .abort`/`.sol_panic_` ⇒
`.abort`, OOB syscall ⇒ `.accessViolation`). A per-lift fault corollary
composes the prefix with the terminal fault spec via
`cuTripleWithinMem_seq_fault[_pure]`, surfacing `vmError = some e`. -/

def cuTripleFaultsWithinMem (nSteps nCu : Nat) (entry : Nat) (cr : CodeReq)
    (P : Assertion) (rr : Memory.RegionTable → Prop) (e : VmError) : Prop :=
  ∀ (R : Assertion), R.pcFree →
  ∀ (fetch : Nat → Option Insn), cr.SatisfiedBy fetch →
  ∀ (s : State), (P ** R).holdsFor s → s.pc = entry → s.exitCode = none →
    s.cuConsumed + nSteps + nCu ≤ s.cuBudget →
    rr s.regions →
    ∃ k, k ≤ nSteps ∧
      (executeFn fetch s k).exitCode = some e.toSentinel ∧
      (executeFn fetch s k).vmError = some e ∧
      (executeFn fetch s k).cuConsumed ≤ s.cuConsumed + nSteps + nCu

/-- A non-memory typed-fault triple is a memory one with no region
    requirement (terminal `.abort`/`.sol_panic_` have no memory ops). -/
theorem cuTripleFaultsWithin.toMem {nSteps nCu entry : Nat} {cr : CodeReq}
    {P : Assertion} {e : VmError}
    (h : cuTripleFaultsWithin nSteps nCu entry cr P e) :
    cuTripleFaultsWithinMem nSteps nCu entry cr P (fun _ => True) e := by
  intro R hR fetch hcr s hPR hpc hex hbud _
  exact h R hR fetch hcr s hPR hpc hex hbud

/-- Forget the `vmError` conjunct: a Mem fault triple is a Mem abort triple
    at the fault's sentinel, back-filling `cuTripleAbortsWithinMem` consumers. -/
theorem cuTripleFaultsWithinMem_toAborts {nSteps nCu : Nat} {entry : Nat}
    {cr : CodeReq} {P : Assertion} {rr : Memory.RegionTable → Prop} {e : VmError}
    (h : cuTripleFaultsWithinMem nSteps nCu entry cr P rr e) :
    cuTripleAbortsWithinMem nSteps nCu entry cr P rr e.toSentinel := by
  intro R hR fetch hcr s hPR hpc hex hbud h_reg
  obtain ⟨k, hk, hexit, _, hcu⟩ := h R hR fetch hcr s hPR hpc hex hbud h_reg
  exact ⟨k, hk, hexit, hcu⟩

/-- Frame rule (right) for typed-fault Mem triples: add pc-free `F` on the
    right of the pre (mirror of `cuTripleAbortsWithin_frame_right`). The
    `*_fault_correct` emitter uses this to extend a single-register fault-spec
    pre (`.r1 ↦ᵣ r1V`) to a real prefix's multi-atom post. `rr` is unchanged
    (it constrains only `s.regions`, untouched by the frame). -/
theorem cuTripleFaultsWithinMem_frame_right (F : Assertion) (hF : F.pcFree)
    {N M : Nat} {entry : Nat} {cr : CodeReq} {P : Assertion}
    {rr : Memory.RegionTable → Prop} {e : VmError}
    (h : cuTripleFaultsWithinMem N M entry cr P rr e) :
    cuTripleFaultsWithinMem N M entry cr (P ** F) rr e := by
  intro R hR fetch hcr s hPFR hpc hex hbud h_reg
  have hFR_pcfree : (F ** R).pcFree := pcFree_sepConj hF hR
  have hP_FR : (P ** (F ** R)).holdsFor s := holdsFor_sepConj_assoc.mp hPFR
  exact h (F ** R) hFR_pcfree fetch hcr s hP_FR hpc hex hbud h_reg

/-- Memory-aware sequencing into a typed fault — the `vmError`-carrying
    mirror of `cuTripleWithinMem_seq_abort`. -/
theorem cuTripleWithinMem_seq_fault {N1 N2 M1 M2 : Nat} {pc1 pc2 : Nat}
    {cr1 cr2 : CodeReq} (hd : cr1.Disjoint cr2)
    {P Q : Assertion} {rr1 rr2 : Memory.RegionTable → Prop} {e : VmError}
    (h1 : cuTripleWithinMem N1 M1 pc1 pc2 cr1 P Q rr1)
    (h2 : cuTripleFaultsWithinMem N2 M2 pc2 cr2 Q rr2 e) :
    cuTripleFaultsWithinMem (N1 + N2) (M1 + M2) pc1 (cr1.union cr2) P
      (fun rt => rr1 rt ∧ rr2 rt) e := by
  intro F hF fetch hcr s hPF hpc hex hbud h_reg
  obtain ⟨hreg1, hreg2⟩ := h_reg
  have hcr1 := CodeReq.SatisfiedBy_of_union_left hcr
  have hcr2 := CodeReq.SatisfiedBy_of_union_right hd hcr
  obtain ⟨k1, hk1, hpc_mid, hex_mid, hcu1, hQF⟩ :=
    h1 F hF fetch hcr1 s hPF hpc hex (by omega) hreg1
  have h_reg_mid : rr2 (executeFn fetch s k1).regions := by
    rw [executeFn_preserves_regions]; exact hreg2
  have hbud_mid : (executeFn fetch s k1).cuConsumed + N2 + M2
      ≤ (executeFn fetch s k1).cuBudget := by
    rw [executeFn_preserves_cuBudget]; omega
  obtain ⟨k2, hk2, hex_end, hvm_end, hcu2⟩ :=
    h2 F hF fetch hcr2 (executeFn fetch s k1) hQF hpc_mid hex_mid hbud_mid h_reg_mid
  refine ⟨k1 + k2, Nat.add_le_add hk1 hk2, ?_, ?_, ?_⟩
  · rw [executeFn_compose]; exact hex_end
  · rw [executeFn_compose]; exact hvm_end
  · rw [executeFn_compose]; omega

/-- Variant where the fault tail is non-Mem (`.call .abort`/`.sol_panic_`).
    Mirror of `cuTripleWithinMem_seq_abort_pure`. -/
theorem cuTripleWithinMem_seq_fault_pure {N1 N2 M1 M2 : Nat} {pc1 pc2 : Nat}
    {cr1 cr2 : CodeReq} (hd : cr1.Disjoint cr2)
    {P Q : Assertion} {rr1 : Memory.RegionTable → Prop} {e : VmError}
    (h1 : cuTripleWithinMem N1 M1 pc1 pc2 cr1 P Q rr1)
    (h2 : cuTripleFaultsWithin N2 M2 pc2 cr2 Q e) :
    cuTripleFaultsWithinMem (N1 + N2) (M1 + M2) pc1 (cr1.union cr2) P rr1 e := by
  have h := cuTripleWithinMem_seq_fault hd h1 h2.toMem
  intro F hF fetch hcr s hPF hpc hex hbud h_reg
  exact h F hF fetch hcr s hPF hpc hex hbud ⟨h_reg, trivial⟩

end SVM.SBPF
