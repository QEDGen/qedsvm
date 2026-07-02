/-
  Terminating triple WITH a partial-state post — the whole-transition
  primitive (#40, gap 1).

  `cuTripleAbortsWithinMem` deliberately drops the post ("once aborted, the
  only content is the exit code"), so it cannot state what a whole-transition
  obligation needs: on an abort path the tracked account codecs are
  UNCHANGED, and on the success path they carry the update — claims about the
  final memory at `exitCode = some code`. `.exit` only sets
  `exitCode := some r0` (regs, memory, pc, returnData, callStack untouched,
  see `step` in Execute.lean), so a running post survives the terminal step
  verbatim: `cuTripleExitsWithinMem` keeps it, and
  `cuTripleWithinMem_seq_exit` is the canonical composition — a lifted
  running triple landing at the shared `.exit` pc with `r0 = code`, plus the
  `.exit` itself.
-/

import SVM.SBPF.CPSSpec
import SVM.SBPF.CodecRead

namespace SVM.SBPF

open Memory

/-- `cuTripleExitsWithinMem nSteps nCu entry cr P Q rr code`: from a running
    state with `P ** R` at `pc = entry` (and `rr` on the region table),
    execution reaches within `nSteps` a state with `exitCode = some code`,
    `cuConsumed` up by ≤ `nSteps + nCu`, and `Q ** R` STILL HOLDING of the
    exited partial state — the post-carrying analog of
    `cuTripleAbortsWithinMem`. -/
def cuTripleExitsWithinMem (nSteps nCu : Nat) (entry : Nat) (cr : CodeReq)
    (P Q : Assertion) (rr : Memory.RegionTable → Prop) (code : Nat) : Prop :=
  ∀ (R : Assertion), R.pcFree →
  ∀ (fetch : Nat → Option Insn), cr.SatisfiedBy fetch →
  ∀ (s : State), (P ** R).holdsFor s → s.pc = entry → s.exitCode = none →
    s.cuConsumed + nSteps + nCu ≤ s.cuBudget →
    rr s.regions →
    ∃ k, k ≤ nSteps ∧
      (executeFn fetch s k).exitCode = some code ∧
      (executeFn fetch s k).cuConsumed ≤ s.cuConsumed + nSteps + nCu ∧
      (Q ** R).holdsFor (executeFn fetch s k)

/-- `holdsFor` survives the exit step: `CompatibleWith` only reads
    regs/mem/pc/returnData/callStack, all untouched by setting `exitCode`
    and charging CU. -/
theorem holdsFor_exit_step {X : Assertion} {s : State} {v : Nat}
    (h : X.holdsFor s) :
    X.holdsFor (chargeCu { s with exitCode := some v }) := by
  obtain ⟨hp, hc, hX⟩ := h
  exact ⟨hp, { regs := hc.regs, mem := hc.mem, pc := hc.pc,
               returnData := hc.returnData, callStack := hc.callStack }, hX⟩

/-- `.exit` from a state satisfying `(.r0 ↦ᵣ code) ** callStackIs [] ** Q`:
    exits with `some code` and the WHOLE pre surviving as the post. The
    post-carrying analog of `exit_aborts_spec_cuTriple`. The exit-channel
    atoms sit FIRST so a right-associated `Q := setup ** codecs` tail keeps
    the transition-obligation shape (`AsmRefinesTransitionPath`) syntactic. -/
theorem exit_exits_spec_cuTriple (Q : Assertion) (code pc : Nat) :
    cuTripleExitsWithinMem 1 0 pc (CodeReq.singleton pc .exit)
      ((.r0 ↦ᵣ code) ** callStackIs [] ** Q)
      ((.r0 ↦ᵣ code) ** callStackIs [] ** Q)
      (fun _ => True) code := by
  intro R hR fetch hcr s hPR hpc hex hbud _
  -- Extract the r0 value and the empty call stack from the pre.
  have hmid := holdsFor_sepConj_left hPR
  have h_r0 : s.regs.get .r0 = code := by
    obtain ⟨hp, hc, hpred⟩ := holdsFor_sepConj_left hmid
    exact hc.regs .r0 code (hpred ▸ PartialState.singletonReg_regs_self)
  have h_cs : s.callStack = [] := by
    obtain ⟨hp, hc, hpred⟩ :=
      holdsFor_sepConj_left (holdsFor_sepConj_right hmid)
    refine hc.callStack [] ?_
    rw [show hp = PartialState.singletonCallStack [] from hpred]
    exact PartialState.singletonCallStack_callStack_self
  have hfetch : fetch s.pc = some .exit := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hexec : executeFn fetch s 1 = chargeCu (step .exit s) := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch,
        executeFn_zero]
  have hstep : step .exit s = { s with exitCode := some (s.regs.get .r0) } := by
    simp only [step, h_cs]
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_⟩
  · rw [hexec, hstep]
    show some (s.regs.get .r0) = some code
    rw [h_r0]
  · rw [hexec, hstep]
    show s.cuConsumed + 1 ≤ s.cuConsumed + 1 + 0
    omega
  · rw [hexec, hstep, h_r0]
    exact holdsFor_exit_step hPR

/-- Memory-aware sequencing into a post-carrying exit: `P{c₁}Q` chained with
    an exiting `Q{c₂}⟨code, Q'⟩` yields `P{c₁;c₂}⟨code, Q'⟩` — bounds sum,
    code reqs union, regions conjunct (mirrors `cuTripleWithinMem_seq_abort`,
    keeping the post). -/
theorem cuTripleWithinMem_seq_exits {N1 N2 M1 M2 : Nat} {pc1 pc2 : Nat}
    {cr1 cr2 : CodeReq} (hd : cr1.Disjoint cr2)
    {P Q Q' : Assertion} {rr1 rr2 : Memory.RegionTable → Prop} {code : Nat}
    (h1 : cuTripleWithinMem N1 M1 pc1 pc2 cr1 P Q rr1)
    (h2 : cuTripleExitsWithinMem N2 M2 pc2 cr2 Q Q' rr2 code) :
    cuTripleExitsWithinMem (N1 + N2) (M1 + M2) pc1 (cr1.union cr2) P Q'
      (fun rt => rr1 rt ∧ rr2 rt) code := by
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
  obtain ⟨k2, hk2, hex_end, hcu2, hQ'F⟩ :=
    h2 F hF fetch hcr2 (executeFn fetch s k1) hQF hpc_mid hex_mid hbud_mid
      h_reg_mid
  refine ⟨k1 + k2, Nat.add_le_add hk1 hk2, ?_, ?_, ?_⟩
  · rw [executeFn_compose]; exact hex_end
  · rw [executeFn_compose]; omega
  · rw [executeFn_compose]; exact hQ'F

/-- The canonical terminal composition (#40): a lifted running triple landing
    at the shared `.exit` pc with `r0 = code` and an empty call stack, plus
    the `.exit` itself, terminates with `exitCode = some code` and the
    running post INTACT — unlike `cuTripleWithinMem_seq_abort_pure`, which
    drops it. -/
theorem cuTripleWithinMem_seq_exit {N M : Nat} {pc1 pcExit : Nat}
    {cr : CodeReq} (hd : cr.Disjoint (CodeReq.singleton pcExit .exit))
    {P Q : Assertion} {rr : Memory.RegionTable → Prop} {code : Nat}
    (h1 : cuTripleWithinMem N M pc1 pcExit cr P
            ((.r0 ↦ᵣ code) ** callStackIs [] ** Q) rr) :
    cuTripleExitsWithinMem (N + 1) M pc1
      (cr.union (CodeReq.singleton pcExit .exit)) P
      ((.r0 ↦ᵣ code) ** callStackIs [] ** Q) rr code := by
  have h := cuTripleWithinMem_seq_exits hd h1
    (exit_exits_spec_cuTriple Q code pcExit)
  intro F hF fetch hcr s hPF hpc hex hbud h_reg
  exact h F hF fetch hcr s hPF hpc hex hbud ⟨h_reg, trivial⟩

end SVM.SBPF
