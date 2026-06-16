/-
  Gap #1, Milestone 1 (hand-written; Milestone 2 will mechanize this as a
  qedlift `dispatch.rs` emitter): WHOLE-PROGRAM dispatch-completeness for the
  SPL p_token program.

  GOAL (Option (a), full per-arm partition): prove that, starting at the shared
  entrypoint (logical PC 198), EVERY possible instruction-discriminator + account
  state either follows one of the six proven arms (Transfer / TransferChecked /
  MintTo / Burn / CloseAccount / InitializeMint2) to its proven outcome, OR
  reaches a fail-closed fault. Together with the per-arm lift theorems this
  states that no unproven path can escape the dispatcher.

  This file builds that result BOTTOM-UP, one dispatch level at a time. It is a
  multi-session effort (see `docs/DISPATCH_COMPLETENESS_PLAN.md` for the full CFG
  map and roadmap); each increment is kernel-checked and committed.

  The p_token "dispatcher" is NOT a clean single-byte cascade: it is a multi-
  level decision tree over a BYTE at `[r1+0]` and DWORDs at `[r1+88]`, `[r1+...]`,
  with the arm bodies inlined and shared join points (e.g. PC 312 is the error
  skip for some arms but a body continuation for others). r2 is reused across the
  byte/dword reads. This file models the routing as a TOTAL function and proves,
  via the NO-PATH-HYPOTHESIS jump specs (`jeq_imm_spec` / `jne_imm_spec`, whose
  exit PC is `if cond then target else pc+1`), that the routing covers every
  discriminator byte at once (an implicit `Fin 256` exhaustiveness, since `Route`
  is total).

  INCREMENT 1 (this file, now): the first-byte routing level (PCs 198/199/200) —
  `Route` over all 256 discriminator bytes, kernel-checked. Deeper levels (the
  `[r1+88]` dword sub-dispatch), the fault leaf, and composition with the arm
  lifts are the next increments (roadmap in the plan doc).
-/

import SVM.SBPF.InstructionSpecs
import SVM.SBPF.Tactic.SL
import SVM.SBPF.Macros

namespace Examples.PTokenDispatchComplete

open SVM.SBPF
open Memory

/-! ## Generic infrastructure (candidates for promotion to `CPSSpec.lean`)

Two structural weakenings the dispatch-completeness proof needs repeatedly but
which `CPSSpec.lean` only provides for the non-memory triple. Kept local for now
(reviewable on this branch); promote once the shape stabilises. -/

/-- Monotonicity of a memory triple in the step bound (mem analogue of
    `cuTripleWithin_mono_nSteps`): a shorter execution is also a longer-budget
    one. Lets a 2-step branch share a uniform `nSteps` with 3-step branches. -/
theorem cuTripleWithinMem_mono_nSteps {N N' M e x : Nat} {cr : CodeReq}
    {P Q : Assertion} {rr : Memory.RegionTable → Prop}
    (hle : N ≤ N')
    (h : cuTripleWithinMem N M e x cr P Q rr) :
    cuTripleWithinMem N' M e x cr P Q rr := by
  intro R hR fetch hcr s hPR hpc hex hbud hreg
  obtain ⟨k, hk, hpc', hex', hcu, hQR⟩ :=
    h R hR fetch hcr s hPR hpc hex (by omega) hreg
  exact ⟨k, Nat.le_trans hk hle, hpc', hex', by omega, hQR⟩

/-- Weaken a memory triple's `CodeReq`: a triple requiring `cr` also holds under
    any `cr'` whose satisfaction implies `cr`'s (e.g. a larger left-biased union;
    discharge with `SatisfiedBy_of_union_left`). Lets branches that walk fewer
    PCs share the full dispatcher `CodeReq`. -/
theorem cuTripleWithinMem_weaken_cr {N M e x : Nat} {cr cr' : CodeReq}
    {P Q : Assertion} {rr : Memory.RegionTable → Prop}
    (himpl : ∀ fetch, cr'.SatisfiedBy fetch → cr.SatisfiedBy fetch)
    (h : cuTripleWithinMem N M e x cr P Q rr) :
    cuTripleWithinMem N M e x cr' P Q rr := by
  intro R hR fetch hcr' s hPR hpc hex hbud hreg
  exact h R hR fetch (himpl fetch hcr') s hPR hpc hex hbud hreg

/-! ## First-byte dispatch (PCs 198 → 199 → 200): generalized over ALL discriminators

- PC 198: `ldxb r2 ← [r1+0]`  (load the discriminator byte into r2)
- PC 199: `jeq r2 3 → 304`     (disc = 3 → Transfer/MintTo/… family @ 304; else → 200)
- PC 200: `jne r2 4 → 312`     (disc = 4 → TransferChecked/InitMint2 family @ 201; else → 312)

`H1Dispatch` proved only the `disc = 3` case (by collapsing the `jeq` with a
discriminator hypothesis). Here `Route` keeps every byte:

    Route disc = if disc = 3 then 304 else if disc = 4 then 201 else 312

NB the byte at PC 198 only separates {3} / {4} / {else}; both Transfer AND MintTo
have disc byte = 3 and diverge later on the `[r1+88]` dword (the next increment).
So 304 / 201 are FAMILY entries, not single arms; 312 is the shared region the
`else` (and several validation failures) fall into. -/

/-- Where the first-byte dispatcher sends discriminator byte `disc`. Total over
    `[0, 256)` (the `% 256` of the loaded byte), so coverage is automatic. -/
def Route (disc : Nat) : Nat :=
  if disc % 256 = toU64 3 then 304
  else if disc % 256 = toU64 4 then 201
  else 312

/-- CodeReq for the 3-insn first-byte dispatcher. -/
def dispatchCr : CodeReq :=
  cr![ 198 ↦ .ldx .byte .r2 .r1 0,
       199 ↦ .jeq .r2 (.imm 3) 304,
       200 ↦ .jne .r2 (.imm 4) 312 ]

/-- 2-insn first level (PCs 198/199), every discriminator: exit is
    `if disc%256 = 3 then 304 else 200`. The `H1Dispatch` lemma, generalized off
    its `disc = 3` hypothesis (the `jeq`'s `if` is kept, not collapsed). -/
theorem entry_route_l1 (initR1 initR2 disc : Nat) :
    cuTripleWithinMem 2 0 198 (if disc % 256 = toU64 3 then 304 else 200)
      (cr![ 198 ↦ .ldx .byte .r2 .r1 0, 199 ↦ .jeq .r2 (.imm 3) 304 ])
      ((.r1 ↦ᵣ initR1) ** (.r2 ↦ᵣ initR2) ** (effectiveAddr initR1 0 ↦ₘ disc))
      ((.r1 ↦ᵣ initR1) ** (.r2 ↦ᵣ disc % 256) ** (effectiveAddr initR1 0 ↦ₘ disc))
      (fun rt => rt.containsRange (effectiveAddr initR1 0) 1 = true) := by
  have h0 := ldxb_spec .r2 .r1 0 initR2 initR1 disc 198 (by decide)
  have h1 := jeq_imm_spec .r2 3 (disc % 256) 199 304
  sl_block_iter [h0, h1]

/-- First-byte dispatch completeness: from PC 198, EVERY discriminator byte
    routes to `Route disc` (304 / 201 / 312) in ≤ 3 steps. Proved by a three-way
    case split on the byte; each case chains the no-path-hypothesis jump specs.
    Since `Route` is a total function the three cases exhaust `[0, 256)`. -/
theorem entry_route (initR1 initR2 disc : Nat) :
    cuTripleWithinMem 3 0 198 (Route disc) dispatchCr
      ((.r1 ↦ᵣ initR1) ** (.r2 ↦ᵣ initR2) ** (effectiveAddr initR1 0 ↦ₘ disc))
      ((.r1 ↦ᵣ initR1) ** (.r2 ↦ᵣ disc % 256) ** (effectiveAddr initR1 0 ↦ₘ disc))
      (fun rt => rt.containsRange (effectiveAddr initR1 0) 1 = true) := by
  have h0 := ldxb_spec .r2 .r1 0 initR2 initR1 disc 198 (by decide)
  unfold Route
  by_cases h3 : disc % 256 = toU64 3
  · -- disc = 3 → 304, walked in 2 steps; bump nSteps to 3 and widen the cr to
    -- include PC 200 (never executed on this branch). Reuse `entry_route_l1`.
    rw [if_pos h3]
    have chain := entry_route_l1 initR1 initR2 disc
    rw [if_pos h3] at chain
    exact cuTripleWithinMem_weaken_cr
      (fun _ hsat => CodeReq.SatisfiedBy_of_union_left hsat)
      (cuTripleWithinMem_mono_nSteps (by omega) chain)
  · rw [if_neg h3]
    have h1 := jeq_imm_spec .r2 3 (disc % 256) 199 304
    rw [if_neg h3] at h1
    unfold dispatchCr
    by_cases h4 : disc % 256 = toU64 4
    · -- disc = 4 → 201 (PC 200 jne not taken), walked in 3 steps.
      rw [if_pos h4]
      have h2 := jne_imm_spec .r2 4 (disc % 256) 200 312
      rw [if_neg (fun hn => hn h4)] at h2
      sl_block_iter [h0, h1, h2]
    · -- disc ∉ {3,4} → 312 (PC 200 jne taken), walked in 3 steps.
      rw [if_neg h4]
      have h2 := jne_imm_spec .r2 4 (disc % 256) 200 312
      rw [if_pos h4] at h2
      sl_block_iter [h0, h1, h2]

end Examples.PTokenDispatchComplete
