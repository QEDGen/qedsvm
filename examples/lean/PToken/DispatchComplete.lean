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

/-! ## Second level, byte=3 family (PCs 304 → 305): the `[r1+88]` dword sub-dispatch

`entry_route` sends disc byte = 3 to PC 304, where a SECOND discriminator — a
DWORD at `[r1+88]` — separates the Transfer arm from the MintTo arm (both have
disc byte 3):

- PC 304: `ldxdw r2 ← [r1+88]`  (reload r2 with the [r1+88] dword)
- PC 305: `jne r2 165 → 312`    (dword = 165 → Transfer continues @ 306;
                                  else → 312, the MintTo body / shared region)

`route_byte3_family` covers BOTH levels (PCs 198/199/304/305) for EVERY
[r1+88] dword value, given the disc byte is 3. -/

/-- Where the byte=3 family goes after the `[r1+88]` dword discriminator: 306
    (Transfer continues) or 312 (MintTo body / shared region). Total over the
    dword's `< 2^64` range. -/
def Route304 (dword : Nat) : Nat := if dword = toU64 165 then 306 else 312

/-- CodeReq for the byte=3 family's first two dispatch levels. -/
def cr304Family : CodeReq :=
  cr![ 198 ↦ .ldx .byte .r2 .r1 0,
       199 ↦ .jeq .r2 (.imm 3) 304,
       304 ↦ .ldx .dword .r2 .r1 88,
       305 ↦ .jne .r2 (.imm 165) 312 ]

/-- Byte=3 family routing completeness: when the discriminator byte is 3, EVERY
    `[r1+88]` dword routes from PC 198 to `Route304 dword` (306 / 312) in 4 steps.
    Composes the byte level (`jeq 3 → 304`) with the dword sub-dispatch
    (`ldxdw [r1+88]` + `jne 165 → 312`). -/
theorem route_byte3_family
    (initR1 initR2 byte dword : Nat)
    (h3 : byte % 256 = toU64 3) (hdword : dword < 2 ^ 64) :
    cuTripleWithinMem 4 0 198 (Route304 dword) cr304Family
      ((.r1 ↦ᵣ initR1) ** (.r2 ↦ᵣ initR2) **
        (effectiveAddr initR1 0 ↦ₘ byte) ** (effectiveAddr initR1 88 ↦U64 dword))
      ((.r1 ↦ᵣ initR1) ** (.r2 ↦ᵣ dword) **
        (effectiveAddr initR1 0 ↦ₘ byte) ** (effectiveAddr initR1 88 ↦U64 dword))
      (fun rt => rt.containsRange (effectiveAddr initR1 0) 1 = true ∧
                 rt.containsRange (effectiveAddr initR1 88) 8 = true) := by
  have h0 := ldxb_spec .r2 .r1 0 initR2 initR1 byte 198 (by decide)
  have h1 := jeq_imm_spec .r2 3 (byte % 256) 199 304
  rw [if_pos h3] at h1
  have h2 := ldxdw_spec .r2 .r1 88 (byte % 256) initR1 dword 304 (by decide) hdword
  unfold Route304 cr304Family
  by_cases h165 : dword = toU64 165
  · -- dword = 165 → Transfer continues @ 306 (PC 305 jne not taken).
    rw [if_pos h165]
    have h3' := jne_imm_spec .r2 165 dword 305 312
    rw [if_neg (fun hn => hn h165)] at h3'
    sl_block_iter [h0, h1, h2, h3']
  · -- dword ≠ 165 → MintTo body / shared region @ 312 (PC 305 jne taken).
    rw [if_neg h165]
    have h3' := jne_imm_spec .r2 165 dword 305 312
    rw [if_pos h165] at h3'
    sl_block_iter [h0, h1, h2, h3']

/-! ## Second level, byte=4 family (PCs 201 → 202): the symmetric `[r1+88]` sub-dispatch

`entry_route` sends disc byte = 4 to PC 201, where the `[r1+88]` dword is checked
(TransferChecked / InitializeMint2 family):

- PC 201: `ldxdw r2 ← [r1+88]`
- PC 202: `jne r2 165 → 312`  (dword = 165 → continue @ 203; else → 312)

Symmetric to `route_byte3_family`; walks PCs 198/199/200/201/202. -/

/-- Where the byte=4 family goes after the `[r1+88]` dword check: 203 (continue)
    or 312 (shared region). -/
def Route4 (dword : Nat) : Nat := if dword = toU64 165 then 203 else 312

/-- CodeReq for the byte=4 family's first two dispatch levels. -/
def cr4Family : CodeReq :=
  cr![ 198 ↦ .ldx .byte .r2 .r1 0,
       199 ↦ .jeq .r2 (.imm 3) 304,
       200 ↦ .jne .r2 (.imm 4) 312,
       201 ↦ .ldx .dword .r2 .r1 88,
       202 ↦ .jne .r2 (.imm 165) 312 ]

/-- Byte=4 family routing completeness: when the discriminator byte is 4, EVERY
    `[r1+88]` dword routes from PC 198 to `Route4 dword` (203 / 312) in 5 steps. -/
theorem route_byte4_family
    (initR1 initR2 byte dword : Nat)
    (h4 : byte % 256 = toU64 4) (hdword : dword < 2 ^ 64) :
    cuTripleWithinMem 5 0 198 (Route4 dword) cr4Family
      ((.r1 ↦ᵣ initR1) ** (.r2 ↦ᵣ initR2) **
        (effectiveAddr initR1 0 ↦ₘ byte) ** (effectiveAddr initR1 88 ↦U64 dword))
      ((.r1 ↦ᵣ initR1) ** (.r2 ↦ᵣ dword) **
        (effectiveAddr initR1 0 ↦ₘ byte) ** (effectiveAddr initR1 88 ↦U64 dword))
      (fun rt => rt.containsRange (effectiveAddr initR1 0) 1 = true ∧
                 rt.containsRange (effectiveAddr initR1 88) 8 = true) := by
  have h0 := ldxb_spec .r2 .r1 0 initR2 initR1 byte 198 (by decide)
  have h1 := jeq_imm_spec .r2 3 (byte % 256) 199 304
  rw [if_neg (show ¬(byte % 256 = toU64 3) by rw [h4]; decide)] at h1
  have h2 := jne_imm_spec .r2 4 (byte % 256) 200 312
  rw [if_neg (fun hn => hn h4)] at h2
  have h3 := ldxdw_spec .r2 .r1 88 (byte % 256) initR1 dword 201 (by decide) hdword
  unfold Route4 cr4Family
  by_cases h165 : dword = toU64 165
  · rw [if_pos h165]
    have h4' := jne_imm_spec .r2 165 dword 202 312
    rw [if_neg (fun hn => hn h165)] at h4'
    sl_block_iter [h0, h1, h2, h3, h4']
  · rw [if_neg h165]
    have h4' := jne_imm_spec .r2 165 dword 202 312
    rw [if_pos h165] at h4'
    sl_block_iter [h0, h1, h2, h3, h4']

/-! ## Fault-leaf primitive: the error-return idiom aborts

The dispatcher's fail-closed paths terminate in the idiom `mov64 r0 <errcode>;
exit` (e.g. PC 9247 `mov64 r0 10` / PC 9248 `exit` returns error code 10). This
primitive proves that idiom ABORTS with `exitCode = toU64 errcode`, the
reusable building block for the fault leaf: any unmatched-discriminator path that
reaches such a block aborts (`exit_aborts_spec` reads r0; the `mov` pins it to
the error code). Composed via `cuTripleAbortsWithin_seq_abort` (`mov` is a normal
step; `exit` is the abort). The `callStackIs []` atom carries `exit`'s top-level
condition (the success/error exit needs an empty call stack). -/
theorem error_return_aborts (errcode vR0Old pc : Nat) :
    cuTripleAbortsWithin 2 0 pc
      (cr![ pc ↦ .mov64 .r0 (.imm errcode), pc + 1 ↦ .exit ])
      ((.r0 ↦ᵣ vR0Old) ** callStackIs [])
      (toU64 errcode) := by
  have h1 := cuTripleWithin_frame_right (callStackIs []) (pcFree_callStackIs [])
    (mov64_imm_spec .r0 errcode vR0Old pc (by decide))
  have h2 := exit_aborts_spec_cuTriple (toU64 errcode) (pc + 1)
  have hd : (CodeReq.singleton pc (.mov64 .r0 (.imm errcode))).Disjoint
            (CodeReq.singleton (pc + 1) .exit) := by sl_disjoint_codereq
  exact cuTripleAbortsWithin_seq_abort hd h1 h2

/-! ## The PC 312 shared sub-dispatcher (entry prologue, PCs 312 → 315)

PC 312 is the major shared join (reached by byte=3 ∧ dword≠165 [MintTo],
byte∉{3,4} [InitializeMint2, …], and unmatched discriminators). Its prologue
re-reads `[r1+0]` as a FULL 8-byte word and makes the first sub-dispatch
decision:

- 312 `mov64 r0 ← r1`; 313 `add64 r0 += 8`;
- 314 `ldxdw_bytes r7 ← [r1+0]`  (r7 = the LE 8-byte word, via `ldxdw_bytes_spec`
                                  over 8 owned byte cells);
- 315 `jeq r7 0 → 418`           (word = 0 → 418; else → 316, the 316–320
                                  arithmetic + further r7 sub-dispatch at 321/322).

`route_312_prologue` covers PCs 312 → 315 for EVERY 8-byte word. The full
sub-dispatch (the 316–320 arithmetic + word=1→330 / word=2→323 / else→3361
branches) and the fault leaf (routing unmatched words to their DISTINCT
error-return exits — the 23 exits don't share a common tail) are the remaining
312-region work; see docs/DISPATCH_COMPLETENESS_PLAN.md. -/

theorem route_312_prologue
    (vR0Old baseAddr vR7Old b0 b1 b2 b3 b4 b5 b6 b7 : Nat)
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256)
    (hb4 : b4 < 256) (hb5 : b5 < 256) (hb6 : b6 < 256) (hb7 : b7 < 256) :
    cuTripleWithinMem 4 0 312
      (if (b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 *
          (b4 + 256 * (b5 + 256 * (b6 + 256 * b7))))))) = toU64 0 then 418 else 316)
      (cr![ 312 ↦ .mov64 .r0 (.reg .r1),
            313 ↦ .add64 .r0 (.imm 8),
            314 ↦ .ldx .dword .r7 .r1 0,
            315 ↦ .jeq .r7 (.imm 0) 418 ])
      ((.r0 ↦ᵣ vR0Old) ** (.r1 ↦ᵣ baseAddr) ** (.r7 ↦ᵣ vR7Old) **
        ((effectiveAddr baseAddr 0 ↦ₘ b0) ** (effectiveAddr baseAddr 0 + 1 ↦ₘ b1) **
         (effectiveAddr baseAddr 0 + 2 ↦ₘ b2) ** (effectiveAddr baseAddr 0 + 3 ↦ₘ b3) **
         (effectiveAddr baseAddr 0 + 4 ↦ₘ b4) ** (effectiveAddr baseAddr 0 + 5 ↦ₘ b5) **
         (effectiveAddr baseAddr 0 + 6 ↦ₘ b6) ** (effectiveAddr baseAddr 0 + 7 ↦ₘ b7)))
      ((.r0 ↦ᵣ wrapAdd baseAddr (toU64 8)) ** (.r1 ↦ᵣ baseAddr) **
        (.r7 ↦ᵣ (b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 *
          (b4 + 256 * (b5 + 256 * (b6 + 256 * b7)))))))) **
        ((effectiveAddr baseAddr 0 ↦ₘ b0) ** (effectiveAddr baseAddr 0 + 1 ↦ₘ b1) **
         (effectiveAddr baseAddr 0 + 2 ↦ₘ b2) ** (effectiveAddr baseAddr 0 + 3 ↦ₘ b3) **
         (effectiveAddr baseAddr 0 + 4 ↦ₘ b4) ** (effectiveAddr baseAddr 0 + 5 ↦ₘ b5) **
         (effectiveAddr baseAddr 0 + 6 ↦ₘ b6) ** (effectiveAddr baseAddr 0 + 7 ↦ₘ b7)))
      (fun rt => rt.containsRange (effectiveAddr baseAddr 0) 8 = true) := by
  have h0 := mov64_reg_spec .r0 .r1 vR0Old baseAddr 312 (by decide)
  have h1 := add64_imm_spec .r0 8 baseAddr 313 (by decide)
  have h2 := ldxdw_bytes_spec .r7 .r1 0 vR7Old baseAddr b0 b1 b2 b3 b4 b5 b6 b7
    (effectiveAddr baseAddr 0) (effectiveAddr baseAddr 0 + 1) (effectiveAddr baseAddr 0 + 2)
    (effectiveAddr baseAddr 0 + 3) (effectiveAddr baseAddr 0 + 4) (effectiveAddr baseAddr 0 + 5)
    (effectiveAddr baseAddr 0 + 6) (effectiveAddr baseAddr 0 + 7) 314 (by decide)
    hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 rfl rfl rfl rfl rfl rfl rfl rfl
  have h3 := jeq_imm_spec .r7 0 (b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 *
    (b4 + 256 * (b5 + 256 * (b6 + 256 * b7))))))) 315 418
  sl_block_iter [h0, h1, h2, h3]

/-! ## The PC 312 sub-dispatcher body (PCs 316 → 322): the word∈{1,2,else} branches

After the `word = 0` check at 315 falls through (word ≠ 0), the 312 region runs
address arithmetic then sub-dispatches on the same 8-byte word `r7`:

- 316 `stxdw [r10-2072] ← r0`; 317 `ldxdw r2 ← [r1+88]`; 318 `add64 r1 += r2`;
  319 `add64 r1 += 10351`; 320 `and64 r1 &= -8`  (the 316–320 arithmetic);
- 321 `jeq r7 1 → 330`  (word = 1 → 330, e.g. InitializeMint2);
- 322 `jne r7 2 → 3361` (word = 2 → 323; else → 3361).

`route_312_body` covers PCs 316 → 322 for EVERY word, routing to `Route312body
word` (330 / 323 / 3361). The arithmetic is carried through the chain (post
`r0`/`r1`/`r2`/stack are concrete symbolic values) but only `r7` is read by the
dispatch, so the post is uniform across the three word cases (only the exit PC
and step count differ; word=1 jumps at 321 in 6 steps, the rest in 7). Composing
`route_312_prologue` (else-branch → 316) with this gives the 312 region's full
first-level sub-dispatch. -/

/-- The uniform post-state of the 312 body (PCs 316–320 arithmetic): r0 / r10 /
    the read-only `[r1+88]` cell unchanged, r1 reshaped by `add;add;and`, r2 ←
    the `[r1+88]` dword, the stack cell ← r0. Shared by both body lemmas (the
    jeq/jne at 321/322 are pure, so the word case only changes the exit PC). -/
private def body312Post (baseAddr r0In dword88 word vR10Old : Nat) : Assertion :=
  (.r0 ↦ᵣ r0In) **
    (.r1 ↦ᵣ ((wrapAdd (wrapAdd baseAddr dword88) (toU64 10351)) &&& toU64 (-8))
              % U64_MODULUS) **
    (.r2 ↦ᵣ dword88) ** (.r7 ↦ᵣ word) ** (.r10 ↦ᵣ vR10Old) **
    (effectiveAddr baseAddr 88 ↦U64 dword88) **
    (effectiveAddr vR10Old (-2072) ↦U64 r0In)

private def body312Pre (baseAddr r0In vR2Old word vR10Old dword88 oldStack : Nat) :
    Assertion :=
  (.r0 ↦ᵣ r0In) ** (.r1 ↦ᵣ baseAddr) ** (.r2 ↦ᵣ vR2Old) ** (.r7 ↦ᵣ word) **
    (.r10 ↦ᵣ vR10Old) ** (effectiveAddr baseAddr 88 ↦U64 dword88) **
    (effectiveAddr vR10Old (-2072) ↦U64 oldStack)

private def body312Rr (baseAddr vR10Old : Nat) : Memory.RegionTable → Prop :=
  fun rt => rt.containsWritable (effectiveAddr vR10Old (-2072)) 8 = true ∧
            rt.containsRange (effectiveAddr baseAddr 88) 8 = true

/-- 312 body, word = 1 → 330 (the `jeq r7 1` at PC 321 is taken; PCs 316–321,
    6 steps). 330 is the InitializeMint2-family continuation. -/
theorem route_312_to_330
    (baseAddr r0In vR2Old word vR10Old dword88 oldStack : Nat)
    (hdword88 : dword88 < 2 ^ 64) (h1 : word = toU64 1) :
    cuTripleWithinMem 6 0 316 330
      (cr![ 316 ↦ .stx .dword .r10 (-2072) .r0, 317 ↦ .ldx .dword .r2 .r1 88,
            318 ↦ .add64 .r1 (.reg .r2), 319 ↦ .add64 .r1 (.imm 10351),
            320 ↦ .and64 .r1 (.imm (-8)), 321 ↦ .jeq .r7 (.imm 1) 330 ])
      (body312Pre baseAddr r0In vR2Old word vR10Old dword88 oldStack)
      (body312Post baseAddr r0In dword88 word vR10Old)
      (body312Rr baseAddr vR10Old) := by
  unfold body312Pre body312Post body312Rr
  have h316 := stxdw_spec .r10 .r0 (-2072) vR10Old r0In oldStack 316
  have h317 := ldxdw_spec .r2 .r1 88 vR2Old baseAddr dword88 317 (by decide) hdword88
  have h318 := add64_reg_spec .r1 .r2 baseAddr dword88 318 (by decide)
  have h319 := add64_imm_spec .r1 10351 (wrapAdd baseAddr dword88) 319 (by decide)
  have h320 := and64_imm_spec .r1 (-8)
    (wrapAdd (wrapAdd baseAddr dword88) (toU64 10351)) 320 (by decide)
  have h321 := jeq_imm_spec .r7 1 word 321 330
  rw [if_pos h1] at h321
  sl_block_iter [h316, h317, h318, h319, h320, h321]

/-- 312 body, word ≠ 1 → 323 (word = 2) / 3361 (else) (the `jeq r7 1` falls
    through, then `jne r7 2` at PC 322; PCs 316–322, 7 steps). -/
theorem route_312_body_other
    (baseAddr r0In vR2Old word vR10Old dword88 oldStack : Nat)
    (hdword88 : dword88 < 2 ^ 64) (hne1 : word ≠ toU64 1) :
    cuTripleWithinMem 7 0 316 (if word = toU64 2 then 323 else 3361)
      (cr![ 316 ↦ .stx .dword .r10 (-2072) .r0, 317 ↦ .ldx .dword .r2 .r1 88,
            318 ↦ .add64 .r1 (.reg .r2), 319 ↦ .add64 .r1 (.imm 10351),
            320 ↦ .and64 .r1 (.imm (-8)), 321 ↦ .jeq .r7 (.imm 1) 330,
            322 ↦ .jne .r7 (.imm 2) 3361 ])
      (body312Pre baseAddr r0In vR2Old word vR10Old dword88 oldStack)
      (body312Post baseAddr r0In dword88 word vR10Old)
      (body312Rr baseAddr vR10Old) := by
  unfold body312Pre body312Post body312Rr
  have h316 := stxdw_spec .r10 .r0 (-2072) vR10Old r0In oldStack 316
  have h317 := ldxdw_spec .r2 .r1 88 vR2Old baseAddr dword88 317 (by decide) hdword88
  have h318 := add64_reg_spec .r1 .r2 baseAddr dword88 318 (by decide)
  have h319 := add64_imm_spec .r1 10351 (wrapAdd baseAddr dword88) 319 (by decide)
  have h320 := and64_imm_spec .r1 (-8)
    (wrapAdd (wrapAdd baseAddr dword88) (toU64 10351)) 320 (by decide)
  have h321 := jeq_imm_spec .r7 1 word 321 330
  rw [if_neg hne1] at h321
  by_cases h2 : word = toU64 2
  · rw [if_pos h2]
    have h322 := jne_imm_spec .r7 2 word 322 3361
    rw [if_neg (fun hn => hn h2)] at h322
    sl_block_iter [h316, h317, h318, h319, h320, h321, h322]
  · rw [if_neg h2]
    have h322 := jne_imm_spec .r7 2 word 322 3361
    rw [if_pos h2] at h322
    sl_block_iter [h316, h317, h318, h319, h320, h321, h322]

end Examples.PTokenDispatchComplete
