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

import SVM.SBPF.InstructionSpecs
import SVM.SBPF.Tactic.SL
import SVM.SBPF.SpecGen

namespace SVM.SBPF

/-! ## Two-mov macro

The sBPF macro:

```
  pc=0:  mov64 r1, 7
  pc=1:  mov64 r2, 8
```

Spec: starting from any initial values for r1 and r2, after 2 compute
units, r1 holds 7 and r2 holds 8. -/

theorem two_mov_macro_spec (vOld1 vOld2 : Nat) :
    cuTripleWithin 2 0 0 2
      ((CodeReq.singleton 0 (.mov64 .r1 (.imm 7))).union
       (CodeReq.singleton 1 (.mov64 .r2 (.imm 8))))
      ((.r1 ↦ᵣ vOld1) ** (.r2 ↦ᵣ vOld2))
      ((.r1 ↦ᵣ toU64 7) ** (.r2 ↦ᵣ toU64 8)) := by
  -- `sl_block_iter` infers the frames per step: step 1 right-frames
  -- `r2` onto `mov r1`, step 2 left-frames the already-updated `r1`
  -- onto `mov r2`. Both framings are picked automatically by the
  -- prefix/suffix atom match.
  have h1 := mov64_imm_spec .r1 7 vOld1 0 (by decide)
  have h2 := mov64_imm_spec .r2 8 vOld2 1 (by decide)
  sl_block_iter [h1, h2]

/-- Same macro as `two_mov_macro_spec`, proved via `sl_block_auto`.
    Demonstrates the boilerplate-free pattern: the tactic reads the
    goal's CodeReq, dispatches each Insn to the corresponding spec
    (here: `mov64_imm_spec` × 2), threads the value mvars through
    `slBlockIter`'s `isDefEq` to unify with `vOld1` / `vOld2`, and
    auto-discharges the `.r1 ≠ .r10` / `.r2 ≠ .r10` side conds. -/
theorem two_mov_macro_spec_auto (vOld1 vOld2 : Nat) :
    cuTripleWithin 2 0 0 2
      ((CodeReq.singleton 0 (.mov64 .r1 (.imm 7))).union
       (CodeReq.singleton 1 (.mov64 .r2 (.imm 8))))
      ((.r1 ↦ᵣ vOld1) ** (.r2 ↦ᵣ vOld2))
      ((.r1 ↦ᵣ toU64 7) ** (.r2 ↦ᵣ toU64 8)) := by
  sl_block_auto

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
    cuTripleWithin 2 0 0 2
      ((CodeReq.singleton 0 (.mov64 .r1 (.imm 10))).union
       (CodeReq.singleton 1 (.add64 .r1 (.imm 5))))
      (.r1 ↦ᵣ vOld)
      (.r1 ↦ᵣ wrapAdd (toU64 10) (toU64 5)) := by
  -- Both steps own only `r1`, no framing needed at either step.
  -- `sl_block_iter` composes via `cuTripleWithin_seq` (both pure).
  have h1 := mov64_imm_spec .r1 10 vOld 0 (by decide)
  have h2 := add64_imm_spec .r1 5 (toU64 10) 1 (by decide)
  sl_block_iter [h1, h2]

/-! ## Reg-source macro: `r1 := 100 + r2`

Demonstrates the methodology with a register-source ALU op. r2 is
framed-through the first instruction (`mov64 r1, 100` doesn't touch
it), then consumed by the reg-source `add64 r1, r2` whose two-atom
precondition `(r1 ↦ᵣ 100) ** (r2 ↦ᵣ v)` matches the framed state.

```
  pc=0:  mov64 r1, 100
  pc=1:  add64 r1, r2
```

After 2 compute units, `r1 = wrapAdd (toU64 100) v` and `r2` is
unchanged. -/

theorem mov_then_add_reg_macro_spec (vR1Old vR2Old : Nat) :
    cuTripleWithin 2 0 0 2
      ((CodeReq.singleton 0 (.mov64 .r1 (.imm 100))).union
       (CodeReq.singleton 1 (.add64 .r1 (.reg .r2))))
      ((.r1 ↦ᵣ vR1Old) ** (.r2 ↦ᵣ vR2Old))
      ((.r1 ↦ᵣ wrapAdd (toU64 100) vR2Old) ** (.r2 ↦ᵣ vR2Old)) := by
  -- `sl_block_iter` right-frames `r2` onto `mov r1`, then composes
  -- with `add64 r1 r2` (which already owns both registers).
  have h1 := mov64_imm_spec .r1 100 vR1Old 0 (by decide)
  have h2 := add64_reg_spec .r1 .r2 (toU64 100) vR2Old 1 (by decide)
  sl_block_iter [h1, h2]

/-! ## Memory-op macro: `load byte, then increment register`

First end-to-end SL macro that exercises memory ownership. Two
instructions:

```
  pc=0: ldxb r2, r1, 0   -- load byte at [r1] into r2
  pc=1: add64 r2, 1      -- r2 := r2 + 1
```

The byte at `[r1]` is read but not modified; `r1` is unchanged. The
post says `r2 = wrapAdd (oldByte % 256) 1`. CU bound = 2.

Plumbing exercised:
- `cuTripleWithinMem_seq` chains a memory triple (`ldxb_spec`) with
  a non-memory triple (`add64_imm_spec` lifted via `cuTripleWithin.toMem`).
- `cuTripleWithin_frame_right` brings `r1` and the mem byte through
  the ALU step.
- `cuTripleWithinMem_weaken` collapses the composed `rr = (containsRange ∧ True)`
  back to `containsRange`. -/

open Memory in
theorem load_then_add_macro_spec (baseAddr vR2Old oldByte : Nat) :
    cuTripleWithinMem 2 0 0 2
      ((CodeReq.singleton 0 (.ldx .byte .r2 .r1 0)).union
       (CodeReq.singleton 1 (.add64 .r2 (.imm 1))))
      ((.r2 ↦ᵣ vR2Old) ** (.r1 ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr 0 ↦ₘ oldByte))
      ((.r2 ↦ᵣ wrapAdd (oldByte % 256) (toU64 1)) ** (.r1 ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr 0 ↦ₘ oldByte))
      (fun rt => rt.containsRange (effectiveAddr baseAddr 0) 1 = true) := by
  -- `sl_block_iter` composes a memory step (`ldxb`) with a pure step
  -- (`add64`) using `cuTripleWithinMem_seq_pure_right`, which keeps
  -- only the memory step's `rr` (no trivial `True` factor). No goal
  -- reshape needed — chain's `rr` matches the stated `containsRange`.
  have h1 := ldxb_spec .r2 .r1 0 vR2Old baseAddr oldByte 0 (by decide)
  have h2_alu := add64_imm_spec .r2 1 (oldByte % 256) 1 (by decide)
  sl_block_iter [h1, h2_alu]

/-! ## Memory-op macro: increment a byte in memory

Read-modify-write cycle — the full Phase D shape. Three instructions:

```
  pc=0: ldxb r2, r1, 0    -- r2 := byte at [r1]
  pc=1: add64 r2, 1       -- r2 := r2 + 1
  pc=2: stxb r1, 0, r2    -- byte at [r1] := r2 & 0xff
```

CU bound = 3. Post: byte at [r1] becomes `(oldByte + 1) & 0xff`
(after wrapAdd + writeU8 masking).

Plumbing exercised:
- Reuses `load_then_add_macro_spec` for the prefix.
- Combines `cuTripleWithinMem_weaken` with `sepConj_swap_first_two` to
  reshape `stxb_spec`'s pre/post from `r1 ** r2 ** mem` order to the
  prefix's `r2 ** r1 ** mem` order.
- `cuTripleWithinMem_seq` chains the prefix with the reshaped stxb,
  unioning region conditions (containsRange ∧ containsWritable). -/

open Memory in
theorem byte_increment_macro_spec (baseAddr vR2Old oldByte : Nat) :
    cuTripleWithinMem 3 0 0 3
      (((CodeReq.singleton 0 (.ldx .byte .r2 .r1 0)).union
        (CodeReq.singleton 1 (.add64 .r2 (.imm 1)))).union
       (CodeReq.singleton 2 (.stx .byte .r1 0 .r2)))
      ((.r2 ↦ᵣ vR2Old) ** (.r1 ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr 0 ↦ₘ oldByte))
      ((.r2 ↦ᵣ wrapAdd (oldByte % 256) (toU64 1)) ** (.r1 ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr 0 ↦ₘ (wrapAdd (oldByte % 256) (toU64 1) % 256)))
      (fun rt => rt.containsRange (effectiveAddr baseAddr 0) 1 = true ∧
                  rt.containsWritable (effectiveAddr baseAddr 0) 1 = true) := by
  -- Direct 3-step composition via `sl_block_iter` — no sub-macro
  -- factoring needed. `sl_swap_first` reshapes `stxb_spec`'s pre/post
  -- atom order from `(r1 ** r2 ** mem)` to `(r2 ** r1 ** mem)` so the
  -- frame extractor can align it against the running state. The chain
  -- composes via `_seq_pure_right` (step 1 mem + step 2 pure) then
  -- `_seq` (chain mem + step 3 mem), yielding the goal's
  -- `containsRange ∧ containsWritable` `rr` directly.
  have h1 := ldxb_spec .r2 .r1 0 vR2Old baseAddr oldByte 0 (by decide)
  have h2_alu := add64_imm_spec .r2 1 (oldByte % 256) 1 (by decide)
  have h3 := sl_swap_first (stxb_spec .r1 .r2 0 baseAddr
    (wrapAdd (oldByte % 256) (toU64 1)) oldByte 2)
  sl_block_iter [h1, h2_alu, h3]


/-! ## byte_increment via `sl_block_auto` — no manual `have` / `sl_swap_first`

Same theorem as `byte_increment_macro_spec` above, proved through
`sl_block_auto`. The tactic walks the CodeReq, builds `ldxb_spec`,
`add64_imm_spec`, and `stxb_spec` applications with mvars for the
value args, and lets `slBlockIter`'s permutation reshape handle
`stxb_spec`'s `(baseReg ** valReg ** mem)` atom order (which
differs from the chain's `(valReg ** baseReg ** mem)` after step 1).
The `dst ≠ .r10` side conds are auto-discharged; no `v < 2^N`
bounds for the byte width. -/
open Memory in
theorem byte_increment_macro_spec_auto (baseAddr vR2Old oldByte : Nat) :
    cuTripleWithinMem 3 0 0 3
      (((CodeReq.singleton 0 (.ldx .byte .r2 .r1 0)).union
        (CodeReq.singleton 1 (.add64 .r2 (.imm 1)))).union
       (CodeReq.singleton 2 (.stx .byte .r1 0 .r2)))
      ((.r2 ↦ᵣ vR2Old) ** (.r1 ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr 0 ↦ₘ oldByte))
      ((.r2 ↦ᵣ wrapAdd (oldByte % 256) (toU64 1)) ** (.r1 ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr 0 ↦ₘ (wrapAdd (oldByte % 256) (toU64 1) % 256)))
      (fun rt => rt.containsRange (effectiveAddr baseAddr 0) 1 = true ∧
                  rt.containsWritable (effectiveAddr baseAddr 0) 1 = true) := by
  sl_block_auto

/-! ## halfword store-immediate via `sl_block_auto` — the ST_H_IMM pin

Pins the SpecGen dispatch for `.st .half` (`sth_spec`): two adjacent
halfword immediate stores into separate `↦U16` cells, the second with
a negative immediate to exercise the `toU64` truncation in the post
(`toU64 imm % 2 ^ (2 * 8)`). Like the other store-imm wrappers there
are no residual side goals. -/
open Memory in
theorem halfword_store_imm_macro_spec_auto (baseAddr oldH0 oldH1 : Nat) :
    cuTripleWithinMem 2 0 0 2
      ((CodeReq.singleton 0 (.st .half .r1 0 0x1234)).union
       (CodeReq.singleton 1 (.st .half .r1 2 (-1))))
      ((.r1 ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr 0 ↦U16 oldH0) **
        (effectiveAddr baseAddr 2 ↦U16 oldH1))
      ((.r1 ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr 0 ↦U16 (toU64 0x1234 % 2 ^ (2 * 8))) **
        (effectiveAddr baseAddr 2 ↦U16 (toU64 (-1) % 2 ^ (2 * 8))))
      (fun rt => rt.containsWritable (effectiveAddr baseAddr 0) 2 = true ∧
                  rt.containsWritable (effectiveAddr baseAddr 2) 2 = true) := by
  sl_block_auto

/-! ## Error-exit collapse — the one-`apply` discharge

The error-path collapse lemmas (`InstructionSpecs/Terminating.lean`)
discharge a constant-exit landing in a single `exact`. Worked here on
both real idioms qedrecover tags as `constExitBlocks`: the in-block
form (`mov64 r0, c; exit`) and the shared-exit form
(`lddw r0, c; ja tgt` with a bare `exit` at `tgt` — pinocchio's
`ProgramError` encoding `c <<< 32` rides the lddw variant). -/

/-- Dispatch-mismatch landing, in-block form: aborts with code 5. -/
theorem error_exit_macro_spec (vR0Old : Nat) :
    cuTripleAbortsWithin 2 0 10
      ((CodeReq.singleton 10 (.mov64 .r0 (.imm 5))).union
        (CodeReq.singleton 11 .exit))
      ((.r0 ↦ᵣ vR0Old) ** callStackIs [])
      (toU64 5) :=
  errorExit_spec 5 vR0Old 10

/-- Shared-exit landing, pinocchio shape: `lddw r0, 19 <<< 32; ja 90`
    with the bare `exit` at 90. Aborts with `toU64 (19 <<< 32)`. -/
theorem error_exit_ja_macro_spec (vR0Old : Nat) :
    cuTripleAbortsWithin 3 0 10
      (((CodeReq.singleton 10 (.lddw .r0 (19 <<< 32))).union
        (CodeReq.singleton 11 (.ja 90))).union
        (CodeReq.singleton 90 .exit))
      ((.r0 ↦ᵣ vR0Old) ** callStackIs [])
      (toU64 (19 <<< 32)) :=
  errorExitJa_lddw_spec (19 <<< 32) vR0Old 10 90 (by omega) (by omega)

/-! ## lamport_transfer via `sl_block_auto` — bounds via residual goals

Same theorem as `lamport_transfer_macro_spec` above. `sl_block_auto`
generates 2 `ldxdw_spec` + 2 `stxdw_spec` + 2 ALU specs with mvars
for the value args. The `srcLam < 2 ^ 64` and `dstLam < 2 ^ 64`
bounds carried by `ldxdw_spec` are left as residual user goals once
the value mvars have been unified by `extractFrame`'s `isDefEq`.
The caller closes them via `assumption` against the theorem's
`hSrcLam` / `hDstLam` hypotheses. -/
open Memory in
theorem lamport_transfer_macro_spec_auto
    (srcPtr dstPtr amount vR4 vR5 srcLam dstLam : Nat)
    (hSrcLam : srcLam < 2 ^ 64) (hDstLam : dstLam < 2 ^ 64) :
    cuTripleWithinMem 6 0 0 6
      ((((((CodeReq.singleton 0 (.ldx .dword .r4 .r1 0)).union
            (CodeReq.singleton 1 (.sub64 .r4 (.reg .r3)))).union
            (CodeReq.singleton 2 (.stx .dword .r1 0 .r4))).union
            (CodeReq.singleton 3 (.ldx .dword .r5 .r2 0))).union
            (CodeReq.singleton 4 (.add64 .r5 (.reg .r3)))).union
            (CodeReq.singleton 5 (.stx .dword .r2 0 .r5)))
      ((.r1 ↦ᵣ srcPtr) ** (.r2 ↦ᵣ dstPtr) ** (.r3 ↦ᵣ amount) **
       (.r4 ↦ᵣ vR4) ** (.r5 ↦ᵣ vR5) **
       (effectiveAddr srcPtr 0 ↦U64 srcLam) **
       (effectiveAddr dstPtr 0 ↦U64 dstLam))
      ((.r1 ↦ᵣ srcPtr) ** (.r2 ↦ᵣ dstPtr) ** (.r3 ↦ᵣ amount) **
       (.r4 ↦ᵣ wrapSub srcLam amount) ** (.r5 ↦ᵣ wrapAdd dstLam amount) **
       (effectiveAddr srcPtr 0 ↦U64 wrapSub srcLam amount) **
       (effectiveAddr dstPtr 0 ↦U64 wrapAdd dstLam amount))
      (fun rt =>
        ((rt.containsRange (effectiveAddr srcPtr 0) 8 = true ∧
          rt.containsWritable (effectiveAddr srcPtr 0) 8 = true) ∧
         rt.containsRange (effectiveAddr dstPtr 0) 8 = true) ∧
        rt.containsWritable (effectiveAddr dstPtr 0) 8 = true) := by
  sl_block_auto <;> assumption

/-! ## Bridge demo — downgrading an SL macro to a concrete `executeFn` fact

Applies `cuTripleWithinMem.toExec` to `byte_increment_macro_spec`. The
resulting fact is the SL macro's content expressed entirely in terms of
`executeFn`: given a `fetch` that matches the three macro instructions,
a state satisfying the read-modify-write precondition, and the region
requirement, there is a `k ≤ 3` such that `executeFn fetch s k` lands at
pc = 3 with the post-state holding.

This is the form `wp_exec`-style proofs of larger programs can consume:
plug the macro into a longer execution as a single k-step jump rather
than re-deriving every per-instruction step. -/

open Memory in
theorem byte_increment_macro_executeFn
    (baseAddr vR2Old oldByte : Nat)
    {fetch : Nat → Option Insn}
    (hcr : (((CodeReq.singleton 0 (.ldx .byte .r2 .r1 0)).union
            (CodeReq.singleton 1 (.add64 .r2 (.imm 1)))).union
           (CodeReq.singleton 2 (.stx .byte .r1 0 .r2))).SatisfiedBy fetch)
    {s : State}
    (hP : ((.r2 ↦ᵣ vR2Old) ** (.r1 ↦ᵣ baseAddr) **
            (effectiveAddr baseAddr 0 ↦ₘ oldByte)).holdsFor s)
    (hpc : s.pc = 0) (hex : s.exitCode = none)
    (hbud : s.cuConsumed + 3 + 0 ≤ s.cuBudget)
    (h_reg : s.regions.containsRange (effectiveAddr baseAddr 0) 1 = true ∧
             s.regions.containsWritable (effectiveAddr baseAddr 0) 1 = true) :
    ∃ k, k ≤ 3 ∧
      (executeFn fetch s k).pc = 3 ∧
      (executeFn fetch s k).exitCode = none ∧
      ((.r2 ↦ᵣ wrapAdd (oldByte % 256) (toU64 1)) ** (.r1 ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr 0 ↦ₘ (wrapAdd (oldByte % 256) (toU64 1) % 256))).holdsFor
        (executeFn fetch s k) := by
  obtain ⟨k, hk, hpc', hex', _, hQ⟩ :=
    (byte_increment_macro_spec baseAddr vR2Old oldByte).toExec hcr hP hpc hex hbud h_reg
  exact ⟨k, hk, hpc', hex', hQ⟩

/-! ## Lamport transfer — first real Solana primitive (Phase D)

A six-instruction macro that decrements one u64 lamport balance and
increments another by the same amount. This is the operation Solana's
runtime performs inside `system_program::transfer` and is the SL track's
first "verified Solana macro" — a meaningful primitive proven from
per-instruction sBPF semantics.

```
  pc=0: ldxdw r4, r1, 0    -- r4 := *src    (load source lamports)
  pc=1: sub64 r4, r3        -- r4 := r4 - amount
  pc=2: stxdw r1, 0, r4    -- *src := r4   (write back decremented source)
  pc=3: ldxdw r5, r2, 0    -- r5 := *dst    (load dest lamports)
  pc=4: add64 r5, r3        -- r5 := r5 + amount
  pc=5: stxdw r2, 0, r5    -- *dst := r5   (write back incremented dest)
```

Calling convention: r1 = src ptr, r2 = dst ptr, r3 = amount. r4/r5 are
scratch. CU bound = 6.

The interesting plumbing this exercises:
- 7-atom state (5 regs + 2 U64 mem cells), more than any prior macro.
- Multi-atom info.pre framing — `ldxdw` / `stxdw` specs own 3 atoms each,
  so framed steps have non-right-folded `(P ** F)` shape; `sl_block_iter`
  right-normalizes after each frame application to keep the chain in
  canonical right-folded form.
- Atom interleaving — step 1 (`sub64 r4 r3`) and step 4 (`add64 r5 r3`)
  consume non-adjacent registers, so the frame-extractor falls back to
  permutation via `sepConj_swap_first_two` / `sepConj_assoc` chains.
  Steps 2/3/5 also need permutation (different shapes from chain post).
- 4 memory steps' region requirements left-fold into the final
  `((cR_src ∧ cW_src) ∧ cR_dst) ∧ cW_dst` shape via `cuTripleWithinMem_seq`. -/

open Memory in
theorem lamport_transfer_macro_spec
    (srcPtr dstPtr amount vR4 vR5 srcLam dstLam : Nat)
    (hSrcLam : srcLam < 2 ^ 64) (hDstLam : dstLam < 2 ^ 64) :
    cuTripleWithinMem 6 0 0 6
      ((((((CodeReq.singleton 0 (.ldx .dword .r4 .r1 0)).union
            (CodeReq.singleton 1 (.sub64 .r4 (.reg .r3)))).union
            (CodeReq.singleton 2 (.stx .dword .r1 0 .r4))).union
            (CodeReq.singleton 3 (.ldx .dword .r5 .r2 0))).union
            (CodeReq.singleton 4 (.add64 .r5 (.reg .r3)))).union
            (CodeReq.singleton 5 (.stx .dword .r2 0 .r5)))
      ((.r1 ↦ᵣ srcPtr) ** (.r2 ↦ᵣ dstPtr) ** (.r3 ↦ᵣ amount) **
       (.r4 ↦ᵣ vR4) ** (.r5 ↦ᵣ vR5) **
       (effectiveAddr srcPtr 0 ↦U64 srcLam) **
       (effectiveAddr dstPtr 0 ↦U64 dstLam))
      ((.r1 ↦ᵣ srcPtr) ** (.r2 ↦ᵣ dstPtr) ** (.r3 ↦ᵣ amount) **
       (.r4 ↦ᵣ wrapSub srcLam amount) ** (.r5 ↦ᵣ wrapAdd dstLam amount) **
       (effectiveAddr srcPtr 0 ↦U64 wrapSub srcLam amount) **
       (effectiveAddr dstPtr 0 ↦U64 wrapAdd dstLam amount))
      (fun rt =>
        ((rt.containsRange (effectiveAddr srcPtr 0) 8 = true ∧
          rt.containsWritable (effectiveAddr srcPtr 0) 8 = true) ∧
         rt.containsRange (effectiveAddr dstPtr 0) 8 = true) ∧
        rt.containsWritable (effectiveAddr dstPtr 0) 8 = true) := by
  have h0 := ldxdw_spec .r4 .r1 0 vR4 srcPtr srcLam 0 (by decide) hSrcLam
  have h1 := sub64_reg_spec .r4 .r3 srcLam amount 1 (by decide)
  have h2 := stxdw_spec .r1 .r4 0 srcPtr (wrapSub srcLam amount) srcLam 2
  have h3 := ldxdw_spec .r5 .r2 0 vR5 dstPtr dstLam 3 (by decide) hDstLam
  have h4 := add64_reg_spec .r5 .r3 dstLam amount 4 (by decide)
  have h5 := stxdw_spec .r2 .r5 0 dstPtr (wrapAdd dstLam amount) dstLam 5
  sl_block_iter [h0, h1, h2, h3, h4, h5]

/-! ## Lamport transfer — executeFn bridge -/

open Memory in
theorem lamport_transfer_macro_executeFn
    (srcPtr dstPtr amount vR4 vR5 srcLam dstLam : Nat)
    (hSrcLam : srcLam < 2 ^ 64) (hDstLam : dstLam < 2 ^ 64)
    {fetch : Nat → Option Insn}
    (hcr : ((((((CodeReq.singleton 0 (.ldx .dword .r4 .r1 0)).union
                (CodeReq.singleton 1 (.sub64 .r4 (.reg .r3)))).union
                (CodeReq.singleton 2 (.stx .dword .r1 0 .r4))).union
                (CodeReq.singleton 3 (.ldx .dword .r5 .r2 0))).union
                (CodeReq.singleton 4 (.add64 .r5 (.reg .r3)))).union
                (CodeReq.singleton 5 (.stx .dword .r2 0 .r5))).SatisfiedBy fetch)
    {s : State}
    (hP : ((.r1 ↦ᵣ srcPtr) ** (.r2 ↦ᵣ dstPtr) ** (.r3 ↦ᵣ amount) **
            (.r4 ↦ᵣ vR4) ** (.r5 ↦ᵣ vR5) **
            (effectiveAddr srcPtr 0 ↦U64 srcLam) **
            (effectiveAddr dstPtr 0 ↦U64 dstLam)).holdsFor s)
    (hpc : s.pc = 0) (hex : s.exitCode = none)
    (hbud : s.cuConsumed + 6 + 0 ≤ s.cuBudget)
    (h_reg :
      ((s.regions.containsRange (effectiveAddr srcPtr 0) 8 = true ∧
        s.regions.containsWritable (effectiveAddr srcPtr 0) 8 = true) ∧
       s.regions.containsRange (effectiveAddr dstPtr 0) 8 = true) ∧
      s.regions.containsWritable (effectiveAddr dstPtr 0) 8 = true) :
    ∃ k, k ≤ 6 ∧
      (executeFn fetch s k).pc = 6 ∧
      (executeFn fetch s k).exitCode = none ∧
      ((.r1 ↦ᵣ srcPtr) ** (.r2 ↦ᵣ dstPtr) ** (.r3 ↦ᵣ amount) **
        (.r4 ↦ᵣ wrapSub srcLam amount) ** (.r5 ↦ᵣ wrapAdd dstLam amount) **
        (effectiveAddr srcPtr 0 ↦U64 wrapSub srcLam amount) **
        (effectiveAddr dstPtr 0 ↦U64 wrapAdd dstLam amount)).holdsFor
        (executeFn fetch s k) := by
  obtain ⟨k, hk, hpc', hex', _, hQ⟩ :=
    (lamport_transfer_macro_spec srcPtr dstPtr amount vR4 vR5 srcLam dstLam
        hSrcLam hDstLam).toExec hcr hP hpc hex hbud h_reg
  exact ⟨k, hk, hpc', hex', hQ⟩

/-! ## 16-byte memcpy via 2x u64 dword (Phase D)

Copies 16 bytes from `src` to `dst` as two u64 dword moves. Reuses
`r3` as the load scratch across both halves — the value held in `r3`
between steps 1 and 2 is the *first* loaded dword (`v0`), and ldxdw
step 2 overwrites it with `v1`. Threading the value through the
reused register exercises the spec's `vOldDst` parameter at each
load.

```
  pc=0: ldxdw r3, r1, 0    -- r3 := *(u64)(src + 0)
  pc=1: stxdw r2, 0, r3    -- *(u64)(dst + 0) := r3
  pc=2: ldxdw r3, r1, 8    -- r3 := *(u64)(src + 8)   (overwrites r3=v0)
  pc=3: stxdw r2, 8, r3    -- *(u64)(dst + 8) := r3
```

7-atom state (r1, r2, r3, srcMem@0, srcMem@8, dstMem@0, dstMem@8).
CU bound = 4. 4 consecutive memory steps land 4 `rr` factors left-
folded into `((cR_s0 ∧ cW_d0) ∧ cR_s8) ∧ cW_d8`. -/

open Memory in
theorem u64_memcpy_16_macro_spec
    (srcPtr dstPtr vR3 v0 v1 d0 d1 : Nat)
    (hv0 : v0 < 2 ^ 64) (hv1 : v1 < 2 ^ 64) :
    cuTripleWithinMem 4 0 0 4
      ((((CodeReq.singleton 0 (.ldx .dword .r3 .r1 0)).union
          (CodeReq.singleton 1 (.stx .dword .r2 0 .r3))).union
          (CodeReq.singleton 2 (.ldx .dword .r3 .r1 8))).union
          (CodeReq.singleton 3 (.stx .dword .r2 8 .r3)))
      ((.r1 ↦ᵣ srcPtr) ** (.r2 ↦ᵣ dstPtr) ** (.r3 ↦ᵣ vR3) **
       (effectiveAddr srcPtr 0 ↦U64 v0) **
       (effectiveAddr srcPtr 8 ↦U64 v1) **
       (effectiveAddr dstPtr 0 ↦U64 d0) **
       (effectiveAddr dstPtr 8 ↦U64 d1))
      ((.r1 ↦ᵣ srcPtr) ** (.r2 ↦ᵣ dstPtr) ** (.r3 ↦ᵣ v1) **
       (effectiveAddr srcPtr 0 ↦U64 v0) **
       (effectiveAddr srcPtr 8 ↦U64 v1) **
       (effectiveAddr dstPtr 0 ↦U64 v0) **
       (effectiveAddr dstPtr 8 ↦U64 v1))
      (fun rt =>
        ((rt.containsRange (effectiveAddr srcPtr 0) 8 = true ∧
          rt.containsWritable (effectiveAddr dstPtr 0) 8 = true) ∧
         rt.containsRange (effectiveAddr srcPtr 8) 8 = true) ∧
        rt.containsWritable (effectiveAddr dstPtr 8) 8 = true) := by
  have h0 := ldxdw_spec .r3 .r1 0 vR3 srcPtr v0 0 (by decide) hv0
  have h1 := stxdw_spec .r2 .r3 0 dstPtr v0 d0 1
  have h2 := ldxdw_spec .r3 .r1 8 v0  srcPtr v1 2 (by decide) hv1
  have h3 := stxdw_spec .r2 .r3 8 dstPtr v1 d1 3
  sl_block_iter [h0, h1, h2, h3]

/-! ## u64_memcpy_16 via `sl_block_auto` -/

open Memory in
theorem u64_memcpy_16_macro_spec_auto
    (srcPtr dstPtr vR3 v0 v1 d0 d1 : Nat)
    (hv0 : v0 < 2 ^ 64) (hv1 : v1 < 2 ^ 64) :
    cuTripleWithinMem 4 0 0 4
      ((((CodeReq.singleton 0 (.ldx .dword .r3 .r1 0)).union
          (CodeReq.singleton 1 (.stx .dword .r2 0 .r3))).union
          (CodeReq.singleton 2 (.ldx .dword .r3 .r1 8))).union
          (CodeReq.singleton 3 (.stx .dword .r2 8 .r3)))
      ((.r1 ↦ᵣ srcPtr) ** (.r2 ↦ᵣ dstPtr) ** (.r3 ↦ᵣ vR3) **
       (effectiveAddr srcPtr 0 ↦U64 v0) **
       (effectiveAddr srcPtr 8 ↦U64 v1) **
       (effectiveAddr dstPtr 0 ↦U64 d0) **
       (effectiveAddr dstPtr 8 ↦U64 d1))
      ((.r1 ↦ᵣ srcPtr) ** (.r2 ↦ᵣ dstPtr) ** (.r3 ↦ᵣ v1) **
       (effectiveAddr srcPtr 0 ↦U64 v0) **
       (effectiveAddr srcPtr 8 ↦U64 v1) **
       (effectiveAddr dstPtr 0 ↦U64 v0) **
       (effectiveAddr dstPtr 8 ↦U64 v1))
      (fun rt =>
        ((rt.containsRange (effectiveAddr srcPtr 0) 8 = true ∧
          rt.containsWritable (effectiveAddr dstPtr 0) 8 = true) ∧
         rt.containsRange (effectiveAddr srcPtr 8) 8 = true) ∧
        rt.containsWritable (effectiveAddr dstPtr 8) 8 = true) := by
  sl_block_auto <;> assumption

/-! ## 16-byte memcpy — executeFn bridge -/

open Memory in
theorem u64_memcpy_16_macro_executeFn
    (srcPtr dstPtr vR3 v0 v1 d0 d1 : Nat)
    (hv0 : v0 < 2 ^ 64) (hv1 : v1 < 2 ^ 64)
    {fetch : Nat → Option Insn}
    (hcr : ((((CodeReq.singleton 0 (.ldx .dword .r3 .r1 0)).union
              (CodeReq.singleton 1 (.stx .dword .r2 0 .r3))).union
              (CodeReq.singleton 2 (.ldx .dword .r3 .r1 8))).union
              (CodeReq.singleton 3 (.stx .dword .r2 8 .r3))).SatisfiedBy fetch)
    {s : State}
    (hP : ((.r1 ↦ᵣ srcPtr) ** (.r2 ↦ᵣ dstPtr) ** (.r3 ↦ᵣ vR3) **
            (effectiveAddr srcPtr 0 ↦U64 v0) **
            (effectiveAddr srcPtr 8 ↦U64 v1) **
            (effectiveAddr dstPtr 0 ↦U64 d0) **
            (effectiveAddr dstPtr 8 ↦U64 d1)).holdsFor s)
    (hpc : s.pc = 0) (hex : s.exitCode = none)
    (hbud : s.cuConsumed + 4 + 0 ≤ s.cuBudget)
    (h_reg :
      ((s.regions.containsRange (effectiveAddr srcPtr 0) 8 = true ∧
        s.regions.containsWritable (effectiveAddr dstPtr 0) 8 = true) ∧
       s.regions.containsRange (effectiveAddr srcPtr 8) 8 = true) ∧
      s.regions.containsWritable (effectiveAddr dstPtr 8) 8 = true) :
    ∃ k, k ≤ 4 ∧
      (executeFn fetch s k).pc = 4 ∧
      (executeFn fetch s k).exitCode = none ∧
      ((.r1 ↦ᵣ srcPtr) ** (.r2 ↦ᵣ dstPtr) ** (.r3 ↦ᵣ v1) **
        (effectiveAddr srcPtr 0 ↦U64 v0) **
        (effectiveAddr srcPtr 8 ↦U64 v1) **
        (effectiveAddr dstPtr 0 ↦U64 v0) **
        (effectiveAddr dstPtr 8 ↦U64 v1)).holdsFor
        (executeFn fetch s k) := by
  obtain ⟨k, hk, hpc', hex', _, hQ⟩ :=
    (u64_memcpy_16_macro_spec srcPtr dstPtr vR3 v0 v1 d0 d1 hv0 hv1).toExec
      hcr hP hpc hex hbud h_reg
  exact ⟨k, hk, hpc', hex', hQ⟩

/-! ## If-else macro (Phase E foundation)

First branching-track demo. The layout:

```
pc=0: jeq r1, 0, .true_block     ; target = 3
pc=1: mov64 r2, 100               ; false branch starts here
pc=2: ja .end                     ; target = 4
pc=3: mov64 r2, 200               ; .true_block (true branch)
pc=4: <join PC>
```

True branch (`vR1 = toU64 0`): 0 → 3 → 4 (2 steps). Sets r2 = 200.
False branch (`vR1 ≠ toU64 0`): 0 → 1 → 2 → 4 (3 steps). Sets r2 = 100.

Bound: 1 (jeq) + max 1 2 = 3 CU. The triple's post conditions r2's
value on the branch outcome: `if vR1 = toU64 0 then toU64 200 else
toU64 100`.

Plumbing exercised:
- `cuTripleWithin.toBranch` to convert the existing `jeq_imm_spec`
  into the branch family.
- `cuTripleWithinBranch_frame_right` to bring `(.r2 ↦ᵣ vR2)` through
  the branch step.
- `cuTripleWithin_seq` to chain the false-branch's `mov64 + ja`.
- `cuTripleWithinBranch_join` to merge at pc=4. -/

theorem if_else_macro_spec (vR1 vR2 : Nat) :
    cuTripleWithin 3 0 0 4
      (((CodeReq.singleton 0 (.jeq .r1 (.imm 0) 3)).union
         (CodeReq.singleton 3 (.mov64 .r2 (.imm 200)))).union
         ((CodeReq.singleton 1 (.mov64 .r2 (.imm 100))).union
          (CodeReq.singleton 2 (.ja 4))))
      ((.r1 ↦ᵣ vR1) ** (.r2 ↦ᵣ vR2))
      ((.r1 ↦ᵣ vR1) **
        (.r2 ↦ᵣ (if vR1 = toU64 0 then toU64 200 else toU64 100))) := by
  -- Branch spec, pre-framed to widen its 1-atom state to (r1 ** r2).
  have h_br := cuTripleWithinBranch_frame_right (.r2 ↦ᵣ vR2) (pcFree_regIs _ _)
                 (jeq_imm_branch_spec .r1 0 vR1 0 3)
  -- True branch: a single `mov64 r2, 200` (r1 auto-framed).
  have h_T_r2 := mov64_imm_spec .r2 200 vR2 3 (by decide)
  -- False branch: `mov64 r2, 100` then `ja 4`. ja_spec's emp/emp gets
  -- auto-widened to the current chain state by `sl_branch`.
  have h_F_mov_r2 := mov64_imm_spec .r2 100 vR2 1 (by decide)
  sl_branch h_br [h_T_r2] [h_F_mov_r2, ja_spec 4 2]

/-! ## SPL-Token-shaped 2-way discriminant dispatch (Phase E session 2)

First real branching macro that combines memory + branch + join. The
macro models the SPL Token entrypoint pattern:

```
pc=0: ldxb r2, r1, 0       ; r2 = instruction_data[0] (discriminant byte)
pc=1: jeq r2, 0, 4         ; if discriminant == 0 jump to .case_0
pc=2: mov64 r0, 100         ; default: r0 = 100  (e.g. InvalidInstruction)
pc=3: ja 5                  ; → .end
pc=4: mov64 r0, 200         ; .case_0: r0 = 200  (e.g. Success path)
pc=5: <join>
```

Calling convention: r1 = pointer to instruction_data, r0 = scratch.
The discriminant is read once, then dispatch routes to one of two
handlers; both handlers terminate at the join PC.

Bound:
- ldxb: 1 CU
- branch_join: 1 (jeq) + max 1 2 = 3 CU
- Total: 4 CU.

State: 4 atoms — `(.r0 ↦ᵣ vR0) ** (.r1 ↦ᵣ baseAddr) ** (.r2 ↦ᵣ vR2) **
(mem ↦ₘ discByte)`. r0 is mutated by the handlers; r2 holds the
discriminant after the load; r1 and the memory cell carry through.

Plumbing exercised:
- `ldxb_spec` provides the memory triple for the discriminant load.
- `cuTripleWithinBranch_frame_*` carries r0 + r1 + memory through the
  branch step.
- `cuTripleWithin_seq` chains `mov + ja` in the false branch.
- `cuTripleWithinBranch_join` merges at pc=5.
- `cuTripleWithinMem_seq_pure_right` composes the (mem) ldxb with the
  (pure) dispatch chain to produce a single memory triple.
- Reshape weakens align the atom orderings between ldxb's post
  (`r2 ** r1 ** mem ** r0`) and the dispatch's pre (`r2 ** r0 ** r1
  ** mem`). -/

open Memory in
theorem spl_token_2way_dispatch_macro_spec
    (baseAddr vR0 vR2 discByte : Nat) :
    cuTripleWithinMem 4 0 0 5
      ((CodeReq.singleton 0 (.ldx .byte .r2 .r1 0)).union
        (((CodeReq.singleton 1 (.jeq .r2 (.imm 0) 4)).union
          (CodeReq.singleton 4 (.mov64 .r0 (.imm 200)))).union
          ((CodeReq.singleton 2 (.mov64 .r0 (.imm 100))).union
           (CodeReq.singleton 3 (.ja 5)))))
      ((.r0 ↦ᵣ vR0) ** (.r2 ↦ᵣ vR2) **
        (.r1 ↦ᵣ baseAddr) ** (effectiveAddr baseAddr 0 ↦ₘ discByte))
      ((.r0 ↦ᵣ (if discByte % 256 = toU64 0 then toU64 200 else toU64 100)) **
        (.r2 ↦ᵣ discByte % 256) **
        (.r1 ↦ᵣ baseAddr) ** (effectiveAddr baseAddr 0 ↦ₘ discByte))
      (fun rt => rt.containsRange (effectiveAddr baseAddr 0) 1 = true) := by
  -- Canonical atom order throughout: `r0 ** r2 ** r1 ** mem`. ldxb is
  -- framed with `r0` on the LEFT so its natural `r2 ** r1 ** mem`
  -- post takes that prefix; the dispatch's `r0 ** r2` pre is matched
  -- by sepConj associativity.

  -- Stage 1: dispatch chain (pc=1 → pc=5), 2-atom state `(r0 ** r2)`.
  -- Pre-frame the bare branch spec to widen to the 2-atom state.
  have h_br := cuTripleWithinBranch_frame_left (.r0 ↦ᵣ vR0) (pcFree_regIs _ _)
                 (jeq_imm_branch_spec .r2 0 (discByte % 256) 1 4)
  have h_T_r0 := mov64_imm_spec .r0 200 vR0 4 (by decide)
  have h_F_mov_r0 := mov64_imm_spec .r0 100 vR0 2 (by decide)
  -- ja_spec's emp/emp auto-widened by sl_branch's chain builder.
  have h_dispatch_2atom : cuTripleWithin 3 0 1 5
        (((CodeReq.singleton 1 (.jeq .r2 (.imm 0) 4)).union
          (CodeReq.singleton 4 (.mov64 .r0 (.imm 200)))).union
         ((CodeReq.singleton 2 (.mov64 .r0 (.imm 100))).union
          (CodeReq.singleton 3 (.ja 5))))
        ((.r0 ↦ᵣ vR0) ** (.r2 ↦ᵣ discByte % 256))
        ((.r0 ↦ᵣ (if discByte % 256 = toU64 0 then toU64 200 else toU64 100)) **
          (.r2 ↦ᵣ discByte % 256)) := by
    sl_branch h_br [h_T_r0] [h_F_mov_r0, ja_spec 5 3]
  -- Stage 2: frame with `(.r1 ↦ᵣ baseAddr) ** (mem ↦ₘ discByte)` on
  -- the RIGHT, then re-associate via `sepConj_assoc` so the 4-atom
  -- shape is right-folded `r0 ** r2 ** r1 ** mem`.
  have h_dispatch_4atom_raw := cuTripleWithin_frame_right
    ((.r1 ↦ᵣ baseAddr) ** (effectiveAddr baseAddr 0 ↦ₘ discByte))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_memByteIs _ _))
    h_dispatch_2atom
  have h_dispatch_4atom_post :=
    cuTripleWithin_reshape_post sepConj_assoc h_dispatch_4atom_raw
  have h_dispatch_4atom :=
    cuTripleWithin_reshape_pre sepConj_assoc h_dispatch_4atom_post
  -- Stage 3: ldxb framed with r0 on the LEFT.
  have h_ldxb := ldxb_spec .r2 .r1 0 vR2 baseAddr discByte 0 (by decide)
  have h_ldxb_4atom : cuTripleWithinMem 1 0 0 1
      (CodeReq.singleton 0 (.ldx .byte .r2 .r1 0))
      ((.r0 ↦ᵣ vR0) ** (.r2 ↦ᵣ vR2) ** (.r1 ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr 0 ↦ₘ discByte))
      ((.r0 ↦ᵣ vR0) ** (.r2 ↦ᵣ discByte % 256) ** (.r1 ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr 0 ↦ₘ discByte))
      (fun rt => rt.containsRange (effectiveAddr baseAddr 0) 1 = true) :=
    cuTripleWithinMem_frame_left (.r0 ↦ᵣ vR0) (pcFree_regIs _ _) h_ldxb
  -- Stage 4: compose ldxb (memory) with dispatch (pure) via the
  -- mem+pure seq rule. The intermediate Q is ldxb's post = dispatch's
  -- pre (both `r0 ** r2 ** r1 ** mem` with `r2 = discByte % 256`).
  exact cuTripleWithinMem_seq_pure_right
    (CodeReq.Disjoint_union_right
      (CodeReq.Disjoint_union_right
        (CodeReq.singleton_disjoint_singleton _ _ (by decide))
        (CodeReq.singleton_disjoint_singleton _ _ (by decide)))
      (CodeReq.Disjoint_union_right
        (CodeReq.singleton_disjoint_singleton _ _ (by decide))
        (CodeReq.singleton_disjoint_singleton _ _ (by decide))))
    h_ldxb_4atom h_dispatch_4atom

/-! ## PDA derivation macros — retired under H6

The six PDA derivation macros (`pda_n0_macro_spec` / `_executeFn`,
`pda_n1_macro_spec` / `_executeFn`, `pda_n1_stack_macro_spec` /
`_executeFn`) composed `call_create_program_address_n{0,1}_spec` (now
retired, see `InstructionSpecs/Syscalls/Pda.lean`) to prove the 4-step PDA
derivation writes the derived address at `*r4`. Under H6 `Pda.execCreate`
region-checks its program_id / seed / output slices, so that success path is
region-conditional and the unconditional triples no longer hold as stated.
The macros were unconsumed (nothing composed them downstream), so they are
retired alongside their underlying specs; the honest H6 behaviour is the
`Pda.execCreate_faults_oob` fault-direction lemma. -/

/-! ## SpecGen extension smoke tests

Confirm `sl_block_auto` dispatches the new Insn families (32-bit ALU,
`neg64`/`neg32`, `lddw`, div/mod) added in this session. Each `example`
is a tiny linear sequence; if any dispatch arm is mis-wired,
`sl_block_auto` throws at elaboration time and the build breaks. -/

example (vOld1 vOld2 : Nat) :
    cuTripleWithin 2 0 0 2
      ((CodeReq.singleton 0 (.lddw .r1 42)).union
       (CodeReq.singleton 1 (.add32 .r2 (.imm 5))))
      ((.r1 ↦ᵣ vOld1) ** (.r2 ↦ᵣ vOld2))
      ((.r1 ↦ᵣ toU64 42) ** (.r2 ↦ᵣ wrapAdd32 vOld2 (toU64 5))) := by
  sl_block_auto

example (vOld : Nat) :
    cuTripleWithin 2 0 0 2
      ((CodeReq.singleton 0 (.neg64 .r1)).union
       (CodeReq.singleton 1 (.neg32 .r1)))
      (.r1 ↦ᵣ vOld)
      (.r1 ↦ᵣ wrapNeg32 (wrapNeg vOld)) := by
  sl_block_auto

example (vOld : Nat) :
    cuTripleWithin 2 0 0 2
      ((CodeReq.singleton 0 (.mov32 .r1 (.imm 100))).union
       (CodeReq.singleton 1 (.mul32 .r1 (.imm 3))))
      (.r1 ↦ᵣ vOld)
      (.r1 ↦ᵣ wrapMul32 (toU64 100 % U32_MODULUS) (toU64 3)) := by
  sl_block_auto

