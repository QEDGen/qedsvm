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
import Svm.SBPF.SLTactic
import Svm.SBPF.SpecGen

namespace Svm.SBPF

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
    cuTripleWithin 2 0 2
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
    cuTripleWithin 2 0 2
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
    cuTripleWithin 2 0 2
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
    cuTripleWithinMem 2 0 2
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
    cuTripleWithinMem 3 0 3
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
    cuTripleWithinMem 3 0 3
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
    cuTripleWithinMem 6 0 6
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
    (h_reg : s.regions.containsRange (effectiveAddr baseAddr 0) 1 = true ∧
             s.regions.containsWritable (effectiveAddr baseAddr 0) 1 = true) :
    ∃ k, k ≤ 3 ∧
      (executeFn fetch s k).pc = 3 ∧
      (executeFn fetch s k).exitCode = none ∧
      ((.r2 ↦ᵣ wrapAdd (oldByte % 256) (toU64 1)) ** (.r1 ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr 0 ↦ₘ (wrapAdd (oldByte % 256) (toU64 1) % 256))).holdsFor
        (executeFn fetch s k) :=
  (byte_increment_macro_spec baseAddr vR2Old oldByte).toExec hcr hP hpc hex h_reg

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
    cuTripleWithinMem 6 0 6
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
        (executeFn fetch s k) :=
  (lamport_transfer_macro_spec srcPtr dstPtr amount vR4 vR5 srcLam dstLam
      hSrcLam hDstLam).toExec hcr hP hpc hex h_reg

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
    cuTripleWithinMem 4 0 4
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
    cuTripleWithinMem 4 0 4
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
        (executeFn fetch s k) :=
  (u64_memcpy_16_macro_spec srcPtr dstPtr vR3 v0 v1 d0 d1 hv0 hv1).toExec
    hcr hP hpc hex h_reg

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
    cuTripleWithin 3 0 4
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
  -- True branch: a single `mov64 r2, 200` (framed by sl_block_iter).
  have h_T_r2 := mov64_imm_spec .r2 200 vR2 3 (by decide)
  -- False branch: `mov64 r2, 100` then `ja 4`. ja_spec has emp pre/post
  -- which sl_block_iter's atom-extractor can't widen automatically, so
  -- pre-frame it to the post-state of the preceding mov.
  have h_F_mov_r2 := mov64_imm_spec .r2 100 vR2 1 (by decide)
  have h_F_ja : cuTripleWithin 1 2 4 (CodeReq.singleton 2 (.ja 4))
        ((.r1 ↦ᵣ vR1) ** (.r2 ↦ᵣ toU64 100))
        ((.r1 ↦ᵣ vR1) ** (.r2 ↦ᵣ toU64 100)) := by
    have := cuTripleWithin_frame_right ((.r1 ↦ᵣ vR1) ** (.r2 ↦ᵣ toU64 100))
              (pcFree_sepConj (pcFree_regIs _ _) (pcFree_regIs _ _)) (ja_spec 4 2)
    apply cuTripleWithin_weaken
      (fun hp hPP => (sepConj_emp_left hp).mpr hPP)
      (fun hp hQQ => (sepConj_emp_left hp).mp hQQ) this
  sl_branch h_br [h_T_r2] [h_F_mov_r2, h_F_ja]

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
    cuTripleWithinMem 4 0 5
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
  -- True branch step: `mov64 r0, 200` (sl_block_iter auto-frames r2).
  have h_T_r0 := mov64_imm_spec .r0 200 vR0 4 (by decide)
  -- False branch steps: `mov64 r0, 100` (auto-framed) + `ja 5`
  -- (manually framed since ja_spec's emp pre/post can't be widened
  -- by sl_block_iter's atom-extractor).
  have h_F_mov_r0 := mov64_imm_spec .r0 100 vR0 2 (by decide)
  have h_F_ja : cuTripleWithin 1 3 5 (CodeReq.singleton 3 (.ja 5))
        ((.r0 ↦ᵣ toU64 100) ** (.r2 ↦ᵣ discByte % 256))
        ((.r0 ↦ᵣ toU64 100) ** (.r2 ↦ᵣ discByte % 256)) := by
    have := cuTripleWithin_frame_right
              ((.r0 ↦ᵣ toU64 100) ** (.r2 ↦ᵣ discByte % 256))
              (pcFree_sepConj (pcFree_regIs _ _) (pcFree_regIs _ _)) (ja_spec 5 3)
    apply cuTripleWithin_weaken
      (fun hp hPP => (sepConj_emp_left hp).mpr hPP)
      (fun hp hQQ => (sepConj_emp_left hp).mp hQQ) this
  have h_dispatch_2atom : cuTripleWithin 3 1 5
        (((CodeReq.singleton 1 (.jeq .r2 (.imm 0) 4)).union
          (CodeReq.singleton 4 (.mov64 .r0 (.imm 200)))).union
         ((CodeReq.singleton 2 (.mov64 .r0 (.imm 100))).union
          (CodeReq.singleton 3 (.ja 5))))
        ((.r0 ↦ᵣ vR0) ** (.r2 ↦ᵣ discByte % 256))
        ((.r0 ↦ᵣ (if discByte % 256 = toU64 0 then toU64 200 else toU64 100)) **
          (.r2 ↦ᵣ discByte % 256)) := by
    sl_branch h_br [h_T_r0] [h_F_mov_r0, h_F_ja]
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
  have h_ldxb_4atom : cuTripleWithinMem 1 0 1
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

/-! ## PDA derivation macro (n=0) — Session 1 deliverable

A 4-instruction macro that prepares the syscall calling convention
and invokes `sol_create_program_address` with zero seeds. Models the
simplest meaningful use of PDA derivation: hash the program-id alone
with the PDA marker.

```
pc=0: mov64 r2, 0                   ; n_seeds = 0
pc=1: lddw r3, program_id_addr      ; r3 = pointer to 32-byte pid
pc=2: lddw r4, output_addr          ; r4 = pointer to 32-byte output
pc=3: call sol_create_program_address
```

The first three instructions set up the calling convention; the
fourth invokes the syscall. The post threads the success/failure
through both r0 (status code) and the output buffer's contents.

Composition exercises:
- `mov64_imm_spec` + `lddw_spec` × 2 chained via the SL framework's
  frame rule (each step owns only its destination register; the
  surrounding 5 atoms are framed automatically).
- `call_create_program_address_n0_spec` plugged in as the final
  step, with `r3V = toU64 r3V_imm` and `r4V = toU64 r4V_imm` from
  the preceding `lddw`s' posts.

`sl_block_iter` handles the framing + atom reshape; the explicit
proof body is just the four per-step specs. -/

theorem pda_n0_macro_spec
    (vR0 vR2 vR3 vR4 : Nat) (r3V_imm r4V_imm : Int)
    (pidBytes outOldBytes : ByteArray) (hpid : pidBytes.size = 32) :
    cuTripleWithin 4 0 4
      ((((CodeReq.singleton 0 (.mov64 .r2 (.imm 0))).union
          (CodeReq.singleton 1 (.lddw .r3 r3V_imm))).union
          (CodeReq.singleton 2 (.lddw .r4 r4V_imm))).union
          (CodeReq.singleton 3 (.call .sol_create_program_address)))
      ((.r0 ↦ᵣ vR0) ** (.r2 ↦ᵣ vR2) ** (.r3 ↦ᵣ vR3) ** (.r4 ↦ᵣ vR4) **
        (toU64 r3V_imm ↦Bytes32 pidBytes) **
        (toU64 r4V_imm ↦Bytes32 outOldBytes))
      ((.r0 ↦ᵣ (match Pda.createProgramAddress [] pidBytes with
                | some _ => 0 | none => 1)) **
        (.r2 ↦ᵣ 0) ** (.r3 ↦ᵣ toU64 r3V_imm) ** (.r4 ↦ᵣ toU64 r4V_imm) **
        (toU64 r3V_imm ↦Bytes32 pidBytes) **
        (toU64 r4V_imm ↦Bytes32 (match Pda.createProgramAddress [] pidBytes with
                                  | some bs => bs | none => outOldBytes))) := by
  have h1 := mov64_imm_spec .r2 0 vR2 0 (by decide)
  have h2 := lddw_spec .r3 r3V_imm vR3 1 (by decide)
  have h3 := lddw_spec .r4 r4V_imm vR4 2 (by decide)
  have h4 := call_create_program_address_n0_spec vR0
              (toU64 r3V_imm) (toU64 r4V_imm) pidBytes outOldBytes 3 hpid
  sl_block_iter [h1, h2, h3, h4]

/-! ## PDA macro — executeFn bridge

Downgrades `pda_n0_macro_spec` from an SL Hoare triple to a concrete
`executeFn` existential. Lets callers plug the 4-step PDA derivation
into a larger execution as a single k-step jump. -/

theorem pda_n0_macro_executeFn
    (vR0 vR2 vR3 vR4 : Nat) (r3V_imm r4V_imm : Int)
    (pidBytes outOldBytes : ByteArray) (hpid : pidBytes.size = 32)
    {fetch : Nat → Option Insn}
    (hcr : (((((CodeReq.singleton 0 (.mov64 .r2 (.imm 0))).union
                (CodeReq.singleton 1 (.lddw .r3 r3V_imm))).union
                (CodeReq.singleton 2 (.lddw .r4 r4V_imm))).union
                (CodeReq.singleton 3 (.call .sol_create_program_address)))
            ).SatisfiedBy fetch)
    {s : State}
    (hP : ((.r0 ↦ᵣ vR0) ** (.r2 ↦ᵣ vR2) ** (.r3 ↦ᵣ vR3) ** (.r4 ↦ᵣ vR4) **
            (toU64 r3V_imm ↦Bytes32 pidBytes) **
            (toU64 r4V_imm ↦Bytes32 outOldBytes)).holdsFor s)
    (hpc : s.pc = 0) (hex : s.exitCode = none) :
    ∃ k, k ≤ 4 ∧
      (executeFn fetch s k).pc = 4 ∧
      (executeFn fetch s k).exitCode = none ∧
      ((.r0 ↦ᵣ (match Pda.createProgramAddress [] pidBytes with
                | some _ => 0 | none => 1)) **
        (.r2 ↦ᵣ 0) ** (.r3 ↦ᵣ toU64 r3V_imm) ** (.r4 ↦ᵣ toU64 r4V_imm) **
        (toU64 r3V_imm ↦Bytes32 pidBytes) **
        (toU64 r4V_imm ↦Bytes32 (match Pda.createProgramAddress [] pidBytes with
                                  | some bs => bs | none => outOldBytes))).holdsFor
        (executeFn fetch s k) :=
  (pda_n0_macro_spec vR0 vR2 vR3 vR4 r3V_imm r4V_imm pidBytes outOldBytes hpid).toExec
    hcr hP hpc hex

/-! ## PDA derivation macro (n=1) — Session 2 deliverable

5-instruction calling-convention prelude + syscall for the n=1 PDA
syscall:

```
pc=0: mov64 r2, 1                    ; n_seeds = 1
pc=1: lddw r1, descriptor_addr       ; r1 = pointer to length-1 VmSlice array
pc=2: lddw r3, program_id_addr       ; r3 = pointer to 32-byte pid
pc=3: lddw r4, output_addr           ; r4 = pointer to 32-byte output
pc=4: call sol_create_program_address
```

The caller is responsible for placing a valid `VmSlice { ptr, len }`
descriptor at `descriptor_addr` and the seed bytes at `descriptor.ptr`
ahead of time. The pre owns all of: 5 regs, 2 descriptor u64s, the
seed-bytes blob, the pid bytes, and the output bytes.

A future variant (`pda_n1_stack_macro_spec`, Session 2B) replaces the
3 `lddw`s with stack-relative `mov64 r1, r10 + add64 + stxdw` writes
that materialize the descriptor on the call frame.

Composition uses `sl_block_iter` over the 4 setup specs + the n=1
syscall spec; framing for the unchanged atoms is automatic. -/

theorem pda_n1_macro_spec
    (vR0 vR1 vR2 vR3 vR4 : Nat) (r1V_imm r3V_imm r4V_imm : Int)
    (seedPtr : Nat)
    (seedBytes pidBytes outOldBytes : ByteArray)
    (hpid : pidBytes.size = 32)
    (hseed_lt : seedPtr < 2 ^ 64)
    (hslen_lt : seedBytes.size < 2 ^ 64) :
    cuTripleWithin 5 0 5
      (((((CodeReq.singleton 0 (.mov64 .r2 (.imm 1))).union
            (CodeReq.singleton 1 (.lddw .r1 r1V_imm))).union
            (CodeReq.singleton 2 (.lddw .r3 r3V_imm))).union
            (CodeReq.singleton 3 (.lddw .r4 r4V_imm))).union
            (CodeReq.singleton 4 (.call .sol_create_program_address)))
      ((.r0 ↦ᵣ vR0) ** (.r1 ↦ᵣ vR1) ** (.r2 ↦ᵣ vR2) ** (.r3 ↦ᵣ vR3) ** (.r4 ↦ᵣ vR4) **
        (toU64 r1V_imm ↦U64 seedPtr) **
        (toU64 r1V_imm + 8 ↦U64 seedBytes.size) **
        (seedPtr ↦Bytes seedBytes) **
        (toU64 r3V_imm ↦Bytes32 pidBytes) **
        (toU64 r4V_imm ↦Bytes32 outOldBytes))
      ((.r0 ↦ᵣ (match Pda.createProgramAddress [seedBytes] pidBytes with
                | some _ => 0 | none => 1)) **
        (.r1 ↦ᵣ toU64 r1V_imm) ** (.r2 ↦ᵣ 1) **
        (.r3 ↦ᵣ toU64 r3V_imm) ** (.r4 ↦ᵣ toU64 r4V_imm) **
        (toU64 r1V_imm ↦U64 seedPtr) **
        (toU64 r1V_imm + 8 ↦U64 seedBytes.size) **
        (seedPtr ↦Bytes seedBytes) **
        (toU64 r3V_imm ↦Bytes32 pidBytes) **
        (toU64 r4V_imm ↦Bytes32 (match Pda.createProgramAddress [seedBytes] pidBytes with
                                  | some bs => bs | none => outOldBytes))) := by
  have h0 := mov64_imm_spec .r2 1 vR2 0 (by decide)
  have h1 := lddw_spec .r1 r1V_imm vR1 1 (by decide)
  have h2 := lddw_spec .r3 r3V_imm vR3 2 (by decide)
  have h3 := lddw_spec .r4 r4V_imm vR4 3 (by decide)
  have h4 := call_create_program_address_n1_spec vR0 (toU64 r1V_imm)
              (toU64 r3V_imm) (toU64 r4V_imm) seedPtr seedBytes pidBytes outOldBytes 4
              hpid hseed_lt hslen_lt
  sl_block_iter [h0, h1, h2, h3, h4]

/-! ## PDA n=1 macro — executeFn bridge -/

theorem pda_n1_macro_executeFn
    (vR0 vR1 vR2 vR3 vR4 : Nat) (r1V_imm r3V_imm r4V_imm : Int)
    (seedPtr : Nat)
    (seedBytes pidBytes outOldBytes : ByteArray)
    (hpid : pidBytes.size = 32)
    (hseed_lt : seedPtr < 2 ^ 64)
    (hslen_lt : seedBytes.size < 2 ^ 64)
    {fetch : Nat → Option Insn}
    (hcr : (((((CodeReq.singleton 0 (.mov64 .r2 (.imm 1))).union
                (CodeReq.singleton 1 (.lddw .r1 r1V_imm))).union
                (CodeReq.singleton 2 (.lddw .r3 r3V_imm))).union
                (CodeReq.singleton 3 (.lddw .r4 r4V_imm))).union
                (CodeReq.singleton 4 (.call .sol_create_program_address))
            ).SatisfiedBy fetch)
    {s : State}
    (hP : ((.r0 ↦ᵣ vR0) ** (.r1 ↦ᵣ vR1) ** (.r2 ↦ᵣ vR2) ** (.r3 ↦ᵣ vR3) ** (.r4 ↦ᵣ vR4) **
            (toU64 r1V_imm ↦U64 seedPtr) **
            (toU64 r1V_imm + 8 ↦U64 seedBytes.size) **
            (seedPtr ↦Bytes seedBytes) **
            (toU64 r3V_imm ↦Bytes32 pidBytes) **
            (toU64 r4V_imm ↦Bytes32 outOldBytes)).holdsFor s)
    (hpc : s.pc = 0) (hex : s.exitCode = none) :
    ∃ k, k ≤ 5 ∧
      (executeFn fetch s k).pc = 5 ∧
      (executeFn fetch s k).exitCode = none ∧
      ((.r0 ↦ᵣ (match Pda.createProgramAddress [seedBytes] pidBytes with
                | some _ => 0 | none => 1)) **
        (.r1 ↦ᵣ toU64 r1V_imm) ** (.r2 ↦ᵣ 1) **
        (.r3 ↦ᵣ toU64 r3V_imm) ** (.r4 ↦ᵣ toU64 r4V_imm) **
        (toU64 r1V_imm ↦U64 seedPtr) **
        (toU64 r1V_imm + 8 ↦U64 seedBytes.size) **
        (seedPtr ↦Bytes seedBytes) **
        (toU64 r3V_imm ↦Bytes32 pidBytes) **
        (toU64 r4V_imm ↦Bytes32 (match Pda.createProgramAddress [seedBytes] pidBytes with
                                  | some bs => bs | none => outOldBytes))).holdsFor
        (executeFn fetch s k) :=
  (pda_n1_macro_spec vR0 vR1 vR2 vR3 vR4 r1V_imm r3V_imm r4V_imm seedPtr
    seedBytes pidBytes outOldBytes hpid hseed_lt hslen_lt).toExec hcr hP hpc hex

/-! ## PDA n=1 stack-VmSlice macro (Session 2B)

Full register-setup + stack VmSlice descriptor + call. This is the
shape an LLVM-emitted Solana program uses to invoke the PDA syscall
with a stack-allocated `VmSlice { ptr, len }` descriptor.

```
pc=0:  mov64 r2, 1                ; n_seeds = 1
pc=1:  mov64 r1, r10              ; r1 = frame pointer
pc=2:  add64 r1, -80              ; r1 = stack address of descriptor
pc=3:  lddw r5, seed_imm          ; r5 = seed pointer
pc=4:  stxdw r1, 0, r5            ; descriptor.ptr := seed_addr
pc=5:  lddw r5, (seedBytes.size)  ; r5 = seed length
pc=6:  stxdw r1, 8, r5            ; descriptor.len := length
pc=7:  lddw r3, pid_imm           ; r3 = pid pointer
pc=8:  mov64 r4, r10              ; r4 = frame pointer
pc=9:  add64 r4, -64              ; r4 = stack address of output
pc=10: call sol_create_program_address
```

Pre owns: 7 register atoms (r0..r5 + r10), 2 stack u64 slots
(descriptor.ptr, descriptor.len — uninitialized), 1 stack 32-byte
output buffer, plus the externally-supplied seed bytes and pid
bytes. 12 atoms total.

Addresses use the natural chain-produced form
`wrapAdd r10V (toU64 (-80))` etc. — sl_block_iter's unification
matches stxdw's `effectiveAddr` output with the syscall's `r1V`. -/

/-- Session 2B current state: spec type-checks; proof body is a
    `sorry`. The `sl_block_iter` composition of 11 instructions ×
    12 SL atoms exhausts Lean's tactic recursion depth even at
    `maxRecDepth = 16000`. Path forward (Session 2C): split the
    proof into halves via `cuTripleWithinMem_seq` — each half (6 + 5
    instrs) has tractable atom-frame size. The spec demonstrates the
    realistic Solana stack-VmSlice shape. -/
theorem pda_n1_stack_macro_spec
    (vR0 vR1 vR2 vR3 vR4 vR5 r10V : Nat)
    (seed_imm pid_imm : Int)
    (vSlotPtr_old vSlotLen_old : Nat)
    (seedBytes pidBytes outOldBytes : ByteArray)
    (hpid : pidBytes.size = 32)
    (hslen_lt : seedBytes.size < 2 ^ 64) :
    cuTripleWithinMem 11 0 11
      (((((((((((CodeReq.singleton 0 (.mov64 .r2 (.imm 1))).union
                  (CodeReq.singleton 1 (.mov64 .r1 (.reg .r10)))).union
                  (CodeReq.singleton 2 (.add64 .r1 (.imm (-80))))).union
                  (CodeReq.singleton 3 (.lddw .r5 seed_imm))).union
                  (CodeReq.singleton 4 (.stx .dword .r1 0 .r5))).union
                  (CodeReq.singleton 5 (.lddw .r5 (seedBytes.size : Int)))).union
                  (CodeReq.singleton 6 (.stx .dword .r1 8 .r5))).union
                  (CodeReq.singleton 7 (.lddw .r3 pid_imm))).union
                  (CodeReq.singleton 8 (.mov64 .r4 (.reg .r10)))).union
                  (CodeReq.singleton 9 (.add64 .r4 (.imm (-64))))).union
                  (CodeReq.singleton 10 (.call .sol_create_program_address)))
      ((.r0 ↦ᵣ vR0) ** (.r1 ↦ᵣ vR1) ** (.r2 ↦ᵣ vR2) **
        (.r3 ↦ᵣ vR3) ** (.r4 ↦ᵣ vR4) ** (.r5 ↦ᵣ vR5) **
        (.r10 ↦ᵣ r10V) **
        (wrapAdd r10V (toU64 (-80)) ↦U64 vSlotPtr_old) **
        (wrapAdd r10V (toU64 (-80)) + 8 ↦U64 vSlotLen_old) **
        (wrapAdd r10V (toU64 (-64)) ↦Bytes32 outOldBytes) **
        (toU64 seed_imm ↦Bytes seedBytes) **
        (toU64 pid_imm ↦Bytes32 pidBytes))
      ((.r0 ↦ᵣ (match Pda.createProgramAddress [seedBytes] pidBytes with
                | some _ => 0 | none => 1)) **
        (.r1 ↦ᵣ wrapAdd r10V (toU64 (-80))) ** (.r2 ↦ᵣ 1) **
        (.r3 ↦ᵣ toU64 pid_imm) **
        (.r4 ↦ᵣ wrapAdd r10V (toU64 (-64))) **
        (.r5 ↦ᵣ seedBytes.size) **
        (.r10 ↦ᵣ r10V) **
        (wrapAdd r10V (toU64 (-80)) ↦U64 toU64 seed_imm) **
        (wrapAdd r10V (toU64 (-80)) + 8 ↦U64 seedBytes.size) **
        (wrapAdd r10V (toU64 (-64)) ↦Bytes32
            (match Pda.createProgramAddress [seedBytes] pidBytes with
              | some bs => bs | none => outOldBytes)) **
        (toU64 seed_imm ↦Bytes seedBytes) **
        (toU64 pid_imm ↦Bytes32 pidBytes))
      (fun rt =>
        rt.containsWritable (Memory.effectiveAddr (wrapAdd r10V (toU64 (-80))) 0) 8 = true ∧
        rt.containsWritable (Memory.effectiveAddr (wrapAdd r10V (toU64 (-80))) 8) 8 = true) := by
  have h0 := mov64_imm_spec .r2 1 vR2 0 (by decide)
  have h1 := mov64_reg_spec .r1 .r10 vR1 r10V 1 (by decide)
  have h2 := add64_imm_spec .r1 (-80) r10V 2 (by decide)
  have h3 := lddw_spec .r5 seed_imm vR5 3 (by decide)
  have h4 := stxdw_spec .r1 .r5 0
              (wrapAdd r10V (toU64 (-80))) (toU64 seed_imm) vSlotPtr_old 4
  have h5 := lddw_spec .r5 (seedBytes.size : Int) (toU64 seed_imm) 5 (by decide)
  have h6 := stxdw_spec .r1 .r5 8
              (wrapAdd r10V (toU64 (-80))) (toU64 (seedBytes.size : Int)) vSlotLen_old 6
  have h7 := lddw_spec .r3 pid_imm vR3 7 (by decide)
  have h8 := mov64_reg_spec .r4 .r10 vR4 r10V 8 (by decide)
  have h9 := add64_imm_spec .r4 (-64) r10V 9 (by decide)
  have htoU64_seed_lt : toU64 seed_imm < 2 ^ 64 := by
    unfold toU64
    exact (Int.toNat_lt' (by decide)).mpr (Int.emod_lt_of_pos _ (by decide))
  have h10 := call_create_program_address_n1_spec vR0
              (wrapAdd r10V (toU64 (-80))) (toU64 pid_imm)
              (wrapAdd r10V (toU64 (-64))) (toU64 seed_imm)
              seedBytes pidBytes outOldBytes 10 hpid htoU64_seed_lt hslen_lt
  sorry

