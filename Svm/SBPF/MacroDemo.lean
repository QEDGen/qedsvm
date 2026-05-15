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

end Svm.SBPF
