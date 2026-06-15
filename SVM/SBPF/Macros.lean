/-
  Multi-instruction macro proofs — the verified-macro-assembler methodology
  end-to-end: per-instruction Hoare triples compose via the sequencing rule
  (`cuTripleWithin_seq`) + frame rules into a single whole-macro triple with a
  verified CU bound. Demonstrates that the methodology actually composes.
-/

import SVM.SBPF.InstructionSpecs
import SVM.SBPF.Tactic.SL
import SVM.SBPF.SpecGen

namespace SVM.SBPF

/-! ## Two-mov macro

```
  pc=0:  mov64 r1, 7
  pc=1:  mov64 r2, 8
```

After 2 CU, r1 holds 7 and r2 holds 8 (from any initial values). -/

theorem two_mov_macro_spec (vOld1 vOld2 : Nat) :
    cuTripleWithin 2 0 0 2
      ((CodeReq.singleton 0 (.mov64 .r1 (.imm 7))).union
       (CodeReq.singleton 1 (.mov64 .r2 (.imm 8))))
      ((.r1 ↦ᵣ vOld1) ** (.r2 ↦ᵣ vOld2))
      ((.r1 ↦ᵣ toU64 7) ** (.r2 ↦ᵣ toU64 8)) := by
  -- `sl_block_iter` infers frames per step (step 1 right-frames `r2`, step 2
  -- left-frames the updated `r1`) via prefix/suffix atom match.
  have h1 := mov64_imm_spec .r1 7 vOld1 0 (by decide)
  have h2 := mov64_imm_spec .r2 8 vOld2 1 (by decide)
  sl_block_iter [h1, h2]

/-- `two_mov_macro_spec` via `sl_block_auto`: the tactic reads the goal's
    CodeReq, dispatches each Insn to its spec, threads value mvars via `isDefEq`,
    and auto-discharges the `≠ .r10` side conds. -/
theorem two_mov_macro_spec_auto (vOld1 vOld2 : Nat) :
    cuTripleWithin 2 0 0 2
      ((CodeReq.singleton 0 (.mov64 .r1 (.imm 7))).union
       (CodeReq.singleton 1 (.mov64 .r2 (.imm 8))))
      ((.r1 ↦ᵣ vOld1) ** (.r2 ↦ᵣ vOld2))
      ((.r1 ↦ᵣ toU64 7) ** (.r2 ↦ᵣ toU64 8)) := by
  sl_block_auto

/-! ## Computation macro: `r1 := 10 + 5`

```
  pc=0:  mov64 r1, 10
  pc=1:  add64 r1, 5
```

After 2 CU, r1 holds `wrapAdd (toU64 10) (toU64 5) = 15`. Both insns own only
`(.r1 ↦ᵣ vOld)`, no framing; intermediate `toU64 10` threads through the seq
rule. -/

theorem add_constants_macro_spec (vOld : Nat) :
    cuTripleWithin 2 0 0 2
      ((CodeReq.singleton 0 (.mov64 .r1 (.imm 10))).union
       (CodeReq.singleton 1 (.add64 .r1 (.imm 5))))
      (.r1 ↦ᵣ vOld)
      (.r1 ↦ᵣ wrapAdd (toU64 10) (toU64 5)) := by
  have h1 := mov64_imm_spec .r1 10 vOld 0 (by decide)
  have h2 := add64_imm_spec .r1 5 (toU64 10) 1 (by decide)
  sl_block_iter [h1, h2]

/-! ## Reg-source macro: `r1 := 100 + r2`

r2 is framed through `mov64 r1, 100`, then consumed by the reg-source
`add64 r1, r2`.

```
  pc=0:  mov64 r1, 100
  pc=1:  add64 r1, r2
```

After 2 CU, `r1 = wrapAdd (toU64 100) v` and `r2` unchanged. -/

theorem mov_then_add_reg_macro_spec (vR1Old vR2Old : Nat) :
    cuTripleWithin 2 0 0 2
      ((CodeReq.singleton 0 (.mov64 .r1 (.imm 100))).union
       (CodeReq.singleton 1 (.add64 .r1 (.reg .r2))))
      ((.r1 ↦ᵣ vR1Old) ** (.r2 ↦ᵣ vR2Old))
      ((.r1 ↦ᵣ wrapAdd (toU64 100) vR2Old) ** (.r2 ↦ᵣ vR2Old)) := by
  have h1 := mov64_imm_spec .r1 100 vR1Old 0 (by decide)
  have h2 := add64_reg_spec .r1 .r2 (toU64 100) vR2Old 1 (by decide)
  sl_block_iter [h1, h2]

/-! ## Memory-op macro: `load byte, then increment register`

First SL macro exercising memory ownership.

```
  pc=0: ldxb r2, r1, 0   -- load byte at [r1] into r2
  pc=1: add64 r2, 1      -- r2 := r2 + 1
```

Byte at `[r1]` read not modified, `r1` unchanged; post `r2 = wrapAdd (oldByte %
256) 1`, CU bound = 2. Exercises `cuTripleWithinMem_seq` (mem + non-mem),
`frame_right` (carry `r1`+byte through the ALU), and `_weaken` (collapse
`containsRange ∧ True`). -/

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
  -- mem step (`ldxb`) + pure step (`add64`) via `_seq_pure_right`, which keeps
  -- only the mem step's `rr` (matching the stated `containsRange`, no reshape).
  have h1 := ldxb_spec .r2 .r1 0 vR2Old baseAddr oldByte 0 (by decide)
  have h2_alu := add64_imm_spec .r2 1 (oldByte % 256) 1 (by decide)
  sl_block_iter [h1, h2_alu]

/-! ## Memory-op macro: increment a byte in memory

Read-modify-write cycle (full Phase D shape).

```
  pc=0: ldxb r2, r1, 0    -- r2 := byte at [r1]
  pc=1: add64 r2, 1       -- r2 := r2 + 1
  pc=2: stxb r1, 0, r2    -- byte at [r1] := r2 & 0xff
```

CU bound = 3. Post: byte at [r1] becomes `(oldByte + 1) & 0xff`. Exercises
`sl_swap_first` (reshape stxb's `r1 ** r2 ** mem` to `r2 ** r1 ** mem`) and
`_seq` (union `containsRange ∧ containsWritable`). -/

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
  -- `sl_swap_first` reshapes stxb's `(r1 ** r2 ** mem)` to `(r2 ** r1 ** mem)`
  -- so the frame extractor aligns it; chain composes via `_seq_pure_right`
  -- then `_seq`, yielding `containsRange ∧ containsWritable` directly.
  have h1 := ldxb_spec .r2 .r1 0 vR2Old baseAddr oldByte 0 (by decide)
  have h2_alu := add64_imm_spec .r2 1 (oldByte % 256) 1 (by decide)
  have h3 := sl_swap_first (stxb_spec .r1 .r2 0 baseAddr
    (wrapAdd (oldByte % 256) (toU64 1)) oldByte 2)
  sl_block_iter [h1, h2_alu, h3]


/-! ## byte_increment via `sl_block_auto` — no manual `have` / `sl_swap_first`

`byte_increment_macro_spec` via `sl_block_auto`: the tactic builds the three
specs with value mvars and lets `slBlockIter`'s permutation reshape handle
stxb's differing atom order; `≠ .r10` side conds auto-discharged. -/
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

Pins the SpecGen dispatch for `.st .half` (`sth_spec`): two adjacent halfword
immediate stores, the second negative to exercise the `toU64` truncation. No
residual side goals. -/
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

The error-path collapse lemmas discharge a constant-exit landing in one `exact`.
Both idioms qedrecover tags as `constExitBlocks`: in-block (`mov64 r0, c; exit`)
and shared-exit (`lddw r0, c; ja tgt`, bare `exit` at `tgt` — pinocchio's
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

`lamport_transfer_macro_spec` via `sl_block_auto`: `ldxdw_spec`'s `srcLam/dstLam
< 2^64` bounds are left as residual goals after mvar unification, closed by
`assumption` against `hSrcLam` / `hDstLam`. -/
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

`cuTripleWithinMem.toExec` on `byte_increment_macro_spec`: re-expresses the macro
purely in `executeFn` terms (∃ k ≤ 3, `executeFn fetch s k` lands at pc=3 with the
post). This is the form larger-program proofs consume — plug the macro in as a
single k-step jump rather than re-deriving each step. -/

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

Decrements one u64 lamport balance and increments another (the
`system_program::transfer` operation), proven from per-instruction semantics.

```
  pc=0: ldxdw r4, r1, 0    -- r4 := *src
  pc=1: sub64 r4, r3        -- r4 := r4 - amount
  pc=2: stxdw r1, 0, r4    -- *src := r4
  pc=3: ldxdw r5, r2, 0    -- r5 := *dst
  pc=4: add64 r5, r3        -- r5 := r5 + amount
  pc=5: stxdw r2, 0, r5    -- *dst := r5
```

r1=src, r2=dst, r3=amount; r4/r5 scratch; CU bound = 6. Exercises a 7-atom
state, multi-atom framing with right-normalization, non-adjacent atom
interleaving (frame-extractor falls back to permutation), and 4 mem steps'
region requirements left-folding into `((cR_src ∧ cW_src) ∧ cR_dst) ∧ cW_dst`. -/

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

Copies 16 bytes src→dst as two u64 dword moves, reusing `r3` as load scratch
(ldxdw step 2 overwrites `v0` with `v1`, exercising the spec's `vOldDst`).

```
  pc=0: ldxdw r3, r1, 0    -- r3 := *(u64)(src + 0)
  pc=1: stxdw r2, 0, r3    -- *(u64)(dst + 0) := r3
  pc=2: ldxdw r3, r1, 8    -- r3 := *(u64)(src + 8)   (overwrites r3=v0)
  pc=3: stxdw r2, 8, r3    -- *(u64)(dst + 8) := r3
```

7-atom state, CU bound = 4; 4 mem steps left-fold into
`((cR_s0 ∧ cW_d0) ∧ cR_s8) ∧ cW_d8`. -/

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

First branching-track demo.

```
pc=0: jeq r1, 0, .true_block     ; target = 3
pc=1: mov64 r2, 100               ; false branch
pc=2: ja .end                     ; target = 4
pc=3: mov64 r2, 200               ; true branch
pc=4: <join PC>
```

True (`vR1 = toU64 0`): 0→3→4, r2 = 200. False: 0→1→2→4, r2 = 100. Bound = 1 +
max 1 2 = 3 CU; post `if vR1 = toU64 0 then toU64 200 else toU64 100`. Exercises
`toBranch`, `Branch_frame_right`, `_seq`, and `Branch_join`. -/

theorem if_else_macro_spec (vR1 vR2 : Nat) :
    cuTripleWithin 3 0 0 4
      (((CodeReq.singleton 0 (.jeq .r1 (.imm 0) 3)).union
         (CodeReq.singleton 3 (.mov64 .r2 (.imm 200)))).union
         ((CodeReq.singleton 1 (.mov64 .r2 (.imm 100))).union
          (CodeReq.singleton 2 (.ja 4))))
      ((.r1 ↦ᵣ vR1) ** (.r2 ↦ᵣ vR2))
      ((.r1 ↦ᵣ vR1) **
        (.r2 ↦ᵣ (if vR1 = toU64 0 then toU64 200 else toU64 100))) := by
  -- branch spec pre-framed to widen its 1-atom state to (r1 ** r2)
  have h_br := cuTripleWithinBranch_frame_right (.r2 ↦ᵣ vR2) (pcFree_regIs _ _)
                 (jeq_imm_branch_spec .r1 0 vR1 0 3)
  have h_T_r2 := mov64_imm_spec .r2 200 vR2 3 (by decide)
  -- false branch: ja_spec's emp/emp auto-widened by `sl_branch`
  have h_F_mov_r2 := mov64_imm_spec .r2 100 vR2 1 (by decide)
  sl_branch h_br [h_T_r2] [h_F_mov_r2, ja_spec 4 2]

/-! ## SPL-Token-shaped 2-way discriminant dispatch (Phase E session 2)

First branching macro combining memory + branch + join (the SPL Token
entrypoint pattern).

```
pc=0: ldxb r2, r1, 0       ; r2 = instruction_data[0] (discriminant)
pc=1: jeq r2, 0, 4         ; if discriminant == 0 → .case_0
pc=2: mov64 r0, 100         ; default
pc=3: ja 5                  ; → .end
pc=4: mov64 r0, 200         ; .case_0
pc=5: <join>
```

r1 = instruction_data ptr, r0 = scratch; discriminant read once, dispatch routes
to one of two handlers, both joining at pc=5. CU bound = 4. 4-atom state.
Exercises `ldxb_spec`, `Branch_frame_*`, `_seq`, `Branch_join`,
`_seq_pure_right`, and atom-order reshape weakens between ldxb's post and the
dispatch's pre. -/

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
  -- Canonical atom order throughout: `r0 ** r2 ** r1 ** mem`; ldxb framed with
  -- `r0` on the LEFT, dispatch's `r0 ** r2` pre matched by sepConj assoc.

  -- Stage 1: dispatch chain (pc=1 → pc=5), 2-atom state `(r0 ** r2)`.
  have h_br := cuTripleWithinBranch_frame_left (.r0 ↦ᵣ vR0) (pcFree_regIs _ _)
                 (jeq_imm_branch_spec .r2 0 (discByte % 256) 1 4)
  have h_T_r0 := mov64_imm_spec .r0 200 vR0 4 (by decide)
  have h_F_mov_r0 := mov64_imm_spec .r0 100 vR0 2 (by decide)
  have h_dispatch_2atom : cuTripleWithin 3 0 1 5
        (((CodeReq.singleton 1 (.jeq .r2 (.imm 0) 4)).union
          (CodeReq.singleton 4 (.mov64 .r0 (.imm 200)))).union
         ((CodeReq.singleton 2 (.mov64 .r0 (.imm 100))).union
          (CodeReq.singleton 3 (.ja 5))))
        ((.r0 ↦ᵣ vR0) ** (.r2 ↦ᵣ discByte % 256))
        ((.r0 ↦ᵣ (if discByte % 256 = toU64 0 then toU64 200 else toU64 100)) **
          (.r2 ↦ᵣ discByte % 256)) := by
    sl_branch h_br [h_T_r0] [h_F_mov_r0, ja_spec 5 3]
  -- Stage 2: frame `r1 ** mem` on the RIGHT, re-associate via `sepConj_assoc`
  -- to the right-folded `r0 ** r2 ** r1 ** mem`.
  have h_dispatch_4atom_raw := cuTripleWithin_frame_right
    ((.r1 ↦ᵣ baseAddr) ** (effectiveAddr baseAddr 0 ↦ₘ discByte))
    (pcFree_sepConj (pcFree_regIs _ _) (pcFree_memByteIs _ _))
    h_dispatch_2atom
  have h_dispatch_4atom_post :=
    cuTripleWithin_reshape_post sepConj_assoc h_dispatch_4atom_raw
  have h_dispatch_4atom :=
    cuTripleWithin_reshape_pre sepConj_assoc h_dispatch_4atom_post
  -- Stage 3: ldxb framed with r0 on the LEFT
  have h_ldxb := ldxb_spec .r2 .r1 0 vR2 baseAddr discByte 0 (by decide)
  have h_ldxb_4atom : cuTripleWithinMem 1 0 0 1
      (CodeReq.singleton 0 (.ldx .byte .r2 .r1 0))
      ((.r0 ↦ᵣ vR0) ** (.r2 ↦ᵣ vR2) ** (.r1 ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr 0 ↦ₘ discByte))
      ((.r0 ↦ᵣ vR0) ** (.r2 ↦ᵣ discByte % 256) ** (.r1 ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr 0 ↦ₘ discByte))
      (fun rt => rt.containsRange (effectiveAddr baseAddr 0) 1 = true) :=
    cuTripleWithinMem_frame_left (.r0 ↦ᵣ vR0) (pcFree_regIs _ _) h_ldxb
  -- Stage 4: compose ldxb (mem) + dispatch (pure) via the mem+pure seq rule;
  -- intermediate Q = ldxb's post = dispatch's pre.
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

The six PDA derivation macros composed `call_create_program_address_n{0,1}_spec`
(now retired) to prove the 4-step derivation writes the address at `*r4`. Under
H6 `Pda.execCreate` region-checks its slices, so the success path is
region-conditional and the unconditional triples no longer hold. Being
unconsumed, they are retired; honest H6 behaviour is `Pda.execCreate_faults_oob`. -/

/-! ## SpecGen extension smoke tests

Confirm `sl_block_auto` dispatches the new Insn families (32-bit ALU,
`neg64`/`neg32`, `lddw`, div/mod). A mis-wired dispatch arm throws at
elaboration and breaks the build. -/

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

