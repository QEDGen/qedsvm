/-
  Spike: can `sl_block_iter` compose over real p-token bytecode?

  The p-token Transfer instruction's execution path is ~200-500 sBPF
  instructions. Before committing to spec-composing the full path
  (1-3 weeks of work per estimate), this spike validates the core
  unknown: does the SL composition tactic scale beyond synthetic
  macros (proven up to ~11 instructions in `Macros.lean`) onto real,
  compiler-emitted bytecode patterns?

  Source: `qedsvm-rs/tests/fixtures/p_token.so` (release
  `p-token@v1.0.0-rc.1`, April 2025). Disassembled via
  `llvm-objdump -d` from platform-tools v1.48. Disassembly snapshot
  saved at `qedsvm-rs/tests/fixtures/p_token.disasm`.

  Three slices, ascending size:

  - **Slice A (2 insns)**: entrypoint preamble at .text+0x00.
    `mov64 r7, r1` ; `ldxb r1, [r7 + 0x41]`.
    Validates the basic bytes→spec flow on real bytecode.

  - **Slice B (4 insns)**: a linear block at .text+0x60.
    `mov64 r1, r7` ; `add64 r1, 0x30` ; `ldxb r2, [r7 + 0x38]` ;
    `stxdw [r10 - 0x30], r1`. Exercises stack writes.

  - **Slice C (9 insns)**: the full linear block .text+0x60 to +0xa0.
    Adds pointer arithmetic with loaded data, a second load via the
    computed address, and three more stack writes. Largest realistic
    scaling test before branches kick in.

  Each slice ships its CodeReq, the per-step spec hypotheses, and the
  `sl_block_iter` composition. Build with `lake build Examples`.

  Outcome of this file determines the effort number for the full
  Layer 3 Transfer spec.
-/

import Svm.SBPF.InstructionSpecs
import Svm.SBPF.SLTactic
import Svm.SBPF.SpecGen
import Svm.SBPF.Macros

namespace Examples.PTokenSpike

open Svm.SBPF
open Memory

/-! ## Slice A — 2-instruction entrypoint preamble

```
0120: bf 17 00 00 00 00 00 00      mov64 r7, r1
0128: 71 71 41 00 00 00 00 00      ldxb  r1, [r7 + 0x41]
```

After: r7 = initial r1, r1 = byte at [initial r1 + 0x41].

State: 3 atoms. No stack, no pointer arithmetic, single mem read. -/

theorem slice_a_spec (initR1 initR7 b : Nat) :
    cuTripleWithinMem 2 0 2
      ((CodeReq.singleton 0 (.mov64 .r7 (.reg .r1))).union
       (CodeReq.singleton 1 (.ldx .byte .r1 .r7 0x41)))
      ((.r1 ↦ᵣ initR1) ** (.r7 ↦ᵣ initR7) **
        (effectiveAddr initR1 0x41 ↦ₘ b))
      ((.r1 ↦ᵣ b % 256) ** (.r7 ↦ᵣ initR1) **
        (effectiveAddr initR1 0x41 ↦ₘ b))
      (fun rt => rt.containsRange (effectiveAddr initR1 0x41) 1 = true) := by
  have h1 := mov64_reg_spec .r7 .r1 initR7 initR1 0 (by decide)
  have h2 := ldxb_spec .r1 .r7 0x41 initR1 initR1 b 1 (by decide)
  sl_block_iter [h1, h2]

/-! ## Slice B — 4-instruction linear block at .text+0x60

```
0180: bf 71 00 00 00 00 00 00      mov64 r1, r7
0188: 07 01 00 00 30 00 00 00      add64 r1, 0x30
0190: 71 72 38 00 00 00 00 00      ldxb  r2, [r7 + 0x38]
0198: 7b 1a d0 ff 00 00 00 00      stxdw [r10 - 0x30], r1
```

After: r1 = initR7 + 0x30, r2 = byte at [r7+0x38], stack[-0x30] = r1.

Adds stack write reasoning (stxdw via r10 offset). 5 atoms (4 regs + 2 mem
cells). PCs match the disassembly's logical PC indices: 0x180/8 = 48, 49,
50, 51 — but for the spike we use the local PC range [0, 4). -/

theorem slice_b_spec (initR1 initR2 initR7 initR10 b stackOld : Nat) :
    cuTripleWithinMem 4 0 4
      ((((CodeReq.singleton 0 (.mov64 .r1 (.reg .r7))).union
          (CodeReq.singleton 1 (.add64 .r1 (.imm 0x30)))).union
          (CodeReq.singleton 2 (.ldx .byte .r2 .r7 0x38))).union
          (CodeReq.singleton 3 (.stx .dword .r10 (-0x30) .r1)))
      ((.r1 ↦ᵣ initR1) ** (.r2 ↦ᵣ initR2) ** (.r7 ↦ᵣ initR7) **
        (.r10 ↦ᵣ initR10) **
        (effectiveAddr initR7 0x38 ↦ₘ b) **
        (effectiveAddr initR10 (-0x30) ↦U64 stackOld))
      ((.r1 ↦ᵣ wrapAdd initR7 (toU64 0x30)) ** (.r2 ↦ᵣ b % 256) **
        (.r7 ↦ᵣ initR7) ** (.r10 ↦ᵣ initR10) **
        (effectiveAddr initR7 0x38 ↦ₘ b) **
        (effectiveAddr initR10 (-0x30) ↦U64 wrapAdd initR7 (toU64 0x30)))
      (fun rt =>
        rt.containsRange (effectiveAddr initR7 0x38) 1 = true ∧
        rt.containsRange (effectiveAddr initR10 (-0x30)) 8 = true ∧
        rt.containsWritable (effectiveAddr initR10 (-0x30)) 8 = true) := by
  have h1 := mov64_reg_spec .r1 .r7 initR1 initR7 0 (by decide)
  have h2 := add64_imm_spec .r1 0x30 initR7 1 (by decide)
  have h3 := ldxb_spec .r2 .r7 0x38 initR2 initR7 b 2 (by decide)
  have h4 := stxdw_spec .r10 .r1 (-0x30) initR10 (wrapAdd initR7 (toU64 0x30)) stackOld 3
  sl_block_iter [h1, h2, h3, h4]

/-! ## Slice C — 9-instruction linear block at .text+0x60

```
0180: bf 71 00 00 00 00 00 00      mov64 r1, r7
0188: 07 01 00 00 30 00 00 00      add64 r1, 0x30
0190: 71 72 38 00 00 00 00 00      ldxb  r2, [r7 + 0x38]
0198: 7b 1a d0 ff 00 00 00 00      stxdw [r10 - 0x30], r1
01a0: 0f 21 00 00 00 00 00 00      add64 r1, r2
01a8: 71 11 ff ff 00 00 00 00      ldxb  r1, [r1 - 0x1]
01b0: 7b 5a f0 ff 00 00 00 00      stxdw [r10 - 0x10], r5
01b8: 7b 2a f8 ff 00 00 00 00      stxdw [r10 - 0x8], r2
01c0: 7b 1a d8 ff 00 00 00 00      stxdw [r10 - 0x28], r1
```

The dependent-address test: after instructions 0..4, r1 holds
`r7 + 0x30 + b1` where `b1` is the byte loaded at offset 0x38. The
ldxb at PC 5 then reads from `[r1 - 1]` = `[r7 + 0x30 + b1 - 1]`,
which has a symbolic address. The precondition owns the byte at
that computed address as a separate atom.

9 instructions, 11 atoms (5 regs + 2 input-buffer mem cells +
4 stack mem cells). This exceeds the previous proven max
(`pda_n1_stack_macro_spec` at 11 instructions / 13 atoms is in the
same neighborhood, but had the `sl_rw_abs` workaround). Hitting the
structural-reduction wall here, if it happens, would surface the
need for the `sl_rw_abs` mitigation on real bytecode. -/

set_option maxHeartbeats 800000 in
theorem slice_c_spec
    (initR1 initR2 initR5 initR7 initR10 b1 b2
     stackOld_30 stackOld_10 stackOld_8 stackOld_28 : Nat)
    (hb1 : b1 < 256) :
    cuTripleWithinMem 9 0 9
      ((((((((((CodeReq.singleton 0 (.mov64 .r1 (.reg .r7))).union
              (CodeReq.singleton 1 (.add64 .r1 (.imm 0x30)))).union
              (CodeReq.singleton 2 (.ldx .byte .r2 .r7 0x38))).union
              (CodeReq.singleton 3 (.stx .dword .r10 (-0x30) .r1))).union
              (CodeReq.singleton 4 (.add64 .r1 (.reg .r2)))).union
              (CodeReq.singleton 5 (.ldx .byte .r1 .r1 (-1)))).union
              (CodeReq.singleton 6 (.stx .dword .r10 (-0x10) .r5))).union
              (CodeReq.singleton 7 (.stx .dword .r10 (-0x8) .r2))).union
              (CodeReq.singleton 8 (.stx .dword .r10 (-0x28) .r1)))
      ((.r1 ↦ᵣ initR1) ** (.r2 ↦ᵣ initR2) ** (.r5 ↦ᵣ initR5) **
        (.r7 ↦ᵣ initR7) ** (.r10 ↦ᵣ initR10) **
        (effectiveAddr initR7 0x38 ↦ₘ b1) **
        (effectiveAddr (wrapAdd (wrapAdd initR7 (toU64 0x30)) b1) (-1) ↦ₘ b2) **
        (effectiveAddr initR10 (-0x30) ↦U64 stackOld_30) **
        (effectiveAddr initR10 (-0x10) ↦U64 stackOld_10) **
        (effectiveAddr initR10 (-0x8) ↦U64 stackOld_8) **
        (effectiveAddr initR10 (-0x28) ↦U64 stackOld_28))
      ((.r1 ↦ᵣ b2 % 256) ** (.r2 ↦ᵣ b1 % 256) ** (.r5 ↦ᵣ initR5) **
        (.r7 ↦ᵣ initR7) ** (.r10 ↦ᵣ initR10) **
        (effectiveAddr initR7 0x38 ↦ₘ b1) **
        (effectiveAddr (wrapAdd (wrapAdd initR7 (toU64 0x30)) b1) (-1) ↦ₘ b2) **
        (effectiveAddr initR10 (-0x30) ↦U64 wrapAdd initR7 (toU64 0x30)) **
        (effectiveAddr initR10 (-0x10) ↦U64 initR5) **
        (effectiveAddr initR10 (-0x8) ↦U64 b1 % 256) **
        (effectiveAddr initR10 (-0x28) ↦U64 b2 % 256))
      (fun rt =>
        rt.containsRange (effectiveAddr initR7 0x38) 1 = true ∧
        rt.containsRange (effectiveAddr (wrapAdd (wrapAdd initR7 (toU64 0x30)) b1) (-1)) 1 = true ∧
        rt.containsRange (effectiveAddr initR10 (-0x30)) 8 = true ∧
        rt.containsWritable (effectiveAddr initR10 (-0x30)) 8 = true ∧
        rt.containsRange (effectiveAddr initR10 (-0x10)) 8 = true ∧
        rt.containsWritable (effectiveAddr initR10 (-0x10)) 8 = true ∧
        rt.containsRange (effectiveAddr initR10 (-0x8)) 8 = true ∧
        rt.containsWritable (effectiveAddr initR10 (-0x8)) 8 = true ∧
        rt.containsRange (effectiveAddr initR10 (-0x28)) 8 = true ∧
        rt.containsWritable (effectiveAddr initR10 (-0x28)) 8 = true) := by
  have h1 := mov64_reg_spec .r1 .r7 initR1 initR7 0 (by decide)
  have h2 := add64_imm_spec .r1 0x30 initR7 1 (by decide)
  have h3 := ldxb_spec .r2 .r7 0x38 initR2 initR7 b1 2 (by decide)
  have h4 := stxdw_spec .r10 .r1 (-0x30) initR10 (wrapAdd initR7 (toU64 0x30)) stackOld_30 3
  -- After step 3: r1 = wrapAdd initR7 (toU64 0x30), r2 = b1 % 256.
  -- Step 4: r1 += r2  ⇒  r1 = wrapAdd (wrapAdd initR7 (toU64 0x30)) (b1 % 256).
  -- Since b1 < 256, (b1 % 256) = b1, but we keep the % 256 form for atom-matching.
  have h5 := add64_reg_spec .r1 .r2 (wrapAdd initR7 (toU64 0x30)) (b1 % 256) 4 (by decide)
  -- Step 5: ldxb r1, [r1 - 1]. baseAddr = r1 after step 4.
  -- The memory atom in the precondition uses `b1` (not `b1 % 256`) in its address,
  -- so we rewrite using `Nat.mod_eq_of_lt hb1 : b1 % 256 = b1` to align.
  have h6 := ldxb_spec .r1 .r1 (-1)
    (wrapAdd (wrapAdd initR7 (toU64 0x30)) (b1 % 256))
    (wrapAdd (wrapAdd initR7 (toU64 0x30)) (b1 % 256)) b2 5 (by decide)
  have h7 := stxdw_spec .r10 .r5 (-0x10) initR10 initR5 stackOld_10 6
  have h8 := stxdw_spec .r10 .r2 (-0x8) initR10 (b1 % 256) stackOld_8 7
  have h9 := stxdw_spec .r10 .r1 (-0x28) initR10 (b2 % 256) stackOld_28 8
  -- Bridge: the precondition's mem-atom address uses `b1`; h6 introduces
  -- `b1 % 256`. Rewrite the precondition's address shape inside the chain
  -- via `Nat.mod_eq_of_lt hb1`.
  have hb1_mod : b1 % 256 = b1 := Nat.mod_eq_of_lt hb1
  rw [← hb1_mod]
  sl_block_iter [h1, h2, h3, h4, h5, h6, h7, h8, h9]

end Examples.PTokenSpike
