/-
  Hoare spec for the blueshift `asm-timeout` program (56 bytes, 6 logical insns).
  Source: https://github.com/blueshift-gg/asm under `asm-timeout/`

  Proves: decode pin + `asm_timeout_prefix_spec` (3-insn decision prefix,
  pc → 3 or 4 depending on current vs target). Full end-to-end lift would need
  two macro proofs (one per branch) or an `sl_branch` variant; the prefix is
  the spec-revealing part.
-/

import SVM.SBPF.Macros
import SVM.SBPF.RunnerBridge

namespace Examples.AsmTimeout

open SVM.SBPF
open SVM.SBPF.Runner
open Memory

/-- `.text` of `asm-timeout.so` (56 bytes), file offset `0x78`. -/
def asmTimeoutText : ByteArray :=
  ⟨#[
    0x79, 0x10, 0x60, 0x00, 0x00, 0x00, 0x00, 0x00, -- ldxdw r0, [r1+0x60]
    0x79, 0x13, 0x98, 0x28, 0x00, 0x00, 0x00, 0x00, -- ldxdw r3, [r1+0x2898]
    0x2d, 0x30, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, -- jgt r0, r3, +1 (→ pc=4)
    0x95, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, -- exit
    0x18, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, -- lddw r0, 1 (low 32 bits)
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, -- lddw r0, 1 (high 32 bits)
    0x95, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00  -- exit
  ]⟩

/-- 6 decoded instructions (`lddw` at byte-offset 32 collapses to a single PC=4 entry). -/
def asmTimeoutInsns : Array Insn :=
  #[ .ldx .dword .r0 .r1 0x60,
     .ldx .dword .r3 .r1 0x2898,
     .jgt .r0 (.reg .r3) 4,
     .exit,
     .lddw .r0 1,
     .exit ]

theorem asmTimeout_decodes :
    Decode.decodeProgram asmTimeoutText = some asmTimeoutInsns := by
  native_decide

/-- 3-insn decision prefix: loads current/target slots, branches to pc=4 (timeout)
    or pc=3 (in-window). r0=current, r3=target; other regs/mem unchanged. -/
theorem asm_timeout_prefix_spec
    (inputAddr vR0_old vR3_old current target : Nat)
    (h_current_bound : current < 2 ^ 64)
    (h_target_bound : target < 2 ^ 64) :
    cuTripleWithinMem 3 0 0 (if current > target then 4 else 3)
      (((CodeReq.singleton 0 (.ldx .dword .r0 .r1 0x60)).union
         (CodeReq.singleton 1 (.ldx .dword .r3 .r1 0x2898))).union
         (CodeReq.singleton 2 (.jgt .r0 (.reg .r3) 4)))
      ((.r0 ↦ᵣ vR0_old) ** (.r1 ↦ᵣ inputAddr) ** (.r3 ↦ᵣ vR3_old) **
        (effectiveAddr inputAddr 0x60 ↦U64 current) **
        (effectiveAddr inputAddr 0x2898 ↦U64 target))
      ((.r0 ↦ᵣ current) ** (.r1 ↦ᵣ inputAddr) ** (.r3 ↦ᵣ target) **
        (effectiveAddr inputAddr 0x60 ↦U64 current) **
        (effectiveAddr inputAddr 0x2898 ↦U64 target))
      (fun rt =>
        rt.containsRange (effectiveAddr inputAddr 0x60) 8 = true ∧
        rt.containsRange (effectiveAddr inputAddr 0x2898) 8 = true) := by
  have h0 := ldxdw_spec .r0 .r1 0x60 vR0_old inputAddr current 0
                        (by decide) h_current_bound
  have h1 := ldxdw_spec .r3 .r1 0x2898 vR3_old inputAddr target 1
                        (by decide) h_target_bound
  have h2 := jgt_reg_spec .r0 .r3 current target 2 4
  sl_block_iter [h0, h1, h2]

end Examples.AsmTimeout
