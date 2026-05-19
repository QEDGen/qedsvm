/-
  Worked example — Lean Hoare spec for the blueshift `asm-timeout` program.

  The program is 56 bytes of hand-written sBPF assembly (source:
  https://github.com/blueshift-gg/asm under `asm-timeout/`):

  ```
  entrypoint:
      ldxdw r0, [r1+0x0060]    ; r0 := current_slot
      ldxdw r3, [r1+0x2898]    ; r3 := target_slot
      jgt r0, r3, end          ; if current > target → end (timed out)
      exit                     ; in window: exit with r0 = current
  end:
      lddw r0, 1               ; timed out: r0 := 1
      exit                     ; exit with r0 = 1
  ```

  Decoded as 6 logical instructions (`lddw` occupies 2 byte-slots but
  decodes to a single logical entry). This file:

  1. Embeds the `.text` bytes from `asm-timeout.so`.
  2. Proves `Decode.decodeProgram` produces the expected 6-element
     `Array Insn`.
  3. Proves `asm_timeout_prefix_spec` — the leading 3 instructions
     (ldxdw + ldxdw + jgt) load the two memory slots and branch to
     either pc=3 (in-window exit) or pc=4 (timeout, lddw + exit).

  Demonstrates that *real* hand-written sBPF assembly admits a Lean
  Hoare spec through qedsvm's macro infrastructure. The full
  end-to-end lift to `Runner.run` halted output requires either two
  separate macro proofs (one per exit branch) or an `sl_branch`
  variant with non-converging branches; the prefix proof here is the
  branching primitive itself, which is the most spec-revealing part.
-/

import Svm.SBPF.Macros
import Svm.SBPF.RunnerBridge

namespace Examples.AsmTimeout

open Svm.SBPF
open Svm.SBPF.Runner
open Memory

/-- The `.text` section of `asm-timeout.so` (56 bytes), extracted at
    file offset `0x78`. Comments on each 8-byte slot. -/
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

/-- The 6 decoded instructions. `lddw` collapses the 2 byte-slots
    starting at byte offset 32 into a single logical entry at pc=4. -/
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

/-- The first 3 instructions (load, load, jgt) — the "decision" portion
    of asm-timeout. After execution:

    - `r0 = current` (loaded from memory at `inputAddr + 0x60`).
    - `r3 = target`  (loaded from memory at `inputAddr + 0x2898`).
    - `pc = 4` if `current > target` (timeout path → lddw + exit).
    - `pc = 3` otherwise (in-window path → exit directly).

    Memory and registers other than r0/r3 are unchanged. -/
theorem asm_timeout_prefix_spec
    (inputAddr vR0_old vR3_old current target : Nat)
    (h_current_bound : current < 2 ^ 64)
    (h_target_bound : target < 2 ^ 64) :
    cuTripleWithinMem 3 0 (if current > target then 4 else 3)
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
