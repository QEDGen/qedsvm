/-
  Layer 3b artifact #2: Hoare triple over the 4-instruction **setup**
  of the p-token Transfer arm — bytes 0x76e8-0x7700 of
  `qedsvm-rs/tests/fixtures/p_token.so` (release
  `p-token@v1.0.0-rc.1`).

  Scope intentionally small. The original session N+1 plan
  (`docs/next-session-plan.md`) was to prove these 4 setup insns plus
  the `call_local 0x21dd` at 0x7708 in a single artifact, but the
  callee turned out to be a 29-insn compiler-rt IEEE-754 softfloat
  helper. That bundled three unknowns (call-frame mechanics +
  IEEE-754 semantics + `sl_branch`-at-scale). This artifact closes the
  cheapest of the three:

  - **Methodology unknown retired:** r10-relative stack stores in a
    Layer 3b precondition. `PTokenValidationPrelude.lean` only used
    input-buffer reads of the form `effectiveAddr initR1 OFFSET ↦U64 …`
    with non-negative offsets. This file confirms `stxdw` against
    `effectiveAddr initR10 (-2088) ↦U64 …` (negative offset, r10 as
    base) composes through `sl_block_iter` without ceremony.

  The 4 instructions, lifted from
  `qedsvm-rs/tests/fixtures/p_token.disasm` via
  `qedsvm-rs/src/bin/disasm_to_lean.rs`:

  ```
  76e8: b7 01 00 00 00 00 ..    mov64 r1, 0x0
  76f0: 7b 1a d8 f7 00 00 ..    stxdw [r10 - 0x828], r1
  76f8: bf 61 00 00 00 00 ..    mov64 r1, r6
  7700: b7 02 00 00 00 00 ..    mov64 r2, 0x0
  ```

  Semantics: zeroes a u64 slot on the caller's frame at offset
  `-0x828` from r10 (likely the `lamports_out` ref-cell for the
  `try_borrow_mut_lamports` cascade pinocchio emits before the FP
  Rent-exempt comparison), then loads r1 with r6 (a saved input
  pointer) and zeroes r2 as the first call argument. After execution
  the next instruction is the `call_local 0x21dd` at 0x7708 (proved
  in a separate artifact — see N+3 in `docs/next-session-plan.md`).

  Spec: linear 4-CU walk advancing PC 0 → 4 (local PC numbering),
  preserving r6 and r10, setting r1 := initR6 and r2 := 0, and
  writing 0 to the stack slot at `effectiveAddr initR10 (-0x828)`.
-/

import SVM.SBPF.InstructionSpecs
import SVM.SBPF.Tactic.SL
import SVM.SBPF.Macros

namespace Examples.PTokenTransferArmSetup

open SVM.SBPF
open Memory

/-- Stack slot offset used by `stxdw` (instruction at local PC 1).
    `-0x828 = -2088` matches the disasm-to-lean rendering. -/
def stackSlotOff : Int := -2088

/-- The CodeReq for the 4-instruction Transfer-arm setup. -/
def transferArmSetupCr : CodeReq :=
  cr![ 0 ↦ .mov64 .r1 (.imm 0),
       1 ↦ .stx .dword .r10 stackSlotOff .r1,
       2 ↦ .mov64 .r1 (.reg .r6),
       3 ↦ .mov64 .r2 (.imm 0) ]

theorem p_token_transfer_arm_setup_spec
    (initR1 initR2 initR6 initR10 oldStackVal : Nat) :
    cuTripleWithinMem 4 0 0 4 transferArmSetupCr
      ((.r1 ↦ᵣ initR1) ** (.r10 ↦ᵣ initR10) **
        (effectiveAddr initR10 stackSlotOff ↦U64 oldStackVal) **
        (.r6 ↦ᵣ initR6) ** (.r2 ↦ᵣ initR2))
      ((.r1 ↦ᵣ initR6) ** (.r10 ↦ᵣ initR10) **
        (effectiveAddr initR10 stackSlotOff ↦U64 toU64 0) **
        (.r6 ↦ᵣ initR6) ** (.r2 ↦ᵣ toU64 0))
      (fun rt => rt.containsWritable (effectiveAddr initR10 stackSlotOff) 8 = true) := by
  -- h0 writes r1 := toU64 0; vOld is initR1.
  have h0 := mov64_imm_spec .r1 0 initR1 0 (by decide)
  -- h1 writes 0 to the stack slot; vSrc is r1's value (toU64 0).
  have h1 := stxdw_spec .r10 .r1 stackSlotOff initR10 (toU64 0) oldStackVal 1
  -- h2 writes r1 := initR6; vOld is r1's value after h1 (toU64 0).
  have h2 := mov64_reg_spec .r1 .r6 (toU64 0) initR6 2 (by decide)
  -- h3 writes r2 := toU64 0; vOld is initR2.
  have h3 := mov64_imm_spec .r2 0 initR2 3 (by decide)
  sl_block_iter [h0, h1, h2, h3]

end Examples.PTokenTransferArmSetup
