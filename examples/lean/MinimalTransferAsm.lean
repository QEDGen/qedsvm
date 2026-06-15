/-
  Synthetic asm anchor for the refinement pilot (Tasks 7-8).

  7-insn sBPF: ldxdw/sub64/stxdw for the source account, ldxdw/add64/stxdw for dest,
  then exit. r1=from base, r2=to base, r4=amount; offset 64 = SPL Token v4 `amount` field.

  Chosen over a Layer 3b fragment because the existing L3b artifacts all prove FP/softfloat
  plumbing, not the amount field. A future "codegen matches" lemma can generalize when L3b
  closes the balance-mutation slice.

  SCOPE: triple covers PCs 0..5 only; exit at PC 6 is in the bytes but not the obligation.
-/

import SVM.SBPF.InstructionSpecs
import SVM.SBPF.Tactic.SL
import SVM.SBPF.Macros
import SVM.SBPF.RunnerBridge

namespace Examples.MinimalTransferAsm

open SVM.SBPF
open Memory

/-- SPL Token v4 `amount` field byte offset; matches `SVM.Solana.AMOUNT_OFF`. -/
def amountOff : Int := 64

/-! ## Encoding (7 × 8 = 56 bytes, `opcode|(src<<4|dst)|off16LE|imm32LE`). -/
def minimalTransferBytes : ByteArray :=
  ⟨#[ -- 0: ldxdw r3, [r1 + 64]
      0x79, 0x13, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00,
      -- 1: sub64 r3, r4
      0x1f, 0x43, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      -- 2: stxdw [r1 + 64], r3
      0x7b, 0x31, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00,
      -- 3: ldxdw r3, [r2 + 64]
      0x79, 0x23, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00,
      -- 4: add64 r3, r4
      0x0f, 0x43, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      -- 5: stxdw [r2 + 64], r3
      0x7b, 0x32, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00,
      -- 6: exit
      0x95, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 ]⟩

/-- Decoded instruction array for minimalTransferBytes. -/
def minimalTransferInsns : Array Insn :=
  #[ .ldx .dword .r3 .r1 amountOff,
     .sub64 .r3 (.reg .r4),
     .stx .dword .r1 amountOff .r3,
     .ldx .dword .r3 .r2 amountOff,
     .add64 .r3 (.reg .r4),
     .stx .dword .r2 amountOff .r3,
     .exit ]

theorem minimalTransfer_decodes :
    Decode.decodeProgram minimalTransferBytes = some minimalTransferInsns := by
  native_decide

/-! ## CodeReq for PCs 0..5; exit at PC 6 excluded from the triple. -/

def minimalTransferCr : CodeReq :=
  (((((CodeReq.singleton 0 (.ldx .dword .r3 .r1 amountOff)).union
      (CodeReq.singleton 1 (.sub64 .r3 (.reg .r4)))).union
      (CodeReq.singleton 2 (.stx .dword .r1 amountOff .r3))).union
      (CodeReq.singleton 3 (.ldx .dword .r3 .r2 amountOff))).union
      (CodeReq.singleton 4 (.add64 .r3 (.reg .r4)))).union
      (CodeReq.singleton 5 (.stx .dword .r2 amountOff .r3))

/-! ## Asm-level triple

Pre: r1/r2=account bases, r3=scratch (clobbered), r4=amount, U64s at +64 offsets.
Post: r1/r2/r4 unchanged; balances shifted via `wrapSub`/`wrapAdd` (wrapping is
asm truth; Task 8 refinement lemma discharges the no-overflow guard). -/

theorem minimal_transfer_spec
    (srcAddr dstAddr amount srcBalance dstBalance vR3Old : Nat)
    (h_srcBal : srcBalance < 2 ^ 64)
    (h_dstBal : dstBalance < 2 ^ 64) :
    cuTripleWithinMem 6 0 0 6 minimalTransferCr
      ((.r1 ↦ᵣ srcAddr) ** (.r2 ↦ᵣ dstAddr) **
       (.r3 ↦ᵣ vR3Old) ** (.r4 ↦ᵣ amount) **
       (effectiveAddr srcAddr amountOff ↦U64 srcBalance) **
       (effectiveAddr dstAddr amountOff ↦U64 dstBalance))
      ((.r1 ↦ᵣ srcAddr) ** (.r2 ↦ᵣ dstAddr) **
       (.r3 ↦ᵣ wrapAdd dstBalance amount) ** (.r4 ↦ᵣ amount) **
       (effectiveAddr srcAddr amountOff ↦U64 wrapSub srcBalance amount) **
       (effectiveAddr dstAddr amountOff ↦U64 wrapAdd dstBalance amount))
      (fun rt =>
        ((rt.containsRange (effectiveAddr srcAddr amountOff) 8 = true ∧
            rt.containsWritable (effectiveAddr srcAddr amountOff) 8 = true) ∧
          rt.containsRange (effectiveAddr dstAddr amountOff) 8 = true) ∧
        rt.containsWritable (effectiveAddr dstAddr amountOff) 8 = true) := by
  have h0 := ldxdw_spec .r3 .r1 amountOff vR3Old srcAddr srcBalance 0
              (by decide) h_srcBal
  have h1 := sub64_reg_spec .r3 .r4 srcBalance amount 1 (by decide)
  have h2 := stxdw_spec .r1 .r3 amountOff srcAddr
              (wrapSub srcBalance amount) srcBalance 2
  have h3 := ldxdw_spec .r3 .r2 amountOff (wrapSub srcBalance amount)
              dstAddr dstBalance 3 (by decide) h_dstBal
  have h4 := add64_reg_spec .r3 .r4 dstBalance amount 4 (by decide)
  have h5 := stxdw_spec .r2 .r3 amountOff dstAddr
              (wrapAdd dstBalance amount) dstBalance 5
  unfold minimalTransferCr
  sl_block_iter [h0, h1, h2, h3, h4, h5]

end Examples.MinimalTransferAsm
