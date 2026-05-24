/-
  Synthetic minimal anchor for the spec-to-asm refinement pilot.

  Hand-encoded 7-insn sBPF program that performs the balance-shift
  pattern at the heart of any token Transfer:

  ```
  0: ldxdw r3, [r1 + 64]    ; r3 := from.amount   (load 8 bytes @ offset 64)
  1: sub64 r3, r4            ; r3 -= amount         (amount lives in r4)
  2: stxdw [r1 + 64], r3    ; from.amount := r3
  3: ldxdw r3, [r2 + 64]    ; r3 := to.amount
  4: add64 r3, r4            ; r3 += amount
  5: stxdw [r2 + 64], r3    ; to.amount := r3
  6: exit
  ```

  Convention: r1 = from-account base, r2 = to-account base,
  r4 = transfer amount; offset 64 matches the SPL Token v4 Pack
  layout's `amount` field (see `Svm/Solana/TokenAccount.lean`).
  r3 is a scratch register for load-modify-store.

  This is the refinement-pilot's asm-side anchor (Tasks 7-8 — see
  Svm/Solana/Abstract/Refinement.lean and the matching
  refines_TokenTransfer lemma). We chose a synthetic anchor over a
  proven Layer 3b fragment because the existing Layer 3b artifacts
  (PTokenTransferArmSetup / PTokenTransferArm / *TwoCalls* /
  *TwoCallsExt*) all prove FP softfloat plumbing — none of them touch
  the TokenAccount amount field. When Layer 3b eventually closes the
  balance-mutation slice of real pinocchio Transfer, a follow-up
  "codegen matches" lemma should let `refines_TokenTransfer`
  generalise to that asm shape.

  Scope: triple covers PCs 0..5 (the 6 ALU/mem insns). Exit at PC 6
  is included in the bytes for end-to-end runnability but not in the
  Hoare triple — the refinement obligation only needs the balance
  shift.
-/

import Svm.SBPF.InstructionSpecs
import Svm.SBPF.SLTactic
import Svm.SBPF.Macros
import Svm.SBPF.RunnerBridge

namespace Examples.MinimalTransferAsm

open Svm.SBPF
open Memory

/-- Byte offset of the `amount` field in an SPL Token v4 account.
    Matches `Svm.Solana.AMOUNT_OFF`. -/
def amountOff : Int := 64

/-! ## Encoding

Hand-encoded bytes, 7 × 8 = 56 bytes. Encoding follows
`Svm.SBPF.Decode.decodeInsn`:
`opcode | (src<<4 | dst) | off16 LE | imm32 LE`.

Opcodes:
  * `0x79` = `ldx .dword` — `dst := mem64[src + off16]`
  * `0x1f` = `sub64 dst, src` (reg form)
  * `0x7b` = `stx .dword` — `mem64[dst + off16] := src`
  * `0x0f` = `add64 dst, src` (reg form)
  * `0x95` = `exit` -/
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

/-- The seven decoded instructions. -/
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

/-! ## CodeReq — the six ALU/mem insns at PCs 0..5

The exit at PC 6 is *not* in the CodeReq — the triple stops at PC 6
(arrives there but doesn't step through it). -/

def minimalTransferCr : CodeReq :=
  (((((CodeReq.singleton 0 (.ldx .dword .r3 .r1 amountOff)).union
      (CodeReq.singleton 1 (.sub64 .r3 (.reg .r4)))).union
      (CodeReq.singleton 2 (.stx .dword .r1 amountOff .r3))).union
      (CodeReq.singleton 3 (.ldx .dword .r3 .r2 amountOff))).union
      (CodeReq.singleton 4 (.add64 .r3 (.reg .r4)))).union
      (CodeReq.singleton 5 (.stx .dword .r2 amountOff .r3))

/-! ## The asm-level triple — the refinement pilot's anchor

Pre: r1, r2 are the two account base addresses, r3 holds an
arbitrary scratch value (gets clobbered), r4 holds the transfer
amount, the U64 atoms at `+64` offsets hold the current balances.

Post: r1, r2 unchanged; r3 ends holding the dst account's new
balance (the value of the last load+add); r4 unchanged; both U64
atoms shifted via `wrapSub`/`wrapAdd`.

The Hoare-triple's wrapping arithmetic (`wrapSub`/`wrapAdd`) is the
asm-level truth. The Task 8 refinement lemma will discharge the
no-overflow precondition from the abstract spec to convert these
to plain `Nat` subtract/add for the user-facing theorem. -/

theorem minimal_transfer_spec
    (srcAddr dstAddr amount srcBalance dstBalance vR3Old : Nat)
    (h_srcBal : srcBalance < 2 ^ 64)
    (h_dstBal : dstBalance < 2 ^ 64) :
    cuTripleWithinMem 6 0 6 minimalTransferCr
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
