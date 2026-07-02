/-
  AsmRefinesFieldUpdates asm-refines theorem for the SPL token/mint arms. MECHANICALLY
  EMITTED by qedlift's refinement codegen from the lift's atoms + the IDL
  arm name. One `(base, preFields, postFields)` triple per account on the
  layout-general vault route: each coarse codec is reshaped to fine via
  `codecCoarse_eq_fine` (`account_agg`) and the untouched cells are framed —
  no bespoke record predicate, no aggregation module (#25).
-/

import SVM.SBPF.Tactic.SL
import SVM.SBPF.Tactic.Discharge
import SVM.Solana.Abstract.Refinement
import Generated.PTokenTransferTracedLifted

namespace Examples.PTokenTransferRefinement
open SVM SVM.SBPF SVM.SBPF.Memory

set_option maxHeartbeats 1600000 in
theorem refines_asm
    (cr : CodeReq) (rr : Memory.RegionTable → Prop)
    (baseAddr oldMemB_0 vR2Old oldMemD_1 oldMemB_2 oldMemD_3 oldMemB_4 oldMemD_5 vR4Old vR3Old oldMemD_6 oldMemB_7 vR6Old vR7Old oldMemB_8 oldMemB_9 vR5Old oldMemD_10 oldMemD_11 oldMemD_12 oldMemD_13 vR0Old oldMemD_14 oldMemD_15 oldMemD_16 oldMemD_17 oldMemD_18 oldMemD_19 oldMemD_20 oldMemB_21 oldMemD_22 oldMemD_23 oldMemD_24 oldMemD_25 oldMemD_26 oldMemD_27 oldMemD_28 oldMemB_29 oldMemD_30 oldMemB_31 o5 o6 o7 o8 : Nat)
    (fg1 fg4 fg9 fg11 : ByteArray)
    (h_b0 : oldMemB_21 < 256)
    (h_b2 : oldMemB_8 < 256)
    (h_b3 : oldMemB_31 < 256)
    (h_b10 : oldMemB_9 < 256)
    (hfg1_sz : fg1.size = 35)
    (hfg9_sz : fg9.size = 36)
    (lift : cuTripleWithinMem 75 0 198 3542 cr
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦ₘ oldMemB_0) **
      (.r2 ↦ᵣ vR2Old) **
      (effectiveAddr baseAddr 88 ↦U64 oldMemD_1) **
      (effectiveAddr baseAddr 10512 ↦ₘ oldMemB_2) **
      (effectiveAddr baseAddr 10592 ↦U64 oldMemD_3) **
      (effectiveAddr baseAddr 21016 ↦ₘ oldMemB_4) **
      (effectiveAddr baseAddr 21096 ↦U64 oldMemD_5) **
      (.r4 ↦ᵣ vR4Old) **
      (.r3 ↦ᵣ vR3Old) **
      (effectiveAddr addr0 31352 ↦U64 oldMemD_6) **
      (effectiveAddr addr0 31360 ↦ₘ oldMemB_7) **
      (.r6 ↦ᵣ vR6Old) **
      (.r7 ↦ᵣ vR7Old) **
      (effectiveAddr baseAddr 204 ↦ₘ oldMemB_8) **
      (effectiveAddr baseAddr 10708 ↦ₘ oldMemB_9) **
      (.r5 ↦ᵣ vR5Old) **
      (effectiveAddr addr0 31361 ↦U64 oldMemD_10) **
      (effectiveAddr baseAddr 160 ↦U64 oldMemD_11) **
      (effectiveAddr baseAddr 10600 ↦U64 oldMemD_12) **
      (effectiveAddr baseAddr 96 ↦U64 oldMemD_13) **
      (.r0 ↦ᵣ vR0Old) **
      (effectiveAddr baseAddr 10608 ↦U64 oldMemD_14) **
      (effectiveAddr baseAddr 104 ↦U64 oldMemD_15) **
      (effectiveAddr baseAddr 10616 ↦U64 oldMemD_16) **
      (effectiveAddr baseAddr 112 ↦U64 oldMemD_17) **
      (effectiveAddr baseAddr 10624 ↦U64 oldMemD_18) **
      (effectiveAddr baseAddr 120 ↦U64 oldMemD_19) **
      (effectiveAddr baseAddr 21024 ↦U64 oldMemD_20) **
      (effectiveAddr baseAddr 168 ↦ₘ oldMemB_21) **
      (effectiveAddr baseAddr 128 ↦U64 oldMemD_22) **
      (effectiveAddr baseAddr 21032 ↦U64 oldMemD_23) **
      (effectiveAddr baseAddr 136 ↦U64 oldMemD_24) **
      (effectiveAddr baseAddr 21040 ↦U64 oldMemD_25) **
      (effectiveAddr baseAddr 144 ↦U64 oldMemD_26) **
      (effectiveAddr baseAddr 21048 ↦U64 oldMemD_27) **
      (effectiveAddr baseAddr 152 ↦U64 oldMemD_28) **
      (effectiveAddr baseAddr 21017 ↦ₘ oldMemB_29) **
      (effectiveAddr baseAddr 10664 ↦U64 oldMemD_30) **
      (effectiveAddr baseAddr 205 ↦ₘ oldMemB_31))
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦ₘ oldMemB_0) **
      (.r2 ↦ᵣ oldMemD_10) **
      (effectiveAddr baseAddr 88 ↦U64 oldMemD_1) **
      (effectiveAddr baseAddr 10512 ↦ₘ oldMemB_2) **
      (effectiveAddr baseAddr 10592 ↦U64 oldMemD_3) **
      (effectiveAddr baseAddr 21016 ↦ₘ oldMemB_4) **
      (effectiveAddr baseAddr 21096 ↦U64 oldMemD_5) **
      (.r4 ↦ᵣ oldMemB_29 % 256) **
      (.r3 ↦ᵣ oldMemB_31 % 256) **
      (effectiveAddr addr0 31352 ↦U64 oldMemD_6) **
      (effectiveAddr addr0 31360 ↦ₘ oldMemB_7) **
      (.r6 ↦ᵣ toU64 0) **
      (.r7 ↦ᵣ toU64 4) **
      (effectiveAddr baseAddr 204 ↦ₘ oldMemB_8) **
      (effectiveAddr baseAddr 10708 ↦ₘ oldMemB_9) **
      (.r5 ↦ᵣ oldMemD_27) **
      (effectiveAddr addr0 31361 ↦U64 oldMemD_10) **
      (effectiveAddr baseAddr 160 ↦U64 oldMemD_11 - oldMemD_10) **
      (effectiveAddr baseAddr 10600 ↦U64 oldMemD_12) **
      (effectiveAddr baseAddr 96 ↦U64 oldMemD_13) **
      (.r0 ↦ᵣ toU64 0) **
      (effectiveAddr baseAddr 10608 ↦U64 oldMemD_14) **
      (effectiveAddr baseAddr 104 ↦U64 oldMemD_15) **
      (effectiveAddr baseAddr 10616 ↦U64 oldMemD_16) **
      (effectiveAddr baseAddr 112 ↦U64 oldMemD_17) **
      (effectiveAddr baseAddr 10624 ↦U64 oldMemD_18) **
      (effectiveAddr baseAddr 120 ↦U64 oldMemD_19) **
      (effectiveAddr baseAddr 21024 ↦U64 oldMemD_20) **
      (effectiveAddr baseAddr 168 ↦ₘ oldMemB_21) **
      (effectiveAddr baseAddr 128 ↦U64 oldMemD_22) **
      (effectiveAddr baseAddr 21032 ↦U64 oldMemD_23) **
      (effectiveAddr baseAddr 136 ↦U64 oldMemD_24) **
      (effectiveAddr baseAddr 21040 ↦U64 oldMemD_25) **
      (effectiveAddr baseAddr 144 ↦U64 oldMemD_26) **
      (effectiveAddr baseAddr 21048 ↦U64 oldMemD_27) **
      (effectiveAddr baseAddr 152 ↦U64 oldMemD_28) **
      (effectiveAddr baseAddr 21017 ↦ₘ oldMemB_29) **
      (effectiveAddr baseAddr 10664 ↦U64 oldMemD_30 + oldMemD_10) **
      (effectiveAddr baseAddr 205 ↦ₘ oldMemB_31)) rr) :
    SVM.Solana.Abstract.AsmRefinesFieldUpdates cr 75 0 198 3542 rr
      [((baseAddr + 96),
        [(0, .pubkey ⟨oldMemD_13, oldMemD_15, oldMemD_17, oldMemD_19⟩), (32, .pubkey ⟨oldMemD_22, oldMemD_24, oldMemD_26, oldMemD_28⟩), (64, .u64 oldMemD_11), (72, .blob [.byte (oldMemB_21), .gap fg1, .byte (oldMemB_8), .byte (oldMemB_31), .gap fg4])],
        [(0, .pubkey ⟨oldMemD_13, oldMemD_15, oldMemD_17, oldMemD_19⟩), (32, .pubkey ⟨oldMemD_22, oldMemD_24, oldMemD_26, oldMemD_28⟩), (64, .u64 (oldMemD_11 - oldMemD_10)), (72, .blob [.byte (oldMemB_21), .gap fg1, .byte (oldMemB_8), .byte (oldMemB_31), .gap fg4])]),
       ((baseAddr + 10600),
        [(0, .pubkey ⟨oldMemD_12, oldMemD_14, oldMemD_16, oldMemD_18⟩), (32, .pubkey ⟨o5, o6, o7, o8⟩), (64, .u64 oldMemD_30), (72, .blob [.gap fg9, .byte (oldMemB_9), .gap fg11])],
        [(0, .pubkey ⟨oldMemD_12, oldMemD_14, oldMemD_16, oldMemD_18⟩), (32, .pubkey ⟨o5, o6, o7, o8⟩), (64, .u64 (oldMemD_30 + oldMemD_10)), (72, .blob [.gap fg9, .byte (oldMemB_9), .gap fg11])])]
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦ₘ oldMemB_0) **
      (.r2 ↦ᵣ vR2Old) **
      (effectiveAddr baseAddr 88 ↦U64 oldMemD_1) **
      (effectiveAddr baseAddr 10512 ↦ₘ oldMemB_2) **
      (effectiveAddr baseAddr 10592 ↦U64 oldMemD_3) **
      (effectiveAddr baseAddr 21016 ↦ₘ oldMemB_4) **
      (effectiveAddr baseAddr 21096 ↦U64 oldMemD_5) **
      (.r4 ↦ᵣ vR4Old) **
      (.r3 ↦ᵣ vR3Old) **
      (effectiveAddr addr0 31352 ↦U64 oldMemD_6) **
      (effectiveAddr addr0 31360 ↦ₘ oldMemB_7) **
      (.r6 ↦ᵣ vR6Old) **
      (.r7 ↦ᵣ vR7Old) **
      (.r5 ↦ᵣ vR5Old) **
      (effectiveAddr addr0 31361 ↦U64 oldMemD_10) **
      (.r0 ↦ᵣ vR0Old) **
      (effectiveAddr baseAddr 21024 ↦U64 oldMemD_20) **
      (effectiveAddr baseAddr 21032 ↦U64 oldMemD_23) **
      (effectiveAddr baseAddr 21040 ↦U64 oldMemD_25) **
      (effectiveAddr baseAddr 21048 ↦U64 oldMemD_27) **
      (effectiveAddr baseAddr 21017 ↦ₘ oldMemB_29))
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦ₘ oldMemB_0) **
      (.r2 ↦ᵣ oldMemD_10) **
      (effectiveAddr baseAddr 88 ↦U64 oldMemD_1) **
      (effectiveAddr baseAddr 10512 ↦ₘ oldMemB_2) **
      (effectiveAddr baseAddr 10592 ↦U64 oldMemD_3) **
      (effectiveAddr baseAddr 21016 ↦ₘ oldMemB_4) **
      (effectiveAddr baseAddr 21096 ↦U64 oldMemD_5) **
      (.r4 ↦ᵣ oldMemB_29 % 256) **
      (.r3 ↦ᵣ oldMemB_31 % 256) **
      (effectiveAddr addr0 31352 ↦U64 oldMemD_6) **
      (effectiveAddr addr0 31360 ↦ₘ oldMemB_7) **
      (.r6 ↦ᵣ toU64 0) **
      (.r7 ↦ᵣ toU64 4) **
      (.r5 ↦ᵣ oldMemD_27) **
      (effectiveAddr addr0 31361 ↦U64 oldMemD_10) **
      (.r0 ↦ᵣ toU64 0) **
      (effectiveAddr baseAddr 21024 ↦U64 oldMemD_20) **
      (effectiveAddr baseAddr 21032 ↦U64 oldMemD_23) **
      (effectiveAddr baseAddr 21040 ↦U64 oldMemD_25) **
      (effectiveAddr baseAddr 21048 ↦U64 oldMemD_27) **
      (effectiveAddr baseAddr 21017 ↦ₘ oldMemB_29)) := by
  unfold SVM.Solana.Abstract.AsmRefinesFieldUpdates
  simp only [SVM.Solana.Abstract.codecsPre, SVM.Solana.Abstract.codecsPost]
  rw [codecCoarse_eq_fine (baseAddr + 96)
        [(0, .pubkey ⟨oldMemD_13, oldMemD_15, oldMemD_17, oldMemD_19⟩), (32, .pubkey ⟨oldMemD_22, oldMemD_24, oldMemD_26, oldMemD_28⟩), (64, .u64 oldMemD_11), (72, .blob [.byte (oldMemB_21), .gap fg1, .byte (oldMemB_8), .byte (oldMemB_31), .gap fg4])]
        (by simp [codecValid, FieldVal.fineValid, segsValid, FieldSeg.valid] <;> omega),
      codecCoarse_eq_fine (baseAddr + 10600)
        [(0, .pubkey ⟨oldMemD_12, oldMemD_14, oldMemD_16, oldMemD_18⟩), (32, .pubkey ⟨o5, o6, o7, o8⟩), (64, .u64 oldMemD_30), (72, .blob [.gap fg9, .byte (oldMemB_9), .gap fg11])]
        (by simp [codecValid, FieldVal.fineValid, segsValid, FieldSeg.valid] <;> omega),
      codecCoarse_eq_fine (baseAddr + 96)
        [(0, .pubkey ⟨oldMemD_13, oldMemD_15, oldMemD_17, oldMemD_19⟩), (32, .pubkey ⟨oldMemD_22, oldMemD_24, oldMemD_26, oldMemD_28⟩), (64, .u64 (oldMemD_11 - oldMemD_10)), (72, .blob [.byte (oldMemB_21), .gap fg1, .byte (oldMemB_8), .byte (oldMemB_31), .gap fg4])]
        (by simp [codecValid, FieldVal.fineValid, segsValid, FieldSeg.valid] <;> omega),
      codecCoarse_eq_fine (baseAddr + 10600)
        [(0, .pubkey ⟨oldMemD_12, oldMemD_14, oldMemD_16, oldMemD_18⟩), (32, .pubkey ⟨o5, o6, o7, o8⟩), (64, .u64 (oldMemD_30 + oldMemD_10)), (72, .blob [.gap fg9, .byte (oldMemB_9), .gap fg11])]
        (by simp [codecValid, FieldVal.fineValid, segsValid, FieldSeg.valid] <;> omega)]
  simp only [codecFine, FieldVal.fine, pubkeyIs, segsSL, FieldSeg.sl, FieldSeg.size, hfg1_sz, hfg9_sz, sepConj_emp_right_eq, Nat.add_zero, Nat.add_assoc, Nat.reduceAdd]
  have framed := cuTripleWithinMem_frame_right
    ( (effectiveAddr baseAddr 169 ↦Bytes fg1) **
      (effectiveAddr baseAddr 206 ↦Bytes fg4) **
      (effectiveAddr baseAddr 10632 ↦U64 o5) **
      (effectiveAddr baseAddr 10640 ↦U64 o6) **
      (effectiveAddr baseAddr 10648 ↦U64 o7) **
      (effectiveAddr baseAddr 10656 ↦U64 o8) **
      (effectiveAddr baseAddr 10672 ↦Bytes fg9) **
      (effectiveAddr baseAddr 10709 ↦Bytes fg11) )
    (by sl_pcfree) lift
  sl_exact framed

/-- qedgen `ensures`-shape for the `src` account, mechanically
    discharged: its `u64` field (offset 64) shifts by `oldMemD_10`. -/
theorem ensures_src
    (oldMemB_8 oldMemD_10 oldMemD_11 oldMemD_13 oldMemD_15 oldMemD_17 oldMemD_19 oldMemB_21 oldMemD_22 oldMemD_24 oldMemD_26 oldMemD_28 oldMemB_31 : Nat)
    (fg1 fg4 : ByteArray) :
    u64FieldAt 64 [(0, .pubkey ⟨oldMemD_13, oldMemD_15, oldMemD_17, oldMemD_19⟩), (32, .pubkey ⟨oldMemD_22, oldMemD_24, oldMemD_26, oldMemD_28⟩), (64, .u64 (oldMemD_11 - oldMemD_10)), (72, .blob [.byte (oldMemB_21), .gap fg1, .byte (oldMemB_8), .byte (oldMemB_31), .gap fg4])]
      = u64FieldAt 64 [(0, .pubkey ⟨oldMemD_13, oldMemD_15, oldMemD_17, oldMemD_19⟩), (32, .pubkey ⟨oldMemD_22, oldMemD_24, oldMemD_26, oldMemD_28⟩), (64, .u64 oldMemD_11), (72, .blob [.byte (oldMemB_21), .gap fg1, .byte (oldMemB_8), .byte (oldMemB_31), .gap fg4])] - oldMemD_10 := by
  qedsvm_discharge

/-- qedgen `ensures`-shape for the `dst` account, mechanically
    discharged: its `u64` field (offset 64) shifts by `oldMemD_10`. -/
theorem ensures_dst
    (oldMemB_9 oldMemD_10 oldMemD_12 oldMemD_14 oldMemD_16 oldMemD_18 oldMemD_30 o5 o6 o7 o8 : Nat)
    (fg9 fg11 : ByteArray) :
    u64FieldAt 64 [(0, .pubkey ⟨oldMemD_12, oldMemD_14, oldMemD_16, oldMemD_18⟩), (32, .pubkey ⟨o5, o6, o7, o8⟩), (64, .u64 (oldMemD_30 + oldMemD_10)), (72, .blob [.gap fg9, .byte (oldMemB_9), .gap fg11])]
      = u64FieldAt 64 [(0, .pubkey ⟨oldMemD_12, oldMemD_14, oldMemD_16, oldMemD_18⟩), (32, .pubkey ⟨o5, o6, o7, o8⟩), (64, .u64 oldMemD_30), (72, .blob [.gap fg9, .byte (oldMemB_9), .gap fg11])] + oldMemD_10 := by
  qedsvm_discharge

end Examples.PTokenTransferRefinement
