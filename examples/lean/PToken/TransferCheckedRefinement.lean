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
import Generated.PTokenTransferCheckedTracedLifted

namespace Examples.PTokenTransferCheckedRefinement
open SVM SVM.SBPF SVM.SBPF.Memory

set_option maxHeartbeats 1600000 in
theorem refines_asm
    (cr : CodeReq) (rr : Memory.RegionTable → Prop)
    (baseAddr oldMemB_0 vR2Old oldMemD_1 oldMemB_2 oldMemD_3 oldMemB_4 oldMemD_5 oldMemB_6 oldMemD_7 vR4Old vR5Old oldMemD_8 oldMemB_9 vR6Old vR7Old oldMemB_10 oldMemB_11 vR3Old oldMemD_12 oldMemD_13 oldMemD_14 vR0Old oldMemD_15 oldMemD_16 vR8Old oldMemD_17 vR10Old oldMemD_18 oldMemD_19 oldMemD_20 vR9Old oldMemD_21 oldMemD_22 oldMemD_23 oldMemD_24 oldMemD_25 oldMemD_26 oldMemB_27 oldMemB_28 oldMemB_29 oldMemD_30 oldMemB_31 oldMemD_32 oldMemD_33 oldMemD_34 oldMemD_35 oldMemD_36 oldMemD_37 oldMemD_38 oldMemB_39 oldMemD_40 oldMemB_41 o5 o6 o7 o8 : Nat)
    (fg1 fg4 fg9 fg11 : ByteArray)
    (h_b0 : oldMemB_31 < 256)
    (h_b2 : oldMemB_10 < 256)
    (h_b3 : oldMemB_41 < 256)
    (h_b10 : oldMemB_11 < 256)
    (hfg1_sz : fg1.size = 35)
    (hfg9_sz : fg9.size = 36)
    (lift : cuTripleWithinMem 104 0 198 3542 cr
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦ₘ oldMemB_0) **
      (.r2 ↦ᵣ vR2Old) **
      (effectiveAddr baseAddr 88 ↦U64 oldMemD_1) **
      (effectiveAddr baseAddr 10512 ↦ₘ oldMemB_2) **
      (effectiveAddr baseAddr 10592 ↦U64 oldMemD_3) **
      (effectiveAddr baseAddr 20936 ↦ₘ oldMemB_4) **
      (effectiveAddr baseAddr 21016 ↦U64 oldMemD_5) **
      (effectiveAddr baseAddr 31440 ↦ₘ oldMemB_6) **
      (effectiveAddr baseAddr 31520 ↦U64 oldMemD_7) **
      (.r4 ↦ᵣ vR4Old) **
      (.r5 ↦ᵣ vR5Old) **
      (effectiveAddr addr0 0 ↦U64 oldMemD_8) **
      (effectiveAddr addr1 0 ↦ₘ oldMemB_9) **
      (.r6 ↦ᵣ vR6Old) **
      (.r7 ↦ᵣ vR7Old) **
      (effectiveAddr baseAddr 204 ↦ₘ oldMemB_10) **
      (effectiveAddr baseAddr 21132 ↦ₘ oldMemB_11) **
      (.r3 ↦ᵣ vR3Old) **
      (effectiveAddr addr2 0 ↦U64 oldMemD_12) **
      (effectiveAddr baseAddr 160 ↦U64 oldMemD_13) **
      (effectiveAddr baseAddr 96 ↦U64 oldMemD_14) **
      (.r0 ↦ᵣ vR0Old) **
      (effectiveAddr baseAddr 21024 ↦U64 oldMemD_15) **
      (effectiveAddr baseAddr 104 ↦U64 oldMemD_16) **
      (.r8 ↦ᵣ vR8Old) **
      (effectiveAddr baseAddr 21032 ↦U64 oldMemD_17) **
      (.r10 ↦ᵣ vR10Old) **
      (effectiveAddr vR10Old (-2080) ↦U64 oldMemD_18) **
      (effectiveAddr baseAddr 112 ↦U64 oldMemD_19) **
      (effectiveAddr baseAddr 21040 ↦U64 oldMemD_20) **
      (.r9 ↦ᵣ vR9Old) **
      (effectiveAddr baseAddr 120 ↦U64 oldMemD_21) **
      (effectiveAddr baseAddr 21048 ↦U64 oldMemD_22) **
      (effectiveAddr baseAddr 10520 ↦U64 oldMemD_23) **
      (effectiveAddr baseAddr 10528 ↦U64 oldMemD_24) **
      (effectiveAddr baseAddr 10536 ↦U64 oldMemD_25) **
      (effectiveAddr baseAddr 10544 ↦U64 oldMemD_26) **
      (effectiveAddr baseAddr 10645 ↦ₘ oldMemB_27) **
      (effectiveAddr addr3 0 ↦ₘ oldMemB_28) **
      (effectiveAddr baseAddr 10644 ↦ₘ oldMemB_29) **
      (effectiveAddr baseAddr 31448 ↦U64 oldMemD_30) **
      (effectiveAddr baseAddr 168 ↦ₘ oldMemB_31) **
      (effectiveAddr baseAddr 128 ↦U64 oldMemD_32) **
      (effectiveAddr baseAddr 31456 ↦U64 oldMemD_33) **
      (effectiveAddr baseAddr 136 ↦U64 oldMemD_34) **
      (effectiveAddr baseAddr 31464 ↦U64 oldMemD_35) **
      (effectiveAddr baseAddr 144 ↦U64 oldMemD_36) **
      (effectiveAddr baseAddr 31472 ↦U64 oldMemD_37) **
      (effectiveAddr baseAddr 152 ↦U64 oldMemD_38) **
      (effectiveAddr baseAddr 31441 ↦ₘ oldMemB_39) **
      (effectiveAddr baseAddr 21088 ↦U64 oldMemD_40) **
      (effectiveAddr baseAddr 205 ↦ₘ oldMemB_41))
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦ₘ oldMemB_0) **
      (.r2 ↦ᵣ oldMemD_12) **
      (effectiveAddr baseAddr 88 ↦U64 oldMemD_1) **
      (effectiveAddr baseAddr 10512 ↦ₘ oldMemB_2) **
      (effectiveAddr baseAddr 10592 ↦U64 oldMemD_3) **
      (effectiveAddr baseAddr 20936 ↦ₘ oldMemB_4) **
      (effectiveAddr baseAddr 21016 ↦U64 oldMemD_5) **
      (effectiveAddr baseAddr 31440 ↦ₘ oldMemB_6) **
      (effectiveAddr baseAddr 31520 ↦U64 oldMemD_7) **
      (.r4 ↦ᵣ oldMemD_7) **
      (.r5 ↦ᵣ oldMemD_38) **
      (effectiveAddr addr0 0 ↦U64 oldMemD_8) **
      (effectiveAddr addr1 0 ↦ₘ oldMemB_9) **
      (.r6 ↦ᵣ toU64 0) **
      (.r7 ↦ᵣ toU64 4) **
      (effectiveAddr baseAddr 204 ↦ₘ oldMemB_10) **
      (effectiveAddr baseAddr 21132 ↦ₘ oldMemB_11) **
      (.r3 ↦ᵣ oldMemB_41 % 256) **
      (effectiveAddr addr2 0 ↦U64 oldMemD_12) **
      (effectiveAddr baseAddr 160 ↦U64 oldMemD_13 - oldMemD_12) **
      (effectiveAddr baseAddr 96 ↦U64 oldMemD_14) **
      (.r0 ↦ᵣ toU64 0) **
      (effectiveAddr baseAddr 21024 ↦U64 oldMemD_15) **
      (effectiveAddr baseAddr 104 ↦U64 oldMemD_16) **
      (.r8 ↦ᵣ oldMemD_16) **
      (effectiveAddr baseAddr 21032 ↦U64 oldMemD_17) **
      (.r10 ↦ᵣ vR10Old) **
      (effectiveAddr vR10Old (-2080) ↦U64 oldMemD_13) **
      (effectiveAddr baseAddr 112 ↦U64 oldMemD_19) **
      (effectiveAddr baseAddr 21040 ↦U64 oldMemD_20) **
      (.r9 ↦ᵣ oldMemD_21) **
      (effectiveAddr baseAddr 120 ↦U64 oldMemD_21) **
      (effectiveAddr baseAddr 21048 ↦U64 oldMemD_22) **
      (effectiveAddr baseAddr 10520 ↦U64 oldMemD_23) **
      (effectiveAddr baseAddr 10528 ↦U64 oldMemD_24) **
      (effectiveAddr baseAddr 10536 ↦U64 oldMemD_25) **
      (effectiveAddr baseAddr 10544 ↦U64 oldMemD_26) **
      (effectiveAddr baseAddr 10645 ↦ₘ oldMemB_27) **
      (effectiveAddr addr3 0 ↦ₘ oldMemB_28) **
      (effectiveAddr baseAddr 10644 ↦ₘ oldMemB_29) **
      (effectiveAddr baseAddr 31448 ↦U64 oldMemD_30) **
      (effectiveAddr baseAddr 168 ↦ₘ oldMemB_31) **
      (effectiveAddr baseAddr 128 ↦U64 oldMemD_32) **
      (effectiveAddr baseAddr 31456 ↦U64 oldMemD_33) **
      (effectiveAddr baseAddr 136 ↦U64 oldMemD_34) **
      (effectiveAddr baseAddr 31464 ↦U64 oldMemD_35) **
      (effectiveAddr baseAddr 144 ↦U64 oldMemD_36) **
      (effectiveAddr baseAddr 31472 ↦U64 oldMemD_37) **
      (effectiveAddr baseAddr 152 ↦U64 oldMemD_38) **
      (effectiveAddr baseAddr 31441 ↦ₘ oldMemB_39) **
      (effectiveAddr baseAddr 21088 ↦U64 oldMemD_40 + oldMemD_12) **
      (effectiveAddr baseAddr 205 ↦ₘ oldMemB_41)) rr) :
    SVM.Solana.Abstract.AsmRefinesFieldUpdates cr 104 0 198 3542 rr
      [((baseAddr + 96),
        [(0, .pubkey ⟨oldMemD_14, oldMemD_16, oldMemD_19, oldMemD_21⟩), (32, .pubkey ⟨oldMemD_32, oldMemD_34, oldMemD_36, oldMemD_38⟩), (64, .u64 oldMemD_13), (72, .blob [.byte (oldMemB_31), .gap fg1, .byte (oldMemB_10), .byte (oldMemB_41), .gap fg4])],
        [(0, .pubkey ⟨oldMemD_14, oldMemD_16, oldMemD_19, oldMemD_21⟩), (32, .pubkey ⟨oldMemD_32, oldMemD_34, oldMemD_36, oldMemD_38⟩), (64, .u64 (oldMemD_13 - oldMemD_12)), (72, .blob [.byte (oldMemB_31), .gap fg1, .byte (oldMemB_10), .byte (oldMemB_41), .gap fg4])]),
       ((baseAddr + 21024),
        [(0, .pubkey ⟨oldMemD_15, oldMemD_17, oldMemD_20, oldMemD_22⟩), (32, .pubkey ⟨o5, o6, o7, o8⟩), (64, .u64 oldMemD_40), (72, .blob [.gap fg9, .byte (oldMemB_11), .gap fg11])],
        [(0, .pubkey ⟨oldMemD_15, oldMemD_17, oldMemD_20, oldMemD_22⟩), (32, .pubkey ⟨o5, o6, o7, o8⟩), (64, .u64 (oldMemD_40 + oldMemD_12)), (72, .blob [.gap fg9, .byte (oldMemB_11), .gap fg11])])]
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦ₘ oldMemB_0) **
      (.r2 ↦ᵣ vR2Old) **
      (effectiveAddr baseAddr 88 ↦U64 oldMemD_1) **
      (effectiveAddr baseAddr 10512 ↦ₘ oldMemB_2) **
      (effectiveAddr baseAddr 10592 ↦U64 oldMemD_3) **
      (effectiveAddr baseAddr 20936 ↦ₘ oldMemB_4) **
      (effectiveAddr baseAddr 21016 ↦U64 oldMemD_5) **
      (effectiveAddr baseAddr 31440 ↦ₘ oldMemB_6) **
      (effectiveAddr baseAddr 31520 ↦U64 oldMemD_7) **
      (.r4 ↦ᵣ vR4Old) **
      (.r5 ↦ᵣ vR5Old) **
      (effectiveAddr addr0 0 ↦U64 oldMemD_8) **
      (effectiveAddr addr1 0 ↦ₘ oldMemB_9) **
      (.r6 ↦ᵣ vR6Old) **
      (.r7 ↦ᵣ vR7Old) **
      (.r3 ↦ᵣ vR3Old) **
      (effectiveAddr addr2 0 ↦U64 oldMemD_12) **
      (.r0 ↦ᵣ vR0Old) **
      (.r8 ↦ᵣ vR8Old) **
      (.r10 ↦ᵣ vR10Old) **
      (effectiveAddr vR10Old (-2080) ↦U64 oldMemD_18) **
      (.r9 ↦ᵣ vR9Old) **
      (effectiveAddr baseAddr 10520 ↦U64 oldMemD_23) **
      (effectiveAddr baseAddr 10528 ↦U64 oldMemD_24) **
      (effectiveAddr baseAddr 10536 ↦U64 oldMemD_25) **
      (effectiveAddr baseAddr 10544 ↦U64 oldMemD_26) **
      (effectiveAddr baseAddr 10645 ↦ₘ oldMemB_27) **
      (effectiveAddr addr3 0 ↦ₘ oldMemB_28) **
      (effectiveAddr baseAddr 10644 ↦ₘ oldMemB_29) **
      (effectiveAddr baseAddr 31448 ↦U64 oldMemD_30) **
      (effectiveAddr baseAddr 31456 ↦U64 oldMemD_33) **
      (effectiveAddr baseAddr 31464 ↦U64 oldMemD_35) **
      (effectiveAddr baseAddr 31472 ↦U64 oldMemD_37) **
      (effectiveAddr baseAddr 31441 ↦ₘ oldMemB_39))
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦ₘ oldMemB_0) **
      (.r2 ↦ᵣ oldMemD_12) **
      (effectiveAddr baseAddr 88 ↦U64 oldMemD_1) **
      (effectiveAddr baseAddr 10512 ↦ₘ oldMemB_2) **
      (effectiveAddr baseAddr 10592 ↦U64 oldMemD_3) **
      (effectiveAddr baseAddr 20936 ↦ₘ oldMemB_4) **
      (effectiveAddr baseAddr 21016 ↦U64 oldMemD_5) **
      (effectiveAddr baseAddr 31440 ↦ₘ oldMemB_6) **
      (effectiveAddr baseAddr 31520 ↦U64 oldMemD_7) **
      (.r4 ↦ᵣ oldMemD_7) **
      (.r5 ↦ᵣ oldMemD_38) **
      (effectiveAddr addr0 0 ↦U64 oldMemD_8) **
      (effectiveAddr addr1 0 ↦ₘ oldMemB_9) **
      (.r6 ↦ᵣ toU64 0) **
      (.r7 ↦ᵣ toU64 4) **
      (.r3 ↦ᵣ oldMemB_41 % 256) **
      (effectiveAddr addr2 0 ↦U64 oldMemD_12) **
      (.r0 ↦ᵣ toU64 0) **
      (.r8 ↦ᵣ oldMemD_16) **
      (.r10 ↦ᵣ vR10Old) **
      (effectiveAddr vR10Old (-2080) ↦U64 oldMemD_13) **
      (.r9 ↦ᵣ oldMemD_21) **
      (effectiveAddr baseAddr 10520 ↦U64 oldMemD_23) **
      (effectiveAddr baseAddr 10528 ↦U64 oldMemD_24) **
      (effectiveAddr baseAddr 10536 ↦U64 oldMemD_25) **
      (effectiveAddr baseAddr 10544 ↦U64 oldMemD_26) **
      (effectiveAddr baseAddr 10645 ↦ₘ oldMemB_27) **
      (effectiveAddr addr3 0 ↦ₘ oldMemB_28) **
      (effectiveAddr baseAddr 10644 ↦ₘ oldMemB_29) **
      (effectiveAddr baseAddr 31448 ↦U64 oldMemD_30) **
      (effectiveAddr baseAddr 31456 ↦U64 oldMemD_33) **
      (effectiveAddr baseAddr 31464 ↦U64 oldMemD_35) **
      (effectiveAddr baseAddr 31472 ↦U64 oldMemD_37) **
      (effectiveAddr baseAddr 31441 ↦ₘ oldMemB_39)) := by
  unfold SVM.Solana.Abstract.AsmRefinesFieldUpdates
  simp only [SVM.Solana.Abstract.codecsPre, SVM.Solana.Abstract.codecsPost]
  rw [codecCoarse_eq_fine (baseAddr + 96)
        [(0, .pubkey ⟨oldMemD_14, oldMemD_16, oldMemD_19, oldMemD_21⟩), (32, .pubkey ⟨oldMemD_32, oldMemD_34, oldMemD_36, oldMemD_38⟩), (64, .u64 oldMemD_13), (72, .blob [.byte (oldMemB_31), .gap fg1, .byte (oldMemB_10), .byte (oldMemB_41), .gap fg4])]
        (by simp [codecValid, FieldVal.fineValid, segsValid, FieldSeg.valid] <;> omega),
      codecCoarse_eq_fine (baseAddr + 21024)
        [(0, .pubkey ⟨oldMemD_15, oldMemD_17, oldMemD_20, oldMemD_22⟩), (32, .pubkey ⟨o5, o6, o7, o8⟩), (64, .u64 oldMemD_40), (72, .blob [.gap fg9, .byte (oldMemB_11), .gap fg11])]
        (by simp [codecValid, FieldVal.fineValid, segsValid, FieldSeg.valid] <;> omega),
      codecCoarse_eq_fine (baseAddr + 96)
        [(0, .pubkey ⟨oldMemD_14, oldMemD_16, oldMemD_19, oldMemD_21⟩), (32, .pubkey ⟨oldMemD_32, oldMemD_34, oldMemD_36, oldMemD_38⟩), (64, .u64 (oldMemD_13 - oldMemD_12)), (72, .blob [.byte (oldMemB_31), .gap fg1, .byte (oldMemB_10), .byte (oldMemB_41), .gap fg4])]
        (by simp [codecValid, FieldVal.fineValid, segsValid, FieldSeg.valid] <;> omega),
      codecCoarse_eq_fine (baseAddr + 21024)
        [(0, .pubkey ⟨oldMemD_15, oldMemD_17, oldMemD_20, oldMemD_22⟩), (32, .pubkey ⟨o5, o6, o7, o8⟩), (64, .u64 (oldMemD_40 + oldMemD_12)), (72, .blob [.gap fg9, .byte (oldMemB_11), .gap fg11])]
        (by simp [codecValid, FieldVal.fineValid, segsValid, FieldSeg.valid] <;> omega)]
  simp only [codecFine, FieldVal.fine, pubkeyIs, segsSL, FieldSeg.sl, FieldSeg.size, hfg1_sz, hfg9_sz, sepConj_emp_right_eq, Nat.add_zero, Nat.add_assoc, Nat.reduceAdd]
  have framed := cuTripleWithinMem_frame_right
    ( (effectiveAddr baseAddr 169 ↦Bytes fg1) **
      (effectiveAddr baseAddr 206 ↦Bytes fg4) **
      (effectiveAddr baseAddr 21056 ↦U64 o5) **
      (effectiveAddr baseAddr 21064 ↦U64 o6) **
      (effectiveAddr baseAddr 21072 ↦U64 o7) **
      (effectiveAddr baseAddr 21080 ↦U64 o8) **
      (effectiveAddr baseAddr 21096 ↦Bytes fg9) **
      (effectiveAddr baseAddr 21133 ↦Bytes fg11) )
    (by sl_pcfree) lift
  sl_exact framed

/-- qedgen `ensures`-shape for the `src` account, mechanically
    discharged: its `u64` field (offset 64) shifts by `oldMemD_12`. -/
theorem ensures_src
    (oldMemB_10 oldMemD_12 oldMemD_13 oldMemD_14 oldMemD_16 oldMemD_19 oldMemD_21 oldMemB_31 oldMemD_32 oldMemD_34 oldMemD_36 oldMemD_38 oldMemB_41 : Nat)
    (fg1 fg4 : ByteArray) :
    u64FieldAt 64 [(0, .pubkey ⟨oldMemD_14, oldMemD_16, oldMemD_19, oldMemD_21⟩), (32, .pubkey ⟨oldMemD_32, oldMemD_34, oldMemD_36, oldMemD_38⟩), (64, .u64 (oldMemD_13 - oldMemD_12)), (72, .blob [.byte (oldMemB_31), .gap fg1, .byte (oldMemB_10), .byte (oldMemB_41), .gap fg4])]
      = u64FieldAt 64 [(0, .pubkey ⟨oldMemD_14, oldMemD_16, oldMemD_19, oldMemD_21⟩), (32, .pubkey ⟨oldMemD_32, oldMemD_34, oldMemD_36, oldMemD_38⟩), (64, .u64 oldMemD_13), (72, .blob [.byte (oldMemB_31), .gap fg1, .byte (oldMemB_10), .byte (oldMemB_41), .gap fg4])] - oldMemD_12 := by
  qedsvm_discharge

/-- qedgen `ensures`-shape for the `dst` account, mechanically
    discharged: its `u64` field (offset 64) shifts by `oldMemD_12`. -/
theorem ensures_dst
    (oldMemB_11 oldMemD_12 oldMemD_15 oldMemD_17 oldMemD_20 oldMemD_22 oldMemD_40 o5 o6 o7 o8 : Nat)
    (fg9 fg11 : ByteArray) :
    u64FieldAt 64 [(0, .pubkey ⟨oldMemD_15, oldMemD_17, oldMemD_20, oldMemD_22⟩), (32, .pubkey ⟨o5, o6, o7, o8⟩), (64, .u64 (oldMemD_40 + oldMemD_12)), (72, .blob [.gap fg9, .byte (oldMemB_11), .gap fg11])]
      = u64FieldAt 64 [(0, .pubkey ⟨oldMemD_15, oldMemD_17, oldMemD_20, oldMemD_22⟩), (32, .pubkey ⟨o5, o6, o7, o8⟩), (64, .u64 oldMemD_40), (72, .blob [.gap fg9, .byte (oldMemB_11), .gap fg11])] + oldMemD_12 := by
  qedsvm_discharge

end Examples.PTokenTransferCheckedRefinement
