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
import Generated.PTokenMintToTracedLifted

namespace Examples.PTokenMintToRefinement
open SVM SVM.SBPF SVM.SBPF.Memory

set_option maxHeartbeats 1600000 in
theorem refines_asm
    (cr : CodeReq) (rr : Memory.RegionTable → Prop)
    (baseAddr oldMemB_0 vR2Old oldMemD_1 vR0Old oldMemB_2 oldMemB_3 oldMemB_4 oldMemB_5 oldMemB_6 oldMemB_7 oldMemB_8 vR7Old vR10Old oldMemD_9 vR3Old oldMemB_10 oldMemD_11 oldMemD_12 oldMemB_13 oldMemD_14 oldMemD_15 vR4Old oldMemD_16 vR9Old oldMemB_17 vR5Old vR8Old vR6Old oldMemB_18 oldMemB_19 oldMemD_20 oldMemD_21 oldMemD_22 oldMemD_23 oldMemD_24 oldMemD_25 oldMemD_26 oldMemD_27 oldMemB_28 oldMemB_29 oldMemD_30 oldMemD_31 oldMemD_32 oldMemD_33 oldMemD_34 oldMemD_35 oldMemD_36 oldMemD_37 oldMemD_38 oldMemB_39 oldMemD_40 oldMemD_41 o5 o6 o7 o8 : Nat)
    (fg1 fg2 fg4 fg9 fg12 : ByteArray)
    (h_b0 : oldMemB_29 < 256)
    (h_b3 : oldMemB_28 < 256)
    (h_b10 : oldMemB_18 < 256)
    (h_b11 : oldMemB_19 < 256)
    (hfg1_sz : fg1.size = 3)
    (hfg2_sz : fg2.size = 1)
    (hfg9_sz : fg9.size = 36)
    (lift : cuTripleWithinMem 119 0 198 3542 cr
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦ₘ oldMemB_0) **
      (.r2 ↦ᵣ vR2Old) **
      (effectiveAddr baseAddr 88 ↦U64 oldMemD_1) **
      (.r0 ↦ᵣ vR0Old) **
      (effectiveAddr baseAddr 0 + 1 ↦ₘ oldMemB_2) **
      (effectiveAddr baseAddr 0 + 2 ↦ₘ oldMemB_3) **
      (effectiveAddr baseAddr 0 + 3 ↦ₘ oldMemB_4) **
      (effectiveAddr baseAddr 0 + 4 ↦ₘ oldMemB_5) **
      (effectiveAddr baseAddr 0 + 5 ↦ₘ oldMemB_6) **
      (effectiveAddr baseAddr 0 + 6 ↦ₘ oldMemB_7) **
      (effectiveAddr baseAddr 0 + 7 ↦ₘ oldMemB_8) **
      (.r7 ↦ᵣ vR7Old) **
      (.r10 ↦ᵣ vR10Old) **
      (effectiveAddr vR10Old (-2072) ↦U64 oldMemD_9) **
      (.r3 ↦ᵣ vR3Old) **
      (effectiveAddr addr0 0 ↦ₘ oldMemB_10) **
      (effectiveAddr addr1 8 ↦U64 oldMemD_11) **
      (effectiveAddr addr0 80 ↦U64 oldMemD_12) **
      (effectiveAddr addr2 0 ↦ₘ oldMemB_13) **
      (effectiveAddr addr1 16 ↦U64 oldMemD_14) **
      (effectiveAddr addr2 80 ↦U64 oldMemD_15) **
      (.r4 ↦ᵣ vR4Old) **
      (effectiveAddr addr3 0 ↦U64 oldMemD_16) **
      (.r9 ↦ᵣ vR9Old) **
      (effectiveAddr addr3 8 ↦ₘ oldMemB_17) **
      (.r5 ↦ᵣ vR5Old) **
      (.r8 ↦ᵣ vR8Old) **
      (.r6 ↦ᵣ vR6Old) **
      (effectiveAddr addr0 196 ↦ₘ oldMemB_18) **
      (effectiveAddr addr0 197 ↦ₘ oldMemB_19) **
      (effectiveAddr addr0 88 ↦U64 oldMemD_20) **
      (effectiveAddr addr4 8 ↦U64 oldMemD_21) **
      (effectiveAddr addr0 96 ↦U64 oldMemD_22) **
      (effectiveAddr addr4 16 ↦U64 oldMemD_23) **
      (effectiveAddr addr0 104 ↦U64 oldMemD_24) **
      (effectiveAddr addr4 24 ↦U64 oldMemD_25) **
      (effectiveAddr addr0 112 ↦U64 oldMemD_26) **
      (effectiveAddr addr4 32 ↦U64 oldMemD_27) **
      (effectiveAddr addr4 133 ↦ₘ oldMemB_28) **
      (effectiveAddr addr4 88 ↦ₘ oldMemB_29) **
      (effectiveAddr addr2 8 ↦U64 oldMemD_30) **
      (effectiveAddr addr4 92 ↦U64 oldMemD_31) **
      (effectiveAddr addr2 16 ↦U64 oldMemD_32) **
      (effectiveAddr addr4 100 ↦U64 oldMemD_33) **
      (effectiveAddr addr2 24 ↦U64 oldMemD_34) **
      (effectiveAddr addr4 108 ↦U64 oldMemD_35) **
      (effectiveAddr addr2 32 ↦U64 oldMemD_36) **
      (effectiveAddr addr4 116 ↦U64 oldMemD_37) **
      (effectiveAddr addr5 0 ↦U64 oldMemD_38) **
      (effectiveAddr addr2 1 ↦ₘ oldMemB_39) **
      (effectiveAddr addr4 124 ↦U64 oldMemD_40) **
      (effectiveAddr addr0 152 ↦U64 oldMemD_41))
      ((.r1 ↦ᵣ wrapAdd oldMemD_41 oldMemD_38) **
      (effectiveAddr baseAddr 0 ↦ₘ oldMemB_0) **
      (.r2 ↦ᵣ ((toU64 0) &&& toU64 1) % U64_MODULUS) **
      (effectiveAddr baseAddr 88 ↦U64 oldMemD_1) **
      (.r0 ↦ᵣ toU64 0) **
      (effectiveAddr baseAddr 0 + 1 ↦ₘ oldMemB_2) **
      (effectiveAddr baseAddr 0 + 2 ↦ₘ oldMemB_3) **
      (effectiveAddr baseAddr 0 + 3 ↦ₘ oldMemB_4) **
      (effectiveAddr baseAddr 0 + 4 ↦ₘ oldMemB_5) **
      (effectiveAddr baseAddr 0 + 5 ↦ₘ oldMemB_6) **
      (effectiveAddr baseAddr 0 + 6 ↦ₘ oldMemB_7) **
      (effectiveAddr baseAddr 0 + 7 ↦ₘ oldMemB_8) **
      (.r7 ↦ᵣ addr4) **
      (.r10 ↦ᵣ vR10Old) **
      (effectiveAddr vR10Old (-2072) ↦U64 addr4) **
      (.r3 ↦ᵣ addr0) **
      (effectiveAddr addr0 0 ↦ₘ oldMemB_10) **
      (effectiveAddr addr1 8 ↦U64 addr0) **
      (effectiveAddr addr0 80 ↦U64 oldMemD_12) **
      (effectiveAddr addr2 0 ↦ₘ oldMemB_13) **
      (effectiveAddr addr1 16 ↦U64 addr2) **
      (effectiveAddr addr2 80 ↦U64 oldMemD_15) **
      (.r4 ↦ᵣ oldMemD_38) **
      (effectiveAddr addr3 0 ↦U64 oldMemD_16) **
      (.r9 ↦ᵣ toU64 4) **
      (effectiveAddr addr3 8 ↦ₘ oldMemB_17) **
      (.r5 ↦ᵣ oldMemD_40) **
      (.r8 ↦ᵣ addr5) **
      (.r6 ↦ᵣ toU64 0) **
      (effectiveAddr addr0 196 ↦ₘ oldMemB_18) **
      (effectiveAddr addr0 197 ↦ₘ oldMemB_19) **
      (effectiveAddr addr0 88 ↦U64 oldMemD_20) **
      (effectiveAddr addr4 8 ↦U64 oldMemD_21) **
      (effectiveAddr addr0 96 ↦U64 oldMemD_22) **
      (effectiveAddr addr4 16 ↦U64 oldMemD_23) **
      (effectiveAddr addr0 104 ↦U64 oldMemD_24) **
      (effectiveAddr addr4 24 ↦U64 oldMemD_25) **
      (effectiveAddr addr0 112 ↦U64 oldMemD_26) **
      (effectiveAddr addr4 32 ↦U64 oldMemD_27) **
      (effectiveAddr addr4 133 ↦ₘ oldMemB_28) **
      (effectiveAddr addr4 88 ↦ₘ oldMemB_29) **
      (effectiveAddr addr2 8 ↦U64 oldMemD_30) **
      (effectiveAddr addr4 92 ↦U64 oldMemD_31) **
      (effectiveAddr addr2 16 ↦U64 oldMemD_32) **
      (effectiveAddr addr4 100 ↦U64 oldMemD_33) **
      (effectiveAddr addr2 24 ↦U64 oldMemD_34) **
      (effectiveAddr addr4 108 ↦U64 oldMemD_35) **
      (effectiveAddr addr2 32 ↦U64 oldMemD_36) **
      (effectiveAddr addr4 116 ↦U64 oldMemD_37) **
      (effectiveAddr addr5 0 ↦U64 oldMemD_38) **
      (effectiveAddr addr2 1 ↦ₘ oldMemB_39) **
      (effectiveAddr addr4 124 ↦U64 oldMemD_40 + oldMemD_38) **
      (effectiveAddr addr0 152 ↦U64 oldMemD_41 + oldMemD_38)) rr) :
    SVM.Solana.Abstract.AsmRefinesFieldUpdates cr 119 0 198 3542 rr
      [((addr4 + 88),
        [(0, .blob [.byte (oldMemB_29), .gap fg1, .u64 (oldMemD_31), .u64 (oldMemD_33), .u64 (oldMemD_35), .u64 (oldMemD_37)]), (36, .u64 oldMemD_40), (44, .blob [.gap fg2, .byte (oldMemB_28), .gap fg4])],
        [(0, .blob [.byte (oldMemB_29), .gap fg1, .u64 (oldMemD_31), .u64 (oldMemD_33), .u64 (oldMemD_35), .u64 (oldMemD_37)]), (36, .u64 (oldMemD_40 + oldMemD_38)), (44, .blob [.gap fg2, .byte (oldMemB_28), .gap fg4])]),
       ((addr0 + 88),
        [(0, .pubkey ⟨oldMemD_20, oldMemD_22, oldMemD_24, oldMemD_26⟩), (32, .pubkey ⟨o5, o6, o7, o8⟩), (64, .u64 oldMemD_41), (72, .blob [.gap fg9, .byte (oldMemB_18), .byte (oldMemB_19), .gap fg12])],
        [(0, .pubkey ⟨oldMemD_20, oldMemD_22, oldMemD_24, oldMemD_26⟩), (32, .pubkey ⟨o5, o6, o7, o8⟩), (64, .u64 (oldMemD_41 + oldMemD_38)), (72, .blob [.gap fg9, .byte (oldMemB_18), .byte (oldMemB_19), .gap fg12])])]
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦ₘ oldMemB_0) **
      (.r2 ↦ᵣ vR2Old) **
      (effectiveAddr baseAddr 88 ↦U64 oldMemD_1) **
      (.r0 ↦ᵣ vR0Old) **
      (effectiveAddr baseAddr 0 + 1 ↦ₘ oldMemB_2) **
      (effectiveAddr baseAddr 0 + 2 ↦ₘ oldMemB_3) **
      (effectiveAddr baseAddr 0 + 3 ↦ₘ oldMemB_4) **
      (effectiveAddr baseAddr 0 + 4 ↦ₘ oldMemB_5) **
      (effectiveAddr baseAddr 0 + 5 ↦ₘ oldMemB_6) **
      (effectiveAddr baseAddr 0 + 6 ↦ₘ oldMemB_7) **
      (effectiveAddr baseAddr 0 + 7 ↦ₘ oldMemB_8) **
      (.r7 ↦ᵣ vR7Old) **
      (.r10 ↦ᵣ vR10Old) **
      (effectiveAddr vR10Old (-2072) ↦U64 oldMemD_9) **
      (.r3 ↦ᵣ vR3Old) **
      (effectiveAddr addr0 0 ↦ₘ oldMemB_10) **
      (effectiveAddr addr1 8 ↦U64 oldMemD_11) **
      (effectiveAddr addr0 80 ↦U64 oldMemD_12) **
      (effectiveAddr addr2 0 ↦ₘ oldMemB_13) **
      (effectiveAddr addr1 16 ↦U64 oldMemD_14) **
      (effectiveAddr addr2 80 ↦U64 oldMemD_15) **
      (.r4 ↦ᵣ vR4Old) **
      (effectiveAddr addr3 0 ↦U64 oldMemD_16) **
      (.r9 ↦ᵣ vR9Old) **
      (effectiveAddr addr3 8 ↦ₘ oldMemB_17) **
      (.r5 ↦ᵣ vR5Old) **
      (.r8 ↦ᵣ vR8Old) **
      (.r6 ↦ᵣ vR6Old) **
      (effectiveAddr addr4 8 ↦U64 oldMemD_21) **
      (effectiveAddr addr4 16 ↦U64 oldMemD_23) **
      (effectiveAddr addr4 24 ↦U64 oldMemD_25) **
      (effectiveAddr addr4 32 ↦U64 oldMemD_27) **
      (effectiveAddr addr2 8 ↦U64 oldMemD_30) **
      (effectiveAddr addr2 16 ↦U64 oldMemD_32) **
      (effectiveAddr addr2 24 ↦U64 oldMemD_34) **
      (effectiveAddr addr2 32 ↦U64 oldMemD_36) **
      (effectiveAddr addr5 0 ↦U64 oldMemD_38) **
      (effectiveAddr addr2 1 ↦ₘ oldMemB_39))
      ((.r1 ↦ᵣ wrapAdd oldMemD_41 oldMemD_38) **
      (effectiveAddr baseAddr 0 ↦ₘ oldMemB_0) **
      (.r2 ↦ᵣ ((toU64 0) &&& toU64 1) % U64_MODULUS) **
      (effectiveAddr baseAddr 88 ↦U64 oldMemD_1) **
      (.r0 ↦ᵣ toU64 0) **
      (effectiveAddr baseAddr 0 + 1 ↦ₘ oldMemB_2) **
      (effectiveAddr baseAddr 0 + 2 ↦ₘ oldMemB_3) **
      (effectiveAddr baseAddr 0 + 3 ↦ₘ oldMemB_4) **
      (effectiveAddr baseAddr 0 + 4 ↦ₘ oldMemB_5) **
      (effectiveAddr baseAddr 0 + 5 ↦ₘ oldMemB_6) **
      (effectiveAddr baseAddr 0 + 6 ↦ₘ oldMemB_7) **
      (effectiveAddr baseAddr 0 + 7 ↦ₘ oldMemB_8) **
      (.r7 ↦ᵣ addr4) **
      (.r10 ↦ᵣ vR10Old) **
      (effectiveAddr vR10Old (-2072) ↦U64 addr4) **
      (.r3 ↦ᵣ addr0) **
      (effectiveAddr addr0 0 ↦ₘ oldMemB_10) **
      (effectiveAddr addr1 8 ↦U64 addr0) **
      (effectiveAddr addr0 80 ↦U64 oldMemD_12) **
      (effectiveAddr addr2 0 ↦ₘ oldMemB_13) **
      (effectiveAddr addr1 16 ↦U64 addr2) **
      (effectiveAddr addr2 80 ↦U64 oldMemD_15) **
      (.r4 ↦ᵣ oldMemD_38) **
      (effectiveAddr addr3 0 ↦U64 oldMemD_16) **
      (.r9 ↦ᵣ toU64 4) **
      (effectiveAddr addr3 8 ↦ₘ oldMemB_17) **
      (.r5 ↦ᵣ oldMemD_40) **
      (.r8 ↦ᵣ addr5) **
      (.r6 ↦ᵣ toU64 0) **
      (effectiveAddr addr4 8 ↦U64 oldMemD_21) **
      (effectiveAddr addr4 16 ↦U64 oldMemD_23) **
      (effectiveAddr addr4 24 ↦U64 oldMemD_25) **
      (effectiveAddr addr4 32 ↦U64 oldMemD_27) **
      (effectiveAddr addr2 8 ↦U64 oldMemD_30) **
      (effectiveAddr addr2 16 ↦U64 oldMemD_32) **
      (effectiveAddr addr2 24 ↦U64 oldMemD_34) **
      (effectiveAddr addr2 32 ↦U64 oldMemD_36) **
      (effectiveAddr addr5 0 ↦U64 oldMemD_38) **
      (effectiveAddr addr2 1 ↦ₘ oldMemB_39)) := by
  unfold SVM.Solana.Abstract.AsmRefinesFieldUpdates
  simp only [SVM.Solana.Abstract.codecsPre, SVM.Solana.Abstract.codecsPost]
  rw [codecCoarse_eq_fine (addr4 + 88)
        [(0, .blob [.byte (oldMemB_29), .gap fg1, .u64 (oldMemD_31), .u64 (oldMemD_33), .u64 (oldMemD_35), .u64 (oldMemD_37)]), (36, .u64 oldMemD_40), (44, .blob [.gap fg2, .byte (oldMemB_28), .gap fg4])]
        (by simp [codecValid, FieldVal.fineValid, segsValid, FieldSeg.valid] <;> omega),
      codecCoarse_eq_fine (addr0 + 88)
        [(0, .pubkey ⟨oldMemD_20, oldMemD_22, oldMemD_24, oldMemD_26⟩), (32, .pubkey ⟨o5, o6, o7, o8⟩), (64, .u64 oldMemD_41), (72, .blob [.gap fg9, .byte (oldMemB_18), .byte (oldMemB_19), .gap fg12])]
        (by simp [codecValid, FieldVal.fineValid, segsValid, FieldSeg.valid] <;> omega),
      codecCoarse_eq_fine (addr4 + 88)
        [(0, .blob [.byte (oldMemB_29), .gap fg1, .u64 (oldMemD_31), .u64 (oldMemD_33), .u64 (oldMemD_35), .u64 (oldMemD_37)]), (36, .u64 (oldMemD_40 + oldMemD_38)), (44, .blob [.gap fg2, .byte (oldMemB_28), .gap fg4])]
        (by simp [codecValid, FieldVal.fineValid, segsValid, FieldSeg.valid] <;> omega),
      codecCoarse_eq_fine (addr0 + 88)
        [(0, .pubkey ⟨oldMemD_20, oldMemD_22, oldMemD_24, oldMemD_26⟩), (32, .pubkey ⟨o5, o6, o7, o8⟩), (64, .u64 (oldMemD_41 + oldMemD_38)), (72, .blob [.gap fg9, .byte (oldMemB_18), .byte (oldMemB_19), .gap fg12])]
        (by simp [codecValid, FieldVal.fineValid, segsValid, FieldSeg.valid] <;> omega)]
  simp only [codecFine, FieldVal.fine, pubkeyIs, segsSL, FieldSeg.sl, FieldSeg.size, hfg1_sz, hfg2_sz, hfg9_sz, sepConj_emp_right_eq, Nat.add_zero, Nat.add_assoc, Nat.reduceAdd]
  have framed := cuTripleWithinMem_frame_right
    ( (effectiveAddr addr4 89 ↦Bytes fg1) **
      (effectiveAddr addr4 132 ↦Bytes fg2) **
      (effectiveAddr addr4 134 ↦Bytes fg4) **
      (effectiveAddr addr0 120 ↦U64 o5) **
      (effectiveAddr addr0 128 ↦U64 o6) **
      (effectiveAddr addr0 136 ↦U64 o7) **
      (effectiveAddr addr0 144 ↦U64 o8) **
      (effectiveAddr addr0 160 ↦Bytes fg9) **
      (effectiveAddr addr0 198 ↦Bytes fg12) )
    (by sl_pcfree) lift
  sl_exact framed

/-- qedgen `ensures`-shape for the `mint` account, mechanically
    discharged: its `u64` field (offset 36) shifts by `oldMemD_38`. -/
theorem ensures_mint
    (oldMemB_28 oldMemB_29 oldMemD_31 oldMemD_33 oldMemD_35 oldMemD_37 oldMemD_38 oldMemD_40 : Nat)
    (fg1 fg2 fg4 : ByteArray) :
    u64FieldAt 36 [(0, .blob [.byte (oldMemB_29), .gap fg1, .u64 (oldMemD_31), .u64 (oldMemD_33), .u64 (oldMemD_35), .u64 (oldMemD_37)]), (36, .u64 (oldMemD_40 + oldMemD_38)), (44, .blob [.gap fg2, .byte (oldMemB_28), .gap fg4])]
      = u64FieldAt 36 [(0, .blob [.byte (oldMemB_29), .gap fg1, .u64 (oldMemD_31), .u64 (oldMemD_33), .u64 (oldMemD_35), .u64 (oldMemD_37)]), (36, .u64 oldMemD_40), (44, .blob [.gap fg2, .byte (oldMemB_28), .gap fg4])] + oldMemD_38 := by
  qedsvm_discharge

/-- qedgen `ensures`-shape for the `dest` account, mechanically
    discharged: its `u64` field (offset 64) shifts by `oldMemD_38`. -/
theorem ensures_dest
    (oldMemB_18 oldMemB_19 oldMemD_20 oldMemD_22 oldMemD_24 oldMemD_26 oldMemD_38 oldMemD_41 o5 o6 o7 o8 : Nat)
    (fg9 fg12 : ByteArray) :
    u64FieldAt 64 [(0, .pubkey ⟨oldMemD_20, oldMemD_22, oldMemD_24, oldMemD_26⟩), (32, .pubkey ⟨o5, o6, o7, o8⟩), (64, .u64 (oldMemD_41 + oldMemD_38)), (72, .blob [.gap fg9, .byte (oldMemB_18), .byte (oldMemB_19), .gap fg12])]
      = u64FieldAt 64 [(0, .pubkey ⟨oldMemD_20, oldMemD_22, oldMemD_24, oldMemD_26⟩), (32, .pubkey ⟨o5, o6, o7, o8⟩), (64, .u64 oldMemD_41), (72, .blob [.gap fg9, .byte (oldMemB_18), .byte (oldMemB_19), .gap fg12])] + oldMemD_38 := by
  qedsvm_discharge

end Examples.PTokenMintToRefinement
