/-
  AsmRefinesTokenTransfer asm-refines-intrinsic theorem. MECHANICALLY EMITTED by qedlift's
  refinement codegen from the lift's atoms + the IDL arm name. Wires the
  trace-guided lift to `AsmRefinesTokenTransfer` via the codec-aggregation lemmas +
  `cuTripleWithinMem_frame_right` + `sl_exact`.
-/

import SVM.SBPF.Tactic.SL
import SVM.Solana.Abstract.Refinement
import SVM.Solana.TokenFieldCodec
import Generated.PTokenTransferCheckedTracedLifted
import PToken.TransferAggregation

namespace Examples.PTokenTransferCheckedRefinement
open SVM SVM.SBPF SVM.SBPF.Memory
open Examples.PTokenTransferAggregation

set_option maxHeartbeats 800000 in
theorem refines_asm
    (cr : CodeReq) (rr : Memory.RegionTable → Prop)
    (baseAddr oldMemB_0 vR2Old oldMemD_1 oldMemB_2 oldMemD_3 oldMemB_4 oldMemD_5 oldMemB_6 oldMemD_7 vR4Old vR5Old oldMemD_8 oldMemB_9 vR6Old vR7Old oldMemB_10 oldMemB_11 vR3Old oldMemD_12 oldMemD_13 oldMemD_14 vR0Old oldMemD_15 oldMemD_16 vR8Old oldMemD_17 vR10Old oldMemD_18 oldMemD_19 oldMemD_20 vR9Old oldMemD_21 oldMemD_22 oldMemD_23 oldMemD_24 oldMemD_25 oldMemD_26 oldMemB_27 oldMemB_28 oldMemB_29 oldMemD_30 oldMemB_31 oldMemD_32 oldMemD_33 oldMemD_34 oldMemD_35 oldMemD_36 oldMemD_37 oldMemD_38 oldMemB_39 oldMemD_40 oldMemB_41 o0 o1 o2 o3 : Nat)
    (g1 g2 g3 g4 : ByteArray)
    (g1sz : g1.size = 35)
    (h_oldMemB_31 : oldMemB_31 < 256)
    (h_oldMemB_10 : oldMemB_10 < 256)
    (h_oldMemB_41 : oldMemB_41 < 256)
    (g3sz : g3.size = 36)
    (h_oldMemB_11 : oldMemB_11 < 256)
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
    SVM.Solana.Abstract.AsmRefinesTokenTransfer cr 104 0 198 3542 rr (baseAddr + 96) (baseAddr + 21024)
      { mint := ⟨oldMemD_14, oldMemD_16, oldMemD_19, oldMemD_21⟩,
        owner := ⟨oldMemD_32, oldMemD_34, oldMemD_36, oldMemD_38⟩, amount := oldMemD_13,
        rest := PartialState.byteBA oldMemB_31 ++ (g1 ++ (PartialState.byteBA oldMemB_10 ++ (PartialState.byteBA oldMemB_41 ++ g2))) }
      { mint := ⟨oldMemD_15, oldMemD_17, oldMemD_20, oldMemD_22⟩,
        owner := ⟨o0, o1, o2, o3⟩, amount := oldMemD_40,
        rest := g3 ++ (PartialState.byteBA oldMemB_11 ++ g4) }
      oldMemD_12
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
  unfold SVM.Solana.Abstract.AsmRefinesTokenTransfer
  simp only [SVM.Solana.Abstract.Mint.withSupply, SVM.Solana.Abstract.TokenAccount.withAmount]
  rw [src_account_eq (baseAddr + 96) oldMemD_14 oldMemD_16 oldMemD_19 oldMemD_21 oldMemD_32 oldMemD_34 oldMemD_36 oldMemD_38 oldMemD_13 oldMemB_31 oldMemB_10 oldMemB_41 g1 g2 g1sz h_oldMemB_31 h_oldMemB_10 h_oldMemB_41,
      dst_account_eq (baseAddr + 21024) oldMemD_15 oldMemD_17 oldMemD_20 oldMemD_22 o0 o1 o2 o3 oldMemD_40 oldMemB_11 g3 g4 g3sz h_oldMemB_11,
      src_account_eq (baseAddr + 96) oldMemD_14 oldMemD_16 oldMemD_19 oldMemD_21 oldMemD_32 oldMemD_34 oldMemD_36 oldMemD_38 (oldMemD_13 - oldMemD_12) oldMemB_31 oldMemB_10 oldMemB_41 g1 g2 g1sz h_oldMemB_31 h_oldMemB_10 h_oldMemB_41,
      dst_account_eq (baseAddr + 21024) oldMemD_15 oldMemD_17 oldMemD_20 oldMemD_22 o0 o1 o2 o3 (oldMemD_40 + oldMemD_12) oldMemB_11 g3 g4 g3sz h_oldMemB_11]
  simp only [pubkeyIs]
  have framed := cuTripleWithinMem_frame_right
    ( memBytesIs (baseAddr + 169) g1 **
      memBytesIs (baseAddr + 206) g2 **
      (effectiveAddr baseAddr 21056 ↦U64 o0) **
      (effectiveAddr baseAddr 21064 ↦U64 o1) **
      (effectiveAddr baseAddr 21072 ↦U64 o2) **
      (effectiveAddr baseAddr 21080 ↦U64 o3) **
      memBytesIs (baseAddr + 21096) g3 **
      memBytesIs (baseAddr + 21133) g4 )
    (by sl_pcfree) lift
  simp only [Nat.add_assoc, Nat.reduceAdd]
  sl_exact framed

/-- Discharge-route reshape: the `AsmRefinesTokenTransfer` obligation is a layout-general
    field-list (`codecCoarse`/`tokenFields`/`mintFields`) obligation. The
    convergence keystones (`tokenAcctBalance_codec` / `mintSupply_codec`)
    rewrite the bespoke `tokenAcctBalanceOf` / `mintSupplyOf` atoms to the
    field-list codec, so qedgen reads the mutated field off the decoded list
    via the library `*_ensures_*` facts (`qedsvm_discharge`). Pairs with
    `refines_asm` (the lift realises the obligation). -/
theorem refines_field
    (cr : CodeReq) (rr : Memory.RegionTable → Prop)
    (baseAddr oldMemB_0 vR2Old oldMemD_1 oldMemB_2 oldMemD_3 oldMemB_4 oldMemD_5 oldMemB_6 oldMemD_7 vR4Old vR5Old oldMemD_8 oldMemB_9 vR6Old vR7Old oldMemB_10 oldMemB_11 vR3Old oldMemD_12 oldMemD_13 oldMemD_14 vR0Old oldMemD_15 oldMemD_16 vR8Old oldMemD_17 vR10Old oldMemD_18 oldMemD_19 oldMemD_20 vR9Old oldMemD_21 oldMemD_22 oldMemD_23 oldMemD_24 oldMemD_25 oldMemD_26 oldMemB_27 oldMemB_28 oldMemB_29 oldMemD_30 oldMemB_31 oldMemD_32 oldMemD_33 oldMemD_34 oldMemD_35 oldMemD_36 oldMemD_37 oldMemD_38 oldMemB_39 oldMemD_40 oldMemB_41 o0 o1 o2 o3 : Nat)
    (g1 g2 g3 g4 : ByteArray)
    (h : SVM.Solana.Abstract.AsmRefinesTokenTransfer cr 104 0 198 3542 rr (baseAddr + 96) (baseAddr + 21024)
      { mint := ⟨oldMemD_14, oldMemD_16, oldMemD_19, oldMemD_21⟩,
        owner := ⟨oldMemD_32, oldMemD_34, oldMemD_36, oldMemD_38⟩, amount := oldMemD_13,
        rest := PartialState.byteBA oldMemB_31 ++ (g1 ++ (PartialState.byteBA oldMemB_10 ++ (PartialState.byteBA oldMemB_41 ++ g2))) }
      { mint := ⟨oldMemD_15, oldMemD_17, oldMemD_20, oldMemD_22⟩,
        owner := ⟨o0, o1, o2, o3⟩, amount := oldMemD_40,
        rest := g3 ++ (PartialState.byteBA oldMemB_11 ++ g4) }
      oldMemD_12
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
      (effectiveAddr baseAddr 31441 ↦ₘ oldMemB_39))) :
    cuTripleWithinMem 104 0 198 3542 cr
      (((.r1 ↦ᵣ baseAddr) **
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
      (effectiveAddr baseAddr 31441 ↦ₘ oldMemB_39)) **
      codecCoarse (baseAddr + 96) (SVM.Solana.tokenFields ⟨oldMemD_14, oldMemD_16, oldMemD_19, oldMemD_21⟩ ⟨oldMemD_32, oldMemD_34, oldMemD_36, oldMemD_38⟩ oldMemD_13 (PartialState.byteBA oldMemB_31 ++ (g1 ++ (PartialState.byteBA oldMemB_10 ++ (PartialState.byteBA oldMemB_41 ++ g2))))) **
      codecCoarse (baseAddr + 21024) (SVM.Solana.tokenFields ⟨oldMemD_15, oldMemD_17, oldMemD_20, oldMemD_22⟩ ⟨o0, o1, o2, o3⟩ oldMemD_40 (g3 ++ (PartialState.byteBA oldMemB_11 ++ g4))))
      (((.r1 ↦ᵣ baseAddr) **
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
      (effectiveAddr baseAddr 31441 ↦ₘ oldMemB_39)) **
      codecCoarse (baseAddr + 96) (SVM.Solana.tokenFields ⟨oldMemD_14, oldMemD_16, oldMemD_19, oldMemD_21⟩ ⟨oldMemD_32, oldMemD_34, oldMemD_36, oldMemD_38⟩ (oldMemD_13 - oldMemD_12) (PartialState.byteBA oldMemB_31 ++ (g1 ++ (PartialState.byteBA oldMemB_10 ++ (PartialState.byteBA oldMemB_41 ++ g2))))) **
      codecCoarse (baseAddr + 21024) (SVM.Solana.tokenFields ⟨oldMemD_15, oldMemD_17, oldMemD_20, oldMemD_22⟩ ⟨o0, o1, o2, o3⟩ (oldMemD_40 + oldMemD_12) (g3 ++ (PartialState.byteBA oldMemB_11 ++ g4))))
      rr := by
  unfold SVM.Solana.Abstract.AsmRefinesTokenTransfer at h
  simpa only [SVM.Solana.tokenAcctBalanceOf_eq, SVM.Solana.tokenAcctBalanceOf_withAmount, SVM.Solana.tokenAcctBalance_codec] using h

end Examples.PTokenTransferCheckedRefinement
