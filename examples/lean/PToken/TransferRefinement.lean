/-
  AsmRefinesTokenTransfer asm-refines-intrinsic theorem. MECHANICALLY EMITTED by qedlift's
  refinement codegen from the lift's atoms + the IDL arm name. Wires the
  trace-guided lift to `AsmRefinesTokenTransfer` via the codec-aggregation lemmas +
  `cuTripleWithinMem_frame_right` + `sl_exact`.
-/

import SVM.SBPF.Tactic.SL
import SVM.Solana.Abstract.Refinement
import SVM.Solana.TokenFieldCodec
import Generated.PTokenTransferTracedLifted
import PToken.TransferAggregation

namespace Examples.PTokenTransferRefinement
open SVM SVM.SBPF SVM.SBPF.Memory
open Examples.PTokenTransferAggregation

set_option maxHeartbeats 800000 in
theorem refines_asm
    (cr : CodeReq) (rr : Memory.RegionTable → Prop)
    (baseAddr oldMemB_0 vR2Old oldMemD_1 oldMemB_2 oldMemD_3 oldMemB_4 oldMemD_5 vR4Old vR3Old oldMemD_6 oldMemB_7 vR6Old vR7Old oldMemB_8 oldMemB_9 vR5Old oldMemD_10 oldMemD_11 oldMemD_12 oldMemD_13 vR0Old oldMemD_14 oldMemD_15 oldMemD_16 oldMemD_17 oldMemD_18 oldMemD_19 oldMemD_20 oldMemB_21 oldMemD_22 oldMemD_23 oldMemD_24 oldMemD_25 oldMemD_26 oldMemD_27 oldMemD_28 oldMemB_29 oldMemD_30 oldMemB_31 o0 o1 o2 o3 : Nat)
    (g1 g2 g3 g4 : ByteArray)
    (g1sz : g1.size = 35)
    (h_oldMemB_21 : oldMemB_21 < 256)
    (h_oldMemB_8 : oldMemB_8 < 256)
    (h_oldMemB_31 : oldMemB_31 < 256)
    (g3sz : g3.size = 36)
    (h_oldMemB_9 : oldMemB_9 < 256)
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
    SVM.Solana.Abstract.AsmRefinesTokenTransfer cr 75 0 198 3542 rr (baseAddr + 96) (baseAddr + 10600)
      { mint := ⟨oldMemD_13, oldMemD_15, oldMemD_17, oldMemD_19⟩,
        owner := ⟨oldMemD_22, oldMemD_24, oldMemD_26, oldMemD_28⟩, amount := oldMemD_11,
        rest := PartialState.byteBA oldMemB_21 ++ (g1 ++ (PartialState.byteBA oldMemB_8 ++ (PartialState.byteBA oldMemB_31 ++ g2))) }
      { mint := ⟨oldMemD_12, oldMemD_14, oldMemD_16, oldMemD_18⟩,
        owner := ⟨o0, o1, o2, o3⟩, amount := oldMemD_30,
        rest := g3 ++ (PartialState.byteBA oldMemB_9 ++ g4) }
      oldMemD_10
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
  unfold SVM.Solana.Abstract.AsmRefinesTokenTransfer
  simp only [SVM.Solana.Abstract.Mint.withSupply, SVM.Solana.Abstract.TokenAccount.withAmount]
  rw [src_account_eq (baseAddr + 96) oldMemD_13 oldMemD_15 oldMemD_17 oldMemD_19 oldMemD_22 oldMemD_24 oldMemD_26 oldMemD_28 oldMemD_11 oldMemB_21 oldMemB_8 oldMemB_31 g1 g2 g1sz h_oldMemB_21 h_oldMemB_8 h_oldMemB_31,
      dst_account_eq (baseAddr + 10600) oldMemD_12 oldMemD_14 oldMemD_16 oldMemD_18 o0 o1 o2 o3 oldMemD_30 oldMemB_9 g3 g4 g3sz h_oldMemB_9,
      src_account_eq (baseAddr + 96) oldMemD_13 oldMemD_15 oldMemD_17 oldMemD_19 oldMemD_22 oldMemD_24 oldMemD_26 oldMemD_28 (oldMemD_11 - oldMemD_10) oldMemB_21 oldMemB_8 oldMemB_31 g1 g2 g1sz h_oldMemB_21 h_oldMemB_8 h_oldMemB_31,
      dst_account_eq (baseAddr + 10600) oldMemD_12 oldMemD_14 oldMemD_16 oldMemD_18 o0 o1 o2 o3 (oldMemD_30 + oldMemD_10) oldMemB_9 g3 g4 g3sz h_oldMemB_9]
  simp only [pubkeyIs]
  have framed := cuTripleWithinMem_frame_right
    ( memBytesIs (baseAddr + 169) g1 **
      memBytesIs (baseAddr + 206) g2 **
      (effectiveAddr baseAddr 10632 ↦U64 o0) **
      (effectiveAddr baseAddr 10640 ↦U64 o1) **
      (effectiveAddr baseAddr 10648 ↦U64 o2) **
      (effectiveAddr baseAddr 10656 ↦U64 o3) **
      memBytesIs (baseAddr + 10672) g3 **
      memBytesIs (baseAddr + 10709) g4 )
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
    (baseAddr oldMemB_0 vR2Old oldMemD_1 oldMemB_2 oldMemD_3 oldMemB_4 oldMemD_5 vR4Old vR3Old oldMemD_6 oldMemB_7 vR6Old vR7Old oldMemB_8 oldMemB_9 vR5Old oldMemD_10 oldMemD_11 oldMemD_12 oldMemD_13 vR0Old oldMemD_14 oldMemD_15 oldMemD_16 oldMemD_17 oldMemD_18 oldMemD_19 oldMemD_20 oldMemB_21 oldMemD_22 oldMemD_23 oldMemD_24 oldMemD_25 oldMemD_26 oldMemD_27 oldMemD_28 oldMemB_29 oldMemD_30 oldMemB_31 o0 o1 o2 o3 : Nat)
    (g1 g2 g3 g4 : ByteArray)
    (h : SVM.Solana.Abstract.AsmRefinesTokenTransfer cr 75 0 198 3542 rr (baseAddr + 96) (baseAddr + 10600)
      { mint := ⟨oldMemD_13, oldMemD_15, oldMemD_17, oldMemD_19⟩,
        owner := ⟨oldMemD_22, oldMemD_24, oldMemD_26, oldMemD_28⟩, amount := oldMemD_11,
        rest := PartialState.byteBA oldMemB_21 ++ (g1 ++ (PartialState.byteBA oldMemB_8 ++ (PartialState.byteBA oldMemB_31 ++ g2))) }
      { mint := ⟨oldMemD_12, oldMemD_14, oldMemD_16, oldMemD_18⟩,
        owner := ⟨o0, o1, o2, o3⟩, amount := oldMemD_30,
        rest := g3 ++ (PartialState.byteBA oldMemB_9 ++ g4) }
      oldMemD_10
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
      (effectiveAddr baseAddr 21017 ↦ₘ oldMemB_29))) :
    cuTripleWithinMem 75 0 198 3542 cr
      (((.r1 ↦ᵣ baseAddr) **
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
      (effectiveAddr baseAddr 21017 ↦ₘ oldMemB_29)) **
      codecCoarse (baseAddr + 96) (SVM.Solana.tokenFields ⟨oldMemD_13, oldMemD_15, oldMemD_17, oldMemD_19⟩ ⟨oldMemD_22, oldMemD_24, oldMemD_26, oldMemD_28⟩ oldMemD_11 (PartialState.byteBA oldMemB_21 ++ (g1 ++ (PartialState.byteBA oldMemB_8 ++ (PartialState.byteBA oldMemB_31 ++ g2))))) **
      codecCoarse (baseAddr + 10600) (SVM.Solana.tokenFields ⟨oldMemD_12, oldMemD_14, oldMemD_16, oldMemD_18⟩ ⟨o0, o1, o2, o3⟩ oldMemD_30 (g3 ++ (PartialState.byteBA oldMemB_9 ++ g4))))
      (((.r1 ↦ᵣ baseAddr) **
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
      (effectiveAddr baseAddr 21017 ↦ₘ oldMemB_29)) **
      codecCoarse (baseAddr + 96) (SVM.Solana.tokenFields ⟨oldMemD_13, oldMemD_15, oldMemD_17, oldMemD_19⟩ ⟨oldMemD_22, oldMemD_24, oldMemD_26, oldMemD_28⟩ (oldMemD_11 - oldMemD_10) (PartialState.byteBA oldMemB_21 ++ (g1 ++ (PartialState.byteBA oldMemB_8 ++ (PartialState.byteBA oldMemB_31 ++ g2))))) **
      codecCoarse (baseAddr + 10600) (SVM.Solana.tokenFields ⟨oldMemD_12, oldMemD_14, oldMemD_16, oldMemD_18⟩ ⟨o0, o1, o2, o3⟩ (oldMemD_30 + oldMemD_10) (g3 ++ (PartialState.byteBA oldMemB_9 ++ g4))))
      rr := by
  unfold SVM.Solana.Abstract.AsmRefinesTokenTransfer at h
  simpa only [SVM.Solana.tokenAcctBalanceOf_eq, SVM.Solana.tokenAcctBalanceOf_withAmount, SVM.Solana.tokenAcctBalance_codec] using h

end Examples.PTokenTransferRefinement
