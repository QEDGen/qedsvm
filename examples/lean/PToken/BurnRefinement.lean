/-
  AsmRefinesTokenBurn asm-refines-intrinsic theorem. MECHANICALLY EMITTED by qedlift's
  refinement codegen from the lift's atoms + the IDL arm name. Wires the
  trace-guided lift to `AsmRefinesTokenBurn` via the codec-aggregation lemmas +
  `cuTripleWithinMem_frame_right` + `sl_exact`.
-/

import SVM.SBPF.Tactic.SL
import SVM.Solana.Abstract.Refinement
import SVM.Solana.TokenFieldCodec
import Generated.PTokenBurnTracedLifted
import SVM.Solana.MintFieldCodec
import PToken.TransferAggregation
import PToken.MintAggregation

namespace Examples.PTokenBurnRefinement
open SVM SVM.SBPF SVM.SBPF.Memory
open Examples.PTokenTransferAggregation Examples.PTokenMintAggregation

set_option maxHeartbeats 800000 in
theorem refines_asm
    (cr : CodeReq) (rr : Memory.RegionTable → Prop)
    (baseAddr oldMemB_0 vR2Old oldMemD_1 oldMemB_2 oldMemD_3 vR0Old oldMemD_4 vR7Old vR10Old oldMemD_5 vR3Old oldMemB_6 oldMemD_7 oldMemD_8 oldMemB_9 oldMemD_10 oldMemD_11 vR4Old oldMemD_12 vR9Old oldMemB_13 vR5Old vR8Old vR6Old oldMemD_14 oldMemB_15 oldMemD_16 oldMemD_17 oldMemB_18 oldMemB_19 oldMemD_20 oldMemD_21 oldMemD_22 oldMemD_23 oldMemD_24 oldMemD_25 oldMemD_26 oldMemD_27 oldMemD_28 oldMemD_29 oldMemD_30 oldMemD_31 oldMemD_32 oldMemD_33 oldMemD_34 oldMemB_35 oldMemD_36 oldMemD_37 oldMemD_38 oldMemD_39 oldMemD_40 oldMemD_41 oldMemD_42 oldMemD_43 oldMemB_44 oldMemD_45 : Nat)
    (g1 g2 preAuth5 g3 g4 : ByteArray)
    (g1sz : g1.size = 35)
    (h_oldMemB_35 : oldMemB_35 < 256)
    (h_oldMemB_15 : oldMemB_15 < 256)
    (h_oldMemB_19 : oldMemB_19 < 256)
    (h_oldMemB_18 : oldMemB_18 < 256)
    (g3sz : g3.size = 1)
    (lift : cuTripleWithinMem 130 0 198 3542 cr
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦ₘ oldMemB_0) **
      (.r2 ↦ᵣ vR2Old) **
      (effectiveAddr baseAddr 88 ↦U64 oldMemD_1) **
      (effectiveAddr baseAddr 10512 ↦ₘ oldMemB_2) **
      (effectiveAddr baseAddr 10592 ↦U64 oldMemD_3) **
      (.r0 ↦ᵣ vR0Old) **
      (effectiveAddr baseAddr 0 ↦U64 oldMemD_4) **
      (.r7 ↦ᵣ vR7Old) **
      (.r10 ↦ᵣ vR10Old) **
      (effectiveAddr vR10Old (-2072) ↦U64 oldMemD_5) **
      (.r3 ↦ᵣ vR3Old) **
      (effectiveAddr addr0 0 ↦ₘ oldMemB_6) **
      (effectiveAddr addr1 8 ↦U64 oldMemD_7) **
      (effectiveAddr addr0 80 ↦U64 oldMemD_8) **
      (effectiveAddr addr2 0 ↦ₘ oldMemB_9) **
      (effectiveAddr addr1 16 ↦U64 oldMemD_10) **
      (effectiveAddr addr2 80 ↦U64 oldMemD_11) **
      (.r4 ↦ᵣ vR4Old) **
      (effectiveAddr addr3 0 ↦U64 oldMemD_12) **
      (.r9 ↦ᵣ vR9Old) **
      (effectiveAddr addr3 8 ↦ₘ oldMemB_13) **
      (.r5 ↦ᵣ vR5Old) **
      (.r8 ↦ᵣ vR8Old) **
      (.r6 ↦ᵣ vR6Old) **
      (effectiveAddr addr4 80 ↦U64 oldMemD_14) **
      (effectiveAddr addr4 196 ↦ₘ oldMemB_15) **
      (effectiveAddr vR10Old (-2064) ↦U64 addr5) **
      (effectiveAddr addr5 80 ↦U64 oldMemD_17) **
      (effectiveAddr addr5 133 ↦ₘ oldMemB_18) **
      (effectiveAddr addr4 197 ↦ₘ oldMemB_19) **
      (effectiveAddr addr6 0 ↦U64 oldMemD_20) **
      (effectiveAddr addr4 152 ↦U64 oldMemD_21) **
      (effectiveAddr addr4 88 ↦U64 oldMemD_22) **
      (effectiveAddr addr5 8 ↦U64 oldMemD_23) **
      (effectiveAddr addr4 96 ↦U64 oldMemD_24) **
      (effectiveAddr addr5 16 ↦U64 oldMemD_25) **
      (effectiveAddr addr4 104 ↦U64 oldMemD_26) **
      (effectiveAddr addr5 24 ↦U64 oldMemD_27) **
      (effectiveAddr vR10Old (-2096) ↦U64 oldMemD_28) **
      (effectiveAddr addr4 112 ↦U64 oldMemD_29) **
      (effectiveAddr addr5 32 ↦U64 oldMemD_30) **
      (effectiveAddr addr4 120 ↦U64 oldMemD_31) **
      (effectiveAddr vR10Old (-2088) ↦U64 oldMemD_32) **
      (effectiveAddr vR10Old (-2104) ↦U64 oldMemD_33) **
      (effectiveAddr vR10Old (-2056) ↦U64 addr7) **
      (effectiveAddr addr4 160 ↦ₘ oldMemB_35) **
      (effectiveAddr addr7 8 ↦U64 oldMemD_36) **
      (effectiveAddr addr7 16 ↦U64 oldMemD_37) **
      (effectiveAddr addr4 128 ↦U64 oldMemD_38) **
      (effectiveAddr addr7 24 ↦U64 oldMemD_39) **
      (effectiveAddr addr4 136 ↦U64 oldMemD_40) **
      (effectiveAddr addr7 32 ↦U64 oldMemD_41) **
      (effectiveAddr addr4 144 ↦U64 oldMemD_42) **
      (effectiveAddr addr7 80 ↦U64 oldMemD_43) **
      (effectiveAddr addr7 1 ↦ₘ oldMemB_44) **
      (effectiveAddr addr5 124 ↦U64 oldMemD_45))
      ((.r1 ↦ᵣ wrapSub oldMemD_45 oldMemD_20) **
      (effectiveAddr baseAddr 0 ↦ₘ oldMemB_0) **
      (.r2 ↦ᵣ oldMemD_42) **
      (effectiveAddr baseAddr 88 ↦U64 oldMemD_1) **
      (effectiveAddr baseAddr 10512 ↦ₘ oldMemB_2) **
      (effectiveAddr baseAddr 10592 ↦U64 oldMemD_3) **
      (.r0 ↦ᵣ toU64 0) **
      (effectiveAddr baseAddr 0 ↦U64 oldMemD_4) **
      (.r7 ↦ᵣ oldMemD_4) **
      (.r10 ↦ᵣ vR10Old) **
      (effectiveAddr vR10Old (-2072) ↦U64 addr4) **
      (.r3 ↦ᵣ addr5) **
      (effectiveAddr addr0 0 ↦ₘ oldMemB_6) **
      (effectiveAddr addr1 8 ↦U64 addr0) **
      (effectiveAddr addr0 80 ↦U64 oldMemD_8) **
      (effectiveAddr addr2 0 ↦ₘ oldMemB_9) **
      (effectiveAddr addr1 16 ↦U64 addr2) **
      (effectiveAddr addr2 80 ↦U64 oldMemD_11) **
      (.r4 ↦ᵣ addr4) **
      (effectiveAddr addr3 0 ↦U64 oldMemD_12) **
      (.r9 ↦ᵣ toU64 4) **
      (effectiveAddr addr3 8 ↦ₘ oldMemB_13) **
      (.r5 ↦ᵣ oldMemD_20) **
      (.r8 ↦ᵣ addr6) **
      (.r6 ↦ᵣ toU64 0) **
      (effectiveAddr addr4 80 ↦U64 oldMemD_14) **
      (effectiveAddr addr4 196 ↦ₘ oldMemB_15) **
      (effectiveAddr vR10Old (-2064) ↦U64 addr5) **
      (effectiveAddr addr5 80 ↦U64 oldMemD_17) **
      (effectiveAddr addr5 133 ↦ₘ oldMemB_18) **
      (effectiveAddr addr4 197 ↦ₘ oldMemB_19) **
      (effectiveAddr addr6 0 ↦U64 oldMemD_20) **
      (effectiveAddr addr4 152 ↦U64 oldMemD_21 - oldMemD_20) **
      (effectiveAddr addr4 88 ↦U64 oldMemD_22) **
      (effectiveAddr addr5 8 ↦U64 oldMemD_23) **
      (effectiveAddr addr4 96 ↦U64 oldMemD_24) **
      (effectiveAddr addr5 16 ↦U64 oldMemD_25) **
      (effectiveAddr addr4 104 ↦U64 oldMemD_26) **
      (effectiveAddr addr5 24 ↦U64 oldMemD_27) **
      (effectiveAddr vR10Old (-2096) ↦U64 oldMemD_21) **
      (effectiveAddr addr4 112 ↦U64 oldMemD_29) **
      (effectiveAddr addr5 32 ↦U64 oldMemD_30) **
      (effectiveAddr addr4 120 ↦U64 oldMemD_31) **
      (effectiveAddr vR10Old (-2088) ↦U64 oldMemD_20) **
      (effectiveAddr vR10Old (-2104) ↦U64 wrapAdd vR10Old (toU64 (-2048))) **
      (effectiveAddr vR10Old (-2056) ↦U64 addr7) **
      (effectiveAddr addr4 160 ↦ₘ oldMemB_35) **
      (effectiveAddr addr7 8 ↦U64 oldMemD_36) **
      (effectiveAddr addr7 16 ↦U64 oldMemD_37) **
      (effectiveAddr addr4 128 ↦U64 oldMemD_38) **
      (effectiveAddr addr7 24 ↦U64 oldMemD_39) **
      (effectiveAddr addr4 136 ↦U64 oldMemD_40) **
      (effectiveAddr addr7 32 ↦U64 oldMemD_41) **
      (effectiveAddr addr4 144 ↦U64 oldMemD_42) **
      (effectiveAddr addr7 80 ↦U64 oldMemD_43) **
      (effectiveAddr addr7 1 ↦ₘ oldMemB_44) **
      (effectiveAddr addr5 124 ↦U64 oldMemD_45 - oldMemD_20)) rr) :
    SVM.Solana.Abstract.AsmRefinesTokenBurn cr 130 0 198 3542 rr (addr4 + 88) (addr5 + 88)
      { mint := ⟨oldMemD_22, oldMemD_24, oldMemD_26, oldMemD_29⟩,
        owner := ⟨oldMemD_31, oldMemD_38, oldMemD_40, oldMemD_42⟩, amount := oldMemD_21,
        rest := PartialState.byteBA oldMemB_35 ++ (g1 ++ (PartialState.byteBA oldMemB_15 ++ (PartialState.byteBA oldMemB_19 ++ g2))) }
      { preAuth := preAuth5,
        supply := oldMemD_45,
        rest := g3 ++ (PartialState.byteBA oldMemB_18 ++ g4) }
      oldMemD_20
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦ₘ oldMemB_0) **
      (.r2 ↦ᵣ vR2Old) **
      (effectiveAddr baseAddr 88 ↦U64 oldMemD_1) **
      (effectiveAddr baseAddr 10512 ↦ₘ oldMemB_2) **
      (effectiveAddr baseAddr 10592 ↦U64 oldMemD_3) **
      (.r0 ↦ᵣ vR0Old) **
      (effectiveAddr baseAddr 0 ↦U64 oldMemD_4) **
      (.r7 ↦ᵣ vR7Old) **
      (.r10 ↦ᵣ vR10Old) **
      (effectiveAddr vR10Old (-2072) ↦U64 oldMemD_5) **
      (.r3 ↦ᵣ vR3Old) **
      (effectiveAddr addr0 0 ↦ₘ oldMemB_6) **
      (effectiveAddr addr1 8 ↦U64 oldMemD_7) **
      (effectiveAddr addr0 80 ↦U64 oldMemD_8) **
      (effectiveAddr addr2 0 ↦ₘ oldMemB_9) **
      (effectiveAddr addr1 16 ↦U64 oldMemD_10) **
      (effectiveAddr addr2 80 ↦U64 oldMemD_11) **
      (.r4 ↦ᵣ vR4Old) **
      (effectiveAddr addr3 0 ↦U64 oldMemD_12) **
      (.r9 ↦ᵣ vR9Old) **
      (effectiveAddr addr3 8 ↦ₘ oldMemB_13) **
      (.r5 ↦ᵣ vR5Old) **
      (.r8 ↦ᵣ vR8Old) **
      (.r6 ↦ᵣ vR6Old) **
      (effectiveAddr addr4 80 ↦U64 oldMemD_14) **
      (effectiveAddr vR10Old (-2064) ↦U64 addr5) **
      (effectiveAddr addr5 80 ↦U64 oldMemD_17) **
      (effectiveAddr addr6 0 ↦U64 oldMemD_20) **
      (effectiveAddr addr5 8 ↦U64 oldMemD_23) **
      (effectiveAddr addr5 16 ↦U64 oldMemD_25) **
      (effectiveAddr addr5 24 ↦U64 oldMemD_27) **
      (effectiveAddr vR10Old (-2096) ↦U64 oldMemD_28) **
      (effectiveAddr addr5 32 ↦U64 oldMemD_30) **
      (effectiveAddr vR10Old (-2088) ↦U64 oldMemD_32) **
      (effectiveAddr vR10Old (-2104) ↦U64 oldMemD_33) **
      (effectiveAddr vR10Old (-2056) ↦U64 addr7) **
      (effectiveAddr addr7 8 ↦U64 oldMemD_36) **
      (effectiveAddr addr7 16 ↦U64 oldMemD_37) **
      (effectiveAddr addr7 24 ↦U64 oldMemD_39) **
      (effectiveAddr addr7 32 ↦U64 oldMemD_41) **
      (effectiveAddr addr7 80 ↦U64 oldMemD_43) **
      (effectiveAddr addr7 1 ↦ₘ oldMemB_44))
      ((.r1 ↦ᵣ wrapSub oldMemD_45 oldMemD_20) **
      (effectiveAddr baseAddr 0 ↦ₘ oldMemB_0) **
      (.r2 ↦ᵣ oldMemD_42) **
      (effectiveAddr baseAddr 88 ↦U64 oldMemD_1) **
      (effectiveAddr baseAddr 10512 ↦ₘ oldMemB_2) **
      (effectiveAddr baseAddr 10592 ↦U64 oldMemD_3) **
      (.r0 ↦ᵣ toU64 0) **
      (effectiveAddr baseAddr 0 ↦U64 oldMemD_4) **
      (.r7 ↦ᵣ oldMemD_4) **
      (.r10 ↦ᵣ vR10Old) **
      (effectiveAddr vR10Old (-2072) ↦U64 addr4) **
      (.r3 ↦ᵣ addr5) **
      (effectiveAddr addr0 0 ↦ₘ oldMemB_6) **
      (effectiveAddr addr1 8 ↦U64 addr0) **
      (effectiveAddr addr0 80 ↦U64 oldMemD_8) **
      (effectiveAddr addr2 0 ↦ₘ oldMemB_9) **
      (effectiveAddr addr1 16 ↦U64 addr2) **
      (effectiveAddr addr2 80 ↦U64 oldMemD_11) **
      (.r4 ↦ᵣ addr4) **
      (effectiveAddr addr3 0 ↦U64 oldMemD_12) **
      (.r9 ↦ᵣ toU64 4) **
      (effectiveAddr addr3 8 ↦ₘ oldMemB_13) **
      (.r5 ↦ᵣ oldMemD_20) **
      (.r8 ↦ᵣ addr6) **
      (.r6 ↦ᵣ toU64 0) **
      (effectiveAddr addr4 80 ↦U64 oldMemD_14) **
      (effectiveAddr vR10Old (-2064) ↦U64 addr5) **
      (effectiveAddr addr5 80 ↦U64 oldMemD_17) **
      (effectiveAddr addr6 0 ↦U64 oldMemD_20) **
      (effectiveAddr addr5 8 ↦U64 oldMemD_23) **
      (effectiveAddr addr5 16 ↦U64 oldMemD_25) **
      (effectiveAddr addr5 24 ↦U64 oldMemD_27) **
      (effectiveAddr vR10Old (-2096) ↦U64 oldMemD_21) **
      (effectiveAddr addr5 32 ↦U64 oldMemD_30) **
      (effectiveAddr vR10Old (-2088) ↦U64 oldMemD_20) **
      (effectiveAddr vR10Old (-2104) ↦U64 wrapAdd vR10Old (toU64 (-2048))) **
      (effectiveAddr vR10Old (-2056) ↦U64 addr7) **
      (effectiveAddr addr7 8 ↦U64 oldMemD_36) **
      (effectiveAddr addr7 16 ↦U64 oldMemD_37) **
      (effectiveAddr addr7 24 ↦U64 oldMemD_39) **
      (effectiveAddr addr7 32 ↦U64 oldMemD_41) **
      (effectiveAddr addr7 80 ↦U64 oldMemD_43) **
      (effectiveAddr addr7 1 ↦ₘ oldMemB_44)) := by
  unfold SVM.Solana.Abstract.AsmRefinesTokenBurn
  simp only [SVM.Solana.Abstract.Mint.withSupply, SVM.Solana.Abstract.TokenAccount.withAmount]
  rw [src_account_eq (addr4 + 88) oldMemD_22 oldMemD_24 oldMemD_26 oldMemD_29 oldMemD_31 oldMemD_38 oldMemD_40 oldMemD_42 oldMemD_21 oldMemB_35 oldMemB_15 oldMemB_19 g1 g2 g1sz h_oldMemB_35 h_oldMemB_15 h_oldMemB_19,
      mint_supply_eq (addr5 + 88) oldMemD_45 oldMemB_18 preAuth5 g3 g4 g3sz h_oldMemB_18,
      src_account_eq (addr4 + 88) oldMemD_22 oldMemD_24 oldMemD_26 oldMemD_29 oldMemD_31 oldMemD_38 oldMemD_40 oldMemD_42 (oldMemD_21 - oldMemD_20) oldMemB_35 oldMemB_15 oldMemB_19 g1 g2 g1sz h_oldMemB_35 h_oldMemB_15 h_oldMemB_19,
      mint_supply_eq (addr5 + 88) (oldMemD_45 - oldMemD_20) oldMemB_18 preAuth5 g3 g4 g3sz h_oldMemB_18]
  simp only [pubkeyIs]
  have framed := cuTripleWithinMem_frame_right
    ( memBytesIs (addr4 + 161) g1 **
      memBytesIs (addr4 + 198) g2 **
      memBytesIs (addr5 + 88) preAuth5 **
      memBytesIs (addr5 + 132) g3 **
      memBytesIs (addr5 + 134) g4 )
    (by sl_pcfree) lift
  simp only [Nat.add_assoc, Nat.reduceAdd]
  sl_exact framed

/-- Discharge-route reshape: the `AsmRefinesTokenBurn` obligation is a layout-general
    field-list (`codecCoarse`/`tokenFields`/`mintFields`) obligation. The
    convergence keystones (`tokenAcctBalance_codec` / `mintSupply_codec`)
    rewrite the bespoke `tokenAcctBalanceOf` / `mintSupplyOf` atoms to the
    field-list codec, so qedgen reads the mutated field off the decoded list
    via the library `*_ensures_*` facts (`qedsvm_discharge`). Pairs with
    `refines_asm` (the lift realises the obligation). -/
theorem refines_field
    (cr : CodeReq) (rr : Memory.RegionTable → Prop)
    (baseAddr oldMemB_0 vR2Old oldMemD_1 oldMemB_2 oldMemD_3 vR0Old oldMemD_4 vR7Old vR10Old oldMemD_5 vR3Old oldMemB_6 oldMemD_7 oldMemD_8 oldMemB_9 oldMemD_10 oldMemD_11 vR4Old oldMemD_12 vR9Old oldMemB_13 vR5Old vR8Old vR6Old oldMemD_14 oldMemB_15 oldMemD_16 oldMemD_17 oldMemB_18 oldMemB_19 oldMemD_20 oldMemD_21 oldMemD_22 oldMemD_23 oldMemD_24 oldMemD_25 oldMemD_26 oldMemD_27 oldMemD_28 oldMemD_29 oldMemD_30 oldMemD_31 oldMemD_32 oldMemD_33 oldMemD_34 oldMemB_35 oldMemD_36 oldMemD_37 oldMemD_38 oldMemD_39 oldMemD_40 oldMemD_41 oldMemD_42 oldMemD_43 oldMemB_44 oldMemD_45 : Nat)
    (g1 g2 preAuth5 g3 g4 : ByteArray)
    (h : SVM.Solana.Abstract.AsmRefinesTokenBurn cr 130 0 198 3542 rr (addr4 + 88) (addr5 + 88)
      { mint := ⟨oldMemD_22, oldMemD_24, oldMemD_26, oldMemD_29⟩,
        owner := ⟨oldMemD_31, oldMemD_38, oldMemD_40, oldMemD_42⟩, amount := oldMemD_21,
        rest := PartialState.byteBA oldMemB_35 ++ (g1 ++ (PartialState.byteBA oldMemB_15 ++ (PartialState.byteBA oldMemB_19 ++ g2))) }
      { preAuth := preAuth5,
        supply := oldMemD_45,
        rest := g3 ++ (PartialState.byteBA oldMemB_18 ++ g4) }
      oldMemD_20
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦ₘ oldMemB_0) **
      (.r2 ↦ᵣ vR2Old) **
      (effectiveAddr baseAddr 88 ↦U64 oldMemD_1) **
      (effectiveAddr baseAddr 10512 ↦ₘ oldMemB_2) **
      (effectiveAddr baseAddr 10592 ↦U64 oldMemD_3) **
      (.r0 ↦ᵣ vR0Old) **
      (effectiveAddr baseAddr 0 ↦U64 oldMemD_4) **
      (.r7 ↦ᵣ vR7Old) **
      (.r10 ↦ᵣ vR10Old) **
      (effectiveAddr vR10Old (-2072) ↦U64 oldMemD_5) **
      (.r3 ↦ᵣ vR3Old) **
      (effectiveAddr addr0 0 ↦ₘ oldMemB_6) **
      (effectiveAddr addr1 8 ↦U64 oldMemD_7) **
      (effectiveAddr addr0 80 ↦U64 oldMemD_8) **
      (effectiveAddr addr2 0 ↦ₘ oldMemB_9) **
      (effectiveAddr addr1 16 ↦U64 oldMemD_10) **
      (effectiveAddr addr2 80 ↦U64 oldMemD_11) **
      (.r4 ↦ᵣ vR4Old) **
      (effectiveAddr addr3 0 ↦U64 oldMemD_12) **
      (.r9 ↦ᵣ vR9Old) **
      (effectiveAddr addr3 8 ↦ₘ oldMemB_13) **
      (.r5 ↦ᵣ vR5Old) **
      (.r8 ↦ᵣ vR8Old) **
      (.r6 ↦ᵣ vR6Old) **
      (effectiveAddr addr4 80 ↦U64 oldMemD_14) **
      (effectiveAddr vR10Old (-2064) ↦U64 addr5) **
      (effectiveAddr addr5 80 ↦U64 oldMemD_17) **
      (effectiveAddr addr6 0 ↦U64 oldMemD_20) **
      (effectiveAddr addr5 8 ↦U64 oldMemD_23) **
      (effectiveAddr addr5 16 ↦U64 oldMemD_25) **
      (effectiveAddr addr5 24 ↦U64 oldMemD_27) **
      (effectiveAddr vR10Old (-2096) ↦U64 oldMemD_28) **
      (effectiveAddr addr5 32 ↦U64 oldMemD_30) **
      (effectiveAddr vR10Old (-2088) ↦U64 oldMemD_32) **
      (effectiveAddr vR10Old (-2104) ↦U64 oldMemD_33) **
      (effectiveAddr vR10Old (-2056) ↦U64 addr7) **
      (effectiveAddr addr7 8 ↦U64 oldMemD_36) **
      (effectiveAddr addr7 16 ↦U64 oldMemD_37) **
      (effectiveAddr addr7 24 ↦U64 oldMemD_39) **
      (effectiveAddr addr7 32 ↦U64 oldMemD_41) **
      (effectiveAddr addr7 80 ↦U64 oldMemD_43) **
      (effectiveAddr addr7 1 ↦ₘ oldMemB_44))
      ((.r1 ↦ᵣ wrapSub oldMemD_45 oldMemD_20) **
      (effectiveAddr baseAddr 0 ↦ₘ oldMemB_0) **
      (.r2 ↦ᵣ oldMemD_42) **
      (effectiveAddr baseAddr 88 ↦U64 oldMemD_1) **
      (effectiveAddr baseAddr 10512 ↦ₘ oldMemB_2) **
      (effectiveAddr baseAddr 10592 ↦U64 oldMemD_3) **
      (.r0 ↦ᵣ toU64 0) **
      (effectiveAddr baseAddr 0 ↦U64 oldMemD_4) **
      (.r7 ↦ᵣ oldMemD_4) **
      (.r10 ↦ᵣ vR10Old) **
      (effectiveAddr vR10Old (-2072) ↦U64 addr4) **
      (.r3 ↦ᵣ addr5) **
      (effectiveAddr addr0 0 ↦ₘ oldMemB_6) **
      (effectiveAddr addr1 8 ↦U64 addr0) **
      (effectiveAddr addr0 80 ↦U64 oldMemD_8) **
      (effectiveAddr addr2 0 ↦ₘ oldMemB_9) **
      (effectiveAddr addr1 16 ↦U64 addr2) **
      (effectiveAddr addr2 80 ↦U64 oldMemD_11) **
      (.r4 ↦ᵣ addr4) **
      (effectiveAddr addr3 0 ↦U64 oldMemD_12) **
      (.r9 ↦ᵣ toU64 4) **
      (effectiveAddr addr3 8 ↦ₘ oldMemB_13) **
      (.r5 ↦ᵣ oldMemD_20) **
      (.r8 ↦ᵣ addr6) **
      (.r6 ↦ᵣ toU64 0) **
      (effectiveAddr addr4 80 ↦U64 oldMemD_14) **
      (effectiveAddr vR10Old (-2064) ↦U64 addr5) **
      (effectiveAddr addr5 80 ↦U64 oldMemD_17) **
      (effectiveAddr addr6 0 ↦U64 oldMemD_20) **
      (effectiveAddr addr5 8 ↦U64 oldMemD_23) **
      (effectiveAddr addr5 16 ↦U64 oldMemD_25) **
      (effectiveAddr addr5 24 ↦U64 oldMemD_27) **
      (effectiveAddr vR10Old (-2096) ↦U64 oldMemD_21) **
      (effectiveAddr addr5 32 ↦U64 oldMemD_30) **
      (effectiveAddr vR10Old (-2088) ↦U64 oldMemD_20) **
      (effectiveAddr vR10Old (-2104) ↦U64 wrapAdd vR10Old (toU64 (-2048))) **
      (effectiveAddr vR10Old (-2056) ↦U64 addr7) **
      (effectiveAddr addr7 8 ↦U64 oldMemD_36) **
      (effectiveAddr addr7 16 ↦U64 oldMemD_37) **
      (effectiveAddr addr7 24 ↦U64 oldMemD_39) **
      (effectiveAddr addr7 32 ↦U64 oldMemD_41) **
      (effectiveAddr addr7 80 ↦U64 oldMemD_43) **
      (effectiveAddr addr7 1 ↦ₘ oldMemB_44))) :
    cuTripleWithinMem 130 0 198 3542 cr
      (((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦ₘ oldMemB_0) **
      (.r2 ↦ᵣ vR2Old) **
      (effectiveAddr baseAddr 88 ↦U64 oldMemD_1) **
      (effectiveAddr baseAddr 10512 ↦ₘ oldMemB_2) **
      (effectiveAddr baseAddr 10592 ↦U64 oldMemD_3) **
      (.r0 ↦ᵣ vR0Old) **
      (effectiveAddr baseAddr 0 ↦U64 oldMemD_4) **
      (.r7 ↦ᵣ vR7Old) **
      (.r10 ↦ᵣ vR10Old) **
      (effectiveAddr vR10Old (-2072) ↦U64 oldMemD_5) **
      (.r3 ↦ᵣ vR3Old) **
      (effectiveAddr addr0 0 ↦ₘ oldMemB_6) **
      (effectiveAddr addr1 8 ↦U64 oldMemD_7) **
      (effectiveAddr addr0 80 ↦U64 oldMemD_8) **
      (effectiveAddr addr2 0 ↦ₘ oldMemB_9) **
      (effectiveAddr addr1 16 ↦U64 oldMemD_10) **
      (effectiveAddr addr2 80 ↦U64 oldMemD_11) **
      (.r4 ↦ᵣ vR4Old) **
      (effectiveAddr addr3 0 ↦U64 oldMemD_12) **
      (.r9 ↦ᵣ vR9Old) **
      (effectiveAddr addr3 8 ↦ₘ oldMemB_13) **
      (.r5 ↦ᵣ vR5Old) **
      (.r8 ↦ᵣ vR8Old) **
      (.r6 ↦ᵣ vR6Old) **
      (effectiveAddr addr4 80 ↦U64 oldMemD_14) **
      (effectiveAddr vR10Old (-2064) ↦U64 addr5) **
      (effectiveAddr addr5 80 ↦U64 oldMemD_17) **
      (effectiveAddr addr6 0 ↦U64 oldMemD_20) **
      (effectiveAddr addr5 8 ↦U64 oldMemD_23) **
      (effectiveAddr addr5 16 ↦U64 oldMemD_25) **
      (effectiveAddr addr5 24 ↦U64 oldMemD_27) **
      (effectiveAddr vR10Old (-2096) ↦U64 oldMemD_28) **
      (effectiveAddr addr5 32 ↦U64 oldMemD_30) **
      (effectiveAddr vR10Old (-2088) ↦U64 oldMemD_32) **
      (effectiveAddr vR10Old (-2104) ↦U64 oldMemD_33) **
      (effectiveAddr vR10Old (-2056) ↦U64 addr7) **
      (effectiveAddr addr7 8 ↦U64 oldMemD_36) **
      (effectiveAddr addr7 16 ↦U64 oldMemD_37) **
      (effectiveAddr addr7 24 ↦U64 oldMemD_39) **
      (effectiveAddr addr7 32 ↦U64 oldMemD_41) **
      (effectiveAddr addr7 80 ↦U64 oldMemD_43) **
      (effectiveAddr addr7 1 ↦ₘ oldMemB_44)) **
      codecCoarse (addr4 + 88) (SVM.Solana.tokenFields ⟨oldMemD_22, oldMemD_24, oldMemD_26, oldMemD_29⟩ ⟨oldMemD_31, oldMemD_38, oldMemD_40, oldMemD_42⟩ oldMemD_21 (PartialState.byteBA oldMemB_35 ++ (g1 ++ (PartialState.byteBA oldMemB_15 ++ (PartialState.byteBA oldMemB_19 ++ g2))))) **
      codecCoarse (addr5 + 88) (SVM.Solana.mintFields (preAuth5) oldMemD_45 (g3 ++ (PartialState.byteBA oldMemB_18 ++ g4))))
      (((.r1 ↦ᵣ wrapSub oldMemD_45 oldMemD_20) **
      (effectiveAddr baseAddr 0 ↦ₘ oldMemB_0) **
      (.r2 ↦ᵣ oldMemD_42) **
      (effectiveAddr baseAddr 88 ↦U64 oldMemD_1) **
      (effectiveAddr baseAddr 10512 ↦ₘ oldMemB_2) **
      (effectiveAddr baseAddr 10592 ↦U64 oldMemD_3) **
      (.r0 ↦ᵣ toU64 0) **
      (effectiveAddr baseAddr 0 ↦U64 oldMemD_4) **
      (.r7 ↦ᵣ oldMemD_4) **
      (.r10 ↦ᵣ vR10Old) **
      (effectiveAddr vR10Old (-2072) ↦U64 addr4) **
      (.r3 ↦ᵣ addr5) **
      (effectiveAddr addr0 0 ↦ₘ oldMemB_6) **
      (effectiveAddr addr1 8 ↦U64 addr0) **
      (effectiveAddr addr0 80 ↦U64 oldMemD_8) **
      (effectiveAddr addr2 0 ↦ₘ oldMemB_9) **
      (effectiveAddr addr1 16 ↦U64 addr2) **
      (effectiveAddr addr2 80 ↦U64 oldMemD_11) **
      (.r4 ↦ᵣ addr4) **
      (effectiveAddr addr3 0 ↦U64 oldMemD_12) **
      (.r9 ↦ᵣ toU64 4) **
      (effectiveAddr addr3 8 ↦ₘ oldMemB_13) **
      (.r5 ↦ᵣ oldMemD_20) **
      (.r8 ↦ᵣ addr6) **
      (.r6 ↦ᵣ toU64 0) **
      (effectiveAddr addr4 80 ↦U64 oldMemD_14) **
      (effectiveAddr vR10Old (-2064) ↦U64 addr5) **
      (effectiveAddr addr5 80 ↦U64 oldMemD_17) **
      (effectiveAddr addr6 0 ↦U64 oldMemD_20) **
      (effectiveAddr addr5 8 ↦U64 oldMemD_23) **
      (effectiveAddr addr5 16 ↦U64 oldMemD_25) **
      (effectiveAddr addr5 24 ↦U64 oldMemD_27) **
      (effectiveAddr vR10Old (-2096) ↦U64 oldMemD_21) **
      (effectiveAddr addr5 32 ↦U64 oldMemD_30) **
      (effectiveAddr vR10Old (-2088) ↦U64 oldMemD_20) **
      (effectiveAddr vR10Old (-2104) ↦U64 wrapAdd vR10Old (toU64 (-2048))) **
      (effectiveAddr vR10Old (-2056) ↦U64 addr7) **
      (effectiveAddr addr7 8 ↦U64 oldMemD_36) **
      (effectiveAddr addr7 16 ↦U64 oldMemD_37) **
      (effectiveAddr addr7 24 ↦U64 oldMemD_39) **
      (effectiveAddr addr7 32 ↦U64 oldMemD_41) **
      (effectiveAddr addr7 80 ↦U64 oldMemD_43) **
      (effectiveAddr addr7 1 ↦ₘ oldMemB_44)) **
      codecCoarse (addr4 + 88) (SVM.Solana.tokenFields ⟨oldMemD_22, oldMemD_24, oldMemD_26, oldMemD_29⟩ ⟨oldMemD_31, oldMemD_38, oldMemD_40, oldMemD_42⟩ (oldMemD_21 - oldMemD_20) (PartialState.byteBA oldMemB_35 ++ (g1 ++ (PartialState.byteBA oldMemB_15 ++ (PartialState.byteBA oldMemB_19 ++ g2))))) **
      codecCoarse (addr5 + 88) (SVM.Solana.mintFields (preAuth5) (oldMemD_45 - oldMemD_20) (g3 ++ (PartialState.byteBA oldMemB_18 ++ g4))))
      rr := by
  unfold SVM.Solana.Abstract.AsmRefinesTokenBurn at h
  simpa only [SVM.Solana.tokenAcctBalanceOf_eq, SVM.Solana.tokenAcctBalanceOf_withAmount, SVM.Solana.tokenAcctBalance_codec, SVM.Solana.mintSupplyOf_eq, SVM.Solana.mintSupplyOf_withSupply, SVM.Solana.mintSupply_codec] using h

end Examples.PTokenBurnRefinement
