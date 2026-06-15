-- AsmRefinesTokenMintTo. MECHANICALLY EMITTED by qedlift. Do not hand-edit.

import SVM.SBPF.Tactic.SL
import SVM.Solana.Abstract.Refinement
import SVM.Solana.TokenFieldCodec
import Generated.PTokenMintToTracedLifted
import SVM.Solana.MintFieldCodec
import PToken.MintAggregation

namespace Examples.PTokenMintToRefinement
open SVM SVM.SBPF SVM.SBPF.Memory
open Examples.PTokenMintAggregation

set_option maxHeartbeats 800000 in
theorem refines_asm
    (cr : CodeReq) (rr : Memory.RegionTable → Prop)
    (baseAddr oldMemB_0 vR2Old oldMemD_1 vR0Old oldMemB_2 oldMemB_3 oldMemB_4 oldMemB_5 oldMemB_6 oldMemB_7 oldMemB_8 vR7Old vR10Old oldMemD_9 vR3Old oldMemB_10 oldMemD_11 oldMemD_12 oldMemB_13 oldMemD_14 oldMemD_15 vR4Old oldMemD_16 vR9Old oldMemB_17 vR5Old vR8Old vR6Old oldMemB_18 oldMemB_19 oldMemD_20 oldMemD_21 oldMemD_22 oldMemD_23 oldMemD_24 oldMemD_25 oldMemD_26 oldMemD_27 oldMemB_28 oldMemB_29 oldMemD_30 oldMemD_31 oldMemD_32 oldMemD_33 oldMemD_34 oldMemD_35 oldMemD_36 oldMemD_37 oldMemD_38 oldMemB_39 oldMemD_40 oldMemD_41 o0 o1 o2 o3 : Nat)
    (g3 g1 g2 g4 g5 : ByteArray)
    (g3sz : g3.size = 3)
    (h_oldMemB_29 : oldMemB_29 < 256)
    (h_oldMemB_28 : oldMemB_28 < 256)
    (g1sz : g1.size = 1)
    (g4sz : g4.size = 36)
    (h_oldMemB_18 : oldMemB_18 < 256)
    (h_oldMemB_19 : oldMemB_19 < 256)
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
    SVM.Solana.Abstract.AsmRefinesTokenMintTo cr 119 0 198 3542 rr (addr4 + 88) (addr0 + 88)
      { preAuth := PartialState.byteBA oldMemB_29 ++ (g3 ++ (PartialState.u64LE oldMemD_31 ++ (PartialState.u64LE oldMemD_33 ++ (PartialState.u64LE oldMemD_35 ++ PartialState.u64LE oldMemD_37)))),
        supply := oldMemD_40,
        rest := g1 ++ (PartialState.byteBA oldMemB_28 ++ g2) }
      { mint := ⟨oldMemD_20, oldMemD_22, oldMemD_24, oldMemD_26⟩,
        owner := ⟨o0, o1, o2, o3⟩, amount := oldMemD_41,
        rest := g4 ++ (PartialState.byteBA oldMemB_18 ++ (PartialState.byteBA oldMemB_19 ++ g5)) }
      oldMemD_38
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
  unfold SVM.Solana.Abstract.AsmRefinesTokenMintTo
  simp only [SVM.Solana.Abstract.Mint.withSupply, SVM.Solana.Abstract.TokenAccount.withAmount]
  rw [mint_account_eq (addr4 + 88) oldMemB_29 oldMemD_31 oldMemD_33 oldMemD_35 oldMemD_37 oldMemD_40 oldMemB_28 g3 g1 g2 g3sz g1sz h_oldMemB_29 h_oldMemB_28,
      dest_account_eq (addr0 + 88) oldMemD_20 oldMemD_22 oldMemD_24 oldMemD_26 o0 o1 o2 o3 oldMemD_41 oldMemB_18 oldMemB_19 g4 g5 g4sz h_oldMemB_18 h_oldMemB_19,
      mint_account_eq (addr4 + 88) oldMemB_29 oldMemD_31 oldMemD_33 oldMemD_35 oldMemD_37 (oldMemD_40 + oldMemD_38) oldMemB_28 g3 g1 g2 g3sz g1sz h_oldMemB_29 h_oldMemB_28,
      dest_account_eq (addr0 + 88) oldMemD_20 oldMemD_22 oldMemD_24 oldMemD_26 o0 o1 o2 o3 (oldMemD_41 + oldMemD_38) oldMemB_18 oldMemB_19 g4 g5 g4sz h_oldMemB_18 h_oldMemB_19]
  simp only [pubkeyIs]
  have framed := cuTripleWithinMem_frame_right
    ( memBytesIs (addr4 + 89) g3 **
      memBytesIs (addr4 + 132) g1 **
      memBytesIs (addr4 + 134) g2 **
      (effectiveAddr addr0 120 ↦U64 o0) **
      (effectiveAddr addr0 128 ↦U64 o1) **
      (effectiveAddr addr0 136 ↦U64 o2) **
      (effectiveAddr addr0 144 ↦U64 o3) **
      memBytesIs (addr0 + 160) g4 **
      memBytesIs (addr0 + 198) g5 )
    (by sl_pcfree) lift
  simp only [Nat.add_assoc, Nat.reduceAdd]
  sl_exact framed

/-- Reshape `AsmRefinesTokenMintTo` from bespoke atoms to `codecCoarse`/field-list form.
    Pairs with `refines_asm`. -/
theorem refines_field
    (cr : CodeReq) (rr : Memory.RegionTable → Prop)
    (baseAddr oldMemB_0 vR2Old oldMemD_1 vR0Old oldMemB_2 oldMemB_3 oldMemB_4 oldMemB_5 oldMemB_6 oldMemB_7 oldMemB_8 vR7Old vR10Old oldMemD_9 vR3Old oldMemB_10 oldMemD_11 oldMemD_12 oldMemB_13 oldMemD_14 oldMemD_15 vR4Old oldMemD_16 vR9Old oldMemB_17 vR5Old vR8Old vR6Old oldMemB_18 oldMemB_19 oldMemD_20 oldMemD_21 oldMemD_22 oldMemD_23 oldMemD_24 oldMemD_25 oldMemD_26 oldMemD_27 oldMemB_28 oldMemB_29 oldMemD_30 oldMemD_31 oldMemD_32 oldMemD_33 oldMemD_34 oldMemD_35 oldMemD_36 oldMemD_37 oldMemD_38 oldMemB_39 oldMemD_40 oldMemD_41 o0 o1 o2 o3 : Nat)
    (g3 g1 g2 g4 g5 : ByteArray)
    (h : SVM.Solana.Abstract.AsmRefinesTokenMintTo cr 119 0 198 3542 rr (addr4 + 88) (addr0 + 88)
      { preAuth := PartialState.byteBA oldMemB_29 ++ (g3 ++ (PartialState.u64LE oldMemD_31 ++ (PartialState.u64LE oldMemD_33 ++ (PartialState.u64LE oldMemD_35 ++ PartialState.u64LE oldMemD_37)))),
        supply := oldMemD_40,
        rest := g1 ++ (PartialState.byteBA oldMemB_28 ++ g2) }
      { mint := ⟨oldMemD_20, oldMemD_22, oldMemD_24, oldMemD_26⟩,
        owner := ⟨o0, o1, o2, o3⟩, amount := oldMemD_41,
        rest := g4 ++ (PartialState.byteBA oldMemB_18 ++ (PartialState.byteBA oldMemB_19 ++ g5)) }
      oldMemD_38
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
      (effectiveAddr addr2 1 ↦ₘ oldMemB_39))) :
    cuTripleWithinMem 119 0 198 3542 cr
      (((.r1 ↦ᵣ baseAddr) **
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
      (effectiveAddr addr2 1 ↦ₘ oldMemB_39)) **
      codecCoarse (addr4 + 88) (SVM.Solana.mintFields (PartialState.byteBA oldMemB_29 ++ (g3 ++ (PartialState.u64LE oldMemD_31 ++ (PartialState.u64LE oldMemD_33 ++ (PartialState.u64LE oldMemD_35 ++ PartialState.u64LE oldMemD_37))))) oldMemD_40 (g1 ++ (PartialState.byteBA oldMemB_28 ++ g2))) **
      codecCoarse (addr0 + 88) (SVM.Solana.tokenFields ⟨oldMemD_20, oldMemD_22, oldMemD_24, oldMemD_26⟩ ⟨o0, o1, o2, o3⟩ oldMemD_41 (g4 ++ (PartialState.byteBA oldMemB_18 ++ (PartialState.byteBA oldMemB_19 ++ g5)))))
      (((.r1 ↦ᵣ wrapAdd oldMemD_41 oldMemD_38) **
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
      (effectiveAddr addr2 1 ↦ₘ oldMemB_39)) **
      codecCoarse (addr4 + 88) (SVM.Solana.mintFields (PartialState.byteBA oldMemB_29 ++ (g3 ++ (PartialState.u64LE oldMemD_31 ++ (PartialState.u64LE oldMemD_33 ++ (PartialState.u64LE oldMemD_35 ++ PartialState.u64LE oldMemD_37))))) (oldMemD_40 + oldMemD_38) (g1 ++ (PartialState.byteBA oldMemB_28 ++ g2))) **
      codecCoarse (addr0 + 88) (SVM.Solana.tokenFields ⟨oldMemD_20, oldMemD_22, oldMemD_24, oldMemD_26⟩ ⟨o0, o1, o2, o3⟩ (oldMemD_41 + oldMemD_38) (g4 ++ (PartialState.byteBA oldMemB_18 ++ (PartialState.byteBA oldMemB_19 ++ g5)))))
      rr := by
  unfold SVM.Solana.Abstract.AsmRefinesTokenMintTo at h
  simpa only [SVM.Solana.tokenAcctBalanceOf_eq, SVM.Solana.tokenAcctBalanceOf_withAmount, SVM.Solana.tokenAcctBalance_codec, SVM.Solana.mintSupplyOf_eq, SVM.Solana.mintSupplyOf_withSupply, SVM.Solana.mintSupply_codec] using h

end Examples.PTokenMintToRefinement
