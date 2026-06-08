/-
  AsmRefinesTokenMintTo asm-refines-intrinsic theorem. MECHANICALLY EMITTED by qedlift's
  refinement codegen from the lift's atoms + the IDL arm name. Wires the
  trace-guided lift to `AsmRefinesTokenMintTo` via the codec-aggregation lemmas +
  `cuTripleWithinMem_frame_right` + `sl_exact`.
-/

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
    (baseAddr oldMemB_0 vR2Old oldMemD_1 vR0Old oldMemD_2 vR7Old vR10Old oldMemD_3 vR3Old oldMemB_4 oldMemD_5 oldMemD_6 oldMemB_7 oldMemD_8 oldMemD_9 vR4Old oldMemD_10 vR9Old oldMemB_11 vR5Old vR8Old vR6Old oldMemD_12 oldMemD_13 oldMemB_14 oldMemB_15 oldMemD_16 oldMemD_17 oldMemD_18 oldMemD_19 oldMemD_20 oldMemD_21 oldMemD_22 oldMemD_23 oldMemD_24 oldMemB_25 oldMemB_26 oldMemD_27 oldMemD_28 oldMemD_29 oldMemD_30 oldMemD_31 oldMemD_32 oldMemD_33 oldMemD_34 oldMemD_35 oldMemD_36 oldMemD_37 oldMemB_38 oldMemD_39 oldMemD_40 o0 o1 o2 o3 : Nat)
    (g3 g1 g2 g4 g5 : ByteArray)
    (g3sz : g3.size = 3)
    (h_oldMemB_26 : oldMemB_26 < 256)
    (h_oldMemB_25 : oldMemB_25 < 256)
    (g1sz : g1.size = 1)
    (g4sz : g4.size = 36)
    (h_oldMemB_14 : oldMemB_14 < 256)
    (h_oldMemB_15 : oldMemB_15 < 256)
    (lift : cuTripleWithinMem 119 0 198 3542 cr
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦ₘ oldMemB_0) **
      (.r2 ↦ᵣ vR2Old) **
      (effectiveAddr baseAddr 88 ↦U64 oldMemD_1) **
      (.r0 ↦ᵣ vR0Old) **
      (effectiveAddr baseAddr 0 ↦U64 oldMemD_2) **
      (.r7 ↦ᵣ vR7Old) **
      (.r10 ↦ᵣ vR10Old) **
      (effectiveAddr vR10Old (-2072) ↦U64 oldMemD_3) **
      (.r3 ↦ᵣ vR3Old) **
      (effectiveAddr addr0 0 ↦ₘ oldMemB_4) **
      (effectiveAddr addr1 8 ↦U64 oldMemD_5) **
      (effectiveAddr addr0 80 ↦U64 oldMemD_6) **
      (effectiveAddr addr2 0 ↦ₘ oldMemB_7) **
      (effectiveAddr addr1 16 ↦U64 oldMemD_8) **
      (effectiveAddr addr2 80 ↦U64 oldMemD_9) **
      (.r4 ↦ᵣ vR4Old) **
      (effectiveAddr addr3 0 ↦U64 oldMemD_10) **
      (.r9 ↦ᵣ vR9Old) **
      (effectiveAddr addr3 8 ↦ₘ oldMemB_11) **
      (.r5 ↦ᵣ vR5Old) **
      (.r8 ↦ᵣ vR8Old) **
      (.r6 ↦ᵣ vR6Old) **
      (effectiveAddr vR10Old (-2064) ↦U64 addr4) **
      (effectiveAddr addr4 80 ↦U64 oldMemD_13) **
      (effectiveAddr addr4 196 ↦ₘ oldMemB_14) **
      (effectiveAddr addr4 197 ↦ₘ oldMemB_15) **
      (effectiveAddr addr4 88 ↦U64 oldMemD_16) **
      (effectiveAddr addr5 8 ↦U64 oldMemD_17) **
      (effectiveAddr addr4 96 ↦U64 oldMemD_18) **
      (effectiveAddr addr5 16 ↦U64 oldMemD_19) **
      (effectiveAddr addr4 104 ↦U64 oldMemD_20) **
      (effectiveAddr addr5 24 ↦U64 oldMemD_21) **
      (effectiveAddr addr4 112 ↦U64 oldMemD_22) **
      (effectiveAddr addr5 32 ↦U64 oldMemD_23) **
      (effectiveAddr addr5 80 ↦U64 oldMemD_24) **
      (effectiveAddr addr5 133 ↦ₘ oldMemB_25) **
      (effectiveAddr addr5 88 ↦ₘ oldMemB_26) **
      (effectiveAddr vR10Old (-2056) ↦U64 addr6) **
      (effectiveAddr addr6 8 ↦U64 oldMemD_28) **
      (effectiveAddr addr5 92 ↦U64 oldMemD_29) **
      (effectiveAddr addr6 16 ↦U64 oldMemD_30) **
      (effectiveAddr addr5 100 ↦U64 oldMemD_31) **
      (effectiveAddr addr6 24 ↦U64 oldMemD_32) **
      (effectiveAddr addr5 108 ↦U64 oldMemD_33) **
      (effectiveAddr addr6 32 ↦U64 oldMemD_34) **
      (effectiveAddr addr5 116 ↦U64 oldMemD_35) **
      (effectiveAddr addr7 0 ↦U64 oldMemD_36) **
      (effectiveAddr addr6 80 ↦U64 oldMemD_37) **
      (effectiveAddr addr6 1 ↦ₘ oldMemB_38) **
      (effectiveAddr addr5 124 ↦U64 oldMemD_39) **
      (effectiveAddr addr4 152 ↦U64 oldMemD_40))
      ((.r1 ↦ᵣ wrapAdd oldMemD_40 oldMemD_36) **
      (effectiveAddr baseAddr 0 ↦ₘ oldMemB_0) **
      (.r2 ↦ᵣ ((toU64 0) &&& toU64 1) % U64_MODULUS) **
      (effectiveAddr baseAddr 88 ↦U64 oldMemD_1) **
      (.r0 ↦ᵣ toU64 0) **
      (effectiveAddr baseAddr 0 ↦U64 oldMemD_2) **
      (.r7 ↦ᵣ addr5) **
      (.r10 ↦ᵣ vR10Old) **
      (effectiveAddr vR10Old (-2072) ↦U64 addr5) **
      (.r3 ↦ᵣ addr4) **
      (effectiveAddr addr0 0 ↦ₘ oldMemB_4) **
      (effectiveAddr addr1 8 ↦U64 addr0) **
      (effectiveAddr addr0 80 ↦U64 oldMemD_6) **
      (effectiveAddr addr2 0 ↦ₘ oldMemB_7) **
      (effectiveAddr addr1 16 ↦U64 addr2) **
      (effectiveAddr addr2 80 ↦U64 oldMemD_9) **
      (.r4 ↦ᵣ oldMemD_36) **
      (effectiveAddr addr3 0 ↦U64 oldMemD_10) **
      (.r9 ↦ᵣ toU64 4) **
      (effectiveAddr addr3 8 ↦ₘ oldMemB_11) **
      (.r5 ↦ᵣ oldMemD_39) **
      (.r8 ↦ᵣ addr7) **
      (.r6 ↦ᵣ toU64 0) **
      (effectiveAddr vR10Old (-2064) ↦U64 addr4) **
      (effectiveAddr addr4 80 ↦U64 oldMemD_13) **
      (effectiveAddr addr4 196 ↦ₘ oldMemB_14) **
      (effectiveAddr addr4 197 ↦ₘ oldMemB_15) **
      (effectiveAddr addr4 88 ↦U64 oldMemD_16) **
      (effectiveAddr addr5 8 ↦U64 oldMemD_17) **
      (effectiveAddr addr4 96 ↦U64 oldMemD_18) **
      (effectiveAddr addr5 16 ↦U64 oldMemD_19) **
      (effectiveAddr addr4 104 ↦U64 oldMemD_20) **
      (effectiveAddr addr5 24 ↦U64 oldMemD_21) **
      (effectiveAddr addr4 112 ↦U64 oldMemD_22) **
      (effectiveAddr addr5 32 ↦U64 oldMemD_23) **
      (effectiveAddr addr5 80 ↦U64 oldMemD_24) **
      (effectiveAddr addr5 133 ↦ₘ oldMemB_25) **
      (effectiveAddr addr5 88 ↦ₘ oldMemB_26) **
      (effectiveAddr vR10Old (-2056) ↦U64 addr6) **
      (effectiveAddr addr6 8 ↦U64 oldMemD_28) **
      (effectiveAddr addr5 92 ↦U64 oldMemD_29) **
      (effectiveAddr addr6 16 ↦U64 oldMemD_30) **
      (effectiveAddr addr5 100 ↦U64 oldMemD_31) **
      (effectiveAddr addr6 24 ↦U64 oldMemD_32) **
      (effectiveAddr addr5 108 ↦U64 oldMemD_33) **
      (effectiveAddr addr6 32 ↦U64 oldMemD_34) **
      (effectiveAddr addr5 116 ↦U64 oldMemD_35) **
      (effectiveAddr addr7 0 ↦U64 oldMemD_36) **
      (effectiveAddr addr6 80 ↦U64 oldMemD_37) **
      (effectiveAddr addr6 1 ↦ₘ oldMemB_38) **
      (effectiveAddr addr5 124 ↦U64 oldMemD_39 + oldMemD_36) **
      (effectiveAddr addr4 152 ↦U64 oldMemD_40 + oldMemD_36)) rr) :
    SVM.Solana.Abstract.AsmRefinesTokenMintTo cr 119 0 198 3542 rr (addr5 + 88) (addr4 + 88)
      { preAuth := PartialState.byteBA oldMemB_26 ++ (g3 ++ (PartialState.u64LE oldMemD_29 ++ (PartialState.u64LE oldMemD_31 ++ (PartialState.u64LE oldMemD_33 ++ PartialState.u64LE oldMemD_35)))),
        supply := oldMemD_39,
        rest := g1 ++ (PartialState.byteBA oldMemB_25 ++ g2) }
      { mint := ⟨oldMemD_16, oldMemD_18, oldMemD_20, oldMemD_22⟩,
        owner := ⟨o0, o1, o2, o3⟩, amount := oldMemD_40,
        rest := g4 ++ (PartialState.byteBA oldMemB_14 ++ (PartialState.byteBA oldMemB_15 ++ g5)) }
      oldMemD_36
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦ₘ oldMemB_0) **
      (.r2 ↦ᵣ vR2Old) **
      (effectiveAddr baseAddr 88 ↦U64 oldMemD_1) **
      (.r0 ↦ᵣ vR0Old) **
      (effectiveAddr baseAddr 0 ↦U64 oldMemD_2) **
      (.r7 ↦ᵣ vR7Old) **
      (.r10 ↦ᵣ vR10Old) **
      (effectiveAddr vR10Old (-2072) ↦U64 oldMemD_3) **
      (.r3 ↦ᵣ vR3Old) **
      (effectiveAddr addr0 0 ↦ₘ oldMemB_4) **
      (effectiveAddr addr1 8 ↦U64 oldMemD_5) **
      (effectiveAddr addr0 80 ↦U64 oldMemD_6) **
      (effectiveAddr addr2 0 ↦ₘ oldMemB_7) **
      (effectiveAddr addr1 16 ↦U64 oldMemD_8) **
      (effectiveAddr addr2 80 ↦U64 oldMemD_9) **
      (.r4 ↦ᵣ vR4Old) **
      (effectiveAddr addr3 0 ↦U64 oldMemD_10) **
      (.r9 ↦ᵣ vR9Old) **
      (effectiveAddr addr3 8 ↦ₘ oldMemB_11) **
      (.r5 ↦ᵣ vR5Old) **
      (.r8 ↦ᵣ vR8Old) **
      (.r6 ↦ᵣ vR6Old) **
      (effectiveAddr vR10Old (-2064) ↦U64 addr4) **
      (effectiveAddr addr4 80 ↦U64 oldMemD_13) **
      (effectiveAddr addr5 8 ↦U64 oldMemD_17) **
      (effectiveAddr addr5 16 ↦U64 oldMemD_19) **
      (effectiveAddr addr5 24 ↦U64 oldMemD_21) **
      (effectiveAddr addr5 32 ↦U64 oldMemD_23) **
      (effectiveAddr addr5 80 ↦U64 oldMemD_24) **
      (effectiveAddr vR10Old (-2056) ↦U64 addr6) **
      (effectiveAddr addr6 8 ↦U64 oldMemD_28) **
      (effectiveAddr addr6 16 ↦U64 oldMemD_30) **
      (effectiveAddr addr6 24 ↦U64 oldMemD_32) **
      (effectiveAddr addr6 32 ↦U64 oldMemD_34) **
      (effectiveAddr addr7 0 ↦U64 oldMemD_36) **
      (effectiveAddr addr6 80 ↦U64 oldMemD_37) **
      (effectiveAddr addr6 1 ↦ₘ oldMemB_38))
      ((.r1 ↦ᵣ wrapAdd oldMemD_40 oldMemD_36) **
      (effectiveAddr baseAddr 0 ↦ₘ oldMemB_0) **
      (.r2 ↦ᵣ ((toU64 0) &&& toU64 1) % U64_MODULUS) **
      (effectiveAddr baseAddr 88 ↦U64 oldMemD_1) **
      (.r0 ↦ᵣ toU64 0) **
      (effectiveAddr baseAddr 0 ↦U64 oldMemD_2) **
      (.r7 ↦ᵣ addr5) **
      (.r10 ↦ᵣ vR10Old) **
      (effectiveAddr vR10Old (-2072) ↦U64 addr5) **
      (.r3 ↦ᵣ addr4) **
      (effectiveAddr addr0 0 ↦ₘ oldMemB_4) **
      (effectiveAddr addr1 8 ↦U64 addr0) **
      (effectiveAddr addr0 80 ↦U64 oldMemD_6) **
      (effectiveAddr addr2 0 ↦ₘ oldMemB_7) **
      (effectiveAddr addr1 16 ↦U64 addr2) **
      (effectiveAddr addr2 80 ↦U64 oldMemD_9) **
      (.r4 ↦ᵣ oldMemD_36) **
      (effectiveAddr addr3 0 ↦U64 oldMemD_10) **
      (.r9 ↦ᵣ toU64 4) **
      (effectiveAddr addr3 8 ↦ₘ oldMemB_11) **
      (.r5 ↦ᵣ oldMemD_39) **
      (.r8 ↦ᵣ addr7) **
      (.r6 ↦ᵣ toU64 0) **
      (effectiveAddr vR10Old (-2064) ↦U64 addr4) **
      (effectiveAddr addr4 80 ↦U64 oldMemD_13) **
      (effectiveAddr addr5 8 ↦U64 oldMemD_17) **
      (effectiveAddr addr5 16 ↦U64 oldMemD_19) **
      (effectiveAddr addr5 24 ↦U64 oldMemD_21) **
      (effectiveAddr addr5 32 ↦U64 oldMemD_23) **
      (effectiveAddr addr5 80 ↦U64 oldMemD_24) **
      (effectiveAddr vR10Old (-2056) ↦U64 addr6) **
      (effectiveAddr addr6 8 ↦U64 oldMemD_28) **
      (effectiveAddr addr6 16 ↦U64 oldMemD_30) **
      (effectiveAddr addr6 24 ↦U64 oldMemD_32) **
      (effectiveAddr addr6 32 ↦U64 oldMemD_34) **
      (effectiveAddr addr7 0 ↦U64 oldMemD_36) **
      (effectiveAddr addr6 80 ↦U64 oldMemD_37) **
      (effectiveAddr addr6 1 ↦ₘ oldMemB_38)) := by
  unfold SVM.Solana.Abstract.AsmRefinesTokenMintTo
  simp only [SVM.Solana.Abstract.Mint.withSupply, SVM.Solana.Abstract.TokenAccount.withAmount]
  rw [mint_account_eq (addr5 + 88) oldMemB_26 oldMemD_29 oldMemD_31 oldMemD_33 oldMemD_35 oldMemD_39 oldMemB_25 g3 g1 g2 g3sz g1sz h_oldMemB_26 h_oldMemB_25,
      dest_account_eq (addr4 + 88) oldMemD_16 oldMemD_18 oldMemD_20 oldMemD_22 o0 o1 o2 o3 oldMemD_40 oldMemB_14 oldMemB_15 g4 g5 g4sz h_oldMemB_14 h_oldMemB_15,
      mint_account_eq (addr5 + 88) oldMemB_26 oldMemD_29 oldMemD_31 oldMemD_33 oldMemD_35 (oldMemD_39 + oldMemD_36) oldMemB_25 g3 g1 g2 g3sz g1sz h_oldMemB_26 h_oldMemB_25,
      dest_account_eq (addr4 + 88) oldMemD_16 oldMemD_18 oldMemD_20 oldMemD_22 o0 o1 o2 o3 (oldMemD_40 + oldMemD_36) oldMemB_14 oldMemB_15 g4 g5 g4sz h_oldMemB_14 h_oldMemB_15]
  simp only [pubkeyIs]
  have framed := cuTripleWithinMem_frame_right
    ( memBytesIs (addr5 + 89) g3 **
      memBytesIs (addr5 + 132) g1 **
      memBytesIs (addr5 + 134) g2 **
      (effectiveAddr addr4 120 ↦U64 o0) **
      (effectiveAddr addr4 128 ↦U64 o1) **
      (effectiveAddr addr4 136 ↦U64 o2) **
      (effectiveAddr addr4 144 ↦U64 o3) **
      memBytesIs (addr4 + 160) g4 **
      memBytesIs (addr4 + 198) g5 )
    (by sl_pcfree) lift
  simp only [Nat.add_assoc, Nat.reduceAdd]
  sl_exact framed

/-- Discharge-route reshape: the `AsmRefinesTokenMintTo` obligation is a layout-general
    field-list (`codecCoarse`/`tokenFields`/`mintFields`) obligation. The
    convergence keystones (`tokenAcctBalance_codec` / `mintSupply_codec`)
    rewrite the bespoke `tokenAcctBalanceOf` / `mintSupplyOf` atoms to the
    field-list codec, so qedgen reads the mutated field off the decoded list
    via the library `*_ensures_*` facts (`qedsvm_discharge`). Pairs with
    `refines_asm` (the lift realises the obligation). -/
theorem refines_field
    (cr : CodeReq) (rr : Memory.RegionTable → Prop)
    (baseAddr oldMemB_0 vR2Old oldMemD_1 vR0Old oldMemD_2 vR7Old vR10Old oldMemD_3 vR3Old oldMemB_4 oldMemD_5 oldMemD_6 oldMemB_7 oldMemD_8 oldMemD_9 vR4Old oldMemD_10 vR9Old oldMemB_11 vR5Old vR8Old vR6Old oldMemD_12 oldMemD_13 oldMemB_14 oldMemB_15 oldMemD_16 oldMemD_17 oldMemD_18 oldMemD_19 oldMemD_20 oldMemD_21 oldMemD_22 oldMemD_23 oldMemD_24 oldMemB_25 oldMemB_26 oldMemD_27 oldMemD_28 oldMemD_29 oldMemD_30 oldMemD_31 oldMemD_32 oldMemD_33 oldMemD_34 oldMemD_35 oldMemD_36 oldMemD_37 oldMemB_38 oldMemD_39 oldMemD_40 o0 o1 o2 o3 : Nat)
    (g3 g1 g2 g4 g5 : ByteArray)
    (h : SVM.Solana.Abstract.AsmRefinesTokenMintTo cr 119 0 198 3542 rr (addr5 + 88) (addr4 + 88)
      { preAuth := PartialState.byteBA oldMemB_26 ++ (g3 ++ (PartialState.u64LE oldMemD_29 ++ (PartialState.u64LE oldMemD_31 ++ (PartialState.u64LE oldMemD_33 ++ PartialState.u64LE oldMemD_35)))),
        supply := oldMemD_39,
        rest := g1 ++ (PartialState.byteBA oldMemB_25 ++ g2) }
      { mint := ⟨oldMemD_16, oldMemD_18, oldMemD_20, oldMemD_22⟩,
        owner := ⟨o0, o1, o2, o3⟩, amount := oldMemD_40,
        rest := g4 ++ (PartialState.byteBA oldMemB_14 ++ (PartialState.byteBA oldMemB_15 ++ g5)) }
      oldMemD_36
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦ₘ oldMemB_0) **
      (.r2 ↦ᵣ vR2Old) **
      (effectiveAddr baseAddr 88 ↦U64 oldMemD_1) **
      (.r0 ↦ᵣ vR0Old) **
      (effectiveAddr baseAddr 0 ↦U64 oldMemD_2) **
      (.r7 ↦ᵣ vR7Old) **
      (.r10 ↦ᵣ vR10Old) **
      (effectiveAddr vR10Old (-2072) ↦U64 oldMemD_3) **
      (.r3 ↦ᵣ vR3Old) **
      (effectiveAddr addr0 0 ↦ₘ oldMemB_4) **
      (effectiveAddr addr1 8 ↦U64 oldMemD_5) **
      (effectiveAddr addr0 80 ↦U64 oldMemD_6) **
      (effectiveAddr addr2 0 ↦ₘ oldMemB_7) **
      (effectiveAddr addr1 16 ↦U64 oldMemD_8) **
      (effectiveAddr addr2 80 ↦U64 oldMemD_9) **
      (.r4 ↦ᵣ vR4Old) **
      (effectiveAddr addr3 0 ↦U64 oldMemD_10) **
      (.r9 ↦ᵣ vR9Old) **
      (effectiveAddr addr3 8 ↦ₘ oldMemB_11) **
      (.r5 ↦ᵣ vR5Old) **
      (.r8 ↦ᵣ vR8Old) **
      (.r6 ↦ᵣ vR6Old) **
      (effectiveAddr vR10Old (-2064) ↦U64 addr4) **
      (effectiveAddr addr4 80 ↦U64 oldMemD_13) **
      (effectiveAddr addr5 8 ↦U64 oldMemD_17) **
      (effectiveAddr addr5 16 ↦U64 oldMemD_19) **
      (effectiveAddr addr5 24 ↦U64 oldMemD_21) **
      (effectiveAddr addr5 32 ↦U64 oldMemD_23) **
      (effectiveAddr addr5 80 ↦U64 oldMemD_24) **
      (effectiveAddr vR10Old (-2056) ↦U64 addr6) **
      (effectiveAddr addr6 8 ↦U64 oldMemD_28) **
      (effectiveAddr addr6 16 ↦U64 oldMemD_30) **
      (effectiveAddr addr6 24 ↦U64 oldMemD_32) **
      (effectiveAddr addr6 32 ↦U64 oldMemD_34) **
      (effectiveAddr addr7 0 ↦U64 oldMemD_36) **
      (effectiveAddr addr6 80 ↦U64 oldMemD_37) **
      (effectiveAddr addr6 1 ↦ₘ oldMemB_38))
      ((.r1 ↦ᵣ wrapAdd oldMemD_40 oldMemD_36) **
      (effectiveAddr baseAddr 0 ↦ₘ oldMemB_0) **
      (.r2 ↦ᵣ ((toU64 0) &&& toU64 1) % U64_MODULUS) **
      (effectiveAddr baseAddr 88 ↦U64 oldMemD_1) **
      (.r0 ↦ᵣ toU64 0) **
      (effectiveAddr baseAddr 0 ↦U64 oldMemD_2) **
      (.r7 ↦ᵣ addr5) **
      (.r10 ↦ᵣ vR10Old) **
      (effectiveAddr vR10Old (-2072) ↦U64 addr5) **
      (.r3 ↦ᵣ addr4) **
      (effectiveAddr addr0 0 ↦ₘ oldMemB_4) **
      (effectiveAddr addr1 8 ↦U64 addr0) **
      (effectiveAddr addr0 80 ↦U64 oldMemD_6) **
      (effectiveAddr addr2 0 ↦ₘ oldMemB_7) **
      (effectiveAddr addr1 16 ↦U64 addr2) **
      (effectiveAddr addr2 80 ↦U64 oldMemD_9) **
      (.r4 ↦ᵣ oldMemD_36) **
      (effectiveAddr addr3 0 ↦U64 oldMemD_10) **
      (.r9 ↦ᵣ toU64 4) **
      (effectiveAddr addr3 8 ↦ₘ oldMemB_11) **
      (.r5 ↦ᵣ oldMemD_39) **
      (.r8 ↦ᵣ addr7) **
      (.r6 ↦ᵣ toU64 0) **
      (effectiveAddr vR10Old (-2064) ↦U64 addr4) **
      (effectiveAddr addr4 80 ↦U64 oldMemD_13) **
      (effectiveAddr addr5 8 ↦U64 oldMemD_17) **
      (effectiveAddr addr5 16 ↦U64 oldMemD_19) **
      (effectiveAddr addr5 24 ↦U64 oldMemD_21) **
      (effectiveAddr addr5 32 ↦U64 oldMemD_23) **
      (effectiveAddr addr5 80 ↦U64 oldMemD_24) **
      (effectiveAddr vR10Old (-2056) ↦U64 addr6) **
      (effectiveAddr addr6 8 ↦U64 oldMemD_28) **
      (effectiveAddr addr6 16 ↦U64 oldMemD_30) **
      (effectiveAddr addr6 24 ↦U64 oldMemD_32) **
      (effectiveAddr addr6 32 ↦U64 oldMemD_34) **
      (effectiveAddr addr7 0 ↦U64 oldMemD_36) **
      (effectiveAddr addr6 80 ↦U64 oldMemD_37) **
      (effectiveAddr addr6 1 ↦ₘ oldMemB_38))) :
    cuTripleWithinMem 119 0 198 3542 cr
      (((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦ₘ oldMemB_0) **
      (.r2 ↦ᵣ vR2Old) **
      (effectiveAddr baseAddr 88 ↦U64 oldMemD_1) **
      (.r0 ↦ᵣ vR0Old) **
      (effectiveAddr baseAddr 0 ↦U64 oldMemD_2) **
      (.r7 ↦ᵣ vR7Old) **
      (.r10 ↦ᵣ vR10Old) **
      (effectiveAddr vR10Old (-2072) ↦U64 oldMemD_3) **
      (.r3 ↦ᵣ vR3Old) **
      (effectiveAddr addr0 0 ↦ₘ oldMemB_4) **
      (effectiveAddr addr1 8 ↦U64 oldMemD_5) **
      (effectiveAddr addr0 80 ↦U64 oldMemD_6) **
      (effectiveAddr addr2 0 ↦ₘ oldMemB_7) **
      (effectiveAddr addr1 16 ↦U64 oldMemD_8) **
      (effectiveAddr addr2 80 ↦U64 oldMemD_9) **
      (.r4 ↦ᵣ vR4Old) **
      (effectiveAddr addr3 0 ↦U64 oldMemD_10) **
      (.r9 ↦ᵣ vR9Old) **
      (effectiveAddr addr3 8 ↦ₘ oldMemB_11) **
      (.r5 ↦ᵣ vR5Old) **
      (.r8 ↦ᵣ vR8Old) **
      (.r6 ↦ᵣ vR6Old) **
      (effectiveAddr vR10Old (-2064) ↦U64 addr4) **
      (effectiveAddr addr4 80 ↦U64 oldMemD_13) **
      (effectiveAddr addr5 8 ↦U64 oldMemD_17) **
      (effectiveAddr addr5 16 ↦U64 oldMemD_19) **
      (effectiveAddr addr5 24 ↦U64 oldMemD_21) **
      (effectiveAddr addr5 32 ↦U64 oldMemD_23) **
      (effectiveAddr addr5 80 ↦U64 oldMemD_24) **
      (effectiveAddr vR10Old (-2056) ↦U64 addr6) **
      (effectiveAddr addr6 8 ↦U64 oldMemD_28) **
      (effectiveAddr addr6 16 ↦U64 oldMemD_30) **
      (effectiveAddr addr6 24 ↦U64 oldMemD_32) **
      (effectiveAddr addr6 32 ↦U64 oldMemD_34) **
      (effectiveAddr addr7 0 ↦U64 oldMemD_36) **
      (effectiveAddr addr6 80 ↦U64 oldMemD_37) **
      (effectiveAddr addr6 1 ↦ₘ oldMemB_38)) **
      codecCoarse (addr5 + 88) (SVM.Solana.mintFields (PartialState.byteBA oldMemB_26 ++ (g3 ++ (PartialState.u64LE oldMemD_29 ++ (PartialState.u64LE oldMemD_31 ++ (PartialState.u64LE oldMemD_33 ++ PartialState.u64LE oldMemD_35))))) oldMemD_39 (g1 ++ (PartialState.byteBA oldMemB_25 ++ g2))) **
      codecCoarse (addr4 + 88) (SVM.Solana.tokenFields ⟨oldMemD_16, oldMemD_18, oldMemD_20, oldMemD_22⟩ ⟨o0, o1, o2, o3⟩ oldMemD_40 (g4 ++ (PartialState.byteBA oldMemB_14 ++ (PartialState.byteBA oldMemB_15 ++ g5)))))
      (((.r1 ↦ᵣ wrapAdd oldMemD_40 oldMemD_36) **
      (effectiveAddr baseAddr 0 ↦ₘ oldMemB_0) **
      (.r2 ↦ᵣ ((toU64 0) &&& toU64 1) % U64_MODULUS) **
      (effectiveAddr baseAddr 88 ↦U64 oldMemD_1) **
      (.r0 ↦ᵣ toU64 0) **
      (effectiveAddr baseAddr 0 ↦U64 oldMemD_2) **
      (.r7 ↦ᵣ addr5) **
      (.r10 ↦ᵣ vR10Old) **
      (effectiveAddr vR10Old (-2072) ↦U64 addr5) **
      (.r3 ↦ᵣ addr4) **
      (effectiveAddr addr0 0 ↦ₘ oldMemB_4) **
      (effectiveAddr addr1 8 ↦U64 addr0) **
      (effectiveAddr addr0 80 ↦U64 oldMemD_6) **
      (effectiveAddr addr2 0 ↦ₘ oldMemB_7) **
      (effectiveAddr addr1 16 ↦U64 addr2) **
      (effectiveAddr addr2 80 ↦U64 oldMemD_9) **
      (.r4 ↦ᵣ oldMemD_36) **
      (effectiveAddr addr3 0 ↦U64 oldMemD_10) **
      (.r9 ↦ᵣ toU64 4) **
      (effectiveAddr addr3 8 ↦ₘ oldMemB_11) **
      (.r5 ↦ᵣ oldMemD_39) **
      (.r8 ↦ᵣ addr7) **
      (.r6 ↦ᵣ toU64 0) **
      (effectiveAddr vR10Old (-2064) ↦U64 addr4) **
      (effectiveAddr addr4 80 ↦U64 oldMemD_13) **
      (effectiveAddr addr5 8 ↦U64 oldMemD_17) **
      (effectiveAddr addr5 16 ↦U64 oldMemD_19) **
      (effectiveAddr addr5 24 ↦U64 oldMemD_21) **
      (effectiveAddr addr5 32 ↦U64 oldMemD_23) **
      (effectiveAddr addr5 80 ↦U64 oldMemD_24) **
      (effectiveAddr vR10Old (-2056) ↦U64 addr6) **
      (effectiveAddr addr6 8 ↦U64 oldMemD_28) **
      (effectiveAddr addr6 16 ↦U64 oldMemD_30) **
      (effectiveAddr addr6 24 ↦U64 oldMemD_32) **
      (effectiveAddr addr6 32 ↦U64 oldMemD_34) **
      (effectiveAddr addr7 0 ↦U64 oldMemD_36) **
      (effectiveAddr addr6 80 ↦U64 oldMemD_37) **
      (effectiveAddr addr6 1 ↦ₘ oldMemB_38)) **
      codecCoarse (addr5 + 88) (SVM.Solana.mintFields (PartialState.byteBA oldMemB_26 ++ (g3 ++ (PartialState.u64LE oldMemD_29 ++ (PartialState.u64LE oldMemD_31 ++ (PartialState.u64LE oldMemD_33 ++ PartialState.u64LE oldMemD_35))))) (oldMemD_39 + oldMemD_36) (g1 ++ (PartialState.byteBA oldMemB_25 ++ g2))) **
      codecCoarse (addr4 + 88) (SVM.Solana.tokenFields ⟨oldMemD_16, oldMemD_18, oldMemD_20, oldMemD_22⟩ ⟨o0, o1, o2, o3⟩ (oldMemD_40 + oldMemD_36) (g4 ++ (PartialState.byteBA oldMemB_14 ++ (PartialState.byteBA oldMemB_15 ++ g5)))))
      rr := by
  unfold SVM.Solana.Abstract.AsmRefinesTokenMintTo at h
  simpa only [SVM.Solana.tokenAcctBalanceOf_eq, SVM.Solana.tokenAcctBalanceOf_withAmount, SVM.Solana.tokenAcctBalance_codec, SVM.Solana.mintSupplyOf_eq, SVM.Solana.mintSupplyOf_withSupply, SVM.Solana.mintSupply_codec] using h

end Examples.PTokenMintToRefinement
