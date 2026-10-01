/-
  Whole-transition bundle for sbpfv3_vault_deposit (#40 gap 1). MECHANICALLY EMITTED
  by qedlift from the per-path trace-guided lifts (one discovered
  `sbpfv3_vault_deposit_<path>.pcs` trace per path) + the refinement descriptor. ONE
  statement covering every path: under each path's branch guards the program
  TERMINATES with that path's exit code (or FAULTS with its typed error) and
  the tracked account codec transitions accordingly (preservation and fault
  paths hold it fixed).
-/

import Generated.Sbpfv3VaultDepositOverflowLifted
import Generated.Sbpfv3VaultDepositSuccessLifted
import Generated.Sbpfv3VaultDepositUnknownLifted
import Generated.Sbpfv3VaultDepositZeroLifted

namespace Examples.Sbpfv3VaultDepositTransition

open SVM SVM.SBPF SVM.SBPF.Memory SVM.Solana.Abstract

theorem sbpfv3_vault_deposit_transition
    (vR0Old baseAddr m10304 vR2Old amount vR3Old total vR4Old owner0 owner1 owner2 owner3 bump : Nat)
    (hm10304_lt : m10304 < 2 ^ 64)
    (hamount_lt : amount < 2 ^ 64)
    (htotal_lt : total < 2 ^ 64) :
    (m10304 = toU64 1 →
     amount ≠ toU64 0 →
     wrapAdd total amount < total →
     toU64 1 = toU64 1 →
      SVM.Solana.Abstract.AsmRefinesTransitionPath
      (((((((((((((((CodeReq.singleton 0 (.mov64 .r0 (.imm (2)))).union
        (CodeReq.singleton 1 (.ldx .dword .r2 .r1 10400))).union
        (CodeReq.singleton 2 (.jne .r2 (.imm (1)) 16))).union
        (CodeReq.singleton 3 (.ldx .dword .r3 .r1 10408))).union
        (CodeReq.singleton 4 (.jeq .r3 (.imm (0)) 15))).union
        (CodeReq.singleton 5 (.ldx .dword .r4 .r1 128))).union
        (CodeReq.singleton 6 (.mov64 .r2 (.reg .r4)))).union
        (CodeReq.singleton 7 (.add64 .r2 (.reg .r3)))).union
        (CodeReq.singleton 8 (.mov64 .r3 (.imm (1))))).union
        (CodeReq.singleton 9 (.jlt .r2 (.reg .r4) 11))).union
        (CodeReq.singleton 11 (.jeq .r3 (.imm (1)) 17))).union
        (CodeReq.singleton 17 (.mov64 .r0 (.imm (3))))).union
        (CodeReq.singleton 18 (.ja 16)))).union
        (CodeReq.singleton 16 .exit))
      (13 + 1) (0) 0
      (fun rt => ((rt.containsRange (effectiveAddr baseAddr 10400) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10408) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 128) 8 = true)
      (toU64 3)
      [((baseAddr + 96),
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)],
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)])]
      (((.r0 ↦ᵣ vR0Old) **
      (.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 10400 ↦U64 m10304) **
      (.r2 ↦ᵣ vR2Old) **
      (effectiveAddr baseAddr 10408 ↦U64 amount) **
      (.r3 ↦ᵣ vR3Old) **
      (.r4 ↦ᵣ vR4Old)) **
       callStackIs [])
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 10400 ↦U64 m10304) **
      (.r2 ↦ᵣ wrapAdd total amount) **
      (effectiveAddr baseAddr 10408 ↦U64 amount) **
      (.r3 ↦ᵣ toU64 1) **
      (.r4 ↦ᵣ total))) ∧
    (m10304 = toU64 1 →
     amount ≠ toU64 0 →
     ¬ wrapAdd total amount < total →
     toU64 0 ≠ toU64 1 →
     total + amount < 2 ^ 64 →
      SVM.Solana.Abstract.AsmRefinesTransitionPath
      (((((((((((((((((CodeReq.singleton 0 (.mov64 .r0 (.imm (2)))).union
        (CodeReq.singleton 1 (.ldx .dword .r2 .r1 10400))).union
        (CodeReq.singleton 2 (.jne .r2 (.imm (1)) 16))).union
        (CodeReq.singleton 3 (.ldx .dword .r3 .r1 10408))).union
        (CodeReq.singleton 4 (.jeq .r3 (.imm (0)) 15))).union
        (CodeReq.singleton 5 (.ldx .dword .r4 .r1 128))).union
        (CodeReq.singleton 6 (.mov64 .r2 (.reg .r4)))).union
        (CodeReq.singleton 7 (.add64 .r2 (.reg .r3)))).union
        (CodeReq.singleton 8 (.mov64 .r3 (.imm (1))))).union
        (CodeReq.singleton 9 (.jlt .r2 (.reg .r4) 11))).union
        (CodeReq.singleton 10 (.mov64 .r3 (.imm (0))))).union
        (CodeReq.singleton 11 (.jeq .r3 (.imm (1)) 17))).union
        (CodeReq.singleton 12 (.stx .dword .r1 128 .r2))).union
        (CodeReq.singleton 13 (.mov64 .r0 (.imm (0))))).union
        (CodeReq.singleton 14 (.ja 16)))).union
        (CodeReq.singleton 16 .exit))
      (15 + 1) (0) 0
      (fun rt => (((rt.containsRange (effectiveAddr baseAddr 10400) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10408) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 128) 8 = true) ∧
                  rt.containsWritable (effectiveAddr baseAddr 128) 8 = true)
      (toU64 0)
      [((baseAddr + 96),
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)],
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 (total + amount)), (40, .byte bump)])]
      (((.r0 ↦ᵣ vR0Old) **
      (.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 10400 ↦U64 m10304) **
      (.r2 ↦ᵣ vR2Old) **
      (effectiveAddr baseAddr 10408 ↦U64 amount) **
      (.r3 ↦ᵣ vR3Old) **
      (.r4 ↦ᵣ vR4Old)) **
       callStackIs [])
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 10400 ↦U64 m10304) **
      (.r2 ↦ᵣ wrapAdd total amount) **
      (effectiveAddr baseAddr 10408 ↦U64 amount) **
      (.r3 ↦ᵣ toU64 0) **
      (.r4 ↦ᵣ total))) ∧
    (m10304 ≠ toU64 1 →
      SVM.Solana.Abstract.AsmRefinesTransitionPath
      (((((CodeReq.singleton 0 (.mov64 .r0 (.imm (2)))).union
        (CodeReq.singleton 1 (.ldx .dword .r2 .r1 10400))).union
        (CodeReq.singleton 2 (.jne .r2 (.imm (1)) 16)))).union
        (CodeReq.singleton 16 .exit))
      (3 + 1) (0) 0
      (fun rt => rt.containsRange (effectiveAddr baseAddr 10400) 8 = true)
      (toU64 2)
      [((baseAddr + 96),
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)],
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)])]
      (((.r0 ↦ᵣ vR0Old) **
      (.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 10400 ↦U64 m10304) **
      (.r2 ↦ᵣ vR2Old)) **
       callStackIs [])
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 10400 ↦U64 m10304) **
      (.r2 ↦ᵣ m10304))) ∧
    (m10304 = toU64 1 →
     amount = toU64 0 →
      SVM.Solana.Abstract.AsmRefinesTransitionPath
      ((((((((CodeReq.singleton 0 (.mov64 .r0 (.imm (2)))).union
        (CodeReq.singleton 1 (.ldx .dword .r2 .r1 10400))).union
        (CodeReq.singleton 2 (.jne .r2 (.imm (1)) 16))).union
        (CodeReq.singleton 3 (.ldx .dword .r3 .r1 10408))).union
        (CodeReq.singleton 4 (.jeq .r3 (.imm (0)) 15))).union
        (CodeReq.singleton 15 (.mov64 .r0 (.imm (1)))))).union
        (CodeReq.singleton 16 .exit))
      (6 + 1) (0) 0
      (fun rt => (rt.containsRange (effectiveAddr baseAddr 10400) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10408) 8 = true)
      (toU64 1)
      [((baseAddr + 96),
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)],
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)])]
      (((.r0 ↦ᵣ vR0Old) **
      (.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 10400 ↦U64 m10304) **
      (.r2 ↦ᵣ vR2Old) **
      (effectiveAddr baseAddr 10408 ↦U64 amount) **
      (.r3 ↦ᵣ vR3Old)) **
       callStackIs [])
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 10400 ↦U64 m10304) **
      (.r2 ↦ᵣ m10304) **
      (effectiveAddr baseAddr 10408 ↦U64 amount) **
      (.r3 ↦ᵣ amount))) :=
  ⟨fun hg0 hg1 hg2 hg3 =>
      Examples.Lifted.Sbpfv3VaultDepositOverflow.Sbpfv3VaultDepositOverflow_transition_path vR0Old baseAddr m10304 vR2Old amount vR3Old total vR4Old hm10304_lt hamount_lt htotal_lt hg0 hg1 hg2 hg3 owner0 owner1 owner2 owner3 bump,
   fun hg0 hg1 hg2 hg3 hg4 =>
      Examples.Lifted.Sbpfv3VaultDepositSuccess.Sbpfv3VaultDepositSuccess_transition_path vR0Old baseAddr m10304 vR2Old amount vR3Old total vR4Old hm10304_lt hamount_lt htotal_lt hg0 hg1 hg2 hg3 hg4 owner0 owner1 owner2 owner3 bump,
   fun hg0 =>
      Examples.Lifted.Sbpfv3VaultDepositUnknown.Sbpfv3VaultDepositUnknown_transition_path vR0Old baseAddr m10304 vR2Old hm10304_lt hg0 owner0 owner1 owner2 owner3 total bump,
   fun hg0 hg1 =>
      Examples.Lifted.Sbpfv3VaultDepositZero.Sbpfv3VaultDepositZero_transition_path vR0Old baseAddr m10304 vR2Old amount vR3Old hm10304_lt hamount_lt hg0 hg1 owner0 owner1 owner2 owner3 total bump⟩

end Examples.Sbpfv3VaultDepositTransition
