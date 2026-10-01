/-
  Whole-transition bundle for sbpfv3_vault_authorized (#40 gap 1). MECHANICALLY EMITTED
  by qedlift from the per-path trace-guided lifts (one discovered
  `sbpfv3_vault_authorized_<path>.pcs` trace per path) + the refinement descriptor. ONE
  statement covering every path: under each path's branch guards the program
  TERMINATES with that path's exit code (or FAULTS with its typed error) and
  the tracked account codec transitions accordingly (preservation and fault
  paths hold it fixed).
-/

import Generated.Sbpfv3VaultAuthorizedDuplicateLifted
import Generated.Sbpfv3VaultAuthorizedExecutableLifted
import Generated.Sbpfv3VaultAuthorizedLongInstructionLifted
import Generated.Sbpfv3VaultAuthorizedMissingAccountLifted
import Generated.Sbpfv3VaultAuthorizedMissingSignerLifted
import Generated.Sbpfv3VaultAuthorizedNonemptyAuthorityLifted
import Generated.Sbpfv3VaultAuthorizedOverflowLifted
import Generated.Sbpfv3VaultAuthorizedReadonlyLifted
import Generated.Sbpfv3VaultAuthorizedShortInstructionLifted
import Generated.Sbpfv3VaultAuthorizedShortVaultLifted
import Generated.Sbpfv3VaultAuthorizedSuccessLifted
import Generated.Sbpfv3VaultAuthorizedUnknownLifted
import Generated.Sbpfv3VaultAuthorizedWrongOwner0Lifted
import Generated.Sbpfv3VaultAuthorizedWrongOwner1Lifted
import Generated.Sbpfv3VaultAuthorizedWrongOwner2Lifted
import Generated.Sbpfv3VaultAuthorizedWrongOwner3Lifted
import Generated.Sbpfv3VaultAuthorizedWrongProgramOwner0Lifted
import Generated.Sbpfv3VaultAuthorizedWrongProgramOwner1Lifted
import Generated.Sbpfv3VaultAuthorizedWrongProgramOwner2Lifted
import Generated.Sbpfv3VaultAuthorizedWrongProgramOwner3Lifted
import Generated.Sbpfv3VaultAuthorizedZeroLifted

namespace Examples.Sbpfv3VaultAuthorizedTransition

open SVM SVM.SBPF SVM.SBPF.Memory SVM.Solana.Abstract

theorem sbpfv3_vault_authorized_transition
    (vR0Old baseAddr mNeg96 vR2Old mNeg88 mNeg8 m10296 owner0 owner1 owner2 owner3 total bump m10376 m20632 mNeg86 mNeg85 m10297 m20656 mNeg48 vR3Old m20664 mNeg40 m20672 mNeg32 m20680 mNeg24 m10304 m10312 m10320 m10328 m20640 amount vR4Old : Nat)
    (hmNeg96_lt : mNeg96 < 2 ^ 64)
    (hmNeg8_lt : mNeg8 < 2 ^ 64)
    (hm10376_lt : m10376 < 2 ^ 64)
    (hm20632_lt : m20632 < 2 ^ 64)
    (hm20656_lt : m20656 < 2 ^ 64)
    (hmNeg48_lt : mNeg48 < 2 ^ 64)
    (hm20664_lt : m20664 < 2 ^ 64)
    (hmNeg40_lt : mNeg40 < 2 ^ 64)
    (hm20672_lt : m20672 < 2 ^ 64)
    (hmNeg32_lt : mNeg32 < 2 ^ 64)
    (hm20680_lt : m20680 < 2 ^ 64)
    (hmNeg24_lt : mNeg24 < 2 ^ 64)
    (hm10304_lt : m10304 < 2 ^ 64)
    (howner0_lt : owner0 < 2 ^ 64)
    (hm10312_lt : m10312 < 2 ^ 64)
    (howner1_lt : owner1 < 2 ^ 64)
    (hm10320_lt : m10320 < 2 ^ 64)
    (howner2_lt : owner2 < 2 ^ 64)
    (hm10328_lt : m10328 < 2 ^ 64)
    (howner3_lt : owner3 < 2 ^ 64)
    (hm20640_lt : m20640 < 2 ^ 64)
    (hamount_lt : amount < 2 ^ 64)
    (htotal_lt : total < 2 ^ 64) :
    (mNeg96 = toU64 2 →
     mNeg88 % 256 = toU64 255 →
     mNeg8 = toU64 41 →
     m10296 % 256 ≠ toU64 255 →
      SVM.Solana.Abstract.AsmRefinesTransitionPath
      (((((((((((CodeReq.singleton 0 (.mov64 .r0 (.imm (6)))).union
        (CodeReq.singleton 1 (.ldx .dword .r2 .r1 0))).union
        (CodeReq.singleton 2 (.jne .r2 (.imm (2)) 63))).union
        (CodeReq.singleton 3 (.ldx .byte .r2 .r1 8))).union
        (CodeReq.singleton 4 (.jne .r2 (.imm (255)) 63))).union
        (CodeReq.singleton 5 (.ldx .dword .r2 .r1 88))).union
        (CodeReq.singleton 6 (.jne .r2 (.imm (41)) 63))).union
        (CodeReq.singleton 7 (.ldx .byte .r2 .r1 10392))).union
        (CodeReq.singleton 8 (.jne .r2 (.imm (255)) 63)))).union
        (CodeReq.singleton 63 .exit))
      (9 + 1) (0) 0
      (fun rt => (((rt.containsRange (effectiveAddr baseAddr 0) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 8) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 88) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10392) 1 = true)
      (toU64 6)
      [((baseAddr + 96),
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)],
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)])]
      (((.r0 ↦ᵣ vR0Old) **
      (.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ vR2Old) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8) **
      (effectiveAddr baseAddr 10392 ↦ₘ m10296)) **
       callStackIs [])
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ m10296 % 256) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8) **
      (effectiveAddr baseAddr 10392 ↦ₘ m10296))) ∧
    (mNeg96 = toU64 2 →
     mNeg88 % 256 = toU64 255 →
     mNeg8 = toU64 41 →
     m10296 % 256 = toU64 255 →
     m10376 = toU64 0 →
     m20632 = toU64 16 →
     mNeg86 % 256 = toU64 1 →
     mNeg85 % 256 ≠ toU64 0 →
      SVM.Solana.Abstract.AsmRefinesTransitionPath
      (((((((((((((((((((((CodeReq.singleton 0 (.mov64 .r0 (.imm (6)))).union
        (CodeReq.singleton 1 (.ldx .dword .r2 .r1 0))).union
        (CodeReq.singleton 2 (.jne .r2 (.imm (2)) 63))).union
        (CodeReq.singleton 3 (.ldx .byte .r2 .r1 8))).union
        (CodeReq.singleton 4 (.jne .r2 (.imm (255)) 63))).union
        (CodeReq.singleton 5 (.ldx .dword .r2 .r1 88))).union
        (CodeReq.singleton 6 (.jne .r2 (.imm (41)) 63))).union
        (CodeReq.singleton 7 (.ldx .byte .r2 .r1 10392))).union
        (CodeReq.singleton 8 (.jne .r2 (.imm (255)) 63))).union
        (CodeReq.singleton 9 (.ldx .dword .r2 .r1 10472))).union
        (CodeReq.singleton 10 (.jne .r2 (.imm (0)) 63))).union
        (CodeReq.singleton 11 (.mov64 .r0 (.imm (7))))).union
        (CodeReq.singleton 12 (.ldx .dword .r2 .r1 20728))).union
        (CodeReq.singleton 13 (.jne .r2 (.imm (16)) 63))).union
        (CodeReq.singleton 14 (.mov64 .r0 (.imm (8))))).union
        (CodeReq.singleton 15 (.ldx .byte .r2 .r1 10))).union
        (CodeReq.singleton 16 (.jne .r2 (.imm (1)) 63))).union
        (CodeReq.singleton 17 (.ldx .byte .r2 .r1 11))).union
        (CodeReq.singleton 18 (.jne .r2 (.imm (0)) 63)))).union
        (CodeReq.singleton 63 .exit))
      (19 + 1) (0) 0
      (fun rt => (((((((rt.containsRange (effectiveAddr baseAddr 0) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 8) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 88) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10392) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10472) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20728) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 11) 1 = true)
      (toU64 8)
      [((baseAddr + 96),
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)],
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)])]
      (((.r0 ↦ᵣ vR0Old) **
      (.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ vR2Old) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8) **
      (effectiveAddr baseAddr 10392 ↦ₘ m10296) **
      (effectiveAddr baseAddr 10472 ↦U64 m10376) **
      (effectiveAddr baseAddr 20728 ↦U64 m20632) **
      (effectiveAddr baseAddr 10 ↦ₘ mNeg86) **
      (effectiveAddr baseAddr 11 ↦ₘ mNeg85)) **
       callStackIs [])
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ mNeg85 % 256) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8) **
      (effectiveAddr baseAddr 10392 ↦ₘ m10296) **
      (effectiveAddr baseAddr 10472 ↦U64 m10376) **
      (effectiveAddr baseAddr 20728 ↦U64 m20632) **
      (effectiveAddr baseAddr 10 ↦ₘ mNeg86) **
      (effectiveAddr baseAddr 11 ↦ₘ mNeg85))) ∧
    (mNeg96 = toU64 2 →
     mNeg88 % 256 = toU64 255 →
     mNeg8 = toU64 41 →
     m10296 % 256 = toU64 255 →
     m10376 = toU64 0 →
     m20632 ≠ toU64 16 →
      SVM.Solana.Abstract.AsmRefinesTransitionPath
      ((((((((((((((((CodeReq.singleton 0 (.mov64 .r0 (.imm (6)))).union
        (CodeReq.singleton 1 (.ldx .dword .r2 .r1 0))).union
        (CodeReq.singleton 2 (.jne .r2 (.imm (2)) 63))).union
        (CodeReq.singleton 3 (.ldx .byte .r2 .r1 8))).union
        (CodeReq.singleton 4 (.jne .r2 (.imm (255)) 63))).union
        (CodeReq.singleton 5 (.ldx .dword .r2 .r1 88))).union
        (CodeReq.singleton 6 (.jne .r2 (.imm (41)) 63))).union
        (CodeReq.singleton 7 (.ldx .byte .r2 .r1 10392))).union
        (CodeReq.singleton 8 (.jne .r2 (.imm (255)) 63))).union
        (CodeReq.singleton 9 (.ldx .dword .r2 .r1 10472))).union
        (CodeReq.singleton 10 (.jne .r2 (.imm (0)) 63))).union
        (CodeReq.singleton 11 (.mov64 .r0 (.imm (7))))).union
        (CodeReq.singleton 12 (.ldx .dword .r2 .r1 20728))).union
        (CodeReq.singleton 13 (.jne .r2 (.imm (16)) 63)))).union
        (CodeReq.singleton 63 .exit))
      (14 + 1) (0) 0
      (fun rt => (((((rt.containsRange (effectiveAddr baseAddr 0) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 8) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 88) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10392) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10472) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20728) 8 = true)
      (toU64 7)
      [((baseAddr + 96),
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)],
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)])]
      (((.r0 ↦ᵣ vR0Old) **
      (.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ vR2Old) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8) **
      (effectiveAddr baseAddr 10392 ↦ₘ m10296) **
      (effectiveAddr baseAddr 10472 ↦U64 m10376) **
      (effectiveAddr baseAddr 20728 ↦U64 m20632)) **
       callStackIs [])
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ m20632) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8) **
      (effectiveAddr baseAddr 10392 ↦ₘ m10296) **
      (effectiveAddr baseAddr 10472 ↦U64 m10376) **
      (effectiveAddr baseAddr 20728 ↦U64 m20632))) ∧
    (mNeg96 ≠ toU64 2 →
      SVM.Solana.Abstract.AsmRefinesTransitionPath
      (((((CodeReq.singleton 0 (.mov64 .r0 (.imm (6)))).union
        (CodeReq.singleton 1 (.ldx .dword .r2 .r1 0))).union
        (CodeReq.singleton 2 (.jne .r2 (.imm (2)) 63)))).union
        (CodeReq.singleton 63 .exit))
      (3 + 1) (0) 0
      (fun rt => rt.containsRange (effectiveAddr baseAddr 0) 8 = true)
      (toU64 6)
      [((baseAddr + 96),
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)],
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)])]
      (((.r0 ↦ᵣ vR0Old) **
      (.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ vR2Old)) **
       callStackIs [])
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ mNeg96))) ∧
    (mNeg96 = toU64 2 →
     mNeg88 % 256 = toU64 255 →
     mNeg8 = toU64 41 →
     m10296 % 256 = toU64 255 →
     m10376 = toU64 0 →
     m20632 = toU64 16 →
     mNeg86 % 256 = toU64 1 →
     mNeg85 % 256 = toU64 0 →
     m10297 % 256 ≠ toU64 1 →
      SVM.Solana.Abstract.AsmRefinesTransitionPath
      ((((((((((((((((((((((((CodeReq.singleton 0 (.mov64 .r0 (.imm (6)))).union
        (CodeReq.singleton 1 (.ldx .dword .r2 .r1 0))).union
        (CodeReq.singleton 2 (.jne .r2 (.imm (2)) 63))).union
        (CodeReq.singleton 3 (.ldx .byte .r2 .r1 8))).union
        (CodeReq.singleton 4 (.jne .r2 (.imm (255)) 63))).union
        (CodeReq.singleton 5 (.ldx .dword .r2 .r1 88))).union
        (CodeReq.singleton 6 (.jne .r2 (.imm (41)) 63))).union
        (CodeReq.singleton 7 (.ldx .byte .r2 .r1 10392))).union
        (CodeReq.singleton 8 (.jne .r2 (.imm (255)) 63))).union
        (CodeReq.singleton 9 (.ldx .dword .r2 .r1 10472))).union
        (CodeReq.singleton 10 (.jne .r2 (.imm (0)) 63))).union
        (CodeReq.singleton 11 (.mov64 .r0 (.imm (7))))).union
        (CodeReq.singleton 12 (.ldx .dword .r2 .r1 20728))).union
        (CodeReq.singleton 13 (.jne .r2 (.imm (16)) 63))).union
        (CodeReq.singleton 14 (.mov64 .r0 (.imm (8))))).union
        (CodeReq.singleton 15 (.ldx .byte .r2 .r1 10))).union
        (CodeReq.singleton 16 (.jne .r2 (.imm (1)) 63))).union
        (CodeReq.singleton 17 (.ldx .byte .r2 .r1 11))).union
        (CodeReq.singleton 18 (.jne .r2 (.imm (0)) 63))).union
        (CodeReq.singleton 19 (.mov64 .r0 (.imm (5))))).union
        (CodeReq.singleton 20 (.ldx .byte .r2 .r1 10393))).union
        (CodeReq.singleton 21 (.jne .r2 (.imm (1)) 63)))).union
        (CodeReq.singleton 63 .exit))
      (22 + 1) (0) 0
      (fun rt => ((((((((rt.containsRange (effectiveAddr baseAddr 0) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 8) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 88) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10392) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10472) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20728) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 11) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10393) 1 = true)
      (toU64 5)
      [((baseAddr + 96),
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)],
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)])]
      (((.r0 ↦ᵣ vR0Old) **
      (.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ vR2Old) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8) **
      (effectiveAddr baseAddr 10392 ↦ₘ m10296) **
      (effectiveAddr baseAddr 10472 ↦U64 m10376) **
      (effectiveAddr baseAddr 20728 ↦U64 m20632) **
      (effectiveAddr baseAddr 10 ↦ₘ mNeg86) **
      (effectiveAddr baseAddr 11 ↦ₘ mNeg85) **
      (effectiveAddr baseAddr 10393 ↦ₘ m10297)) **
       callStackIs [])
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ m10297 % 256) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8) **
      (effectiveAddr baseAddr 10392 ↦ₘ m10296) **
      (effectiveAddr baseAddr 10472 ↦U64 m10376) **
      (effectiveAddr baseAddr 20728 ↦U64 m20632) **
      (effectiveAddr baseAddr 10 ↦ₘ mNeg86) **
      (effectiveAddr baseAddr 11 ↦ₘ mNeg85) **
      (effectiveAddr baseAddr 10393 ↦ₘ m10297))) ∧
    (mNeg96 = toU64 2 →
     mNeg88 % 256 = toU64 255 →
     mNeg8 = toU64 41 →
     m10296 % 256 = toU64 255 →
     m10376 ≠ toU64 0 →
      SVM.Solana.Abstract.AsmRefinesTransitionPath
      (((((((((((((CodeReq.singleton 0 (.mov64 .r0 (.imm (6)))).union
        (CodeReq.singleton 1 (.ldx .dword .r2 .r1 0))).union
        (CodeReq.singleton 2 (.jne .r2 (.imm (2)) 63))).union
        (CodeReq.singleton 3 (.ldx .byte .r2 .r1 8))).union
        (CodeReq.singleton 4 (.jne .r2 (.imm (255)) 63))).union
        (CodeReq.singleton 5 (.ldx .dword .r2 .r1 88))).union
        (CodeReq.singleton 6 (.jne .r2 (.imm (41)) 63))).union
        (CodeReq.singleton 7 (.ldx .byte .r2 .r1 10392))).union
        (CodeReq.singleton 8 (.jne .r2 (.imm (255)) 63))).union
        (CodeReq.singleton 9 (.ldx .dword .r2 .r1 10472))).union
        (CodeReq.singleton 10 (.jne .r2 (.imm (0)) 63)))).union
        (CodeReq.singleton 63 .exit))
      (11 + 1) (0) 0
      (fun rt => ((((rt.containsRange (effectiveAddr baseAddr 0) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 8) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 88) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10392) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10472) 8 = true)
      (toU64 6)
      [((baseAddr + 96),
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)],
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)])]
      (((.r0 ↦ᵣ vR0Old) **
      (.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ vR2Old) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8) **
      (effectiveAddr baseAddr 10392 ↦ₘ m10296) **
      (effectiveAddr baseAddr 10472 ↦U64 m10376)) **
       callStackIs [])
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ m10376) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8) **
      (effectiveAddr baseAddr 10392 ↦ₘ m10296) **
      (effectiveAddr baseAddr 10472 ↦U64 m10376))) ∧
    (mNeg96 = toU64 2 →
     mNeg88 % 256 = toU64 255 →
     mNeg8 = toU64 41 →
     m10296 % 256 = toU64 255 →
     m10376 = toU64 0 →
     m20632 = toU64 16 →
     mNeg86 % 256 = toU64 1 →
     mNeg85 % 256 = toU64 0 →
     m10297 % 256 = toU64 1 →
     mNeg48 = m20656 →
     mNeg40 = m20664 →
     mNeg32 = m20672 →
     mNeg24 = m20680 →
     owner0 = m10304 →
     owner1 = m10312 →
     owner2 = m10320 →
     owner3 = m10328 →
     m20640 = toU64 1 →
     amount ≠ toU64 0 →
     wrapAdd total amount < total →
     toU64 1 = toU64 1 →
      SVM.Solana.Abstract.AsmRefinesTransitionPath
      ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((CodeReq.singleton 0 (.mov64 .r0 (.imm (6)))).union
        (CodeReq.singleton 1 (.ldx .dword .r2 .r1 0))).union
        (CodeReq.singleton 2 (.jne .r2 (.imm (2)) 63))).union
        (CodeReq.singleton 3 (.ldx .byte .r2 .r1 8))).union
        (CodeReq.singleton 4 (.jne .r2 (.imm (255)) 63))).union
        (CodeReq.singleton 5 (.ldx .dword .r2 .r1 88))).union
        (CodeReq.singleton 6 (.jne .r2 (.imm (41)) 63))).union
        (CodeReq.singleton 7 (.ldx .byte .r2 .r1 10392))).union
        (CodeReq.singleton 8 (.jne .r2 (.imm (255)) 63))).union
        (CodeReq.singleton 9 (.ldx .dword .r2 .r1 10472))).union
        (CodeReq.singleton 10 (.jne .r2 (.imm (0)) 63))).union
        (CodeReq.singleton 11 (.mov64 .r0 (.imm (7))))).union
        (CodeReq.singleton 12 (.ldx .dword .r2 .r1 20728))).union
        (CodeReq.singleton 13 (.jne .r2 (.imm (16)) 63))).union
        (CodeReq.singleton 14 (.mov64 .r0 (.imm (8))))).union
        (CodeReq.singleton 15 (.ldx .byte .r2 .r1 10))).union
        (CodeReq.singleton 16 (.jne .r2 (.imm (1)) 63))).union
        (CodeReq.singleton 17 (.ldx .byte .r2 .r1 11))).union
        (CodeReq.singleton 18 (.jne .r2 (.imm (0)) 63))).union
        (CodeReq.singleton 19 (.mov64 .r0 (.imm (5))))).union
        (CodeReq.singleton 20 (.ldx .byte .r2 .r1 10393))).union
        (CodeReq.singleton 21 (.jne .r2 (.imm (1)) 63))).union
        (CodeReq.singleton 22 (.mov64 .r0 (.imm (4))))).union
        (CodeReq.singleton 23 (.ldx .dword .r2 .r1 20752))).union
        (CodeReq.singleton 24 (.ldx .dword .r3 .r1 48))).union
        (CodeReq.singleton 25 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 26 (.ldx .dword .r2 .r1 20760))).union
        (CodeReq.singleton 27 (.ldx .dword .r3 .r1 56))).union
        (CodeReq.singleton 28 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 29 (.ldx .dword .r2 .r1 20768))).union
        (CodeReq.singleton 30 (.ldx .dword .r3 .r1 64))).union
        (CodeReq.singleton 31 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 32 (.ldx .dword .r2 .r1 20776))).union
        (CodeReq.singleton 33 (.ldx .dword .r3 .r1 72))).union
        (CodeReq.singleton 34 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 35 (.ldx .dword .r2 .r1 10400))).union
        (CodeReq.singleton 36 (.ldx .dword .r3 .r1 96))).union
        (CodeReq.singleton 37 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 38 (.ldx .dword .r2 .r1 10408))).union
        (CodeReq.singleton 39 (.ldx .dword .r3 .r1 104))).union
        (CodeReq.singleton 40 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 41 (.ldx .dword .r2 .r1 10416))).union
        (CodeReq.singleton 42 (.ldx .dword .r3 .r1 112))).union
        (CodeReq.singleton 43 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 44 (.ldx .dword .r2 .r1 10424))).union
        (CodeReq.singleton 45 (.ldx .dword .r3 .r1 120))).union
        (CodeReq.singleton 46 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 47 (.mov64 .r0 (.imm (2))))).union
        (CodeReq.singleton 48 (.ldx .dword .r2 .r1 20736))).union
        (CodeReq.singleton 49 (.jne .r2 (.imm (1)) 63))).union
        (CodeReq.singleton 50 (.ldx .dword .r3 .r1 20744))).union
        (CodeReq.singleton 51 (.jeq .r3 (.imm (0)) 62))).union
        (CodeReq.singleton 52 (.ldx .dword .r4 .r1 128))).union
        (CodeReq.singleton 53 (.mov64 .r2 (.reg .r4)))).union
        (CodeReq.singleton 54 (.add64 .r2 (.reg .r3)))).union
        (CodeReq.singleton 55 (.mov64 .r3 (.imm (1))))).union
        (CodeReq.singleton 56 (.jlt .r2 (.reg .r4) 58))).union
        (CodeReq.singleton 58 (.jeq .r3 (.imm (1)) 64))).union
        (CodeReq.singleton 64 (.mov64 .r0 (.imm (3))))).union
        (CodeReq.singleton 65 (.ja 63)))).union
        (CodeReq.singleton 63 .exit))
      (60 + 1) (0) 0
      (fun rt => (((((((((((((((((((((((((((rt.containsRange (effectiveAddr baseAddr 0) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 8) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 88) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10392) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10472) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20728) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 11) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10393) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20752) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 48) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20760) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 56) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20768) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 64) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20776) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 72) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10400) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 96) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10408) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 104) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10416) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 112) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10424) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 120) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20736) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20744) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 128) 8 = true)
      (toU64 3)
      [((baseAddr + 96),
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)],
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)])]
      (((.r0 ↦ᵣ vR0Old) **
      (.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ vR2Old) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8) **
      (effectiveAddr baseAddr 10392 ↦ₘ m10296) **
      (effectiveAddr baseAddr 10472 ↦U64 m10376) **
      (effectiveAddr baseAddr 20728 ↦U64 m20632) **
      (effectiveAddr baseAddr 10 ↦ₘ mNeg86) **
      (effectiveAddr baseAddr 11 ↦ₘ mNeg85) **
      (effectiveAddr baseAddr 10393 ↦ₘ m10297) **
      (effectiveAddr baseAddr 20752 ↦U64 m20656) **
      (effectiveAddr baseAddr 48 ↦U64 mNeg48) **
      (.r3 ↦ᵣ vR3Old) **
      (effectiveAddr baseAddr 20760 ↦U64 m20664) **
      (effectiveAddr baseAddr 56 ↦U64 mNeg40) **
      (effectiveAddr baseAddr 20768 ↦U64 m20672) **
      (effectiveAddr baseAddr 64 ↦U64 mNeg32) **
      (effectiveAddr baseAddr 20776 ↦U64 m20680) **
      (effectiveAddr baseAddr 72 ↦U64 mNeg24) **
      (effectiveAddr baseAddr 10400 ↦U64 m10304) **
      (effectiveAddr baseAddr 10408 ↦U64 m10312) **
      (effectiveAddr baseAddr 10416 ↦U64 m10320) **
      (effectiveAddr baseAddr 10424 ↦U64 m10328) **
      (effectiveAddr baseAddr 20736 ↦U64 m20640) **
      (effectiveAddr baseAddr 20744 ↦U64 amount) **
      (.r4 ↦ᵣ vR4Old)) **
       callStackIs [])
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ wrapAdd total amount) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8) **
      (effectiveAddr baseAddr 10392 ↦ₘ m10296) **
      (effectiveAddr baseAddr 10472 ↦U64 m10376) **
      (effectiveAddr baseAddr 20728 ↦U64 m20632) **
      (effectiveAddr baseAddr 10 ↦ₘ mNeg86) **
      (effectiveAddr baseAddr 11 ↦ₘ mNeg85) **
      (effectiveAddr baseAddr 10393 ↦ₘ m10297) **
      (effectiveAddr baseAddr 20752 ↦U64 m20656) **
      (effectiveAddr baseAddr 48 ↦U64 mNeg48) **
      (.r3 ↦ᵣ toU64 1) **
      (effectiveAddr baseAddr 20760 ↦U64 m20664) **
      (effectiveAddr baseAddr 56 ↦U64 mNeg40) **
      (effectiveAddr baseAddr 20768 ↦U64 m20672) **
      (effectiveAddr baseAddr 64 ↦U64 mNeg32) **
      (effectiveAddr baseAddr 20776 ↦U64 m20680) **
      (effectiveAddr baseAddr 72 ↦U64 mNeg24) **
      (effectiveAddr baseAddr 10400 ↦U64 m10304) **
      (effectiveAddr baseAddr 10408 ↦U64 m10312) **
      (effectiveAddr baseAddr 10416 ↦U64 m10320) **
      (effectiveAddr baseAddr 10424 ↦U64 m10328) **
      (effectiveAddr baseAddr 20736 ↦U64 m20640) **
      (effectiveAddr baseAddr 20744 ↦U64 amount) **
      (.r4 ↦ᵣ total))) ∧
    (mNeg96 = toU64 2 →
     mNeg88 % 256 = toU64 255 →
     mNeg8 = toU64 41 →
     m10296 % 256 = toU64 255 →
     m10376 = toU64 0 →
     m20632 = toU64 16 →
     mNeg86 % 256 ≠ toU64 1 →
      SVM.Solana.Abstract.AsmRefinesTransitionPath
      (((((((((((((((((((CodeReq.singleton 0 (.mov64 .r0 (.imm (6)))).union
        (CodeReq.singleton 1 (.ldx .dword .r2 .r1 0))).union
        (CodeReq.singleton 2 (.jne .r2 (.imm (2)) 63))).union
        (CodeReq.singleton 3 (.ldx .byte .r2 .r1 8))).union
        (CodeReq.singleton 4 (.jne .r2 (.imm (255)) 63))).union
        (CodeReq.singleton 5 (.ldx .dword .r2 .r1 88))).union
        (CodeReq.singleton 6 (.jne .r2 (.imm (41)) 63))).union
        (CodeReq.singleton 7 (.ldx .byte .r2 .r1 10392))).union
        (CodeReq.singleton 8 (.jne .r2 (.imm (255)) 63))).union
        (CodeReq.singleton 9 (.ldx .dword .r2 .r1 10472))).union
        (CodeReq.singleton 10 (.jne .r2 (.imm (0)) 63))).union
        (CodeReq.singleton 11 (.mov64 .r0 (.imm (7))))).union
        (CodeReq.singleton 12 (.ldx .dword .r2 .r1 20728))).union
        (CodeReq.singleton 13 (.jne .r2 (.imm (16)) 63))).union
        (CodeReq.singleton 14 (.mov64 .r0 (.imm (8))))).union
        (CodeReq.singleton 15 (.ldx .byte .r2 .r1 10))).union
        (CodeReq.singleton 16 (.jne .r2 (.imm (1)) 63)))).union
        (CodeReq.singleton 63 .exit))
      (17 + 1) (0) 0
      (fun rt => ((((((rt.containsRange (effectiveAddr baseAddr 0) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 8) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 88) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10392) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10472) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20728) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10) 1 = true)
      (toU64 8)
      [((baseAddr + 96),
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)],
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)])]
      (((.r0 ↦ᵣ vR0Old) **
      (.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ vR2Old) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8) **
      (effectiveAddr baseAddr 10392 ↦ₘ m10296) **
      (effectiveAddr baseAddr 10472 ↦U64 m10376) **
      (effectiveAddr baseAddr 20728 ↦U64 m20632) **
      (effectiveAddr baseAddr 10 ↦ₘ mNeg86)) **
       callStackIs [])
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ mNeg86 % 256) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8) **
      (effectiveAddr baseAddr 10392 ↦ₘ m10296) **
      (effectiveAddr baseAddr 10472 ↦U64 m10376) **
      (effectiveAddr baseAddr 20728 ↦U64 m20632) **
      (effectiveAddr baseAddr 10 ↦ₘ mNeg86))) ∧
    (mNeg96 = toU64 2 →
     mNeg88 % 256 = toU64 255 →
     mNeg8 = toU64 41 →
     m10296 % 256 = toU64 255 →
     m10376 = toU64 0 →
     m20632 ≠ toU64 16 →
      SVM.Solana.Abstract.AsmRefinesTransitionPath
      ((((((((((((((((CodeReq.singleton 0 (.mov64 .r0 (.imm (6)))).union
        (CodeReq.singleton 1 (.ldx .dword .r2 .r1 0))).union
        (CodeReq.singleton 2 (.jne .r2 (.imm (2)) 63))).union
        (CodeReq.singleton 3 (.ldx .byte .r2 .r1 8))).union
        (CodeReq.singleton 4 (.jne .r2 (.imm (255)) 63))).union
        (CodeReq.singleton 5 (.ldx .dword .r2 .r1 88))).union
        (CodeReq.singleton 6 (.jne .r2 (.imm (41)) 63))).union
        (CodeReq.singleton 7 (.ldx .byte .r2 .r1 10392))).union
        (CodeReq.singleton 8 (.jne .r2 (.imm (255)) 63))).union
        (CodeReq.singleton 9 (.ldx .dword .r2 .r1 10472))).union
        (CodeReq.singleton 10 (.jne .r2 (.imm (0)) 63))).union
        (CodeReq.singleton 11 (.mov64 .r0 (.imm (7))))).union
        (CodeReq.singleton 12 (.ldx .dword .r2 .r1 20728))).union
        (CodeReq.singleton 13 (.jne .r2 (.imm (16)) 63)))).union
        (CodeReq.singleton 63 .exit))
      (14 + 1) (0) 0
      (fun rt => (((((rt.containsRange (effectiveAddr baseAddr 0) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 8) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 88) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10392) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10472) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20728) 8 = true)
      (toU64 7)
      [((baseAddr + 96),
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)],
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)])]
      (((.r0 ↦ᵣ vR0Old) **
      (.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ vR2Old) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8) **
      (effectiveAddr baseAddr 10392 ↦ₘ m10296) **
      (effectiveAddr baseAddr 10472 ↦U64 m10376) **
      (effectiveAddr baseAddr 20728 ↦U64 m20632)) **
       callStackIs [])
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ m20632) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8) **
      (effectiveAddr baseAddr 10392 ↦ₘ m10296) **
      (effectiveAddr baseAddr 10472 ↦U64 m10376) **
      (effectiveAddr baseAddr 20728 ↦U64 m20632))) ∧
    (mNeg96 = toU64 2 →
     mNeg88 % 256 = toU64 255 →
     mNeg8 ≠ toU64 41 →
      SVM.Solana.Abstract.AsmRefinesTransitionPath
      (((((((((CodeReq.singleton 0 (.mov64 .r0 (.imm (6)))).union
        (CodeReq.singleton 1 (.ldx .dword .r2 .r1 0))).union
        (CodeReq.singleton 2 (.jne .r2 (.imm (2)) 63))).union
        (CodeReq.singleton 3 (.ldx .byte .r2 .r1 8))).union
        (CodeReq.singleton 4 (.jne .r2 (.imm (255)) 63))).union
        (CodeReq.singleton 5 (.ldx .dword .r2 .r1 88))).union
        (CodeReq.singleton 6 (.jne .r2 (.imm (41)) 63)))).union
        (CodeReq.singleton 63 .exit))
      (7 + 1) (0) 0
      (fun rt => ((rt.containsRange (effectiveAddr baseAddr 0) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 8) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 88) 8 = true)
      (toU64 6)
      [((baseAddr + 96),
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)],
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)])]
      (((.r0 ↦ᵣ vR0Old) **
      (.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ vR2Old) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8)) **
       callStackIs [])
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ mNeg8) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8))) ∧
    (mNeg96 = toU64 2 →
     mNeg88 % 256 = toU64 255 →
     mNeg8 = toU64 41 →
     m10296 % 256 = toU64 255 →
     m10376 = toU64 0 →
     m20632 = toU64 16 →
     mNeg86 % 256 = toU64 1 →
     mNeg85 % 256 = toU64 0 →
     m10297 % 256 = toU64 1 →
     mNeg48 = m20656 →
     mNeg40 = m20664 →
     mNeg32 = m20672 →
     mNeg24 = m20680 →
     owner0 = m10304 →
     owner1 = m10312 →
     owner2 = m10320 →
     owner3 = m10328 →
     m20640 = toU64 1 →
     amount ≠ toU64 0 →
     ¬ wrapAdd total amount < total →
     toU64 0 ≠ toU64 1 →
     total + amount < 2 ^ 64 →
      SVM.Solana.Abstract.AsmRefinesTransitionPath
      ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((CodeReq.singleton 0 (.mov64 .r0 (.imm (6)))).union
        (CodeReq.singleton 1 (.ldx .dword .r2 .r1 0))).union
        (CodeReq.singleton 2 (.jne .r2 (.imm (2)) 63))).union
        (CodeReq.singleton 3 (.ldx .byte .r2 .r1 8))).union
        (CodeReq.singleton 4 (.jne .r2 (.imm (255)) 63))).union
        (CodeReq.singleton 5 (.ldx .dword .r2 .r1 88))).union
        (CodeReq.singleton 6 (.jne .r2 (.imm (41)) 63))).union
        (CodeReq.singleton 7 (.ldx .byte .r2 .r1 10392))).union
        (CodeReq.singleton 8 (.jne .r2 (.imm (255)) 63))).union
        (CodeReq.singleton 9 (.ldx .dword .r2 .r1 10472))).union
        (CodeReq.singleton 10 (.jne .r2 (.imm (0)) 63))).union
        (CodeReq.singleton 11 (.mov64 .r0 (.imm (7))))).union
        (CodeReq.singleton 12 (.ldx .dword .r2 .r1 20728))).union
        (CodeReq.singleton 13 (.jne .r2 (.imm (16)) 63))).union
        (CodeReq.singleton 14 (.mov64 .r0 (.imm (8))))).union
        (CodeReq.singleton 15 (.ldx .byte .r2 .r1 10))).union
        (CodeReq.singleton 16 (.jne .r2 (.imm (1)) 63))).union
        (CodeReq.singleton 17 (.ldx .byte .r2 .r1 11))).union
        (CodeReq.singleton 18 (.jne .r2 (.imm (0)) 63))).union
        (CodeReq.singleton 19 (.mov64 .r0 (.imm (5))))).union
        (CodeReq.singleton 20 (.ldx .byte .r2 .r1 10393))).union
        (CodeReq.singleton 21 (.jne .r2 (.imm (1)) 63))).union
        (CodeReq.singleton 22 (.mov64 .r0 (.imm (4))))).union
        (CodeReq.singleton 23 (.ldx .dword .r2 .r1 20752))).union
        (CodeReq.singleton 24 (.ldx .dword .r3 .r1 48))).union
        (CodeReq.singleton 25 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 26 (.ldx .dword .r2 .r1 20760))).union
        (CodeReq.singleton 27 (.ldx .dword .r3 .r1 56))).union
        (CodeReq.singleton 28 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 29 (.ldx .dword .r2 .r1 20768))).union
        (CodeReq.singleton 30 (.ldx .dword .r3 .r1 64))).union
        (CodeReq.singleton 31 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 32 (.ldx .dword .r2 .r1 20776))).union
        (CodeReq.singleton 33 (.ldx .dword .r3 .r1 72))).union
        (CodeReq.singleton 34 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 35 (.ldx .dword .r2 .r1 10400))).union
        (CodeReq.singleton 36 (.ldx .dword .r3 .r1 96))).union
        (CodeReq.singleton 37 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 38 (.ldx .dword .r2 .r1 10408))).union
        (CodeReq.singleton 39 (.ldx .dword .r3 .r1 104))).union
        (CodeReq.singleton 40 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 41 (.ldx .dword .r2 .r1 10416))).union
        (CodeReq.singleton 42 (.ldx .dword .r3 .r1 112))).union
        (CodeReq.singleton 43 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 44 (.ldx .dword .r2 .r1 10424))).union
        (CodeReq.singleton 45 (.ldx .dword .r3 .r1 120))).union
        (CodeReq.singleton 46 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 47 (.mov64 .r0 (.imm (2))))).union
        (CodeReq.singleton 48 (.ldx .dword .r2 .r1 20736))).union
        (CodeReq.singleton 49 (.jne .r2 (.imm (1)) 63))).union
        (CodeReq.singleton 50 (.ldx .dword .r3 .r1 20744))).union
        (CodeReq.singleton 51 (.jeq .r3 (.imm (0)) 62))).union
        (CodeReq.singleton 52 (.ldx .dword .r4 .r1 128))).union
        (CodeReq.singleton 53 (.mov64 .r2 (.reg .r4)))).union
        (CodeReq.singleton 54 (.add64 .r2 (.reg .r3)))).union
        (CodeReq.singleton 55 (.mov64 .r3 (.imm (1))))).union
        (CodeReq.singleton 56 (.jlt .r2 (.reg .r4) 58))).union
        (CodeReq.singleton 57 (.mov64 .r3 (.imm (0))))).union
        (CodeReq.singleton 58 (.jeq .r3 (.imm (1)) 64))).union
        (CodeReq.singleton 59 (.stx .dword .r1 128 .r2))).union
        (CodeReq.singleton 60 (.mov64 .r0 (.imm (0))))).union
        (CodeReq.singleton 61 (.ja 63)))).union
        (CodeReq.singleton 63 .exit))
      (62 + 1) (0) 0
      (fun rt => ((((((((((((((((((((((((((((rt.containsRange (effectiveAddr baseAddr 0) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 8) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 88) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10392) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10472) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20728) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 11) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10393) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20752) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 48) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20760) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 56) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20768) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 64) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20776) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 72) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10400) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 96) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10408) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 104) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10416) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 112) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10424) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 120) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20736) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20744) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 128) 8 = true) ∧
                  rt.containsWritable (effectiveAddr baseAddr 128) 8 = true)
      (toU64 0)
      [((baseAddr + 96),
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)],
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 (total + amount)), (40, .byte bump)])]
      (((.r0 ↦ᵣ vR0Old) **
      (.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ vR2Old) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8) **
      (effectiveAddr baseAddr 10392 ↦ₘ m10296) **
      (effectiveAddr baseAddr 10472 ↦U64 m10376) **
      (effectiveAddr baseAddr 20728 ↦U64 m20632) **
      (effectiveAddr baseAddr 10 ↦ₘ mNeg86) **
      (effectiveAddr baseAddr 11 ↦ₘ mNeg85) **
      (effectiveAddr baseAddr 10393 ↦ₘ m10297) **
      (effectiveAddr baseAddr 20752 ↦U64 m20656) **
      (effectiveAddr baseAddr 48 ↦U64 mNeg48) **
      (.r3 ↦ᵣ vR3Old) **
      (effectiveAddr baseAddr 20760 ↦U64 m20664) **
      (effectiveAddr baseAddr 56 ↦U64 mNeg40) **
      (effectiveAddr baseAddr 20768 ↦U64 m20672) **
      (effectiveAddr baseAddr 64 ↦U64 mNeg32) **
      (effectiveAddr baseAddr 20776 ↦U64 m20680) **
      (effectiveAddr baseAddr 72 ↦U64 mNeg24) **
      (effectiveAddr baseAddr 10400 ↦U64 m10304) **
      (effectiveAddr baseAddr 10408 ↦U64 m10312) **
      (effectiveAddr baseAddr 10416 ↦U64 m10320) **
      (effectiveAddr baseAddr 10424 ↦U64 m10328) **
      (effectiveAddr baseAddr 20736 ↦U64 m20640) **
      (effectiveAddr baseAddr 20744 ↦U64 amount) **
      (.r4 ↦ᵣ vR4Old)) **
       callStackIs [])
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ wrapAdd total amount) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8) **
      (effectiveAddr baseAddr 10392 ↦ₘ m10296) **
      (effectiveAddr baseAddr 10472 ↦U64 m10376) **
      (effectiveAddr baseAddr 20728 ↦U64 m20632) **
      (effectiveAddr baseAddr 10 ↦ₘ mNeg86) **
      (effectiveAddr baseAddr 11 ↦ₘ mNeg85) **
      (effectiveAddr baseAddr 10393 ↦ₘ m10297) **
      (effectiveAddr baseAddr 20752 ↦U64 m20656) **
      (effectiveAddr baseAddr 48 ↦U64 mNeg48) **
      (.r3 ↦ᵣ toU64 0) **
      (effectiveAddr baseAddr 20760 ↦U64 m20664) **
      (effectiveAddr baseAddr 56 ↦U64 mNeg40) **
      (effectiveAddr baseAddr 20768 ↦U64 m20672) **
      (effectiveAddr baseAddr 64 ↦U64 mNeg32) **
      (effectiveAddr baseAddr 20776 ↦U64 m20680) **
      (effectiveAddr baseAddr 72 ↦U64 mNeg24) **
      (effectiveAddr baseAddr 10400 ↦U64 m10304) **
      (effectiveAddr baseAddr 10408 ↦U64 m10312) **
      (effectiveAddr baseAddr 10416 ↦U64 m10320) **
      (effectiveAddr baseAddr 10424 ↦U64 m10328) **
      (effectiveAddr baseAddr 20736 ↦U64 m20640) **
      (effectiveAddr baseAddr 20744 ↦U64 amount) **
      (.r4 ↦ᵣ total))) ∧
    (mNeg96 = toU64 2 →
     mNeg88 % 256 = toU64 255 →
     mNeg8 = toU64 41 →
     m10296 % 256 = toU64 255 →
     m10376 = toU64 0 →
     m20632 = toU64 16 →
     mNeg86 % 256 = toU64 1 →
     mNeg85 % 256 = toU64 0 →
     m10297 % 256 = toU64 1 →
     mNeg48 = m20656 →
     mNeg40 = m20664 →
     mNeg32 = m20672 →
     mNeg24 = m20680 →
     owner0 = m10304 →
     owner1 = m10312 →
     owner2 = m10320 →
     owner3 = m10328 →
     m20640 ≠ toU64 1 →
      SVM.Solana.Abstract.AsmRefinesTransitionPath
      ((((((((((((((((((((((((((((((((((((((((((((((((((((CodeReq.singleton 0 (.mov64 .r0 (.imm (6)))).union
        (CodeReq.singleton 1 (.ldx .dword .r2 .r1 0))).union
        (CodeReq.singleton 2 (.jne .r2 (.imm (2)) 63))).union
        (CodeReq.singleton 3 (.ldx .byte .r2 .r1 8))).union
        (CodeReq.singleton 4 (.jne .r2 (.imm (255)) 63))).union
        (CodeReq.singleton 5 (.ldx .dword .r2 .r1 88))).union
        (CodeReq.singleton 6 (.jne .r2 (.imm (41)) 63))).union
        (CodeReq.singleton 7 (.ldx .byte .r2 .r1 10392))).union
        (CodeReq.singleton 8 (.jne .r2 (.imm (255)) 63))).union
        (CodeReq.singleton 9 (.ldx .dword .r2 .r1 10472))).union
        (CodeReq.singleton 10 (.jne .r2 (.imm (0)) 63))).union
        (CodeReq.singleton 11 (.mov64 .r0 (.imm (7))))).union
        (CodeReq.singleton 12 (.ldx .dword .r2 .r1 20728))).union
        (CodeReq.singleton 13 (.jne .r2 (.imm (16)) 63))).union
        (CodeReq.singleton 14 (.mov64 .r0 (.imm (8))))).union
        (CodeReq.singleton 15 (.ldx .byte .r2 .r1 10))).union
        (CodeReq.singleton 16 (.jne .r2 (.imm (1)) 63))).union
        (CodeReq.singleton 17 (.ldx .byte .r2 .r1 11))).union
        (CodeReq.singleton 18 (.jne .r2 (.imm (0)) 63))).union
        (CodeReq.singleton 19 (.mov64 .r0 (.imm (5))))).union
        (CodeReq.singleton 20 (.ldx .byte .r2 .r1 10393))).union
        (CodeReq.singleton 21 (.jne .r2 (.imm (1)) 63))).union
        (CodeReq.singleton 22 (.mov64 .r0 (.imm (4))))).union
        (CodeReq.singleton 23 (.ldx .dword .r2 .r1 20752))).union
        (CodeReq.singleton 24 (.ldx .dword .r3 .r1 48))).union
        (CodeReq.singleton 25 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 26 (.ldx .dword .r2 .r1 20760))).union
        (CodeReq.singleton 27 (.ldx .dword .r3 .r1 56))).union
        (CodeReq.singleton 28 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 29 (.ldx .dword .r2 .r1 20768))).union
        (CodeReq.singleton 30 (.ldx .dword .r3 .r1 64))).union
        (CodeReq.singleton 31 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 32 (.ldx .dword .r2 .r1 20776))).union
        (CodeReq.singleton 33 (.ldx .dword .r3 .r1 72))).union
        (CodeReq.singleton 34 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 35 (.ldx .dword .r2 .r1 10400))).union
        (CodeReq.singleton 36 (.ldx .dword .r3 .r1 96))).union
        (CodeReq.singleton 37 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 38 (.ldx .dword .r2 .r1 10408))).union
        (CodeReq.singleton 39 (.ldx .dword .r3 .r1 104))).union
        (CodeReq.singleton 40 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 41 (.ldx .dword .r2 .r1 10416))).union
        (CodeReq.singleton 42 (.ldx .dword .r3 .r1 112))).union
        (CodeReq.singleton 43 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 44 (.ldx .dword .r2 .r1 10424))).union
        (CodeReq.singleton 45 (.ldx .dword .r3 .r1 120))).union
        (CodeReq.singleton 46 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 47 (.mov64 .r0 (.imm (2))))).union
        (CodeReq.singleton 48 (.ldx .dword .r2 .r1 20736))).union
        (CodeReq.singleton 49 (.jne .r2 (.imm (1)) 63)))).union
        (CodeReq.singleton 63 .exit))
      (50 + 1) (0) 0
      (fun rt => (((((((((((((((((((((((((rt.containsRange (effectiveAddr baseAddr 0) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 8) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 88) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10392) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10472) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20728) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 11) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10393) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20752) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 48) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20760) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 56) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20768) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 64) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20776) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 72) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10400) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 96) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10408) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 104) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10416) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 112) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10424) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 120) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20736) 8 = true)
      (toU64 2)
      [((baseAddr + 96),
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)],
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)])]
      (((.r0 ↦ᵣ vR0Old) **
      (.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ vR2Old) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8) **
      (effectiveAddr baseAddr 10392 ↦ₘ m10296) **
      (effectiveAddr baseAddr 10472 ↦U64 m10376) **
      (effectiveAddr baseAddr 20728 ↦U64 m20632) **
      (effectiveAddr baseAddr 10 ↦ₘ mNeg86) **
      (effectiveAddr baseAddr 11 ↦ₘ mNeg85) **
      (effectiveAddr baseAddr 10393 ↦ₘ m10297) **
      (effectiveAddr baseAddr 20752 ↦U64 m20656) **
      (effectiveAddr baseAddr 48 ↦U64 mNeg48) **
      (.r3 ↦ᵣ vR3Old) **
      (effectiveAddr baseAddr 20760 ↦U64 m20664) **
      (effectiveAddr baseAddr 56 ↦U64 mNeg40) **
      (effectiveAddr baseAddr 20768 ↦U64 m20672) **
      (effectiveAddr baseAddr 64 ↦U64 mNeg32) **
      (effectiveAddr baseAddr 20776 ↦U64 m20680) **
      (effectiveAddr baseAddr 72 ↦U64 mNeg24) **
      (effectiveAddr baseAddr 10400 ↦U64 m10304) **
      (effectiveAddr baseAddr 10408 ↦U64 m10312) **
      (effectiveAddr baseAddr 10416 ↦U64 m10320) **
      (effectiveAddr baseAddr 10424 ↦U64 m10328) **
      (effectiveAddr baseAddr 20736 ↦U64 m20640)) **
       callStackIs [])
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ m20640) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8) **
      (effectiveAddr baseAddr 10392 ↦ₘ m10296) **
      (effectiveAddr baseAddr 10472 ↦U64 m10376) **
      (effectiveAddr baseAddr 20728 ↦U64 m20632) **
      (effectiveAddr baseAddr 10 ↦ₘ mNeg86) **
      (effectiveAddr baseAddr 11 ↦ₘ mNeg85) **
      (effectiveAddr baseAddr 10393 ↦ₘ m10297) **
      (effectiveAddr baseAddr 20752 ↦U64 m20656) **
      (effectiveAddr baseAddr 48 ↦U64 mNeg48) **
      (.r3 ↦ᵣ owner3) **
      (effectiveAddr baseAddr 20760 ↦U64 m20664) **
      (effectiveAddr baseAddr 56 ↦U64 mNeg40) **
      (effectiveAddr baseAddr 20768 ↦U64 m20672) **
      (effectiveAddr baseAddr 64 ↦U64 mNeg32) **
      (effectiveAddr baseAddr 20776 ↦U64 m20680) **
      (effectiveAddr baseAddr 72 ↦U64 mNeg24) **
      (effectiveAddr baseAddr 10400 ↦U64 m10304) **
      (effectiveAddr baseAddr 10408 ↦U64 m10312) **
      (effectiveAddr baseAddr 10416 ↦U64 m10320) **
      (effectiveAddr baseAddr 10424 ↦U64 m10328) **
      (effectiveAddr baseAddr 20736 ↦U64 m20640))) ∧
    (mNeg96 = toU64 2 →
     mNeg88 % 256 = toU64 255 →
     mNeg8 = toU64 41 →
     m10296 % 256 = toU64 255 →
     m10376 = toU64 0 →
     m20632 = toU64 16 →
     mNeg86 % 256 = toU64 1 →
     mNeg85 % 256 = toU64 0 →
     m10297 % 256 = toU64 1 →
     mNeg48 = m20656 →
     mNeg40 = m20664 →
     mNeg32 = m20672 →
     mNeg24 = m20680 →
     owner0 ≠ m10304 →
      SVM.Solana.Abstract.AsmRefinesTransitionPath
      ((((((((((((((((((((((((((((((((((((((((CodeReq.singleton 0 (.mov64 .r0 (.imm (6)))).union
        (CodeReq.singleton 1 (.ldx .dword .r2 .r1 0))).union
        (CodeReq.singleton 2 (.jne .r2 (.imm (2)) 63))).union
        (CodeReq.singleton 3 (.ldx .byte .r2 .r1 8))).union
        (CodeReq.singleton 4 (.jne .r2 (.imm (255)) 63))).union
        (CodeReq.singleton 5 (.ldx .dword .r2 .r1 88))).union
        (CodeReq.singleton 6 (.jne .r2 (.imm (41)) 63))).union
        (CodeReq.singleton 7 (.ldx .byte .r2 .r1 10392))).union
        (CodeReq.singleton 8 (.jne .r2 (.imm (255)) 63))).union
        (CodeReq.singleton 9 (.ldx .dword .r2 .r1 10472))).union
        (CodeReq.singleton 10 (.jne .r2 (.imm (0)) 63))).union
        (CodeReq.singleton 11 (.mov64 .r0 (.imm (7))))).union
        (CodeReq.singleton 12 (.ldx .dword .r2 .r1 20728))).union
        (CodeReq.singleton 13 (.jne .r2 (.imm (16)) 63))).union
        (CodeReq.singleton 14 (.mov64 .r0 (.imm (8))))).union
        (CodeReq.singleton 15 (.ldx .byte .r2 .r1 10))).union
        (CodeReq.singleton 16 (.jne .r2 (.imm (1)) 63))).union
        (CodeReq.singleton 17 (.ldx .byte .r2 .r1 11))).union
        (CodeReq.singleton 18 (.jne .r2 (.imm (0)) 63))).union
        (CodeReq.singleton 19 (.mov64 .r0 (.imm (5))))).union
        (CodeReq.singleton 20 (.ldx .byte .r2 .r1 10393))).union
        (CodeReq.singleton 21 (.jne .r2 (.imm (1)) 63))).union
        (CodeReq.singleton 22 (.mov64 .r0 (.imm (4))))).union
        (CodeReq.singleton 23 (.ldx .dword .r2 .r1 20752))).union
        (CodeReq.singleton 24 (.ldx .dword .r3 .r1 48))).union
        (CodeReq.singleton 25 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 26 (.ldx .dword .r2 .r1 20760))).union
        (CodeReq.singleton 27 (.ldx .dword .r3 .r1 56))).union
        (CodeReq.singleton 28 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 29 (.ldx .dword .r2 .r1 20768))).union
        (CodeReq.singleton 30 (.ldx .dword .r3 .r1 64))).union
        (CodeReq.singleton 31 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 32 (.ldx .dword .r2 .r1 20776))).union
        (CodeReq.singleton 33 (.ldx .dword .r3 .r1 72))).union
        (CodeReq.singleton 34 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 35 (.ldx .dword .r2 .r1 10400))).union
        (CodeReq.singleton 36 (.ldx .dword .r3 .r1 96))).union
        (CodeReq.singleton 37 (.jne .r3 (.reg .r2) 63)))).union
        (CodeReq.singleton 63 .exit))
      (38 + 1) (0) 0
      (fun rt => ((((((((((((((((((rt.containsRange (effectiveAddr baseAddr 0) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 8) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 88) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10392) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10472) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20728) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 11) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10393) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20752) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 48) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20760) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 56) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20768) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 64) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20776) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 72) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10400) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 96) 8 = true)
      (toU64 4)
      [((baseAddr + 96),
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)],
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)])]
      (((.r0 ↦ᵣ vR0Old) **
      (.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ vR2Old) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8) **
      (effectiveAddr baseAddr 10392 ↦ₘ m10296) **
      (effectiveAddr baseAddr 10472 ↦U64 m10376) **
      (effectiveAddr baseAddr 20728 ↦U64 m20632) **
      (effectiveAddr baseAddr 10 ↦ₘ mNeg86) **
      (effectiveAddr baseAddr 11 ↦ₘ mNeg85) **
      (effectiveAddr baseAddr 10393 ↦ₘ m10297) **
      (effectiveAddr baseAddr 20752 ↦U64 m20656) **
      (effectiveAddr baseAddr 48 ↦U64 mNeg48) **
      (.r3 ↦ᵣ vR3Old) **
      (effectiveAddr baseAddr 20760 ↦U64 m20664) **
      (effectiveAddr baseAddr 56 ↦U64 mNeg40) **
      (effectiveAddr baseAddr 20768 ↦U64 m20672) **
      (effectiveAddr baseAddr 64 ↦U64 mNeg32) **
      (effectiveAddr baseAddr 20776 ↦U64 m20680) **
      (effectiveAddr baseAddr 72 ↦U64 mNeg24) **
      (effectiveAddr baseAddr 10400 ↦U64 m10304)) **
       callStackIs [])
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ m10304) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8) **
      (effectiveAddr baseAddr 10392 ↦ₘ m10296) **
      (effectiveAddr baseAddr 10472 ↦U64 m10376) **
      (effectiveAddr baseAddr 20728 ↦U64 m20632) **
      (effectiveAddr baseAddr 10 ↦ₘ mNeg86) **
      (effectiveAddr baseAddr 11 ↦ₘ mNeg85) **
      (effectiveAddr baseAddr 10393 ↦ₘ m10297) **
      (effectiveAddr baseAddr 20752 ↦U64 m20656) **
      (effectiveAddr baseAddr 48 ↦U64 mNeg48) **
      (.r3 ↦ᵣ owner0) **
      (effectiveAddr baseAddr 20760 ↦U64 m20664) **
      (effectiveAddr baseAddr 56 ↦U64 mNeg40) **
      (effectiveAddr baseAddr 20768 ↦U64 m20672) **
      (effectiveAddr baseAddr 64 ↦U64 mNeg32) **
      (effectiveAddr baseAddr 20776 ↦U64 m20680) **
      (effectiveAddr baseAddr 72 ↦U64 mNeg24) **
      (effectiveAddr baseAddr 10400 ↦U64 m10304))) ∧
    (mNeg96 = toU64 2 →
     mNeg88 % 256 = toU64 255 →
     mNeg8 = toU64 41 →
     m10296 % 256 = toU64 255 →
     m10376 = toU64 0 →
     m20632 = toU64 16 →
     mNeg86 % 256 = toU64 1 →
     mNeg85 % 256 = toU64 0 →
     m10297 % 256 = toU64 1 →
     mNeg48 = m20656 →
     mNeg40 = m20664 →
     mNeg32 = m20672 →
     mNeg24 = m20680 →
     owner0 = m10304 →
     owner1 ≠ m10312 →
      SVM.Solana.Abstract.AsmRefinesTransitionPath
      (((((((((((((((((((((((((((((((((((((((((((CodeReq.singleton 0 (.mov64 .r0 (.imm (6)))).union
        (CodeReq.singleton 1 (.ldx .dword .r2 .r1 0))).union
        (CodeReq.singleton 2 (.jne .r2 (.imm (2)) 63))).union
        (CodeReq.singleton 3 (.ldx .byte .r2 .r1 8))).union
        (CodeReq.singleton 4 (.jne .r2 (.imm (255)) 63))).union
        (CodeReq.singleton 5 (.ldx .dword .r2 .r1 88))).union
        (CodeReq.singleton 6 (.jne .r2 (.imm (41)) 63))).union
        (CodeReq.singleton 7 (.ldx .byte .r2 .r1 10392))).union
        (CodeReq.singleton 8 (.jne .r2 (.imm (255)) 63))).union
        (CodeReq.singleton 9 (.ldx .dword .r2 .r1 10472))).union
        (CodeReq.singleton 10 (.jne .r2 (.imm (0)) 63))).union
        (CodeReq.singleton 11 (.mov64 .r0 (.imm (7))))).union
        (CodeReq.singleton 12 (.ldx .dword .r2 .r1 20728))).union
        (CodeReq.singleton 13 (.jne .r2 (.imm (16)) 63))).union
        (CodeReq.singleton 14 (.mov64 .r0 (.imm (8))))).union
        (CodeReq.singleton 15 (.ldx .byte .r2 .r1 10))).union
        (CodeReq.singleton 16 (.jne .r2 (.imm (1)) 63))).union
        (CodeReq.singleton 17 (.ldx .byte .r2 .r1 11))).union
        (CodeReq.singleton 18 (.jne .r2 (.imm (0)) 63))).union
        (CodeReq.singleton 19 (.mov64 .r0 (.imm (5))))).union
        (CodeReq.singleton 20 (.ldx .byte .r2 .r1 10393))).union
        (CodeReq.singleton 21 (.jne .r2 (.imm (1)) 63))).union
        (CodeReq.singleton 22 (.mov64 .r0 (.imm (4))))).union
        (CodeReq.singleton 23 (.ldx .dword .r2 .r1 20752))).union
        (CodeReq.singleton 24 (.ldx .dword .r3 .r1 48))).union
        (CodeReq.singleton 25 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 26 (.ldx .dword .r2 .r1 20760))).union
        (CodeReq.singleton 27 (.ldx .dword .r3 .r1 56))).union
        (CodeReq.singleton 28 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 29 (.ldx .dword .r2 .r1 20768))).union
        (CodeReq.singleton 30 (.ldx .dword .r3 .r1 64))).union
        (CodeReq.singleton 31 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 32 (.ldx .dword .r2 .r1 20776))).union
        (CodeReq.singleton 33 (.ldx .dword .r3 .r1 72))).union
        (CodeReq.singleton 34 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 35 (.ldx .dword .r2 .r1 10400))).union
        (CodeReq.singleton 36 (.ldx .dword .r3 .r1 96))).union
        (CodeReq.singleton 37 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 38 (.ldx .dword .r2 .r1 10408))).union
        (CodeReq.singleton 39 (.ldx .dword .r3 .r1 104))).union
        (CodeReq.singleton 40 (.jne .r3 (.reg .r2) 63)))).union
        (CodeReq.singleton 63 .exit))
      (41 + 1) (0) 0
      (fun rt => ((((((((((((((((((((rt.containsRange (effectiveAddr baseAddr 0) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 8) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 88) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10392) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10472) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20728) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 11) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10393) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20752) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 48) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20760) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 56) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20768) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 64) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20776) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 72) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10400) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 96) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10408) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 104) 8 = true)
      (toU64 4)
      [((baseAddr + 96),
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)],
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)])]
      (((.r0 ↦ᵣ vR0Old) **
      (.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ vR2Old) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8) **
      (effectiveAddr baseAddr 10392 ↦ₘ m10296) **
      (effectiveAddr baseAddr 10472 ↦U64 m10376) **
      (effectiveAddr baseAddr 20728 ↦U64 m20632) **
      (effectiveAddr baseAddr 10 ↦ₘ mNeg86) **
      (effectiveAddr baseAddr 11 ↦ₘ mNeg85) **
      (effectiveAddr baseAddr 10393 ↦ₘ m10297) **
      (effectiveAddr baseAddr 20752 ↦U64 m20656) **
      (effectiveAddr baseAddr 48 ↦U64 mNeg48) **
      (.r3 ↦ᵣ vR3Old) **
      (effectiveAddr baseAddr 20760 ↦U64 m20664) **
      (effectiveAddr baseAddr 56 ↦U64 mNeg40) **
      (effectiveAddr baseAddr 20768 ↦U64 m20672) **
      (effectiveAddr baseAddr 64 ↦U64 mNeg32) **
      (effectiveAddr baseAddr 20776 ↦U64 m20680) **
      (effectiveAddr baseAddr 72 ↦U64 mNeg24) **
      (effectiveAddr baseAddr 10400 ↦U64 m10304) **
      (effectiveAddr baseAddr 10408 ↦U64 m10312)) **
       callStackIs [])
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ m10312) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8) **
      (effectiveAddr baseAddr 10392 ↦ₘ m10296) **
      (effectiveAddr baseAddr 10472 ↦U64 m10376) **
      (effectiveAddr baseAddr 20728 ↦U64 m20632) **
      (effectiveAddr baseAddr 10 ↦ₘ mNeg86) **
      (effectiveAddr baseAddr 11 ↦ₘ mNeg85) **
      (effectiveAddr baseAddr 10393 ↦ₘ m10297) **
      (effectiveAddr baseAddr 20752 ↦U64 m20656) **
      (effectiveAddr baseAddr 48 ↦U64 mNeg48) **
      (.r3 ↦ᵣ owner1) **
      (effectiveAddr baseAddr 20760 ↦U64 m20664) **
      (effectiveAddr baseAddr 56 ↦U64 mNeg40) **
      (effectiveAddr baseAddr 20768 ↦U64 m20672) **
      (effectiveAddr baseAddr 64 ↦U64 mNeg32) **
      (effectiveAddr baseAddr 20776 ↦U64 m20680) **
      (effectiveAddr baseAddr 72 ↦U64 mNeg24) **
      (effectiveAddr baseAddr 10400 ↦U64 m10304) **
      (effectiveAddr baseAddr 10408 ↦U64 m10312))) ∧
    (mNeg96 = toU64 2 →
     mNeg88 % 256 = toU64 255 →
     mNeg8 = toU64 41 →
     m10296 % 256 = toU64 255 →
     m10376 = toU64 0 →
     m20632 = toU64 16 →
     mNeg86 % 256 = toU64 1 →
     mNeg85 % 256 = toU64 0 →
     m10297 % 256 = toU64 1 →
     mNeg48 = m20656 →
     mNeg40 = m20664 →
     mNeg32 = m20672 →
     mNeg24 = m20680 →
     owner0 = m10304 →
     owner1 = m10312 →
     owner2 ≠ m10320 →
      SVM.Solana.Abstract.AsmRefinesTransitionPath
      ((((((((((((((((((((((((((((((((((((((((((((((CodeReq.singleton 0 (.mov64 .r0 (.imm (6)))).union
        (CodeReq.singleton 1 (.ldx .dword .r2 .r1 0))).union
        (CodeReq.singleton 2 (.jne .r2 (.imm (2)) 63))).union
        (CodeReq.singleton 3 (.ldx .byte .r2 .r1 8))).union
        (CodeReq.singleton 4 (.jne .r2 (.imm (255)) 63))).union
        (CodeReq.singleton 5 (.ldx .dword .r2 .r1 88))).union
        (CodeReq.singleton 6 (.jne .r2 (.imm (41)) 63))).union
        (CodeReq.singleton 7 (.ldx .byte .r2 .r1 10392))).union
        (CodeReq.singleton 8 (.jne .r2 (.imm (255)) 63))).union
        (CodeReq.singleton 9 (.ldx .dword .r2 .r1 10472))).union
        (CodeReq.singleton 10 (.jne .r2 (.imm (0)) 63))).union
        (CodeReq.singleton 11 (.mov64 .r0 (.imm (7))))).union
        (CodeReq.singleton 12 (.ldx .dword .r2 .r1 20728))).union
        (CodeReq.singleton 13 (.jne .r2 (.imm (16)) 63))).union
        (CodeReq.singleton 14 (.mov64 .r0 (.imm (8))))).union
        (CodeReq.singleton 15 (.ldx .byte .r2 .r1 10))).union
        (CodeReq.singleton 16 (.jne .r2 (.imm (1)) 63))).union
        (CodeReq.singleton 17 (.ldx .byte .r2 .r1 11))).union
        (CodeReq.singleton 18 (.jne .r2 (.imm (0)) 63))).union
        (CodeReq.singleton 19 (.mov64 .r0 (.imm (5))))).union
        (CodeReq.singleton 20 (.ldx .byte .r2 .r1 10393))).union
        (CodeReq.singleton 21 (.jne .r2 (.imm (1)) 63))).union
        (CodeReq.singleton 22 (.mov64 .r0 (.imm (4))))).union
        (CodeReq.singleton 23 (.ldx .dword .r2 .r1 20752))).union
        (CodeReq.singleton 24 (.ldx .dword .r3 .r1 48))).union
        (CodeReq.singleton 25 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 26 (.ldx .dword .r2 .r1 20760))).union
        (CodeReq.singleton 27 (.ldx .dword .r3 .r1 56))).union
        (CodeReq.singleton 28 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 29 (.ldx .dword .r2 .r1 20768))).union
        (CodeReq.singleton 30 (.ldx .dword .r3 .r1 64))).union
        (CodeReq.singleton 31 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 32 (.ldx .dword .r2 .r1 20776))).union
        (CodeReq.singleton 33 (.ldx .dword .r3 .r1 72))).union
        (CodeReq.singleton 34 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 35 (.ldx .dword .r2 .r1 10400))).union
        (CodeReq.singleton 36 (.ldx .dword .r3 .r1 96))).union
        (CodeReq.singleton 37 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 38 (.ldx .dword .r2 .r1 10408))).union
        (CodeReq.singleton 39 (.ldx .dword .r3 .r1 104))).union
        (CodeReq.singleton 40 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 41 (.ldx .dword .r2 .r1 10416))).union
        (CodeReq.singleton 42 (.ldx .dword .r3 .r1 112))).union
        (CodeReq.singleton 43 (.jne .r3 (.reg .r2) 63)))).union
        (CodeReq.singleton 63 .exit))
      (44 + 1) (0) 0
      (fun rt => ((((((((((((((((((((((rt.containsRange (effectiveAddr baseAddr 0) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 8) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 88) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10392) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10472) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20728) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 11) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10393) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20752) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 48) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20760) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 56) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20768) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 64) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20776) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 72) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10400) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 96) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10408) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 104) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10416) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 112) 8 = true)
      (toU64 4)
      [((baseAddr + 96),
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)],
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)])]
      (((.r0 ↦ᵣ vR0Old) **
      (.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ vR2Old) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8) **
      (effectiveAddr baseAddr 10392 ↦ₘ m10296) **
      (effectiveAddr baseAddr 10472 ↦U64 m10376) **
      (effectiveAddr baseAddr 20728 ↦U64 m20632) **
      (effectiveAddr baseAddr 10 ↦ₘ mNeg86) **
      (effectiveAddr baseAddr 11 ↦ₘ mNeg85) **
      (effectiveAddr baseAddr 10393 ↦ₘ m10297) **
      (effectiveAddr baseAddr 20752 ↦U64 m20656) **
      (effectiveAddr baseAddr 48 ↦U64 mNeg48) **
      (.r3 ↦ᵣ vR3Old) **
      (effectiveAddr baseAddr 20760 ↦U64 m20664) **
      (effectiveAddr baseAddr 56 ↦U64 mNeg40) **
      (effectiveAddr baseAddr 20768 ↦U64 m20672) **
      (effectiveAddr baseAddr 64 ↦U64 mNeg32) **
      (effectiveAddr baseAddr 20776 ↦U64 m20680) **
      (effectiveAddr baseAddr 72 ↦U64 mNeg24) **
      (effectiveAddr baseAddr 10400 ↦U64 m10304) **
      (effectiveAddr baseAddr 10408 ↦U64 m10312) **
      (effectiveAddr baseAddr 10416 ↦U64 m10320)) **
       callStackIs [])
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ m10320) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8) **
      (effectiveAddr baseAddr 10392 ↦ₘ m10296) **
      (effectiveAddr baseAddr 10472 ↦U64 m10376) **
      (effectiveAddr baseAddr 20728 ↦U64 m20632) **
      (effectiveAddr baseAddr 10 ↦ₘ mNeg86) **
      (effectiveAddr baseAddr 11 ↦ₘ mNeg85) **
      (effectiveAddr baseAddr 10393 ↦ₘ m10297) **
      (effectiveAddr baseAddr 20752 ↦U64 m20656) **
      (effectiveAddr baseAddr 48 ↦U64 mNeg48) **
      (.r3 ↦ᵣ owner2) **
      (effectiveAddr baseAddr 20760 ↦U64 m20664) **
      (effectiveAddr baseAddr 56 ↦U64 mNeg40) **
      (effectiveAddr baseAddr 20768 ↦U64 m20672) **
      (effectiveAddr baseAddr 64 ↦U64 mNeg32) **
      (effectiveAddr baseAddr 20776 ↦U64 m20680) **
      (effectiveAddr baseAddr 72 ↦U64 mNeg24) **
      (effectiveAddr baseAddr 10400 ↦U64 m10304) **
      (effectiveAddr baseAddr 10408 ↦U64 m10312) **
      (effectiveAddr baseAddr 10416 ↦U64 m10320))) ∧
    (mNeg96 = toU64 2 →
     mNeg88 % 256 = toU64 255 →
     mNeg8 = toU64 41 →
     m10296 % 256 = toU64 255 →
     m10376 = toU64 0 →
     m20632 = toU64 16 →
     mNeg86 % 256 = toU64 1 →
     mNeg85 % 256 = toU64 0 →
     m10297 % 256 = toU64 1 →
     mNeg48 = m20656 →
     mNeg40 = m20664 →
     mNeg32 = m20672 →
     mNeg24 = m20680 →
     owner0 = m10304 →
     owner1 = m10312 →
     owner2 = m10320 →
     owner3 ≠ m10328 →
      SVM.Solana.Abstract.AsmRefinesTransitionPath
      (((((((((((((((((((((((((((((((((((((((((((((((((CodeReq.singleton 0 (.mov64 .r0 (.imm (6)))).union
        (CodeReq.singleton 1 (.ldx .dword .r2 .r1 0))).union
        (CodeReq.singleton 2 (.jne .r2 (.imm (2)) 63))).union
        (CodeReq.singleton 3 (.ldx .byte .r2 .r1 8))).union
        (CodeReq.singleton 4 (.jne .r2 (.imm (255)) 63))).union
        (CodeReq.singleton 5 (.ldx .dword .r2 .r1 88))).union
        (CodeReq.singleton 6 (.jne .r2 (.imm (41)) 63))).union
        (CodeReq.singleton 7 (.ldx .byte .r2 .r1 10392))).union
        (CodeReq.singleton 8 (.jne .r2 (.imm (255)) 63))).union
        (CodeReq.singleton 9 (.ldx .dword .r2 .r1 10472))).union
        (CodeReq.singleton 10 (.jne .r2 (.imm (0)) 63))).union
        (CodeReq.singleton 11 (.mov64 .r0 (.imm (7))))).union
        (CodeReq.singleton 12 (.ldx .dword .r2 .r1 20728))).union
        (CodeReq.singleton 13 (.jne .r2 (.imm (16)) 63))).union
        (CodeReq.singleton 14 (.mov64 .r0 (.imm (8))))).union
        (CodeReq.singleton 15 (.ldx .byte .r2 .r1 10))).union
        (CodeReq.singleton 16 (.jne .r2 (.imm (1)) 63))).union
        (CodeReq.singleton 17 (.ldx .byte .r2 .r1 11))).union
        (CodeReq.singleton 18 (.jne .r2 (.imm (0)) 63))).union
        (CodeReq.singleton 19 (.mov64 .r0 (.imm (5))))).union
        (CodeReq.singleton 20 (.ldx .byte .r2 .r1 10393))).union
        (CodeReq.singleton 21 (.jne .r2 (.imm (1)) 63))).union
        (CodeReq.singleton 22 (.mov64 .r0 (.imm (4))))).union
        (CodeReq.singleton 23 (.ldx .dword .r2 .r1 20752))).union
        (CodeReq.singleton 24 (.ldx .dword .r3 .r1 48))).union
        (CodeReq.singleton 25 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 26 (.ldx .dword .r2 .r1 20760))).union
        (CodeReq.singleton 27 (.ldx .dword .r3 .r1 56))).union
        (CodeReq.singleton 28 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 29 (.ldx .dword .r2 .r1 20768))).union
        (CodeReq.singleton 30 (.ldx .dword .r3 .r1 64))).union
        (CodeReq.singleton 31 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 32 (.ldx .dword .r2 .r1 20776))).union
        (CodeReq.singleton 33 (.ldx .dword .r3 .r1 72))).union
        (CodeReq.singleton 34 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 35 (.ldx .dword .r2 .r1 10400))).union
        (CodeReq.singleton 36 (.ldx .dword .r3 .r1 96))).union
        (CodeReq.singleton 37 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 38 (.ldx .dword .r2 .r1 10408))).union
        (CodeReq.singleton 39 (.ldx .dword .r3 .r1 104))).union
        (CodeReq.singleton 40 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 41 (.ldx .dword .r2 .r1 10416))).union
        (CodeReq.singleton 42 (.ldx .dword .r3 .r1 112))).union
        (CodeReq.singleton 43 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 44 (.ldx .dword .r2 .r1 10424))).union
        (CodeReq.singleton 45 (.ldx .dword .r3 .r1 120))).union
        (CodeReq.singleton 46 (.jne .r3 (.reg .r2) 63)))).union
        (CodeReq.singleton 63 .exit))
      (47 + 1) (0) 0
      (fun rt => ((((((((((((((((((((((((rt.containsRange (effectiveAddr baseAddr 0) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 8) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 88) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10392) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10472) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20728) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 11) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10393) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20752) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 48) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20760) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 56) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20768) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 64) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20776) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 72) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10400) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 96) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10408) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 104) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10416) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 112) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10424) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 120) 8 = true)
      (toU64 4)
      [((baseAddr + 96),
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)],
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)])]
      (((.r0 ↦ᵣ vR0Old) **
      (.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ vR2Old) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8) **
      (effectiveAddr baseAddr 10392 ↦ₘ m10296) **
      (effectiveAddr baseAddr 10472 ↦U64 m10376) **
      (effectiveAddr baseAddr 20728 ↦U64 m20632) **
      (effectiveAddr baseAddr 10 ↦ₘ mNeg86) **
      (effectiveAddr baseAddr 11 ↦ₘ mNeg85) **
      (effectiveAddr baseAddr 10393 ↦ₘ m10297) **
      (effectiveAddr baseAddr 20752 ↦U64 m20656) **
      (effectiveAddr baseAddr 48 ↦U64 mNeg48) **
      (.r3 ↦ᵣ vR3Old) **
      (effectiveAddr baseAddr 20760 ↦U64 m20664) **
      (effectiveAddr baseAddr 56 ↦U64 mNeg40) **
      (effectiveAddr baseAddr 20768 ↦U64 m20672) **
      (effectiveAddr baseAddr 64 ↦U64 mNeg32) **
      (effectiveAddr baseAddr 20776 ↦U64 m20680) **
      (effectiveAddr baseAddr 72 ↦U64 mNeg24) **
      (effectiveAddr baseAddr 10400 ↦U64 m10304) **
      (effectiveAddr baseAddr 10408 ↦U64 m10312) **
      (effectiveAddr baseAddr 10416 ↦U64 m10320) **
      (effectiveAddr baseAddr 10424 ↦U64 m10328)) **
       callStackIs [])
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ m10328) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8) **
      (effectiveAddr baseAddr 10392 ↦ₘ m10296) **
      (effectiveAddr baseAddr 10472 ↦U64 m10376) **
      (effectiveAddr baseAddr 20728 ↦U64 m20632) **
      (effectiveAddr baseAddr 10 ↦ₘ mNeg86) **
      (effectiveAddr baseAddr 11 ↦ₘ mNeg85) **
      (effectiveAddr baseAddr 10393 ↦ₘ m10297) **
      (effectiveAddr baseAddr 20752 ↦U64 m20656) **
      (effectiveAddr baseAddr 48 ↦U64 mNeg48) **
      (.r3 ↦ᵣ owner3) **
      (effectiveAddr baseAddr 20760 ↦U64 m20664) **
      (effectiveAddr baseAddr 56 ↦U64 mNeg40) **
      (effectiveAddr baseAddr 20768 ↦U64 m20672) **
      (effectiveAddr baseAddr 64 ↦U64 mNeg32) **
      (effectiveAddr baseAddr 20776 ↦U64 m20680) **
      (effectiveAddr baseAddr 72 ↦U64 mNeg24) **
      (effectiveAddr baseAddr 10400 ↦U64 m10304) **
      (effectiveAddr baseAddr 10408 ↦U64 m10312) **
      (effectiveAddr baseAddr 10416 ↦U64 m10320) **
      (effectiveAddr baseAddr 10424 ↦U64 m10328))) ∧
    (mNeg96 = toU64 2 →
     mNeg88 % 256 = toU64 255 →
     mNeg8 = toU64 41 →
     m10296 % 256 = toU64 255 →
     m10376 = toU64 0 →
     m20632 = toU64 16 →
     mNeg86 % 256 = toU64 1 →
     mNeg85 % 256 = toU64 0 →
     m10297 % 256 = toU64 1 →
     mNeg48 ≠ m20656 →
      SVM.Solana.Abstract.AsmRefinesTransitionPath
      ((((((((((((((((((((((((((((CodeReq.singleton 0 (.mov64 .r0 (.imm (6)))).union
        (CodeReq.singleton 1 (.ldx .dword .r2 .r1 0))).union
        (CodeReq.singleton 2 (.jne .r2 (.imm (2)) 63))).union
        (CodeReq.singleton 3 (.ldx .byte .r2 .r1 8))).union
        (CodeReq.singleton 4 (.jne .r2 (.imm (255)) 63))).union
        (CodeReq.singleton 5 (.ldx .dword .r2 .r1 88))).union
        (CodeReq.singleton 6 (.jne .r2 (.imm (41)) 63))).union
        (CodeReq.singleton 7 (.ldx .byte .r2 .r1 10392))).union
        (CodeReq.singleton 8 (.jne .r2 (.imm (255)) 63))).union
        (CodeReq.singleton 9 (.ldx .dword .r2 .r1 10472))).union
        (CodeReq.singleton 10 (.jne .r2 (.imm (0)) 63))).union
        (CodeReq.singleton 11 (.mov64 .r0 (.imm (7))))).union
        (CodeReq.singleton 12 (.ldx .dword .r2 .r1 20728))).union
        (CodeReq.singleton 13 (.jne .r2 (.imm (16)) 63))).union
        (CodeReq.singleton 14 (.mov64 .r0 (.imm (8))))).union
        (CodeReq.singleton 15 (.ldx .byte .r2 .r1 10))).union
        (CodeReq.singleton 16 (.jne .r2 (.imm (1)) 63))).union
        (CodeReq.singleton 17 (.ldx .byte .r2 .r1 11))).union
        (CodeReq.singleton 18 (.jne .r2 (.imm (0)) 63))).union
        (CodeReq.singleton 19 (.mov64 .r0 (.imm (5))))).union
        (CodeReq.singleton 20 (.ldx .byte .r2 .r1 10393))).union
        (CodeReq.singleton 21 (.jne .r2 (.imm (1)) 63))).union
        (CodeReq.singleton 22 (.mov64 .r0 (.imm (4))))).union
        (CodeReq.singleton 23 (.ldx .dword .r2 .r1 20752))).union
        (CodeReq.singleton 24 (.ldx .dword .r3 .r1 48))).union
        (CodeReq.singleton 25 (.jne .r3 (.reg .r2) 63)))).union
        (CodeReq.singleton 63 .exit))
      (26 + 1) (0) 0
      (fun rt => ((((((((((rt.containsRange (effectiveAddr baseAddr 0) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 8) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 88) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10392) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10472) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20728) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 11) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10393) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20752) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 48) 8 = true)
      (toU64 4)
      [((baseAddr + 96),
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)],
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)])]
      (((.r0 ↦ᵣ vR0Old) **
      (.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ vR2Old) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8) **
      (effectiveAddr baseAddr 10392 ↦ₘ m10296) **
      (effectiveAddr baseAddr 10472 ↦U64 m10376) **
      (effectiveAddr baseAddr 20728 ↦U64 m20632) **
      (effectiveAddr baseAddr 10 ↦ₘ mNeg86) **
      (effectiveAddr baseAddr 11 ↦ₘ mNeg85) **
      (effectiveAddr baseAddr 10393 ↦ₘ m10297) **
      (effectiveAddr baseAddr 20752 ↦U64 m20656) **
      (effectiveAddr baseAddr 48 ↦U64 mNeg48) **
      (.r3 ↦ᵣ vR3Old)) **
       callStackIs [])
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ m20656) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8) **
      (effectiveAddr baseAddr 10392 ↦ₘ m10296) **
      (effectiveAddr baseAddr 10472 ↦U64 m10376) **
      (effectiveAddr baseAddr 20728 ↦U64 m20632) **
      (effectiveAddr baseAddr 10 ↦ₘ mNeg86) **
      (effectiveAddr baseAddr 11 ↦ₘ mNeg85) **
      (effectiveAddr baseAddr 10393 ↦ₘ m10297) **
      (effectiveAddr baseAddr 20752 ↦U64 m20656) **
      (effectiveAddr baseAddr 48 ↦U64 mNeg48) **
      (.r3 ↦ᵣ mNeg48))) ∧
    (mNeg96 = toU64 2 →
     mNeg88 % 256 = toU64 255 →
     mNeg8 = toU64 41 →
     m10296 % 256 = toU64 255 →
     m10376 = toU64 0 →
     m20632 = toU64 16 →
     mNeg86 % 256 = toU64 1 →
     mNeg85 % 256 = toU64 0 →
     m10297 % 256 = toU64 1 →
     mNeg48 = m20656 →
     mNeg40 ≠ m20664 →
      SVM.Solana.Abstract.AsmRefinesTransitionPath
      (((((((((((((((((((((((((((((((CodeReq.singleton 0 (.mov64 .r0 (.imm (6)))).union
        (CodeReq.singleton 1 (.ldx .dword .r2 .r1 0))).union
        (CodeReq.singleton 2 (.jne .r2 (.imm (2)) 63))).union
        (CodeReq.singleton 3 (.ldx .byte .r2 .r1 8))).union
        (CodeReq.singleton 4 (.jne .r2 (.imm (255)) 63))).union
        (CodeReq.singleton 5 (.ldx .dword .r2 .r1 88))).union
        (CodeReq.singleton 6 (.jne .r2 (.imm (41)) 63))).union
        (CodeReq.singleton 7 (.ldx .byte .r2 .r1 10392))).union
        (CodeReq.singleton 8 (.jne .r2 (.imm (255)) 63))).union
        (CodeReq.singleton 9 (.ldx .dword .r2 .r1 10472))).union
        (CodeReq.singleton 10 (.jne .r2 (.imm (0)) 63))).union
        (CodeReq.singleton 11 (.mov64 .r0 (.imm (7))))).union
        (CodeReq.singleton 12 (.ldx .dword .r2 .r1 20728))).union
        (CodeReq.singleton 13 (.jne .r2 (.imm (16)) 63))).union
        (CodeReq.singleton 14 (.mov64 .r0 (.imm (8))))).union
        (CodeReq.singleton 15 (.ldx .byte .r2 .r1 10))).union
        (CodeReq.singleton 16 (.jne .r2 (.imm (1)) 63))).union
        (CodeReq.singleton 17 (.ldx .byte .r2 .r1 11))).union
        (CodeReq.singleton 18 (.jne .r2 (.imm (0)) 63))).union
        (CodeReq.singleton 19 (.mov64 .r0 (.imm (5))))).union
        (CodeReq.singleton 20 (.ldx .byte .r2 .r1 10393))).union
        (CodeReq.singleton 21 (.jne .r2 (.imm (1)) 63))).union
        (CodeReq.singleton 22 (.mov64 .r0 (.imm (4))))).union
        (CodeReq.singleton 23 (.ldx .dword .r2 .r1 20752))).union
        (CodeReq.singleton 24 (.ldx .dword .r3 .r1 48))).union
        (CodeReq.singleton 25 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 26 (.ldx .dword .r2 .r1 20760))).union
        (CodeReq.singleton 27 (.ldx .dword .r3 .r1 56))).union
        (CodeReq.singleton 28 (.jne .r3 (.reg .r2) 63)))).union
        (CodeReq.singleton 63 .exit))
      (29 + 1) (0) 0
      (fun rt => ((((((((((((rt.containsRange (effectiveAddr baseAddr 0) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 8) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 88) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10392) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10472) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20728) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 11) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10393) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20752) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 48) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20760) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 56) 8 = true)
      (toU64 4)
      [((baseAddr + 96),
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)],
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)])]
      (((.r0 ↦ᵣ vR0Old) **
      (.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ vR2Old) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8) **
      (effectiveAddr baseAddr 10392 ↦ₘ m10296) **
      (effectiveAddr baseAddr 10472 ↦U64 m10376) **
      (effectiveAddr baseAddr 20728 ↦U64 m20632) **
      (effectiveAddr baseAddr 10 ↦ₘ mNeg86) **
      (effectiveAddr baseAddr 11 ↦ₘ mNeg85) **
      (effectiveAddr baseAddr 10393 ↦ₘ m10297) **
      (effectiveAddr baseAddr 20752 ↦U64 m20656) **
      (effectiveAddr baseAddr 48 ↦U64 mNeg48) **
      (.r3 ↦ᵣ vR3Old) **
      (effectiveAddr baseAddr 20760 ↦U64 m20664) **
      (effectiveAddr baseAddr 56 ↦U64 mNeg40)) **
       callStackIs [])
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ m20664) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8) **
      (effectiveAddr baseAddr 10392 ↦ₘ m10296) **
      (effectiveAddr baseAddr 10472 ↦U64 m10376) **
      (effectiveAddr baseAddr 20728 ↦U64 m20632) **
      (effectiveAddr baseAddr 10 ↦ₘ mNeg86) **
      (effectiveAddr baseAddr 11 ↦ₘ mNeg85) **
      (effectiveAddr baseAddr 10393 ↦ₘ m10297) **
      (effectiveAddr baseAddr 20752 ↦U64 m20656) **
      (effectiveAddr baseAddr 48 ↦U64 mNeg48) **
      (.r3 ↦ᵣ mNeg40) **
      (effectiveAddr baseAddr 20760 ↦U64 m20664) **
      (effectiveAddr baseAddr 56 ↦U64 mNeg40))) ∧
    (mNeg96 = toU64 2 →
     mNeg88 % 256 = toU64 255 →
     mNeg8 = toU64 41 →
     m10296 % 256 = toU64 255 →
     m10376 = toU64 0 →
     m20632 = toU64 16 →
     mNeg86 % 256 = toU64 1 →
     mNeg85 % 256 = toU64 0 →
     m10297 % 256 = toU64 1 →
     mNeg48 = m20656 →
     mNeg40 = m20664 →
     mNeg32 ≠ m20672 →
      SVM.Solana.Abstract.AsmRefinesTransitionPath
      ((((((((((((((((((((((((((((((((((CodeReq.singleton 0 (.mov64 .r0 (.imm (6)))).union
        (CodeReq.singleton 1 (.ldx .dword .r2 .r1 0))).union
        (CodeReq.singleton 2 (.jne .r2 (.imm (2)) 63))).union
        (CodeReq.singleton 3 (.ldx .byte .r2 .r1 8))).union
        (CodeReq.singleton 4 (.jne .r2 (.imm (255)) 63))).union
        (CodeReq.singleton 5 (.ldx .dword .r2 .r1 88))).union
        (CodeReq.singleton 6 (.jne .r2 (.imm (41)) 63))).union
        (CodeReq.singleton 7 (.ldx .byte .r2 .r1 10392))).union
        (CodeReq.singleton 8 (.jne .r2 (.imm (255)) 63))).union
        (CodeReq.singleton 9 (.ldx .dword .r2 .r1 10472))).union
        (CodeReq.singleton 10 (.jne .r2 (.imm (0)) 63))).union
        (CodeReq.singleton 11 (.mov64 .r0 (.imm (7))))).union
        (CodeReq.singleton 12 (.ldx .dword .r2 .r1 20728))).union
        (CodeReq.singleton 13 (.jne .r2 (.imm (16)) 63))).union
        (CodeReq.singleton 14 (.mov64 .r0 (.imm (8))))).union
        (CodeReq.singleton 15 (.ldx .byte .r2 .r1 10))).union
        (CodeReq.singleton 16 (.jne .r2 (.imm (1)) 63))).union
        (CodeReq.singleton 17 (.ldx .byte .r2 .r1 11))).union
        (CodeReq.singleton 18 (.jne .r2 (.imm (0)) 63))).union
        (CodeReq.singleton 19 (.mov64 .r0 (.imm (5))))).union
        (CodeReq.singleton 20 (.ldx .byte .r2 .r1 10393))).union
        (CodeReq.singleton 21 (.jne .r2 (.imm (1)) 63))).union
        (CodeReq.singleton 22 (.mov64 .r0 (.imm (4))))).union
        (CodeReq.singleton 23 (.ldx .dword .r2 .r1 20752))).union
        (CodeReq.singleton 24 (.ldx .dword .r3 .r1 48))).union
        (CodeReq.singleton 25 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 26 (.ldx .dword .r2 .r1 20760))).union
        (CodeReq.singleton 27 (.ldx .dword .r3 .r1 56))).union
        (CodeReq.singleton 28 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 29 (.ldx .dword .r2 .r1 20768))).union
        (CodeReq.singleton 30 (.ldx .dword .r3 .r1 64))).union
        (CodeReq.singleton 31 (.jne .r3 (.reg .r2) 63)))).union
        (CodeReq.singleton 63 .exit))
      (32 + 1) (0) 0
      (fun rt => ((((((((((((((rt.containsRange (effectiveAddr baseAddr 0) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 8) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 88) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10392) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10472) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20728) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 11) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10393) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20752) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 48) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20760) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 56) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20768) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 64) 8 = true)
      (toU64 4)
      [((baseAddr + 96),
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)],
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)])]
      (((.r0 ↦ᵣ vR0Old) **
      (.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ vR2Old) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8) **
      (effectiveAddr baseAddr 10392 ↦ₘ m10296) **
      (effectiveAddr baseAddr 10472 ↦U64 m10376) **
      (effectiveAddr baseAddr 20728 ↦U64 m20632) **
      (effectiveAddr baseAddr 10 ↦ₘ mNeg86) **
      (effectiveAddr baseAddr 11 ↦ₘ mNeg85) **
      (effectiveAddr baseAddr 10393 ↦ₘ m10297) **
      (effectiveAddr baseAddr 20752 ↦U64 m20656) **
      (effectiveAddr baseAddr 48 ↦U64 mNeg48) **
      (.r3 ↦ᵣ vR3Old) **
      (effectiveAddr baseAddr 20760 ↦U64 m20664) **
      (effectiveAddr baseAddr 56 ↦U64 mNeg40) **
      (effectiveAddr baseAddr 20768 ↦U64 m20672) **
      (effectiveAddr baseAddr 64 ↦U64 mNeg32)) **
       callStackIs [])
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ m20672) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8) **
      (effectiveAddr baseAddr 10392 ↦ₘ m10296) **
      (effectiveAddr baseAddr 10472 ↦U64 m10376) **
      (effectiveAddr baseAddr 20728 ↦U64 m20632) **
      (effectiveAddr baseAddr 10 ↦ₘ mNeg86) **
      (effectiveAddr baseAddr 11 ↦ₘ mNeg85) **
      (effectiveAddr baseAddr 10393 ↦ₘ m10297) **
      (effectiveAddr baseAddr 20752 ↦U64 m20656) **
      (effectiveAddr baseAddr 48 ↦U64 mNeg48) **
      (.r3 ↦ᵣ mNeg32) **
      (effectiveAddr baseAddr 20760 ↦U64 m20664) **
      (effectiveAddr baseAddr 56 ↦U64 mNeg40) **
      (effectiveAddr baseAddr 20768 ↦U64 m20672) **
      (effectiveAddr baseAddr 64 ↦U64 mNeg32))) ∧
    (mNeg96 = toU64 2 →
     mNeg88 % 256 = toU64 255 →
     mNeg8 = toU64 41 →
     m10296 % 256 = toU64 255 →
     m10376 = toU64 0 →
     m20632 = toU64 16 →
     mNeg86 % 256 = toU64 1 →
     mNeg85 % 256 = toU64 0 →
     m10297 % 256 = toU64 1 →
     mNeg48 = m20656 →
     mNeg40 = m20664 →
     mNeg32 = m20672 →
     mNeg24 ≠ m20680 →
      SVM.Solana.Abstract.AsmRefinesTransitionPath
      (((((((((((((((((((((((((((((((((((((CodeReq.singleton 0 (.mov64 .r0 (.imm (6)))).union
        (CodeReq.singleton 1 (.ldx .dword .r2 .r1 0))).union
        (CodeReq.singleton 2 (.jne .r2 (.imm (2)) 63))).union
        (CodeReq.singleton 3 (.ldx .byte .r2 .r1 8))).union
        (CodeReq.singleton 4 (.jne .r2 (.imm (255)) 63))).union
        (CodeReq.singleton 5 (.ldx .dword .r2 .r1 88))).union
        (CodeReq.singleton 6 (.jne .r2 (.imm (41)) 63))).union
        (CodeReq.singleton 7 (.ldx .byte .r2 .r1 10392))).union
        (CodeReq.singleton 8 (.jne .r2 (.imm (255)) 63))).union
        (CodeReq.singleton 9 (.ldx .dword .r2 .r1 10472))).union
        (CodeReq.singleton 10 (.jne .r2 (.imm (0)) 63))).union
        (CodeReq.singleton 11 (.mov64 .r0 (.imm (7))))).union
        (CodeReq.singleton 12 (.ldx .dword .r2 .r1 20728))).union
        (CodeReq.singleton 13 (.jne .r2 (.imm (16)) 63))).union
        (CodeReq.singleton 14 (.mov64 .r0 (.imm (8))))).union
        (CodeReq.singleton 15 (.ldx .byte .r2 .r1 10))).union
        (CodeReq.singleton 16 (.jne .r2 (.imm (1)) 63))).union
        (CodeReq.singleton 17 (.ldx .byte .r2 .r1 11))).union
        (CodeReq.singleton 18 (.jne .r2 (.imm (0)) 63))).union
        (CodeReq.singleton 19 (.mov64 .r0 (.imm (5))))).union
        (CodeReq.singleton 20 (.ldx .byte .r2 .r1 10393))).union
        (CodeReq.singleton 21 (.jne .r2 (.imm (1)) 63))).union
        (CodeReq.singleton 22 (.mov64 .r0 (.imm (4))))).union
        (CodeReq.singleton 23 (.ldx .dword .r2 .r1 20752))).union
        (CodeReq.singleton 24 (.ldx .dword .r3 .r1 48))).union
        (CodeReq.singleton 25 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 26 (.ldx .dword .r2 .r1 20760))).union
        (CodeReq.singleton 27 (.ldx .dword .r3 .r1 56))).union
        (CodeReq.singleton 28 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 29 (.ldx .dword .r2 .r1 20768))).union
        (CodeReq.singleton 30 (.ldx .dword .r3 .r1 64))).union
        (CodeReq.singleton 31 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 32 (.ldx .dword .r2 .r1 20776))).union
        (CodeReq.singleton 33 (.ldx .dword .r3 .r1 72))).union
        (CodeReq.singleton 34 (.jne .r3 (.reg .r2) 63)))).union
        (CodeReq.singleton 63 .exit))
      (35 + 1) (0) 0
      (fun rt => ((((((((((((((((rt.containsRange (effectiveAddr baseAddr 0) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 8) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 88) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10392) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10472) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20728) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 11) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10393) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20752) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 48) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20760) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 56) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20768) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 64) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20776) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 72) 8 = true)
      (toU64 4)
      [((baseAddr + 96),
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)],
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)])]
      (((.r0 ↦ᵣ vR0Old) **
      (.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ vR2Old) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8) **
      (effectiveAddr baseAddr 10392 ↦ₘ m10296) **
      (effectiveAddr baseAddr 10472 ↦U64 m10376) **
      (effectiveAddr baseAddr 20728 ↦U64 m20632) **
      (effectiveAddr baseAddr 10 ↦ₘ mNeg86) **
      (effectiveAddr baseAddr 11 ↦ₘ mNeg85) **
      (effectiveAddr baseAddr 10393 ↦ₘ m10297) **
      (effectiveAddr baseAddr 20752 ↦U64 m20656) **
      (effectiveAddr baseAddr 48 ↦U64 mNeg48) **
      (.r3 ↦ᵣ vR3Old) **
      (effectiveAddr baseAddr 20760 ↦U64 m20664) **
      (effectiveAddr baseAddr 56 ↦U64 mNeg40) **
      (effectiveAddr baseAddr 20768 ↦U64 m20672) **
      (effectiveAddr baseAddr 64 ↦U64 mNeg32) **
      (effectiveAddr baseAddr 20776 ↦U64 m20680) **
      (effectiveAddr baseAddr 72 ↦U64 mNeg24)) **
       callStackIs [])
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ m20680) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8) **
      (effectiveAddr baseAddr 10392 ↦ₘ m10296) **
      (effectiveAddr baseAddr 10472 ↦U64 m10376) **
      (effectiveAddr baseAddr 20728 ↦U64 m20632) **
      (effectiveAddr baseAddr 10 ↦ₘ mNeg86) **
      (effectiveAddr baseAddr 11 ↦ₘ mNeg85) **
      (effectiveAddr baseAddr 10393 ↦ₘ m10297) **
      (effectiveAddr baseAddr 20752 ↦U64 m20656) **
      (effectiveAddr baseAddr 48 ↦U64 mNeg48) **
      (.r3 ↦ᵣ mNeg24) **
      (effectiveAddr baseAddr 20760 ↦U64 m20664) **
      (effectiveAddr baseAddr 56 ↦U64 mNeg40) **
      (effectiveAddr baseAddr 20768 ↦U64 m20672) **
      (effectiveAddr baseAddr 64 ↦U64 mNeg32) **
      (effectiveAddr baseAddr 20776 ↦U64 m20680) **
      (effectiveAddr baseAddr 72 ↦U64 mNeg24))) ∧
    (mNeg96 = toU64 2 →
     mNeg88 % 256 = toU64 255 →
     mNeg8 = toU64 41 →
     m10296 % 256 = toU64 255 →
     m10376 = toU64 0 →
     m20632 = toU64 16 →
     mNeg86 % 256 = toU64 1 →
     mNeg85 % 256 = toU64 0 →
     m10297 % 256 = toU64 1 →
     mNeg48 = m20656 →
     mNeg40 = m20664 →
     mNeg32 = m20672 →
     mNeg24 = m20680 →
     owner0 = m10304 →
     owner1 = m10312 →
     owner2 = m10320 →
     owner3 = m10328 →
     m20640 = toU64 1 →
     amount = toU64 0 →
      SVM.Solana.Abstract.AsmRefinesTransitionPath
      (((((((((((((((((((((((((((((((((((((((((((((((((((((((CodeReq.singleton 0 (.mov64 .r0 (.imm (6)))).union
        (CodeReq.singleton 1 (.ldx .dword .r2 .r1 0))).union
        (CodeReq.singleton 2 (.jne .r2 (.imm (2)) 63))).union
        (CodeReq.singleton 3 (.ldx .byte .r2 .r1 8))).union
        (CodeReq.singleton 4 (.jne .r2 (.imm (255)) 63))).union
        (CodeReq.singleton 5 (.ldx .dword .r2 .r1 88))).union
        (CodeReq.singleton 6 (.jne .r2 (.imm (41)) 63))).union
        (CodeReq.singleton 7 (.ldx .byte .r2 .r1 10392))).union
        (CodeReq.singleton 8 (.jne .r2 (.imm (255)) 63))).union
        (CodeReq.singleton 9 (.ldx .dword .r2 .r1 10472))).union
        (CodeReq.singleton 10 (.jne .r2 (.imm (0)) 63))).union
        (CodeReq.singleton 11 (.mov64 .r0 (.imm (7))))).union
        (CodeReq.singleton 12 (.ldx .dword .r2 .r1 20728))).union
        (CodeReq.singleton 13 (.jne .r2 (.imm (16)) 63))).union
        (CodeReq.singleton 14 (.mov64 .r0 (.imm (8))))).union
        (CodeReq.singleton 15 (.ldx .byte .r2 .r1 10))).union
        (CodeReq.singleton 16 (.jne .r2 (.imm (1)) 63))).union
        (CodeReq.singleton 17 (.ldx .byte .r2 .r1 11))).union
        (CodeReq.singleton 18 (.jne .r2 (.imm (0)) 63))).union
        (CodeReq.singleton 19 (.mov64 .r0 (.imm (5))))).union
        (CodeReq.singleton 20 (.ldx .byte .r2 .r1 10393))).union
        (CodeReq.singleton 21 (.jne .r2 (.imm (1)) 63))).union
        (CodeReq.singleton 22 (.mov64 .r0 (.imm (4))))).union
        (CodeReq.singleton 23 (.ldx .dword .r2 .r1 20752))).union
        (CodeReq.singleton 24 (.ldx .dword .r3 .r1 48))).union
        (CodeReq.singleton 25 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 26 (.ldx .dword .r2 .r1 20760))).union
        (CodeReq.singleton 27 (.ldx .dword .r3 .r1 56))).union
        (CodeReq.singleton 28 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 29 (.ldx .dword .r2 .r1 20768))).union
        (CodeReq.singleton 30 (.ldx .dword .r3 .r1 64))).union
        (CodeReq.singleton 31 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 32 (.ldx .dword .r2 .r1 20776))).union
        (CodeReq.singleton 33 (.ldx .dword .r3 .r1 72))).union
        (CodeReq.singleton 34 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 35 (.ldx .dword .r2 .r1 10400))).union
        (CodeReq.singleton 36 (.ldx .dword .r3 .r1 96))).union
        (CodeReq.singleton 37 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 38 (.ldx .dword .r2 .r1 10408))).union
        (CodeReq.singleton 39 (.ldx .dword .r3 .r1 104))).union
        (CodeReq.singleton 40 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 41 (.ldx .dword .r2 .r1 10416))).union
        (CodeReq.singleton 42 (.ldx .dword .r3 .r1 112))).union
        (CodeReq.singleton 43 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 44 (.ldx .dword .r2 .r1 10424))).union
        (CodeReq.singleton 45 (.ldx .dword .r3 .r1 120))).union
        (CodeReq.singleton 46 (.jne .r3 (.reg .r2) 63))).union
        (CodeReq.singleton 47 (.mov64 .r0 (.imm (2))))).union
        (CodeReq.singleton 48 (.ldx .dword .r2 .r1 20736))).union
        (CodeReq.singleton 49 (.jne .r2 (.imm (1)) 63))).union
        (CodeReq.singleton 50 (.ldx .dword .r3 .r1 20744))).union
        (CodeReq.singleton 51 (.jeq .r3 (.imm (0)) 62))).union
        (CodeReq.singleton 62 (.mov64 .r0 (.imm (1)))))).union
        (CodeReq.singleton 63 .exit))
      (53 + 1) (0) 0
      (fun rt => ((((((((((((((((((((((((((rt.containsRange (effectiveAddr baseAddr 0) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 8) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 88) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10392) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10472) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20728) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 11) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10393) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20752) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 48) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20760) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 56) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20768) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 64) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20776) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 72) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10400) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 96) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10408) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 104) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10416) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 112) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10424) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 120) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20736) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20744) 8 = true)
      (toU64 1)
      [((baseAddr + 96),
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)],
        [(0, .pubkey ⟨owner0, owner1, owner2, owner3⟩), (32, .u64 total), (40, .byte bump)])]
      (((.r0 ↦ᵣ vR0Old) **
      (.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ vR2Old) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8) **
      (effectiveAddr baseAddr 10392 ↦ₘ m10296) **
      (effectiveAddr baseAddr 10472 ↦U64 m10376) **
      (effectiveAddr baseAddr 20728 ↦U64 m20632) **
      (effectiveAddr baseAddr 10 ↦ₘ mNeg86) **
      (effectiveAddr baseAddr 11 ↦ₘ mNeg85) **
      (effectiveAddr baseAddr 10393 ↦ₘ m10297) **
      (effectiveAddr baseAddr 20752 ↦U64 m20656) **
      (effectiveAddr baseAddr 48 ↦U64 mNeg48) **
      (.r3 ↦ᵣ vR3Old) **
      (effectiveAddr baseAddr 20760 ↦U64 m20664) **
      (effectiveAddr baseAddr 56 ↦U64 mNeg40) **
      (effectiveAddr baseAddr 20768 ↦U64 m20672) **
      (effectiveAddr baseAddr 64 ↦U64 mNeg32) **
      (effectiveAddr baseAddr 20776 ↦U64 m20680) **
      (effectiveAddr baseAddr 72 ↦U64 mNeg24) **
      (effectiveAddr baseAddr 10400 ↦U64 m10304) **
      (effectiveAddr baseAddr 10408 ↦U64 m10312) **
      (effectiveAddr baseAddr 10416 ↦U64 m10320) **
      (effectiveAddr baseAddr 10424 ↦U64 m10328) **
      (effectiveAddr baseAddr 20736 ↦U64 m20640) **
      (effectiveAddr baseAddr 20744 ↦U64 amount)) **
       callStackIs [])
      ((.r1 ↦ᵣ baseAddr) **
      (effectiveAddr baseAddr 0 ↦U64 mNeg96) **
      (.r2 ↦ᵣ m20640) **
      (effectiveAddr baseAddr 8 ↦ₘ mNeg88) **
      (effectiveAddr baseAddr 88 ↦U64 mNeg8) **
      (effectiveAddr baseAddr 10392 ↦ₘ m10296) **
      (effectiveAddr baseAddr 10472 ↦U64 m10376) **
      (effectiveAddr baseAddr 20728 ↦U64 m20632) **
      (effectiveAddr baseAddr 10 ↦ₘ mNeg86) **
      (effectiveAddr baseAddr 11 ↦ₘ mNeg85) **
      (effectiveAddr baseAddr 10393 ↦ₘ m10297) **
      (effectiveAddr baseAddr 20752 ↦U64 m20656) **
      (effectiveAddr baseAddr 48 ↦U64 mNeg48) **
      (.r3 ↦ᵣ amount) **
      (effectiveAddr baseAddr 20760 ↦U64 m20664) **
      (effectiveAddr baseAddr 56 ↦U64 mNeg40) **
      (effectiveAddr baseAddr 20768 ↦U64 m20672) **
      (effectiveAddr baseAddr 64 ↦U64 mNeg32) **
      (effectiveAddr baseAddr 20776 ↦U64 m20680) **
      (effectiveAddr baseAddr 72 ↦U64 mNeg24) **
      (effectiveAddr baseAddr 10400 ↦U64 m10304) **
      (effectiveAddr baseAddr 10408 ↦U64 m10312) **
      (effectiveAddr baseAddr 10416 ↦U64 m10320) **
      (effectiveAddr baseAddr 10424 ↦U64 m10328) **
      (effectiveAddr baseAddr 20736 ↦U64 m20640) **
      (effectiveAddr baseAddr 20744 ↦U64 amount))) :=
  ⟨fun hg0 hg1 hg2 hg3 =>
      Examples.Lifted.Sbpfv3VaultAuthorizedDuplicate.Sbpfv3VaultAuthorizedDuplicate_transition_path vR0Old baseAddr mNeg96 vR2Old mNeg88 mNeg8 m10296 hmNeg96_lt hmNeg8_lt hg0 hg1 hg2 hg3 owner0 owner1 owner2 owner3 total bump,
   fun hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 =>
      Examples.Lifted.Sbpfv3VaultAuthorizedExecutable.Sbpfv3VaultAuthorizedExecutable_transition_path vR0Old baseAddr mNeg96 vR2Old mNeg88 mNeg8 m10296 m10376 m20632 mNeg86 mNeg85 hmNeg96_lt hmNeg8_lt hm10376_lt hm20632_lt hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 owner0 owner1 owner2 owner3 total bump,
   fun hg0 hg1 hg2 hg3 hg4 hg5 =>
      Examples.Lifted.Sbpfv3VaultAuthorizedLongInstruction.Sbpfv3VaultAuthorizedLongInstruction_transition_path vR0Old baseAddr mNeg96 vR2Old mNeg88 mNeg8 m10296 m10376 m20632 hmNeg96_lt hmNeg8_lt hm10376_lt hm20632_lt hg0 hg1 hg2 hg3 hg4 hg5 owner0 owner1 owner2 owner3 total bump,
   fun hg0 =>
      Examples.Lifted.Sbpfv3VaultAuthorizedMissingAccount.Sbpfv3VaultAuthorizedMissingAccount_transition_path vR0Old baseAddr mNeg96 vR2Old hmNeg96_lt hg0 owner0 owner1 owner2 owner3 total bump,
   fun hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 =>
      Examples.Lifted.Sbpfv3VaultAuthorizedMissingSigner.Sbpfv3VaultAuthorizedMissingSigner_transition_path vR0Old baseAddr mNeg96 vR2Old mNeg88 mNeg8 m10296 m10376 m20632 mNeg86 mNeg85 m10297 hmNeg96_lt hmNeg8_lt hm10376_lt hm20632_lt hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 owner0 owner1 owner2 owner3 total bump,
   fun hg0 hg1 hg2 hg3 hg4 =>
      Examples.Lifted.Sbpfv3VaultAuthorizedNonemptyAuthority.Sbpfv3VaultAuthorizedNonemptyAuthority_transition_path vR0Old baseAddr mNeg96 vR2Old mNeg88 mNeg8 m10296 m10376 hmNeg96_lt hmNeg8_lt hm10376_lt hg0 hg1 hg2 hg3 hg4 owner0 owner1 owner2 owner3 total bump,
   fun hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 =>
      Examples.Lifted.Sbpfv3VaultAuthorizedOverflow.Sbpfv3VaultAuthorizedOverflow_transition_path vR0Old baseAddr mNeg96 vR2Old mNeg88 mNeg8 m10296 m10376 m20632 mNeg86 mNeg85 m10297 m20656 mNeg48 vR3Old m20664 mNeg40 m20672 mNeg32 m20680 mNeg24 m10304 owner0 m10312 owner1 m10320 owner2 m10328 owner3 m20640 amount total vR4Old hmNeg96_lt hmNeg8_lt hm10376_lt hm20632_lt hm20656_lt hmNeg48_lt hm20664_lt hmNeg40_lt hm20672_lt hmNeg32_lt hm20680_lt hmNeg24_lt hm10304_lt howner0_lt hm10312_lt howner1_lt hm10320_lt howner2_lt hm10328_lt howner3_lt hm20640_lt hamount_lt htotal_lt hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 bump,
   fun hg0 hg1 hg2 hg3 hg4 hg5 hg6 =>
      Examples.Lifted.Sbpfv3VaultAuthorizedReadonly.Sbpfv3VaultAuthorizedReadonly_transition_path vR0Old baseAddr mNeg96 vR2Old mNeg88 mNeg8 m10296 m10376 m20632 mNeg86 hmNeg96_lt hmNeg8_lt hm10376_lt hm20632_lt hg0 hg1 hg2 hg3 hg4 hg5 hg6 owner0 owner1 owner2 owner3 total bump,
   fun hg0 hg1 hg2 hg3 hg4 hg5 =>
      Examples.Lifted.Sbpfv3VaultAuthorizedShortInstruction.Sbpfv3VaultAuthorizedShortInstruction_transition_path vR0Old baseAddr mNeg96 vR2Old mNeg88 mNeg8 m10296 m10376 m20632 hmNeg96_lt hmNeg8_lt hm10376_lt hm20632_lt hg0 hg1 hg2 hg3 hg4 hg5 owner0 owner1 owner2 owner3 total bump,
   fun hg0 hg1 hg2 =>
      Examples.Lifted.Sbpfv3VaultAuthorizedShortVault.Sbpfv3VaultAuthorizedShortVault_transition_path vR0Old baseAddr mNeg96 vR2Old mNeg88 mNeg8 hmNeg96_lt hmNeg8_lt hg0 hg1 hg2 owner0 owner1 owner2 owner3 total bump,
   fun hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 =>
      Examples.Lifted.Sbpfv3VaultAuthorizedSuccess.Sbpfv3VaultAuthorizedSuccess_transition_path vR0Old baseAddr mNeg96 vR2Old mNeg88 mNeg8 m10296 m10376 m20632 mNeg86 mNeg85 m10297 m20656 mNeg48 vR3Old m20664 mNeg40 m20672 mNeg32 m20680 mNeg24 m10304 owner0 m10312 owner1 m10320 owner2 m10328 owner3 m20640 amount total vR4Old hmNeg96_lt hmNeg8_lt hm10376_lt hm20632_lt hm20656_lt hmNeg48_lt hm20664_lt hmNeg40_lt hm20672_lt hmNeg32_lt hm20680_lt hmNeg24_lt hm10304_lt howner0_lt hm10312_lt howner1_lt hm10320_lt howner2_lt hm10328_lt howner3_lt hm20640_lt hamount_lt htotal_lt hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 hg19 hg20 hg21 bump,
   fun hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 =>
      Examples.Lifted.Sbpfv3VaultAuthorizedUnknown.Sbpfv3VaultAuthorizedUnknown_transition_path vR0Old baseAddr mNeg96 vR2Old mNeg88 mNeg8 m10296 m10376 m20632 mNeg86 mNeg85 m10297 m20656 mNeg48 vR3Old m20664 mNeg40 m20672 mNeg32 m20680 mNeg24 m10304 owner0 m10312 owner1 m10320 owner2 m10328 owner3 m20640 hmNeg96_lt hmNeg8_lt hm10376_lt hm20632_lt hm20656_lt hmNeg48_lt hm20664_lt hmNeg40_lt hm20672_lt hmNeg32_lt hm20680_lt hmNeg24_lt hm10304_lt howner0_lt hm10312_lt howner1_lt hm10320_lt howner2_lt hm10328_lt howner3_lt hm20640_lt hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 total bump,
   fun hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 =>
      Examples.Lifted.Sbpfv3VaultAuthorizedWrongOwner0.Sbpfv3VaultAuthorizedWrongOwner0_transition_path vR0Old baseAddr mNeg96 vR2Old mNeg88 mNeg8 m10296 m10376 m20632 mNeg86 mNeg85 m10297 m20656 mNeg48 vR3Old m20664 mNeg40 m20672 mNeg32 m20680 mNeg24 m10304 owner0 hmNeg96_lt hmNeg8_lt hm10376_lt hm20632_lt hm20656_lt hmNeg48_lt hm20664_lt hmNeg40_lt hm20672_lt hmNeg32_lt hm20680_lt hmNeg24_lt hm10304_lt howner0_lt hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 owner1 owner2 owner3 total bump,
   fun hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 =>
      Examples.Lifted.Sbpfv3VaultAuthorizedWrongOwner1.Sbpfv3VaultAuthorizedWrongOwner1_transition_path vR0Old baseAddr mNeg96 vR2Old mNeg88 mNeg8 m10296 m10376 m20632 mNeg86 mNeg85 m10297 m20656 mNeg48 vR3Old m20664 mNeg40 m20672 mNeg32 m20680 mNeg24 m10304 owner0 m10312 owner1 hmNeg96_lt hmNeg8_lt hm10376_lt hm20632_lt hm20656_lt hmNeg48_lt hm20664_lt hmNeg40_lt hm20672_lt hmNeg32_lt hm20680_lt hmNeg24_lt hm10304_lt howner0_lt hm10312_lt howner1_lt hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 owner2 owner3 total bump,
   fun hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 =>
      Examples.Lifted.Sbpfv3VaultAuthorizedWrongOwner2.Sbpfv3VaultAuthorizedWrongOwner2_transition_path vR0Old baseAddr mNeg96 vR2Old mNeg88 mNeg8 m10296 m10376 m20632 mNeg86 mNeg85 m10297 m20656 mNeg48 vR3Old m20664 mNeg40 m20672 mNeg32 m20680 mNeg24 m10304 owner0 m10312 owner1 m10320 owner2 hmNeg96_lt hmNeg8_lt hm10376_lt hm20632_lt hm20656_lt hmNeg48_lt hm20664_lt hmNeg40_lt hm20672_lt hmNeg32_lt hm20680_lt hmNeg24_lt hm10304_lt howner0_lt hm10312_lt howner1_lt hm10320_lt howner2_lt hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 owner3 total bump,
   fun hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 =>
      Examples.Lifted.Sbpfv3VaultAuthorizedWrongOwner3.Sbpfv3VaultAuthorizedWrongOwner3_transition_path vR0Old baseAddr mNeg96 vR2Old mNeg88 mNeg8 m10296 m10376 m20632 mNeg86 mNeg85 m10297 m20656 mNeg48 vR3Old m20664 mNeg40 m20672 mNeg32 m20680 mNeg24 m10304 owner0 m10312 owner1 m10320 owner2 m10328 owner3 hmNeg96_lt hmNeg8_lt hm10376_lt hm20632_lt hm20656_lt hmNeg48_lt hm20664_lt hmNeg40_lt hm20672_lt hmNeg32_lt hm20680_lt hmNeg24_lt hm10304_lt howner0_lt hm10312_lt howner1_lt hm10320_lt howner2_lt hm10328_lt howner3_lt hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 total bump,
   fun hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 =>
      Examples.Lifted.Sbpfv3VaultAuthorizedWrongProgramOwner0.Sbpfv3VaultAuthorizedWrongProgramOwner0_transition_path vR0Old baseAddr mNeg96 vR2Old mNeg88 mNeg8 m10296 m10376 m20632 mNeg86 mNeg85 m10297 m20656 mNeg48 vR3Old hmNeg96_lt hmNeg8_lt hm10376_lt hm20632_lt hm20656_lt hmNeg48_lt hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 owner0 owner1 owner2 owner3 total bump,
   fun hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 =>
      Examples.Lifted.Sbpfv3VaultAuthorizedWrongProgramOwner1.Sbpfv3VaultAuthorizedWrongProgramOwner1_transition_path vR0Old baseAddr mNeg96 vR2Old mNeg88 mNeg8 m10296 m10376 m20632 mNeg86 mNeg85 m10297 m20656 mNeg48 vR3Old m20664 mNeg40 hmNeg96_lt hmNeg8_lt hm10376_lt hm20632_lt hm20656_lt hmNeg48_lt hm20664_lt hmNeg40_lt hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 owner0 owner1 owner2 owner3 total bump,
   fun hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 =>
      Examples.Lifted.Sbpfv3VaultAuthorizedWrongProgramOwner2.Sbpfv3VaultAuthorizedWrongProgramOwner2_transition_path vR0Old baseAddr mNeg96 vR2Old mNeg88 mNeg8 m10296 m10376 m20632 mNeg86 mNeg85 m10297 m20656 mNeg48 vR3Old m20664 mNeg40 m20672 mNeg32 hmNeg96_lt hmNeg8_lt hm10376_lt hm20632_lt hm20656_lt hmNeg48_lt hm20664_lt hmNeg40_lt hm20672_lt hmNeg32_lt hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 owner0 owner1 owner2 owner3 total bump,
   fun hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 =>
      Examples.Lifted.Sbpfv3VaultAuthorizedWrongProgramOwner3.Sbpfv3VaultAuthorizedWrongProgramOwner3_transition_path vR0Old baseAddr mNeg96 vR2Old mNeg88 mNeg8 m10296 m10376 m20632 mNeg86 mNeg85 m10297 m20656 mNeg48 vR3Old m20664 mNeg40 m20672 mNeg32 m20680 mNeg24 hmNeg96_lt hmNeg8_lt hm10376_lt hm20632_lt hm20656_lt hmNeg48_lt hm20664_lt hmNeg40_lt hm20672_lt hmNeg32_lt hm20680_lt hmNeg24_lt hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 owner0 owner1 owner2 owner3 total bump,
   fun hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 =>
      Examples.Lifted.Sbpfv3VaultAuthorizedZero.Sbpfv3VaultAuthorizedZero_transition_path vR0Old baseAddr mNeg96 vR2Old mNeg88 mNeg8 m10296 m10376 m20632 mNeg86 mNeg85 m10297 m20656 mNeg48 vR3Old m20664 mNeg40 m20672 mNeg32 m20680 mNeg24 m10304 owner0 m10312 owner1 m10320 owner2 m10328 owner3 m20640 amount hmNeg96_lt hmNeg8_lt hm10376_lt hm20632_lt hm20656_lt hmNeg48_lt hm20664_lt hmNeg40_lt hm20672_lt hmNeg32_lt hm20680_lt hmNeg24_lt hm10304_lt howner0_lt hm10312_lt howner1_lt hm10320_lt howner2_lt hm10328_lt howner3_lt hm20640_lt hamount_lt hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg11 hg12 hg13 hg14 hg15 hg16 hg17 hg18 total bump⟩

end Examples.Sbpfv3VaultAuthorizedTransition
