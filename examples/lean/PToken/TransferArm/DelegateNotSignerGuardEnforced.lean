/-
  Pattern library Layer 3 — the SIGNER guard, delegate leg (authority
  tri-case 2/3, sibling of `OwnerNotSignerGuardEnforced.lean`).

  From a pre where the authority equals the account's DELEGATE (not the
  owner) but is not a signer, the lifted error path runs through the
  delegate branch of the owner validation to the shared exit with
  r0 = 34359738368 (ProgramError::MissingRequiredSignature), token cells
  untouched.
-/

import Generated.PTokenTransferDelegateNotSignerLifted
import Lean
import SVM.Solana.Patterns.Guards

namespace Examples.PTokenDelegateNotSignerGuardEnforced

open SVM.SBPF
open Memory
open Examples.Lifted.PTokenTransferDelegateNotSigner

set_option maxHeartbeats 1600000 in
/-- From a non-signing authority that matches the account's delegate, the
    real p-token Transfer HALTS with `exitCode = some (8 <<< 32)`
    (ProgramError::MissingRequiredSignature) — the signer check is ENFORCED
    on the delegate leg too. -/
theorem p_token_delegate_not_signer_enforced
    (baseAddr oldMemB_0 vR2Old oldMemD_1 oldMemB_2 oldMemD_3 oldMemB_4 oldMemD_5 vR4Old vR3Old oldMemD_6 oldMemB_7 vR6Old vR7Old oldMemB_8 oldMemB_9 vR5Old oldMemD_10 oldMemD_11 oldMemD_12 oldMemD_13 vR0Old oldMemD_14 oldMemD_15 oldMemD_16 oldMemD_17 oldMemD_18 oldMemD_19 oldMemD_20 oldMemB_21 oldMemD_22 oldMemD_23 oldMemD_24 vR8Old oldMemD_25 oldMemD_26 oldMemD_27 oldMemD_28 oldMemB_29 vR9Old vR10Old : Nat)
    (addr0 : Nat)
    (h_addr0 : addr0 = wrapAdd baseAddr (((wrapAdd oldMemD_5 (toU64 7)) &&& toU64 (-8)) % U64_MODULUS))
    (holdMemD_1_lt : oldMemD_1 < 2 ^ 64)
    (holdMemD_3_lt : oldMemD_3 < 2 ^ 64)
    (holdMemD_5_lt : oldMemD_5 < 2 ^ 64)
    (holdMemD_6_lt : oldMemD_6 < 2 ^ 64)
    (holdMemD_10_lt : oldMemD_10 < 2 ^ 64)
    (holdMemD_11_lt : oldMemD_11 < 2 ^ 64)
    (holdMemD_12_lt : oldMemD_12 < 2 ^ 64)
    (holdMemD_13_lt : oldMemD_13 < 2 ^ 64)
    (holdMemD_14_lt : oldMemD_14 < 2 ^ 64)
    (holdMemD_15_lt : oldMemD_15 < 2 ^ 64)
    (holdMemD_16_lt : oldMemD_16 < 2 ^ 64)
    (holdMemD_17_lt : oldMemD_17 < 2 ^ 64)
    (holdMemD_18_lt : oldMemD_18 < 2 ^ 64)
    (holdMemD_19_lt : oldMemD_19 < 2 ^ 64)
    (holdMemD_20_lt : oldMemD_20 < 2 ^ 64)
    (holdMemD_22_lt : oldMemD_22 < 2 ^ 64)
    (holdMemD_23_lt : oldMemD_23 < 2 ^ 64)
    (holdMemD_24_lt : oldMemD_24 < 2 ^ 64)
    (holdMemD_25_lt : oldMemD_25 < 2 ^ 64)
    (holdMemD_26_lt : oldMemD_26 < 2 ^ 64)
    (holdMemD_27_lt : oldMemD_27 < 2 ^ 64)
    (holdMemD_28_lt : oldMemD_28 < 2 ^ 64)
    (h_branch0 : oldMemB_0 % 256 = toU64 3)
    (h_branch1 : oldMemD_1 = toU64 165)
    (h_branch2 : oldMemB_2 % 256 = toU64 255)
    (h_branch3 : oldMemD_3 = toU64 165)
    (h_branch4 : oldMemB_4 % 256 = toU64 255)
    (h_branch5 : ¬ oldMemD_6 < toU64 9)
    (h_branch6 : oldMemB_7 % 256 = toU64 3)
    (h_branch7 : ¬ oldMemB_8 % 256 > toU64 2)
    (h_branch8 : oldMemB_8 % 256 ≠ toU64 0)
    (h_branch9 : ¬ oldMemB_9 % 256 > toU64 2)
    (h_branch10 : oldMemB_9 % 256 ≠ toU64 0)
    (h_branch11 : oldMemB_8 % 256 ≠ toU64 2)
    (h_branch12 : oldMemB_9 % 256 ≠ toU64 2)
    (h_branch13 : ¬ oldMemD_11 < oldMemD_10)
    (h_branch14 : oldMemD_13 = oldMemD_12)
    (h_branch15 : oldMemD_15 = oldMemD_14)
    (h_branch16 : oldMemD_17 = oldMemD_16)
    (h_branch17 : oldMemD_19 = oldMemD_18)
    (h_branch18 : oldMemB_21 % 256 = toU64 1)
    (h_branch19 : oldMemD_22 = oldMemD_20)
    (h_branch20 : oldMemD_24 = oldMemD_23)
    (h_branch21 : oldMemD_26 = oldMemD_25)
    (h_branch22 : oldMemD_28 = oldMemD_27)
    (h_branch23 : oldMemD_5 ≠ toU64 355)
    (h_branch24 : oldMemB_29 % 256 = toU64 0)
    (h_branch25 : ¬ toSigned64 ((((toU64 7) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) > toSigned64 (toU64 12))
    (h_branch26 : ¬ toSigned64 ((((toU64 7) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) ≤ toSigned64 (toU64 5))
    (h_branch27 : toSigned64 ((((toU64 7) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) ≤ toSigned64 (toU64 8))
    (h_branch28 : (((toU64 7) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64) ≠ toU64 6)
    (h_branch29 : (((toU64 7) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64) = toU64 7)
    (h_branch30 : ¬ toSigned64 ((((toU64 7) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) > toSigned64 (toU64 12))
    (h_branch31 : ¬ toSigned64 ((((toU64 7) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) ≤ toSigned64 (toU64 5))
    (h_branch32 : toSigned64 ((((toU64 7) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) ≤ toSigned64 (toU64 8))
    (h_branch33 : (((toU64 7) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64) ≠ toU64 6)
    (h_branch34 : (((toU64 7) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64) = toU64 7)
    (nCuLog30 : Nat)
    (hCuLog30 : ∀ s : State, (step (.call .sol_log_) s).cuConsumed ≤ s.cuConsumed + nCuLog30)
    : SVM.Solana.Patterns.EnforcedError (97 + 1) nCuLog30 198
      (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((CodeReq.singleton 198 (.ldx .byte .r2 .r1 0)).union
        (CodeReq.singleton 199 (.jeq .r2 (.imm (3)) 304))).union
        (CodeReq.singleton 304 (.ldx .dword .r2 .r1 88))).union
        (CodeReq.singleton 305 (.jne .r2 (.imm (165)) 312))).union
        (CodeReq.singleton 306 (.ldx .byte .r2 .r1 10512))).union
        (CodeReq.singleton 307 (.jne .r2 (.imm (255)) 312))).union
        (CodeReq.singleton 308 (.ldx .dword .r2 .r1 10592))).union
        (CodeReq.singleton 309 (.jne .r2 (.imm (165)) 312))).union
        (CodeReq.singleton 310 (.ldx .byte .r2 .r1 21016))).union
        (CodeReq.singleton 311 (.jeq .r2 (.imm (255)) 3991))).union
        (CodeReq.singleton 3991 (.ldx .dword .r4 .r1 21096))).union
        (CodeReq.singleton 3992 (.mov64 .r3 (.reg .r4)))).union
        (CodeReq.singleton 3993 (.add64 .r3 (.imm (7))))).union
        (CodeReq.singleton 3994 (.and64 .r3 (.imm (-8))))).union
        (CodeReq.singleton 3995 (.mov64 .r2 (.reg .r1)))).union
        (CodeReq.singleton 3996 (.add64 .r2 (.reg .r3)))).union
        (CodeReq.singleton 3997 (.ldx .dword .r3 .r2 31352))).union
        (CodeReq.singleton 3998 (.jlt .r3 (.imm (9)) 312))).union
        (CodeReq.singleton 3999 (.ldx .byte .r3 .r2 31360))).union
        (CodeReq.singleton 4000 (.jne .r3 (.imm (3)) 312))).union
        (CodeReq.singleton 4001 (.mov64 .r6 (.imm (3))))).union
        (CodeReq.singleton 4002 (.mov64 .r7 (.imm (0))))).union
        (CodeReq.singleton 4003 (.ldx .byte .r3 .r1 204))).union
        (CodeReq.singleton 4004 (.jgt .r3 (.imm (2)) 4725))).union
        (CodeReq.singleton 4005 (.jeq .r3 (.imm (0)) 5080))).union
        (CodeReq.singleton 4006 (.ldx .byte .r5 .r1 10708))).union
        (CodeReq.singleton 4007 (.jgt .r5 (.imm (2)) 4725))).union
        (CodeReq.singleton 4008 (.jeq .r5 (.imm (0)) 5080))).union
        (CodeReq.singleton 4009 (.mov64 .r6 (.imm (0))))).union
        (CodeReq.singleton 4010 (.mov64 .r7 (.imm (17))))).union
        (CodeReq.singleton 4011 (.jeq .r3 (.imm (2)) 4725))).union
        (CodeReq.singleton 4012 (.jeq .r5 (.imm (2)) 4725))).union
        (CodeReq.singleton 4013 (.ldx .dword .r2 .r2 31361))).union
        (CodeReq.singleton 4014 (.mov64 .r7 (.imm (1))))).union
        (CodeReq.singleton 4015 (.ldx .dword .r3 .r1 160))).union
        (CodeReq.singleton 4016 (.jlt .r3 (.reg .r2) 4725))).union
        (CodeReq.singleton 4017 (.ldx .dword .r5 .r1 10600))).union
        (CodeReq.singleton 4018 (.ldx .dword .r0 .r1 96))).union
        (CodeReq.singleton 4019 (.jne .r0 (.reg .r5) 4724))).union
        (CodeReq.singleton 4020 (.ldx .dword .r5 .r1 10608))).union
        (CodeReq.singleton 4021 (.ldx .dword .r0 .r1 104))).union
        (CodeReq.singleton 4022 (.jne .r0 (.reg .r5) 4724))).union
        (CodeReq.singleton 4023 (.ldx .dword .r5 .r1 10616))).union
        (CodeReq.singleton 4024 (.ldx .dword .r0 .r1 112))).union
        (CodeReq.singleton 4025 (.jne .r0 (.reg .r5) 4724))).union
        (CodeReq.singleton 4026 (.ldx .dword .r5 .r1 10624))).union
        (CodeReq.singleton 4027 (.ldx .dword .r0 .r1 120))).union
        (CodeReq.singleton 4028 (.jne .r0 (.reg .r5) 4724))).union
        (CodeReq.singleton 4029 (.ldx .dword .r5 .r1 21024))).union
        (CodeReq.singleton 4030 (.ldx .byte .r0 .r1 168))).union
        (CodeReq.singleton 4031 (.jne .r0 (.imm (1)) 4457))).union
        (CodeReq.singleton 4032 (.ldx .dword .r0 .r1 172))).union
        (CodeReq.singleton 4033 (.jne .r0 (.reg .r5) 4457))).union
        (CodeReq.singleton 4034 (.ldx .dword .r0 .r1 21032))).union
        (CodeReq.singleton 4035 (.ldx .dword .r8 .r1 180))).union
        (CodeReq.singleton 4036 (.jne .r8 (.reg .r0) 4457))).union
        (CodeReq.singleton 4037 (.ldx .dword .r0 .r1 21040))).union
        (CodeReq.singleton 4038 (.ldx .dword .r8 .r1 188))).union
        (CodeReq.singleton 4039 (.jne .r8 (.reg .r0) 4457))).union
        (CodeReq.singleton 4040 (.ldx .dword .r0 .r1 21048))).union
        (CodeReq.singleton 4041 (.ldx .dword .r8 .r1 196))).union
        (CodeReq.singleton 4042 (.jne .r8 (.reg .r0) 4457))).union
        (CodeReq.singleton 4043 (.jne .r4 (.imm (355)) 5215))).union
        (CodeReq.singleton 5215 (.ldx .byte .r4 .r1 21017))).union
        (CodeReq.singleton 5216 (.jeq .r4 (.imm (0)) 5716))).union
        (CodeReq.singleton 5716 (.mov64 .r6 (.imm (7))))).union
        (CodeReq.singleton 5717 (.ja 4725))).union
        (CodeReq.singleton 4725 (.mov64 .r1 (.reg .r6)))).union
        (CodeReq.singleton 4726 (.mov64 .r2 (.reg .r7)))).union
        (CodeReq.singleton 4727 (.call_local 6864))).union
        (CodeReq.singleton 6864 (.lsh64 .r1 (.imm (32))))).union
        (CodeReq.singleton 6865 (.rsh64 .r1 (.imm (32))))).union
        (CodeReq.singleton 6866 (.jsgt .r1 (.imm (12)) 6874))).union
        (CodeReq.singleton 6867 (.jsle .r1 (.imm (5)) 6881))).union
        (CodeReq.singleton 6868 (.jsle .r1 (.imm (8)) 6893))).union
        (CodeReq.singleton 6893 (.jeq .r1 (.imm (6)) 6921))).union
        (CodeReq.singleton 6894 (.jne .r1 (.imm (7)) 6942))).union
        (CodeReq.singleton 6895 (.lddw .r1 (4295070547)))).union
        (CodeReq.singleton 6896 (.mov64 .r2 (.imm (31))))).union
        (CodeReq.singleton 6897 (.ja 6988))).union
        (CodeReq.singleton 6988 (.call .sol_log_))).union
        (CodeReq.singleton 6989 (.exit))).union
        (CodeReq.singleton 4728 (.mov64 .r1 (.reg .r6)))).union
        (CodeReq.singleton 4729 (.mov64 .r2 (.reg .r7)))).union
        (CodeReq.singleton 4730 (.ja 3541))).union
        (CodeReq.singleton 3541 (.call_local 116))).union
        (CodeReq.singleton 116 (.mov64 .r0 (.reg .r2)))).union
        (CodeReq.singleton 117 (.lsh64 .r1 (.imm (32))))).union
        (CodeReq.singleton 118 (.rsh64 .r1 (.imm (32))))).union
        (CodeReq.singleton 119 (.jsgt .r1 (.imm (12)) 126))).union
        (CodeReq.singleton 120 (.jsle .r1 (.imm (5)) 132))).union
        (CodeReq.singleton 121 (.jsle .r1 (.imm (8)) 143))).union
        (CodeReq.singleton 143 (.jeq .r1 (.imm (6)) 165))).union
        (CodeReq.singleton 144 (.jne .r1 (.imm (7)) 180))).union
        (CodeReq.singleton 145 (.lddw .r0 (34359738368)))).union
        (CodeReq.singleton 146 (.ja 197))).union
        (CodeReq.singleton 197 (.exit)))).union
        (CodeReq.singleton 3542 .exit))
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
      (effectiveAddr baseAddr 172 ↦U64 oldMemD_22) **
      (effectiveAddr baseAddr 21032 ↦U64 oldMemD_23) **
      (effectiveAddr baseAddr 180 ↦U64 oldMemD_24) **
      (.r8 ↦ᵣ vR8Old) **
      (effectiveAddr baseAddr 21040 ↦U64 oldMemD_25) **
      (effectiveAddr baseAddr 188 ↦U64 oldMemD_26) **
      (effectiveAddr baseAddr 21048 ↦U64 oldMemD_27) **
      (effectiveAddr baseAddr 196 ↦U64 oldMemD_28) **
      (effectiveAddr baseAddr 21017 ↦ₘ oldMemB_29) **
      (.r9 ↦ᵣ vR9Old) **
      (.r10 ↦ᵣ vR10Old) ** callStackIs [])
      ((.r0 ↦ᵣ 34359738368) ** callStackIs [] **
      (.r1 ↦ᵣ (((toU64 7) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) **
      (effectiveAddr baseAddr 0 ↦ₘ oldMemB_0) **
      (.r2 ↦ᵣ toU64 1) **
      (effectiveAddr baseAddr 88 ↦U64 oldMemD_1) **
      (effectiveAddr baseAddr 10512 ↦ₘ oldMemB_2) **
      (effectiveAddr baseAddr 10592 ↦U64 oldMemD_3) **
      (effectiveAddr baseAddr 21016 ↦ₘ oldMemB_4) **
      (effectiveAddr baseAddr 21096 ↦U64 oldMemD_5) **
      (.r4 ↦ᵣ oldMemB_29 % 256) **
      (.r3 ↦ᵣ oldMemD_11) **
      (effectiveAddr addr0 31352 ↦U64 oldMemD_6) **
      (effectiveAddr addr0 31360 ↦ₘ oldMemB_7) **
      (.r6 ↦ᵣ toU64 7) **
      (.r7 ↦ᵣ toU64 1) **
      (effectiveAddr baseAddr 204 ↦ₘ oldMemB_8) **
      (effectiveAddr baseAddr 10708 ↦ₘ oldMemB_9) **
      (.r5 ↦ᵣ oldMemD_20) **
      (effectiveAddr addr0 31361 ↦U64 oldMemD_10) **
      (effectiveAddr baseAddr 160 ↦U64 oldMemD_11) **
      (effectiveAddr baseAddr 10600 ↦U64 oldMemD_12) **
      (effectiveAddr baseAddr 96 ↦U64 oldMemD_13) **
      (effectiveAddr baseAddr 10608 ↦U64 oldMemD_14) **
      (effectiveAddr baseAddr 104 ↦U64 oldMemD_15) **
      (effectiveAddr baseAddr 10616 ↦U64 oldMemD_16) **
      (effectiveAddr baseAddr 112 ↦U64 oldMemD_17) **
      (effectiveAddr baseAddr 10624 ↦U64 oldMemD_18) **
      (effectiveAddr baseAddr 120 ↦U64 oldMemD_19) **
      (effectiveAddr baseAddr 21024 ↦U64 oldMemD_20) **
      (effectiveAddr baseAddr 168 ↦ₘ oldMemB_21) **
      (effectiveAddr baseAddr 172 ↦U64 oldMemD_22) **
      (effectiveAddr baseAddr 21032 ↦U64 oldMemD_23) **
      (effectiveAddr baseAddr 180 ↦U64 oldMemD_24) **
      (.r8 ↦ᵣ oldMemD_28) **
      (effectiveAddr baseAddr 21040 ↦U64 oldMemD_25) **
      (effectiveAddr baseAddr 188 ↦U64 oldMemD_26) **
      (effectiveAddr baseAddr 21048 ↦U64 oldMemD_27) **
      (effectiveAddr baseAddr 196 ↦U64 oldMemD_28) **
      (effectiveAddr baseAddr 21017 ↦ₘ oldMemB_29) **
      (.r9 ↦ᵣ vR9Old) **
      (.r10 ↦ᵣ vR10Old))
      (fun rt => ((((((((((((((((((((((((((((((rt.containsRange (effectiveAddr baseAddr 0) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 88) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10512) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10592) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 21016) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 21096) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr0 31352) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr0 31360) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 204) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10708) 1 = true) ∧
                  rt.containsRange (effectiveAddr addr0 31361) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 160) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10600) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 96) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10608) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 104) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10616) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 112) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10624) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 120) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 21024) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 168) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 172) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 21032) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 180) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 21040) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 188) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 21048) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 196) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 21017) 1 = true) ∧
                  rt.containsRange (toU64 4295070547) (toU64 31) = true)
      34359738368 := by
  refine ⟨by decide, ?_⟩
  have h := PTokenTransferDelegateNotSigner_lifted_spec baseAddr oldMemB_0 vR2Old oldMemD_1 oldMemB_2 oldMemD_3 oldMemB_4 oldMemD_5 vR4Old vR3Old oldMemD_6 oldMemB_7 vR6Old vR7Old oldMemB_8 oldMemB_9 vR5Old oldMemD_10 oldMemD_11 oldMemD_12 oldMemD_13 vR0Old oldMemD_14 oldMemD_15 oldMemD_16 oldMemD_17 oldMemD_18 oldMemD_19 oldMemD_20 oldMemB_21 oldMemD_22 oldMemD_23 oldMemD_24 vR8Old oldMemD_25 oldMemD_26 oldMemD_27 oldMemD_28 oldMemB_29 vR9Old vR10Old addr0 h_addr0 holdMemD_1_lt holdMemD_3_lt holdMemD_5_lt holdMemD_6_lt holdMemD_10_lt holdMemD_11_lt holdMemD_12_lt holdMemD_13_lt holdMemD_14_lt holdMemD_15_lt holdMemD_16_lt holdMemD_17_lt holdMemD_18_lt holdMemD_19_lt holdMemD_20_lt holdMemD_22_lt holdMemD_23_lt holdMemD_24_lt holdMemD_25_lt holdMemD_26_lt holdMemD_27_lt holdMemD_28_lt h_branch0 h_branch1 h_branch2 h_branch3 h_branch4 h_branch5 h_branch6 h_branch7 h_branch8 h_branch9 h_branch10 h_branch11 h_branch12 h_branch13 h_branch14 h_branch15 h_branch16 h_branch17 h_branch18 h_branch19 h_branch20 h_branch21 h_branch22 h_branch23 h_branch24 h_branch25 h_branch26 h_branch27 h_branch28 h_branch29 h_branch30 h_branch31 h_branch32 h_branch33 h_branch34 nCuLog30 hCuLog30
  rw [show toU64 34359738368 = 34359738368 from by decide] at h
  refine cuTripleWithinMem_seq_exit ?_ ?_
  · repeat' apply CodeReq.Disjoint_union_left
    all_goals exact CodeReq.singleton_disjoint_singleton _ _ (by decide)
  · sl_exact h


/-! ## Axiom gate

`AxiomAudit` cannot import this module (its dylib mix re-triggers the
poisoned-dylib segfault — see the ExamplesCpi lakefile note), so the
standard-axiom assertion lives here, mirroring `#assert_std_axioms`. -/

open Lean Elab Command in
elab "#assert_std_axioms_local " id:ident : command => do
  let cName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axs ← liftCoreM <| collectAxioms cName
  let bad := axs.filter (fun a =>
    !([``propext, ``Classical.choice, ``Quot.sound].contains a))
  unless bad.isEmpty do
    throwError "AXIOM AUDIT FAILED: '{cName}' depends on non-standard \
                axioms: {bad.toList}"

#assert_std_axioms_local Examples.Lifted.PTokenTransferDelegateNotSigner.PTokenTransferDelegateNotSigner_lifted_spec
#assert_std_axioms_local Examples.PTokenDelegateNotSignerGuardEnforced.p_token_delegate_not_signer_enforced

end Examples.PTokenDelegateNotSignerGuardEnforced
