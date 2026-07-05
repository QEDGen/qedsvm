/-
  Pattern library Layer 3 — the OWNER guard (authority tri-case 3/3): an
  authority that is NEITHER the token owner NOR the delegate fails even
  when properly signing. This is the canonical most-skipped check of the
  Solana exploit landscape, stated against the real binary.

  From a pre where the (signing) authority key matches neither the
  account's owner nor its delegate, the lifted error path runs to the
  shared exit with r0 = 4 (TokenError::OwnerMismatch), token cells
  untouched.
-/

import Generated.PTokenTransferOwnerMismatchLifted
import Lean
import SVM.Solana.Patterns.Guards

namespace Examples.PTokenOwnerMismatchGuardEnforced

open SVM.SBPF
open Memory
open Examples.Lifted.PTokenTransferOwnerMismatch

set_option maxHeartbeats 1600000 in
/-- From a signing authority that is neither the token owner nor the
    delegate, the real p-token Transfer HALTS with `exitCode = some 4`
    (TokenError::OwnerMismatch) — the authority check is ENFORCED. -/
theorem p_token_owner_mismatch_enforced
    (baseAddr oldMemB_0 vR2Old oldMemD_1 oldMemB_2 oldMemD_3 oldMemB_4 oldMemD_5 vR4Old vR3Old oldMemD_6 oldMemB_7 vR6Old vR7Old oldMemB_8 oldMemB_9 vR5Old oldMemD_10 oldMemD_11 oldMemD_12 oldMemD_13 vR0Old oldMemD_14 oldMemD_15 oldMemD_16 oldMemD_17 oldMemD_18 oldMemD_19 oldMemD_20 oldMemB_21 oldMemD_22 vR8Old vR9Old vR10Old oldMemD_23 oldMemD_24 : Nat)
    (addr0 : Nat)
    (addr1 : Nat)
    (addr2 : Nat)
    (h_addr0 : addr0 = wrapAdd baseAddr (((wrapAdd oldMemD_5 (toU64 7)) &&& toU64 (-8)) % U64_MODULUS))
    (h_addr1 : addr1 = wrapAdd (toU64 4295072816) ((((let shift := toU64 56 % 64; if (((((((toU64 4) <<< (toU64 32 % 64)) % U64_MODULUS) ||| toU64 26) % U64_MODULUS) <<< (toU64 24 % 64)) % U64_MODULUS) < U64_MODULUS / 2 then (((((((toU64 4) <<< (toU64 32 % 64)) % U64_MODULUS) ||| toU64 26) % U64_MODULUS) <<< (toU64 24 % 64)) % U64_MODULUS) >>> shift else (let shifted := (((((((toU64 4) <<< (toU64 32 % 64)) % U64_MODULUS) ||| toU64 26) % U64_MODULUS) <<< (toU64 24 % 64)) % U64_MODULUS) >>> shift; let highBits := (U64_MODULUS - 1) - (U64_MODULUS / (2 ^ shift) - 1); (shifted ||| highBits) % U64_MODULUS))) <<< (toU64 3 % 64)) % U64_MODULUS))
    (h_addr2 : addr2 = wrapAdd (toU64 4295071984) ((((let shift := toU64 56 % 64; if (((((((toU64 4) <<< (toU64 32 % 64)) % U64_MODULUS) ||| toU64 26) % U64_MODULUS) <<< (toU64 24 % 64)) % U64_MODULUS) < U64_MODULUS / 2 then (((((((toU64 4) <<< (toU64 32 % 64)) % U64_MODULUS) ||| toU64 26) % U64_MODULUS) <<< (toU64 24 % 64)) % U64_MODULUS) >>> shift else (let shifted := (((((((toU64 4) <<< (toU64 32 % 64)) % U64_MODULUS) ||| toU64 26) % U64_MODULUS) <<< (toU64 24 % 64)) % U64_MODULUS) >>> shift; let highBits := (U64_MODULUS - 1) - (U64_MODULUS / (2 ^ shift) - 1); (shifted ||| highBits) % U64_MODULUS))) <<< (toU64 3 % 64)) % U64_MODULUS))
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
    (h_branch18 : oldMemB_21 % 256 ≠ toU64 1)
    (h_branch19 : oldMemD_22 ≠ oldMemD_20)
    (h_branch20 : ¬ toSigned64 ((((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) > toSigned64 (toU64 12))
    (h_branch21 : toSigned64 ((((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) ≤ toSigned64 (toU64 5))
    (h_branch22 : ¬ toSigned64 ((((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) > toSigned64 (toU64 2))
    (h_branch23 : (((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64) = toU64 0)
    (h_branch24 : (((toU64 4) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64) < toU64 20)
    (h_branch25 : ((((((toU64 4) <<< (toU64 32 % 64)) % U64_MODULUS) ||| toU64 26) % U64_MODULUS) &&& toU64 27) % U64_MODULUS = toU64 26)
    (h_branch26 : ¬ toSigned64 ((((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) > toSigned64 (toU64 12))
    (h_branch27 : toSigned64 ((((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) ≤ toSigned64 (toU64 5))
    (h_branch28 : ¬ toSigned64 ((((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) > toSigned64 (toU64 2))
    (h_branch29 : (((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64) = toU64 0)
    (h_branch30 : (((toU64 4) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64) ≠ toU64 0)
    (nCuLog25 : Nat)
    (hCuLog25 : ∀ s : State, (step (.call .sol_log_) s).cuConsumed ≤ s.cuConsumed + nCuLog25)
    : SVM.Solana.Patterns.EnforcedError (98 + 1) nCuLog25 198
      ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((CodeReq.singleton 198 (.ldx .byte .r2 .r1 0)).union
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
        (CodeReq.singleton 4457 (.mov64 .r7 (.imm (4))))).union
        (CodeReq.singleton 4458 (.ldx .dword .r0 .r1 128))).union
        (CodeReq.singleton 4459 (.jne .r0 (.reg .r5) 4725))).union
        (CodeReq.singleton 4725 (.mov64 .r1 (.reg .r6)))).union
        (CodeReq.singleton 4726 (.mov64 .r2 (.reg .r7)))).union
        (CodeReq.singleton 4727 (.call_local 6864))).union
        (CodeReq.singleton 6864 (.lsh64 .r1 (.imm (32))))).union
        (CodeReq.singleton 6865 (.rsh64 .r1 (.imm (32))))).union
        (CodeReq.singleton 6866 (.jsgt .r1 (.imm (12)) 6874))).union
        (CodeReq.singleton 6867 (.jsle .r1 (.imm (5)) 6881))).union
        (CodeReq.singleton 6881 (.jsgt .r1 (.imm (2)) 6903))).union
        (CodeReq.singleton 6882 (.jeq .r1 (.imm (0)) 6927))).union
        (CodeReq.singleton 6927 (.lsh64 .r2 (.imm (32))))).union
        (CodeReq.singleton 6928 (.mov64 .r1 (.reg .r2)))).union
        (CodeReq.singleton 6929 (.rsh64 .r1 (.imm (32))))).union
        (CodeReq.singleton 6930 (.jlt .r1 (.imm (20)) 6972))).union
        (CodeReq.singleton 6972 (.or64 .r2 (.imm (26))))).union
        (CodeReq.singleton 6973 (.mov64 .r1 (.reg .r2)))).union
        (CodeReq.singleton 6974 (.and64 .r1 (.imm (27))))).union
        (CodeReq.singleton 6975 (.jne .r1 (.imm (26)) 6986))).union
        (CodeReq.singleton 6976 (.lsh64 .r2 (.imm (24))))).union
        (CodeReq.singleton 6977 (.arsh64 .r2 (.imm (56))))).union
        (CodeReq.singleton 6978 (.lsh64 .r2 (.imm (3))))).union
        (CodeReq.singleton 6979 (.lddw .r3 (4295071984)))).union
        (CodeReq.singleton 6980 (.add64 .r3 (.reg .r2)))).union
        (CodeReq.singleton 6981 (.lddw .r1 (4295072816)))).union
        (CodeReq.singleton 6982 (.add64 .r1 (.reg .r2)))).union
        (CodeReq.singleton 6983 (.ldx .dword .r1 .r1 0))).union
        (CodeReq.singleton 6984 (.ldx .dword .r2 .r3 0))).union
        (CodeReq.singleton 6985 (.ja 6988))).union
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
        (CodeReq.singleton 132 (.jsgt .r1 (.imm (2)) 151))).union
        (CodeReq.singleton 133 (.jeq .r1 (.imm (0)) 169))).union
        (CodeReq.singleton 169 (.lsh64 .r0 (.imm (32))))).union
        (CodeReq.singleton 170 (.rsh64 .r0 (.imm (32))))).union
        (CodeReq.singleton 171 (.jne .r0 (.imm (0)) 197))).union
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
      (effectiveAddr baseAddr 128 ↦U64 oldMemD_22) **
      (.r8 ↦ᵣ vR8Old) **
      (.r9 ↦ᵣ vR9Old) **
      (.r10 ↦ᵣ vR10Old) **
      (effectiveAddr addr1 0 ↦U64 oldMemD_23) **
      (effectiveAddr addr2 0 ↦U64 oldMemD_24) ** callStackIs [])
      ((.r0 ↦ᵣ 4) ** callStackIs [] **
      (.r1 ↦ᵣ 0) **
      (effectiveAddr baseAddr 0 ↦ₘ oldMemB_0) **
      (.r2 ↦ᵣ toU64 4) **
      (effectiveAddr baseAddr 88 ↦U64 oldMemD_1) **
      (effectiveAddr baseAddr 10512 ↦ₘ oldMemB_2) **
      (effectiveAddr baseAddr 10592 ↦U64 oldMemD_3) **
      (effectiveAddr baseAddr 21016 ↦ₘ oldMemB_4) **
      (effectiveAddr baseAddr 21096 ↦U64 oldMemD_5) **
      (.r4 ↦ᵣ oldMemD_5) **
      (.r3 ↦ᵣ addr2) **
      (effectiveAddr addr0 31352 ↦U64 oldMemD_6) **
      (effectiveAddr addr0 31360 ↦ₘ oldMemB_7) **
      (.r6 ↦ᵣ toU64 0) **
      (.r7 ↦ᵣ toU64 4) **
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
      (effectiveAddr baseAddr 128 ↦U64 oldMemD_22) **
      (.r8 ↦ᵣ vR8Old) **
      (.r9 ↦ᵣ vR9Old) **
      (.r10 ↦ᵣ vR10Old) **
      (effectiveAddr addr1 0 ↦U64 oldMemD_23) **
      (effectiveAddr addr2 0 ↦U64 oldMemD_24))
      (fun rt => (((((((((((((((((((((((((rt.containsRange (effectiveAddr baseAddr 0) 1 = true) ∧
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
                  rt.containsRange (effectiveAddr baseAddr 128) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr1 0) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr2 0) 8 = true) ∧
                  rt.containsRange (oldMemD_23) (oldMemD_24) = true)
      4 := by
  refine ⟨by decide, ?_⟩
  have h := PTokenTransferOwnerMismatch_lifted_spec baseAddr oldMemB_0 vR2Old oldMemD_1 oldMemB_2 oldMemD_3 oldMemB_4 oldMemD_5 vR4Old vR3Old oldMemD_6 oldMemB_7 vR6Old vR7Old oldMemB_8 oldMemB_9 vR5Old oldMemD_10 oldMemD_11 oldMemD_12 oldMemD_13 vR0Old oldMemD_14 oldMemD_15 oldMemD_16 oldMemD_17 oldMemD_18 oldMemD_19 oldMemD_20 oldMemB_21 oldMemD_22 vR8Old vR9Old vR10Old oldMemD_23 oldMemD_24 addr0 addr1 addr2 h_addr0 h_addr1 h_addr2 holdMemD_1_lt holdMemD_3_lt holdMemD_5_lt holdMemD_6_lt holdMemD_10_lt holdMemD_11_lt holdMemD_12_lt holdMemD_13_lt holdMemD_14_lt holdMemD_15_lt holdMemD_16_lt holdMemD_17_lt holdMemD_18_lt holdMemD_19_lt holdMemD_20_lt holdMemD_22_lt holdMemD_23_lt holdMemD_24_lt h_branch0 h_branch1 h_branch2 h_branch3 h_branch4 h_branch5 h_branch6 h_branch7 h_branch8 h_branch9 h_branch10 h_branch11 h_branch12 h_branch13 h_branch14 h_branch15 h_branch16 h_branch17 h_branch18 h_branch19 h_branch20 h_branch21 h_branch22 h_branch23 h_branch24 h_branch25 h_branch26 h_branch27 h_branch28 h_branch29 h_branch30 nCuLog25 hCuLog25
  rw [show (((toU64 4) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)
        = 4 from by decide,
      show (((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)
        = 0 from by decide] at h
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

#assert_std_axioms_local Examples.Lifted.PTokenTransferOwnerMismatch.PTokenTransferOwnerMismatch_lifted_spec
#assert_std_axioms_local Examples.PTokenOwnerMismatchGuardEnforced.p_token_owner_mismatch_enforced

end Examples.PTokenOwnerMismatchGuardEnforced
