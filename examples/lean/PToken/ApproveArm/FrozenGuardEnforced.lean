/-
  Pattern library Layer 3 — the FROZEN guard on the real p-token Approve
  arm: a frozen account cannot delegate.

  From a frozen source (state byte = 2 — the VIOLATION as hypothesis), the
  lifted error path runs to the shared exit with r0 = 17
  (TokenError::AccountFrozen), cells untouched.
-/

import Generated.PTokenApproveFrozenLifted
import Lean
import SVM.Solana.Patterns.Guards

namespace Examples.PTokenApproveFrozenGuard

open SVM.SBPF
open Memory
open Examples.Lifted.PTokenApproveFrozen

set_option maxHeartbeats 1600000 in
/-- From a frozen source account, the real p-token Approve HALTS with
    `exitCode = some 17` (AccountFrozen) — the frozen check is ENFORCED on
    the Approve arm. -/
theorem p_token_approve_frozen_enforced
    (baseAddr oldMemB_0 vR2Old oldMemD_1 oldMemB_2 oldMemD_3 vR0Old oldMemB_4 oldMemB_5 oldMemB_6 oldMemB_7 oldMemB_8 oldMemB_9 oldMemB_10 vR7Old vR10Old oldMemD_11 vR3Old oldMemB_12 oldMemD_13 oldMemD_14 oldMemB_15 oldMemD_16 oldMemD_17 vR4Old oldMemD_18 vR9Old oldMemB_19 vR5Old vR8Old vR6Old oldMemB_20 oldMemD_21 oldMemD_22 : Nat)
    (addr0 : Nat)
    (addr1 : Nat)
    (addr2 : Nat)
    (addr3 : Nat)
    (addr4 : Nat)
    (addr5 : Nat)
    (addr6 : Nat)
    (h_addr0 : addr0 = ((wrapAdd (wrapAdd baseAddr oldMemD_1) (toU64 10351)) &&& toU64 (-8)) % U64_MODULUS)
    (h_addr1 : addr1 = wrapAdd vR10Old (toU64 (-2072)))
    (h_addr2 : addr2 = ((wrapAdd (wrapAdd (addr0) oldMemD_14) (toU64 10343)) &&& toU64 (-8)) % U64_MODULUS)
    (h_addr3 : addr3 = ((wrapAdd (wrapAdd (addr2) oldMemD_17) (toU64 10343)) &&& toU64 (-8)) % U64_MODULUS)
    (h_addr4 : addr4 = wrapAdd baseAddr (toU64 8))
    (h_addr5 : addr5 = wrapAdd (toU64 4295072816) ((((let shift := toU64 56 % 64; if (((((((toU64 17) <<< (toU64 32 % 64)) % U64_MODULUS) ||| toU64 26) % U64_MODULUS) <<< (toU64 24 % 64)) % U64_MODULUS) < U64_MODULUS / 2 then (((((((toU64 17) <<< (toU64 32 % 64)) % U64_MODULUS) ||| toU64 26) % U64_MODULUS) <<< (toU64 24 % 64)) % U64_MODULUS) >>> shift else (let shifted := (((((((toU64 17) <<< (toU64 32 % 64)) % U64_MODULUS) ||| toU64 26) % U64_MODULUS) <<< (toU64 24 % 64)) % U64_MODULUS) >>> shift; let highBits := (U64_MODULUS - 1) - (U64_MODULUS / (2 ^ shift) - 1); (shifted ||| highBits) % U64_MODULUS))) <<< (toU64 3 % 64)) % U64_MODULUS))
    (h_addr6 : addr6 = wrapAdd (toU64 4295071984) ((((let shift := toU64 56 % 64; if (((((((toU64 17) <<< (toU64 32 % 64)) % U64_MODULUS) ||| toU64 26) % U64_MODULUS) <<< (toU64 24 % 64)) % U64_MODULUS) < U64_MODULUS / 2 then (((((((toU64 17) <<< (toU64 32 % 64)) % U64_MODULUS) ||| toU64 26) % U64_MODULUS) <<< (toU64 24 % 64)) % U64_MODULUS) >>> shift else (let shifted := (((((((toU64 17) <<< (toU64 32 % 64)) % U64_MODULUS) ||| toU64 26) % U64_MODULUS) <<< (toU64 24 % 64)) % U64_MODULUS) >>> shift; let highBits := (U64_MODULUS - 1) - (U64_MODULUS / (2 ^ shift) - 1); (shifted ||| highBits) % U64_MODULUS))) <<< (toU64 3 % 64)) % U64_MODULUS))
    (holdMemD_1_lt : oldMemD_1 < 2 ^ 64)
    (holdMemD_3_lt : oldMemD_3 < 2 ^ 64)
    (holdMemB_0_lt : oldMemB_0 < 2 ^ 8)
    (holdMemB_4_lt : oldMemB_4 < 2 ^ 8)
    (holdMemB_5_lt : oldMemB_5 < 2 ^ 8)
    (holdMemB_6_lt : oldMemB_6 < 2 ^ 8)
    (holdMemB_7_lt : oldMemB_7 < 2 ^ 8)
    (holdMemB_8_lt : oldMemB_8 < 2 ^ 8)
    (holdMemB_9_lt : oldMemB_9 < 2 ^ 8)
    (holdMemB_10_lt : oldMemB_10 < 2 ^ 8)
    (holdMemD_14_lt : oldMemD_14 < 2 ^ 64)
    (holdMemD_17_lt : oldMemD_17 < 2 ^ 64)
    (holdMemD_18_lt : oldMemD_18 < 2 ^ 64)
    (holdMemD_21_lt : oldMemD_21 < 2 ^ 64)
    (holdMemD_22_lt : oldMemD_22 < 2 ^ 64)
    (h_branch0 : oldMemB_0 % 256 = toU64 3)
    (h_branch1 : oldMemD_1 = toU64 165)
    (h_branch2 : oldMemB_2 % 256 = toU64 255)
    (h_branch3 : oldMemD_3 ≠ toU64 165)
    (h_branch4 : oldMemB_0 + 256 * (oldMemB_4 + 256 * (oldMemB_5 + 256 * (oldMemB_6 + 256 * (oldMemB_7 + 256 * (oldMemB_8 + 256 * (oldMemB_9 + 256 * oldMemB_10)))))) ≠ toU64 0)
    (h_branch5 : oldMemB_0 + 256 * (oldMemB_4 + 256 * (oldMemB_5 + 256 * (oldMemB_6 + 256 * (oldMemB_7 + 256 * (oldMemB_8 + 256 * (oldMemB_9 + 256 * oldMemB_10)))))) ≠ toU64 1)
    (h_branch6 : oldMemB_0 + 256 * (oldMemB_4 + 256 * (oldMemB_5 + 256 * (oldMemB_6 + 256 * (oldMemB_7 + 256 * (oldMemB_8 + 256 * (oldMemB_9 + 256 * oldMemB_10)))))) ≠ toU64 2)
    (h_branch7 : oldMemB_0 + 256 * (oldMemB_4 + 256 * (oldMemB_5 + 256 * (oldMemB_6 + 256 * (oldMemB_7 + 256 * (oldMemB_8 + 256 * (oldMemB_9 + 256 * oldMemB_10)))))) < toU64 6)
    (h_branch8 : ¬ toSigned64 (oldMemB_0 + 256 * (oldMemB_4 + 256 * (oldMemB_5 + 256 * (oldMemB_6 + 256 * (oldMemB_7 + 256 * (oldMemB_8 + 256 * (oldMemB_9 + 256 * oldMemB_10))))))) ≤ toSigned64 (toU64 2))
    (h_branch9 : oldMemB_0 + 256 * (oldMemB_4 + 256 * (oldMemB_5 + 256 * (oldMemB_6 + 256 * (oldMemB_7 + 256 * (oldMemB_8 + 256 * (oldMemB_9 + 256 * oldMemB_10)))))) = toU64 3)
    (h_branch10 : oldMemB_12 % 256 = toU64 255)
    (h_branch11 : oldMemB_15 % 256 = toU64 255)
    (h_branch12 : oldMemD_18 ≠ toU64 0)
    (h_branch13 : oldMemB_19 % 256 ≠ toU64 255)
    (h_branch14 : ¬ toSigned64 (oldMemB_19 % 256) > toSigned64 (toU64 11))
    (h_branch15 : ¬ toSigned64 (oldMemB_19 % 256) > toSigned64 (toU64 6))
    (h_branch16 : oldMemB_19 % 256 ≠ toU64 0)
    (h_branch17 : oldMemB_19 % 256 ≠ toU64 1)
    (h_branch18 : oldMemB_19 % 256 ≠ toU64 3)
    (h_branch19 : toSigned64 (((oldMemB_19 % 256) &&& toU64 255) % U64_MODULUS) ≤ toSigned64 (toU64 13))
    (h_branch20 : toSigned64 (((oldMemB_19 % 256) &&& toU64 255) % U64_MODULUS) ≤ toSigned64 (toU64 5))
    (h_branch21 : ((oldMemB_19 % 256) &&& toU64 255) % U64_MODULUS ≠ toU64 2)
    (h_branch22 : ((oldMemB_19 % 256) &&& toU64 255) % U64_MODULUS = toU64 4)
    (h_branch23 : ¬ wrapAdd oldMemD_18 (toU64 (-1)) < toU64 8)
    (h_branch24 : ¬ oldMemB_0 + 256 * (oldMemB_4 + 256 * (oldMemB_5 + 256 * (oldMemB_6 + 256 * (oldMemB_7 + 256 * (oldMemB_8 + 256 * (oldMemB_9 + 256 * oldMemB_10)))))) ≤ toU64 2)
    (h_branch25 : oldMemD_1 = toU64 165)
    (h_branch26 : ¬ oldMemB_20 % 256 > toU64 2)
    (h_branch27 : oldMemB_20 % 256 = toU64 2)
    (h_branch28 : (((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64) ≠ toU64 26)
    (h_branch29 : ¬ toSigned64 ((((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) > toSigned64 (toU64 12))
    (h_branch30 : toSigned64 ((((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) ≤ toSigned64 (toU64 5))
    (h_branch31 : ¬ toSigned64 ((((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) > toSigned64 (toU64 2))
    (h_branch32 : (((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64) = toU64 0)
    (h_branch33 : (((toU64 17) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64) < toU64 20)
    (h_branch34 : ((((((toU64 17) <<< (toU64 32 % 64)) % U64_MODULUS) ||| toU64 26) % U64_MODULUS) &&& toU64 27) % U64_MODULUS = toU64 26)
    (h_branch35 : ¬ toSigned64 ((((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) > toSigned64 (toU64 12))
    (h_branch36 : toSigned64 ((((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) ≤ toSigned64 (toU64 5))
    (h_branch37 : ¬ toSigned64 ((((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) > toSigned64 (toU64 2))
    (h_branch38 : (((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64) = toU64 0)
    (h_branch39 : (((toU64 17) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64) ≠ toU64 0)
    (hReloadLt_7359 : wrapAdd baseAddr (toU64 8) < 2 ^ 64)
    (h_alias_7359 : effectiveAddr (wrapAdd vR10Old (toU64 (-2072))) (0) = effectiveAddr (vR10Old) (-2072))
    (h_alias_7360 : effectiveAddr (wrapAdd baseAddr (toU64 8)) (80) = effectiveAddr (baseAddr) (88))
    (nCuLog23 : Nat)
    (hCuLog23 : ∀ s : State, (step (.call .sol_log_) s).cuConsumed ≤ s.cuConsumed + nCuLog23)
    : SVM.Solana.Patterns.EnforcedError (133 + 1) nCuLog23 198
      (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((CodeReq.singleton 198 (.ldx .byte .r2 .r1 0)).union
        (CodeReq.singleton 199 (.jeq .r2 (.imm (3)) 304))).union
        (CodeReq.singleton 304 (.ldx .dword .r2 .r1 88))).union
        (CodeReq.singleton 305 (.jne .r2 (.imm (165)) 312))).union
        (CodeReq.singleton 306 (.ldx .byte .r2 .r1 10512))).union
        (CodeReq.singleton 307 (.jne .r2 (.imm (255)) 312))).union
        (CodeReq.singleton 308 (.ldx .dword .r2 .r1 10592))).union
        (CodeReq.singleton 309 (.jne .r2 (.imm (165)) 312))).union
        (CodeReq.singleton 312 (.mov64 .r0 (.reg .r1)))).union
        (CodeReq.singleton 313 (.add64 .r0 (.imm (8))))).union
        (CodeReq.singleton 314 (.ldx .dword .r7 .r1 0))).union
        (CodeReq.singleton 315 (.jeq .r7 (.imm (0)) 418))).union
        (CodeReq.singleton 316 (.stx .dword .r10 (-2072) .r0))).union
        (CodeReq.singleton 317 (.ldx .dword .r2 .r1 88))).union
        (CodeReq.singleton 318 (.add64 .r1 (.reg .r2)))).union
        (CodeReq.singleton 319 (.add64 .r1 (.imm (10351))))).union
        (CodeReq.singleton 320 (.and64 .r1 (.imm (-8))))).union
        (CodeReq.singleton 321 (.jeq .r7 (.imm (1)) 330))).union
        (CodeReq.singleton 322 (.jne .r7 (.imm (2)) 3361))).union
        (CodeReq.singleton 3361 (.mov64 .r2 (.reg .r10)))).union
        (CodeReq.singleton 3362 (.add64 .r2 (.imm (-2072))))).union
        (CodeReq.singleton 3363 (.mov64 .r3 (.reg .r7)))).union
        (CodeReq.singleton 3364 (.jlt .r7 (.imm (6)) 3453))).union
        (CodeReq.singleton 3453 (.jsle .r3 (.imm (2)) 3578))).union
        (CodeReq.singleton 3454 (.jeq .r3 (.imm (3)) 3585))).union
        (CodeReq.singleton 3585 (.ldx .byte .r3 .r1 0))).union
        (CodeReq.singleton 3586 (.jne .r3 (.imm (255)) 5265))).union
        (CodeReq.singleton 3587 (.stx .dword .r2 8 .r1))).union
        (CodeReq.singleton 3588 (.ldx .dword .r3 .r1 80))).union
        (CodeReq.singleton 3589 (.add64 .r1 (.reg .r3)))).union
        (CodeReq.singleton 3590 (.add64 .r1 (.imm (10343))))).union
        (CodeReq.singleton 3591 (.and64 .r1 (.imm (-8))))).union
        (CodeReq.singleton 3592 (.ldx .byte .r3 .r1 0))).union
        (CodeReq.singleton 3593 (.jne .r3 (.imm (255)) 5274))).union
        (CodeReq.singleton 3594 (.stx .dword .r2 16 .r1))).union
        (CodeReq.singleton 3595 (.ja 326))).union
        (CodeReq.singleton 326 (.ldx .dword .r2 .r1 80))).union
        (CodeReq.singleton 327 (.add64 .r1 (.reg .r2)))).union
        (CodeReq.singleton 328 (.add64 .r1 (.imm (10343))))).union
        (CodeReq.singleton 329 (.and64 .r1 (.imm (-8))))).union
        (CodeReq.singleton 330 (.mov64 .r4 (.reg .r0)))).union
        (CodeReq.singleton 331 (.mov64 .r0 (.reg .r1)))).union
        (CodeReq.singleton 332 (.ldx .dword .r9 .r0 0))).union
        (CodeReq.singleton 333 (.jeq .r9 (.imm (0)) 420))).union
        (CodeReq.singleton 334 (.ldx .byte .r5 .r0 8))).union
        (CodeReq.singleton 335 (.jeq .r5 (.imm (255)) 423))).union
        (CodeReq.singleton 336 (.add64 .r9 (.imm (-1))))).union
        (CodeReq.singleton 337 (.mov64 .r8 (.reg .r0)))).union
        (CodeReq.singleton 338 (.add64 .r8 (.imm (9))))).union
        (CodeReq.singleton 339 (.jsgt .r5 (.imm (11)) 3474))).union
        (CodeReq.singleton 340 (.jsgt .r5 (.imm (6)) 3543))).union
        (CodeReq.singleton 341 (.jeq .r5 (.imm (0)) 3621))).union
        (CodeReq.singleton 342 (.jeq .r5 (.imm (1)) 3741))).union
        (CodeReq.singleton 343 (.jne .r5 (.imm (3)) 3843))).union
        (CodeReq.singleton 3843 (.mov64 .r1 (.reg .r10)))).union
        (CodeReq.singleton 3844 (.add64 .r1 (.imm (-2072))))).union
        (CodeReq.singleton 3845 (.mov64 .r2 (.reg .r7)))).union
        (CodeReq.singleton 3846 (.mov64 .r3 (.reg .r8)))).union
        (CodeReq.singleton 3847 (.mov64 .r4 (.reg .r9)))).union
        (CodeReq.singleton 3848 (.call_local 6990))).union
        (CodeReq.singleton 6990 (.mov64 .r6 (.reg .r1)))).union
        (CodeReq.singleton 6991 (.mov64 .r0 (.imm (0))))).union
        (CodeReq.singleton 6992 (.mov64 .r1 (.imm (12))))).union
        (CodeReq.singleton 6993 (.and64 .r5 (.imm (255))))).union
        (CodeReq.singleton 6994 (.jsle .r5 (.imm (13)) 7031))).union
        (CodeReq.singleton 7031 (.jsle .r5 (.imm (5)) 7167))).union
        (CodeReq.singleton 7167 (.jeq .r5 (.imm (2)) 7608))).union
        (CodeReq.singleton 7168 (.jeq .r5 (.imm (4)) 7356))).union
        (CodeReq.singleton 7356 (.jlt .r4 (.imm (8)) 9248))).union
        (CodeReq.singleton 7357 (.jle .r2 (.imm (2)) 9247))).union
        (CodeReq.singleton 7358 (.mov64 .r1 (.imm (0))))).union
        (CodeReq.singleton 7359 (.ldx .dword .r4 .r6 0))).union
        (CodeReq.singleton 7360 (.ldx .dword .r5 .r4 80))).union
        (CodeReq.singleton 7361 (.jne .r5 (.imm (165)) 8476))).union
        (CodeReq.singleton 7362 (.ldx .byte .r5 .r4 196))).union
        (CodeReq.singleton 7363 (.jgt .r5 (.imm (2)) 8476))).union
        (CodeReq.singleton 7364 (.jeq .r5 (.imm (2)) 7737))).union
        (CodeReq.singleton 7737 (.mov64 .r1 (.imm (17))))).union
        (CodeReq.singleton 7738 (.ja 9248))).union
        (CodeReq.singleton 9248 (.exit))).union
        (CodeReq.singleton 3849 (.mov64 .r8 (.reg .r0)))).union
        (CodeReq.singleton 3850 (.mov64 .r9 (.reg .r1)))).union
        (CodeReq.singleton 3851 (.ja 4061))).union
        (CodeReq.singleton 4061 (.mov64 .r0 (.imm (0))))).union
        (CodeReq.singleton 4062 (.mov64 .r1 (.reg .r8)))).union
        (CodeReq.singleton 4063 (.lsh64 .r1 (.imm (32))))).union
        (CodeReq.singleton 4064 (.rsh64 .r1 (.imm (32))))).union
        (CodeReq.singleton 4065 (.jeq .r1 (.imm (26)) 3542))).union
        (CodeReq.singleton 4066 (.mov64 .r6 (.reg .r8)))).union
        (CodeReq.singleton 4067 (.ja 3536))).union
        (CodeReq.singleton 3536 (.mov64 .r1 (.reg .r6)))).union
        (CodeReq.singleton 3537 (.mov64 .r2 (.reg .r9)))).union
        (CodeReq.singleton 3538 (.call_local 6864))).union
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
        (CodeReq.singleton 3539 (.mov64 .r1 (.reg .r6)))).union
        (CodeReq.singleton 3540 (.mov64 .r2 (.reg .r9)))).union
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
      (.r0 ↦ᵣ vR0Old) **
      (effectiveAddr baseAddr 0 + 1 ↦ₘ oldMemB_4) **
      (effectiveAddr baseAddr 0 + 2 ↦ₘ oldMemB_5) **
      (effectiveAddr baseAddr 0 + 3 ↦ₘ oldMemB_6) **
      (effectiveAddr baseAddr 0 + 4 ↦ₘ oldMemB_7) **
      (effectiveAddr baseAddr 0 + 5 ↦ₘ oldMemB_8) **
      (effectiveAddr baseAddr 0 + 6 ↦ₘ oldMemB_9) **
      (effectiveAddr baseAddr 0 + 7 ↦ₘ oldMemB_10) **
      (.r7 ↦ᵣ vR7Old) **
      (.r10 ↦ᵣ vR10Old) **
      (effectiveAddr vR10Old (-2072) ↦U64 oldMemD_11) **
      (.r3 ↦ᵣ vR3Old) **
      (effectiveAddr addr0 0 ↦ₘ oldMemB_12) **
      (effectiveAddr addr1 8 ↦U64 oldMemD_13) **
      (effectiveAddr addr0 80 ↦U64 oldMemD_14) **
      (effectiveAddr addr2 0 ↦ₘ oldMemB_15) **
      (effectiveAddr addr1 16 ↦U64 oldMemD_16) **
      (effectiveAddr addr2 80 ↦U64 oldMemD_17) **
      (.r4 ↦ᵣ vR4Old) **
      (effectiveAddr addr3 0 ↦U64 oldMemD_18) **
      (.r9 ↦ᵣ vR9Old) **
      (effectiveAddr addr3 8 ↦ₘ oldMemB_19) **
      (.r5 ↦ᵣ vR5Old) **
      (.r8 ↦ᵣ vR8Old) **
      (.r6 ↦ᵣ vR6Old) **
      (effectiveAddr addr4 196 ↦ₘ oldMemB_20) **
      (effectiveAddr addr5 0 ↦U64 oldMemD_21) **
      (effectiveAddr addr6 0 ↦U64 oldMemD_22) ** callStackIs [])
      ((.r0 ↦ᵣ 17) ** callStackIs [] **
      (.r1 ↦ᵣ 0) **
      (effectiveAddr baseAddr 0 ↦ₘ oldMemB_0) **
      (.r2 ↦ᵣ toU64 17) **
      (effectiveAddr baseAddr 88 ↦U64 oldMemD_1) **
      (effectiveAddr baseAddr 10512 ↦ₘ oldMemB_2) **
      (effectiveAddr baseAddr 10592 ↦U64 oldMemD_3) **
      (effectiveAddr baseAddr 0 + 1 ↦ₘ oldMemB_4) **
      (effectiveAddr baseAddr 0 + 2 ↦ₘ oldMemB_5) **
      (effectiveAddr baseAddr 0 + 3 ↦ₘ oldMemB_6) **
      (effectiveAddr baseAddr 0 + 4 ↦ₘ oldMemB_7) **
      (effectiveAddr baseAddr 0 + 5 ↦ₘ oldMemB_8) **
      (effectiveAddr baseAddr 0 + 6 ↦ₘ oldMemB_9) **
      (effectiveAddr baseAddr 0 + 7 ↦ₘ oldMemB_10) **
      (.r7 ↦ᵣ oldMemB_0 + 256 * (oldMemB_4 + 256 * (oldMemB_5 + 256 * (oldMemB_6 + 256 * (oldMemB_7 + 256 * (oldMemB_8 + 256 * (oldMemB_9 + 256 * oldMemB_10))))))) **
      (.r10 ↦ᵣ vR10Old) **
      (effectiveAddr vR10Old (-2072) ↦U64 addr4) **
      (.r3 ↦ᵣ addr6) **
      (effectiveAddr addr0 0 ↦ₘ oldMemB_12) **
      (effectiveAddr addr1 8 ↦U64 addr0) **
      (effectiveAddr addr0 80 ↦U64 oldMemD_14) **
      (effectiveAddr addr2 0 ↦ₘ oldMemB_15) **
      (effectiveAddr addr1 16 ↦U64 addr2) **
      (effectiveAddr addr2 80 ↦U64 oldMemD_17) **
      (.r4 ↦ᵣ addr4) **
      (effectiveAddr addr3 0 ↦U64 oldMemD_18) **
      (.r9 ↦ᵣ toU64 17) **
      (effectiveAddr addr3 8 ↦ₘ oldMemB_19) **
      (.r5 ↦ᵣ oldMemB_20 % 256) **
      (.r8 ↦ᵣ toU64 0) **
      (.r6 ↦ᵣ toU64 0) **
      (effectiveAddr addr4 196 ↦ₘ oldMemB_20) **
      (effectiveAddr addr5 0 ↦U64 oldMemD_21) **
      (effectiveAddr addr6 0 ↦U64 oldMemD_22))
      (fun rt => ((((((((((((((((((((rt.containsRange (effectiveAddr baseAddr 0) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 88) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10512) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10592) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 0) 8 = true) ∧
                  rt.containsWritable (effectiveAddr vR10Old (-2072)) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 88) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr0 0) 1 = true) ∧
                  rt.containsWritable (effectiveAddr addr1 8) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr0 80) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr2 0) 1 = true) ∧
                  rt.containsWritable (effectiveAddr addr1 16) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr2 80) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr3 0) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr3 8) 1 = true) ∧
                  rt.containsRange (effectiveAddr vR10Old (-2072)) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 88) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr4 196) 1 = true) ∧
                  rt.containsRange (effectiveAddr addr5 0) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr6 0) 8 = true) ∧
                  rt.containsRange (oldMemD_21) (oldMemD_22) = true)
      17 := by
  refine ⟨by decide, ?_⟩
  have h := PTokenApproveFrozen_lifted_spec baseAddr oldMemB_0 vR2Old oldMemD_1 oldMemB_2 oldMemD_3 vR0Old oldMemB_4 oldMemB_5 oldMemB_6 oldMemB_7 oldMemB_8 oldMemB_9 oldMemB_10 vR7Old vR10Old oldMemD_11 vR3Old oldMemB_12 oldMemD_13 oldMemD_14 oldMemB_15 oldMemD_16 oldMemD_17 vR4Old oldMemD_18 vR9Old oldMemB_19 vR5Old vR8Old vR6Old oldMemB_20 oldMemD_21 oldMemD_22 addr0 addr1 addr2 addr3 addr4 addr5 addr6 h_addr0 h_addr1 h_addr2 h_addr3 h_addr4 h_addr5 h_addr6 holdMemD_1_lt holdMemD_3_lt holdMemB_0_lt holdMemB_4_lt holdMemB_5_lt holdMemB_6_lt holdMemB_7_lt holdMemB_8_lt holdMemB_9_lt holdMemB_10_lt holdMemD_14_lt holdMemD_17_lt holdMemD_18_lt holdMemD_21_lt holdMemD_22_lt h_branch0 h_branch1 h_branch2 h_branch3 h_branch4 h_branch5 h_branch6 h_branch7 h_branch8 h_branch9 h_branch10 h_branch11 h_branch12 h_branch13 h_branch14 h_branch15 h_branch16 h_branch17 h_branch18 h_branch19 h_branch20 h_branch21 h_branch22 h_branch23 h_branch24 h_branch25 h_branch26 h_branch27 h_branch28 h_branch29 h_branch30 h_branch31 h_branch32 h_branch33 h_branch34 h_branch35 h_branch36 h_branch37 h_branch38 h_branch39 hReloadLt_7359 h_alias_7359 h_alias_7360 nCuLog23 hCuLog23
  rw [show (((toU64 17) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)
        = 17 from by decide,
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

#assert_std_axioms_local Examples.Lifted.PTokenApproveFrozen.PTokenApproveFrozen_lifted_spec
#assert_std_axioms_local Examples.PTokenApproveFrozenGuard.p_token_approve_frozen_enforced

end Examples.PTokenApproveFrozenGuard
