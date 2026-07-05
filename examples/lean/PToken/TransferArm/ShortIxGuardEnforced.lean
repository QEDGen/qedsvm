/-
  Pattern library Layer 3 — the INSTRUCTION-DATA-LENGTH guard on the real
  p-token binary: Transfer instruction data must be at least 9 bytes
  (discriminator + u64 amount).

  From a 1-byte instruction (`jlt ix_len, 9` at pc 3998 taken — the
  VIOLATION as hypothesis), the lifted error path routes through the 312
  hub to the error handler and the shared exit with r0 = 12
  (TokenError::InvalidInstruction), token cells untouched.
-/

import Generated.PTokenTransferShortIxLifted
import Lean
import SVM.Solana.Patterns.Guards

namespace Examples.PTokenShortIxGuardEnforced

open SVM.SBPF
open Memory
open Examples.Lifted.PTokenTransferShortIx

set_option maxHeartbeats 1600000 in
/-- From instruction data shorter than 9 bytes, the real p-token Transfer
    HALTS with `exitCode = some 12` (TokenError::InvalidInstruction), the
    token cells untouched — the instruction-length check is ENFORCED. -/
theorem p_token_short_ix_enforced
    (baseAddr oldMemB_0 vR2Old oldMemD_1 oldMemB_2 oldMemD_3 oldMemB_4 oldMemD_5 vR4Old vR3Old oldMemD_6 vR0Old oldMemB_7 oldMemB_8 oldMemB_9 oldMemB_10 oldMemB_11 oldMemB_12 oldMemB_13 vR7Old vR10Old oldMemD_14 oldMemB_15 oldMemD_16 oldMemD_17 oldMemB_18 oldMemD_19 oldMemD_20 oldMemD_21 vR9Old oldMemB_22 vR5Old vR8Old vR6Old oldMemD_23 oldMemD_24 : Nat)
    (addr0 : Nat)
    (addr1 : Nat)
    (addr2 : Nat)
    (addr3 : Nat)
    (addr4 : Nat)
    (addr5 : Nat)
    (addr6 : Nat)
    (h_addr0 : addr0 = wrapAdd baseAddr (((wrapAdd oldMemD_5 (toU64 7)) &&& toU64 (-8)) % U64_MODULUS))
    (h_addr1 : addr1 = ((wrapAdd (wrapAdd baseAddr oldMemD_1) (toU64 10351)) &&& toU64 (-8)) % U64_MODULUS)
    (h_addr2 : addr2 = wrapAdd vR10Old (toU64 (-2072)))
    (h_addr3 : addr3 = ((wrapAdd (wrapAdd (addr1) oldMemD_17) (toU64 10343)) &&& toU64 (-8)) % U64_MODULUS)
    (h_addr4 : addr4 = ((wrapAdd (wrapAdd (addr3) oldMemD_20) (toU64 10343)) &&& toU64 (-8)) % U64_MODULUS)
    (h_addr5 : addr5 = wrapAdd (toU64 4295072816) ((((let shift := toU64 56 % 64; if (((((((toU64 12) <<< (toU64 32 % 64)) % U64_MODULUS) ||| toU64 26) % U64_MODULUS) <<< (toU64 24 % 64)) % U64_MODULUS) < U64_MODULUS / 2 then (((((((toU64 12) <<< (toU64 32 % 64)) % U64_MODULUS) ||| toU64 26) % U64_MODULUS) <<< (toU64 24 % 64)) % U64_MODULUS) >>> shift else (let shifted := (((((((toU64 12) <<< (toU64 32 % 64)) % U64_MODULUS) ||| toU64 26) % U64_MODULUS) <<< (toU64 24 % 64)) % U64_MODULUS) >>> shift; let highBits := (U64_MODULUS - 1) - (U64_MODULUS / (2 ^ shift) - 1); (shifted ||| highBits) % U64_MODULUS))) <<< (toU64 3 % 64)) % U64_MODULUS))
    (h_addr6 : addr6 = wrapAdd (toU64 4295071984) ((((let shift := toU64 56 % 64; if (((((((toU64 12) <<< (toU64 32 % 64)) % U64_MODULUS) ||| toU64 26) % U64_MODULUS) <<< (toU64 24 % 64)) % U64_MODULUS) < U64_MODULUS / 2 then (((((((toU64 12) <<< (toU64 32 % 64)) % U64_MODULUS) ||| toU64 26) % U64_MODULUS) <<< (toU64 24 % 64)) % U64_MODULUS) >>> shift else (let shifted := (((((((toU64 12) <<< (toU64 32 % 64)) % U64_MODULUS) ||| toU64 26) % U64_MODULUS) <<< (toU64 24 % 64)) % U64_MODULUS) >>> shift; let highBits := (U64_MODULUS - 1) - (U64_MODULUS / (2 ^ shift) - 1); (shifted ||| highBits) % U64_MODULUS))) <<< (toU64 3 % 64)) % U64_MODULUS))
    (holdMemD_1_lt : oldMemD_1 < 2 ^ 64)
    (holdMemD_3_lt : oldMemD_3 < 2 ^ 64)
    (holdMemD_5_lt : oldMemD_5 < 2 ^ 64)
    (holdMemD_6_lt : oldMemD_6 < 2 ^ 64)
    (holdMemB_0_lt : oldMemB_0 < 2 ^ 8)
    (holdMemB_7_lt : oldMemB_7 < 2 ^ 8)
    (holdMemB_8_lt : oldMemB_8 < 2 ^ 8)
    (holdMemB_9_lt : oldMemB_9 < 2 ^ 8)
    (holdMemB_10_lt : oldMemB_10 < 2 ^ 8)
    (holdMemB_11_lt : oldMemB_11 < 2 ^ 8)
    (holdMemB_12_lt : oldMemB_12 < 2 ^ 8)
    (holdMemB_13_lt : oldMemB_13 < 2 ^ 8)
    (holdMemD_17_lt : oldMemD_17 < 2 ^ 64)
    (holdMemD_20_lt : oldMemD_20 < 2 ^ 64)
    (holdMemD_21_lt : oldMemD_21 < 2 ^ 64)
    (holdMemD_23_lt : oldMemD_23 < 2 ^ 64)
    (holdMemD_24_lt : oldMemD_24 < 2 ^ 64)
    (h_branch0 : oldMemB_0 % 256 = toU64 3)
    (h_branch1 : oldMemD_1 = toU64 165)
    (h_branch2 : oldMemB_2 % 256 = toU64 255)
    (h_branch3 : oldMemD_3 = toU64 165)
    (h_branch4 : oldMemB_4 % 256 = toU64 255)
    (h_branch5 : oldMemD_6 < toU64 9)
    (h_branch6 : oldMemB_0 + 256 * (oldMemB_7 + 256 * (oldMemB_8 + 256 * (oldMemB_9 + 256 * (oldMemB_10 + 256 * (oldMemB_11 + 256 * (oldMemB_12 + 256 * oldMemB_13)))))) ≠ toU64 0)
    (h_branch7 : oldMemB_0 + 256 * (oldMemB_7 + 256 * (oldMemB_8 + 256 * (oldMemB_9 + 256 * (oldMemB_10 + 256 * (oldMemB_11 + 256 * (oldMemB_12 + 256 * oldMemB_13)))))) ≠ toU64 1)
    (h_branch8 : oldMemB_0 + 256 * (oldMemB_7 + 256 * (oldMemB_8 + 256 * (oldMemB_9 + 256 * (oldMemB_10 + 256 * (oldMemB_11 + 256 * (oldMemB_12 + 256 * oldMemB_13)))))) ≠ toU64 2)
    (h_branch9 : oldMemB_0 + 256 * (oldMemB_7 + 256 * (oldMemB_8 + 256 * (oldMemB_9 + 256 * (oldMemB_10 + 256 * (oldMemB_11 + 256 * (oldMemB_12 + 256 * oldMemB_13)))))) < toU64 6)
    (h_branch10 : ¬ toSigned64 (oldMemB_0 + 256 * (oldMemB_7 + 256 * (oldMemB_8 + 256 * (oldMemB_9 + 256 * (oldMemB_10 + 256 * (oldMemB_11 + 256 * (oldMemB_12 + 256 * oldMemB_13))))))) ≤ toSigned64 (toU64 2))
    (h_branch11 : oldMemB_0 + 256 * (oldMemB_7 + 256 * (oldMemB_8 + 256 * (oldMemB_9 + 256 * (oldMemB_10 + 256 * (oldMemB_11 + 256 * (oldMemB_12 + 256 * oldMemB_13)))))) = toU64 3)
    (h_branch12 : oldMemB_15 % 256 = toU64 255)
    (h_branch13 : oldMemB_18 % 256 = toU64 255)
    (h_branch14 : oldMemD_21 ≠ toU64 0)
    (h_branch15 : oldMemB_22 % 256 ≠ toU64 255)
    (h_branch16 : ¬ toSigned64 (oldMemB_22 % 256) > toSigned64 (toU64 11))
    (h_branch17 : ¬ toSigned64 (oldMemB_22 % 256) > toSigned64 (toU64 6))
    (h_branch18 : oldMemB_22 % 256 ≠ toU64 0)
    (h_branch19 : oldMemB_22 % 256 ≠ toU64 1)
    (h_branch20 : oldMemB_22 % 256 = toU64 3)
    (h_branch21 : wrapAdd oldMemD_21 (toU64 (-1)) < toU64 8)
    (h_branch22 : ¬ toSigned64 ((((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) > toSigned64 (toU64 12))
    (h_branch23 : toSigned64 ((((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) ≤ toSigned64 (toU64 5))
    (h_branch24 : ¬ toSigned64 ((((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) > toSigned64 (toU64 2))
    (h_branch25 : (((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64) = toU64 0)
    (h_branch26 : (((toU64 12) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64) < toU64 20)
    (h_branch27 : ((((((toU64 12) <<< (toU64 32 % 64)) % U64_MODULUS) ||| toU64 26) % U64_MODULUS) &&& toU64 27) % U64_MODULUS = toU64 26)
    (h_branch28 : ¬ toSigned64 ((((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) > toSigned64 (toU64 12))
    (h_branch29 : toSigned64 ((((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) ≤ toSigned64 (toU64 5))
    (h_branch30 : ¬ toSigned64 ((((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) > toSigned64 (toU64 2))
    (h_branch31 : (((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64) = toU64 0)
    (h_branch32 : (((toU64 12) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64) ≠ toU64 0)
    (nCuLog25 : Nat)
    (hCuLog25 : ∀ s : State, (step (.call .sol_log_) s).cuConsumed ≤ s.cuConsumed + nCuLog25)
    : SVM.Solana.Patterns.EnforcedError (111 + 1) nCuLog25 198
      (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((CodeReq.singleton 198 (.ldx .byte .r2 .r1 0)).union
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
        (CodeReq.singleton 344 (.jlt .r9 (.imm (8)) 3944))).union
        (CodeReq.singleton 3944 (.mov64 .r6 (.imm (0))))).union
        (CodeReq.singleton 3945 (.mov64 .r9 (.imm (12))))).union
        (CodeReq.singleton 3946 (.ja 3536))).union
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
      (effectiveAddr baseAddr 21016 ↦ₘ oldMemB_4) **
      (effectiveAddr baseAddr 21096 ↦U64 oldMemD_5) **
      (.r4 ↦ᵣ vR4Old) **
      (.r3 ↦ᵣ vR3Old) **
      (effectiveAddr addr0 31352 ↦U64 oldMemD_6) **
      (.r0 ↦ᵣ vR0Old) **
      (effectiveAddr baseAddr 0 + 1 ↦ₘ oldMemB_7) **
      (effectiveAddr baseAddr 0 + 2 ↦ₘ oldMemB_8) **
      (effectiveAddr baseAddr 0 + 3 ↦ₘ oldMemB_9) **
      (effectiveAddr baseAddr 0 + 4 ↦ₘ oldMemB_10) **
      (effectiveAddr baseAddr 0 + 5 ↦ₘ oldMemB_11) **
      (effectiveAddr baseAddr 0 + 6 ↦ₘ oldMemB_12) **
      (effectiveAddr baseAddr 0 + 7 ↦ₘ oldMemB_13) **
      (.r7 ↦ᵣ vR7Old) **
      (.r10 ↦ᵣ vR10Old) **
      (effectiveAddr vR10Old (-2072) ↦U64 oldMemD_14) **
      (effectiveAddr addr1 0 ↦ₘ oldMemB_15) **
      (effectiveAddr addr2 8 ↦U64 oldMemD_16) **
      (effectiveAddr addr1 80 ↦U64 oldMemD_17) **
      (effectiveAddr addr3 0 ↦ₘ oldMemB_18) **
      (effectiveAddr addr2 16 ↦U64 oldMemD_19) **
      (effectiveAddr addr3 80 ↦U64 oldMemD_20) **
      (effectiveAddr addr4 0 ↦U64 oldMemD_21) **
      (.r9 ↦ᵣ vR9Old) **
      (effectiveAddr addr4 8 ↦ₘ oldMemB_22) **
      (.r5 ↦ᵣ vR5Old) **
      (.r8 ↦ᵣ vR8Old) **
      (.r6 ↦ᵣ vR6Old) **
      (effectiveAddr addr5 0 ↦U64 oldMemD_23) **
      (effectiveAddr addr6 0 ↦U64 oldMemD_24) ** callStackIs [])
      ((.r0 ↦ᵣ 12) ** callStackIs [] **
      (.r1 ↦ᵣ 0) **
      (effectiveAddr baseAddr 0 ↦ₘ oldMemB_0) **
      (.r2 ↦ᵣ toU64 12) **
      (effectiveAddr baseAddr 88 ↦U64 oldMemD_1) **
      (effectiveAddr baseAddr 10512 ↦ₘ oldMemB_2) **
      (effectiveAddr baseAddr 10592 ↦U64 oldMemD_3) **
      (effectiveAddr baseAddr 21016 ↦ₘ oldMemB_4) **
      (effectiveAddr baseAddr 21096 ↦U64 oldMemD_5) **
      (.r4 ↦ᵣ wrapAdd baseAddr (toU64 8)) **
      (.r3 ↦ᵣ addr6) **
      (effectiveAddr addr0 31352 ↦U64 oldMemD_6) **
      (effectiveAddr baseAddr 0 + 1 ↦ₘ oldMemB_7) **
      (effectiveAddr baseAddr 0 + 2 ↦ₘ oldMemB_8) **
      (effectiveAddr baseAddr 0 + 3 ↦ₘ oldMemB_9) **
      (effectiveAddr baseAddr 0 + 4 ↦ₘ oldMemB_10) **
      (effectiveAddr baseAddr 0 + 5 ↦ₘ oldMemB_11) **
      (effectiveAddr baseAddr 0 + 6 ↦ₘ oldMemB_12) **
      (effectiveAddr baseAddr 0 + 7 ↦ₘ oldMemB_13) **
      (.r7 ↦ᵣ oldMemB_0 + 256 * (oldMemB_7 + 256 * (oldMemB_8 + 256 * (oldMemB_9 + 256 * (oldMemB_10 + 256 * (oldMemB_11 + 256 * (oldMemB_12 + 256 * oldMemB_13))))))) **
      (.r10 ↦ᵣ vR10Old) **
      (effectiveAddr vR10Old (-2072) ↦U64 wrapAdd baseAddr (toU64 8)) **
      (effectiveAddr addr1 0 ↦ₘ oldMemB_15) **
      (effectiveAddr addr2 8 ↦U64 addr1) **
      (effectiveAddr addr1 80 ↦U64 oldMemD_17) **
      (effectiveAddr addr3 0 ↦ₘ oldMemB_18) **
      (effectiveAddr addr2 16 ↦U64 addr3) **
      (effectiveAddr addr3 80 ↦U64 oldMemD_20) **
      (effectiveAddr addr4 0 ↦U64 oldMemD_21) **
      (.r9 ↦ᵣ toU64 12) **
      (effectiveAddr addr4 8 ↦ₘ oldMemB_22) **
      (.r5 ↦ᵣ oldMemB_22 % 256) **
      (.r8 ↦ᵣ wrapAdd (addr4) (toU64 9)) **
      (.r6 ↦ᵣ toU64 0) **
      (effectiveAddr addr5 0 ↦U64 oldMemD_23) **
      (effectiveAddr addr6 0 ↦U64 oldMemD_24))
      (fun rt => ((((((((((((((((((((rt.containsRange (effectiveAddr baseAddr 0) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 88) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10512) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10592) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 21016) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 21096) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr0 31352) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 0) 8 = true) ∧
                  rt.containsWritable (effectiveAddr vR10Old (-2072)) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 88) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr1 0) 1 = true) ∧
                  rt.containsWritable (effectiveAddr addr2 8) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr1 80) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr3 0) 1 = true) ∧
                  rt.containsWritable (effectiveAddr addr2 16) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr3 80) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr4 0) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr4 8) 1 = true) ∧
                  rt.containsRange (effectiveAddr addr5 0) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr6 0) 8 = true) ∧
                  rt.containsRange (oldMemD_23) (oldMemD_24) = true)
      12 := by
  refine ⟨by decide, ?_⟩
  have h := PTokenTransferShortIx_lifted_spec baseAddr oldMemB_0 vR2Old oldMemD_1 oldMemB_2 oldMemD_3 oldMemB_4 oldMemD_5 vR4Old vR3Old oldMemD_6 vR0Old oldMemB_7 oldMemB_8 oldMemB_9 oldMemB_10 oldMemB_11 oldMemB_12 oldMemB_13 vR7Old vR10Old oldMemD_14 oldMemB_15 oldMemD_16 oldMemD_17 oldMemB_18 oldMemD_19 oldMemD_20 oldMemD_21 vR9Old oldMemB_22 vR5Old vR8Old vR6Old oldMemD_23 oldMemD_24 addr0 addr1 addr2 addr3 addr4 addr5 addr6 h_addr0 h_addr1 h_addr2 h_addr3 h_addr4 h_addr5 h_addr6 holdMemD_1_lt holdMemD_3_lt holdMemD_5_lt holdMemD_6_lt holdMemB_0_lt holdMemB_7_lt holdMemB_8_lt holdMemB_9_lt holdMemB_10_lt holdMemB_11_lt holdMemB_12_lt holdMemB_13_lt holdMemD_17_lt holdMemD_20_lt holdMemD_21_lt holdMemD_23_lt holdMemD_24_lt h_branch0 h_branch1 h_branch2 h_branch3 h_branch4 h_branch5 h_branch6 h_branch7 h_branch8 h_branch9 h_branch10 h_branch11 h_branch12 h_branch13 h_branch14 h_branch15 h_branch16 h_branch17 h_branch18 h_branch19 h_branch20 h_branch21 h_branch22 h_branch23 h_branch24 h_branch25 h_branch26 h_branch27 h_branch28 h_branch29 h_branch30 h_branch31 h_branch32 nCuLog25 hCuLog25
  rw [show (((toU64 12) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)
        = 12 from by decide,
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

#assert_std_axioms_local Examples.Lifted.PTokenTransferShortIx.PTokenTransferShortIx_lifted_spec
#assert_std_axioms_local Examples.PTokenShortIxGuardEnforced.p_token_short_ix_enforced

end Examples.PTokenShortIxGuardEnforced
