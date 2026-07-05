/-
  Pattern library Layer 3 — the DECIMALS guard on the real p-token
  TransferChecked arm: the check the *Checked instruction family exists
  for (the caller states the decimals it believes the mint has; a
  mismatch means the caller is confused about which asset it is moving).

  From a pre where the instruction's decimals argument differs from the
  mint's stored decimals (the VIOLATION as hypothesis), the lifted error
  path runs to the shared exit with r0 = 18
  (TokenError::MintDecimalsMismatch), cells untouched.
-/

import Generated.PTokenTransferCheckedDecimalsMismatchLifted
import Lean
import SVM.Solana.Patterns.Guards

namespace Examples.PTokenTransferCheckedDecimalsMismatchGuard

open SVM.SBPF
open Memory
open Examples.Lifted.PTokenTransferCheckedDecimalsMismatch

set_option maxHeartbeats 1600000 in
/-- From a decimals argument that differs from the mint's stored decimals,
    the real p-token TransferChecked HALTS with `exitCode = some 18`
    (TokenError::MintDecimalsMismatch) — the decimals check is
    ENFORCED. -/
theorem p_token_transfer_checked_decimals_mismatch_enforced
    (baseAddr oldMemB_0 vR2Old oldMemD_1 oldMemB_2 oldMemD_3 oldMemB_4 oldMemD_5 oldMemB_6 oldMemD_7 vR4Old vR5Old oldMemD_8 oldMemB_9 vR6Old vR7Old oldMemB_10 oldMemB_11 vR3Old oldMemD_12 oldMemD_13 oldMemD_14 vR0Old oldMemD_15 oldMemD_16 vR8Old oldMemD_17 vR10Old oldMemD_18 oldMemD_19 oldMemD_20 vR9Old oldMemD_21 oldMemD_22 oldMemD_23 oldMemD_24 oldMemD_25 oldMemD_26 oldMemB_27 oldMemB_28 oldMemB_29 oldMemD_30 oldMemD_31 : Nat)
    (addr0 : Nat)
    (addr1 : Nat)
    (addr2 : Nat)
    (addr3 : Nat)
    (addr4 : Nat)
    (addr5 : Nat)
    (h_addr0 : addr0 = wrapAdd (wrapAdd baseAddr (((wrapAdd oldMemD_7 (toU64 7)) &&& toU64 (-8)) % U64_MODULUS)) (toU64 41776))
    (h_addr1 : addr1 = wrapAdd (wrapAdd baseAddr (((wrapAdd oldMemD_7 (toU64 7)) &&& toU64 (-8)) % U64_MODULUS)) (toU64 41784))
    (h_addr2 : addr2 = wrapAdd (wrapAdd baseAddr (((wrapAdd oldMemD_7 (toU64 7)) &&& toU64 (-8)) % U64_MODULUS)) (toU64 41785))
    (h_addr3 : addr3 = wrapAdd (wrapAdd baseAddr (((wrapAdd oldMemD_7 (toU64 7)) &&& toU64 (-8)) % U64_MODULUS)) (toU64 41793))
    (h_addr4 : addr4 = wrapAdd (toU64 4295072816) ((((let shift := toU64 56 % 64; if (((((((toU64 18) <<< (toU64 32 % 64)) % U64_MODULUS) ||| toU64 26) % U64_MODULUS) <<< (toU64 24 % 64)) % U64_MODULUS) < U64_MODULUS / 2 then (((((((toU64 18) <<< (toU64 32 % 64)) % U64_MODULUS) ||| toU64 26) % U64_MODULUS) <<< (toU64 24 % 64)) % U64_MODULUS) >>> shift else (let shifted := (((((((toU64 18) <<< (toU64 32 % 64)) % U64_MODULUS) ||| toU64 26) % U64_MODULUS) <<< (toU64 24 % 64)) % U64_MODULUS) >>> shift; let highBits := (U64_MODULUS - 1) - (U64_MODULUS / (2 ^ shift) - 1); (shifted ||| highBits) % U64_MODULUS))) <<< (toU64 3 % 64)) % U64_MODULUS))
    (h_addr5 : addr5 = wrapAdd (toU64 4295071984) ((((let shift := toU64 56 % 64; if (((((((toU64 18) <<< (toU64 32 % 64)) % U64_MODULUS) ||| toU64 26) % U64_MODULUS) <<< (toU64 24 % 64)) % U64_MODULUS) < U64_MODULUS / 2 then (((((((toU64 18) <<< (toU64 32 % 64)) % U64_MODULUS) ||| toU64 26) % U64_MODULUS) <<< (toU64 24 % 64)) % U64_MODULUS) >>> shift else (let shifted := (((((((toU64 18) <<< (toU64 32 % 64)) % U64_MODULUS) ||| toU64 26) % U64_MODULUS) <<< (toU64 24 % 64)) % U64_MODULUS) >>> shift; let highBits := (U64_MODULUS - 1) - (U64_MODULUS / (2 ^ shift) - 1); (shifted ||| highBits) % U64_MODULUS))) <<< (toU64 3 % 64)) % U64_MODULUS))
    (holdMemD_1_lt : oldMemD_1 < 2 ^ 64)
    (holdMemD_3_lt : oldMemD_3 < 2 ^ 64)
    (holdMemD_5_lt : oldMemD_5 < 2 ^ 64)
    (holdMemD_7_lt : oldMemD_7 < 2 ^ 64)
    (holdMemD_8_lt : oldMemD_8 < 2 ^ 64)
    (holdMemD_12_lt : oldMemD_12 < 2 ^ 64)
    (holdMemD_13_lt : oldMemD_13 < 2 ^ 64)
    (holdMemD_14_lt : oldMemD_14 < 2 ^ 64)
    (holdMemD_15_lt : oldMemD_15 < 2 ^ 64)
    (holdMemD_16_lt : oldMemD_16 < 2 ^ 64)
    (holdMemD_17_lt : oldMemD_17 < 2 ^ 64)
    (holdMemD_19_lt : oldMemD_19 < 2 ^ 64)
    (holdMemD_20_lt : oldMemD_20 < 2 ^ 64)
    (holdMemD_21_lt : oldMemD_21 < 2 ^ 64)
    (holdMemD_22_lt : oldMemD_22 < 2 ^ 64)
    (holdMemD_23_lt : oldMemD_23 < 2 ^ 64)
    (holdMemD_24_lt : oldMemD_24 < 2 ^ 64)
    (holdMemD_25_lt : oldMemD_25 < 2 ^ 64)
    (holdMemD_26_lt : oldMemD_26 < 2 ^ 64)
    (holdMemD_30_lt : oldMemD_30 < 2 ^ 64)
    (holdMemD_31_lt : oldMemD_31 < 2 ^ 64)
    (h_branch0 : oldMemB_0 % 256 ≠ toU64 3)
    (h_branch1 : oldMemB_0 % 256 = toU64 4)
    (h_branch2 : oldMemD_1 = toU64 165)
    (h_branch3 : oldMemB_2 % 256 = toU64 255)
    (h_branch4 : oldMemD_3 = toU64 82)
    (h_branch5 : oldMemB_4 % 256 = toU64 255)
    (h_branch6 : oldMemD_5 = toU64 165)
    (h_branch7 : oldMemB_6 % 256 = toU64 255)
    (h_branch8 : ¬ oldMemD_8 < toU64 10)
    (h_branch9 : oldMemB_9 % 256 = toU64 12)
    (h_branch10 : ¬ oldMemB_10 % 256 > toU64 2)
    (h_branch11 : oldMemB_10 % 256 ≠ toU64 0)
    (h_branch12 : ¬ oldMemB_11 % 256 > toU64 2)
    (h_branch13 : oldMemB_11 % 256 ≠ toU64 0)
    (h_branch14 : oldMemB_10 % 256 ≠ toU64 2)
    (h_branch15 : oldMemB_11 % 256 ≠ toU64 2)
    (h_branch16 : ¬ oldMemD_13 < oldMemD_12)
    (h_branch17 : oldMemD_14 = oldMemD_15)
    (h_branch18 : oldMemD_16 = oldMemD_17)
    (h_branch19 : oldMemD_19 = oldMemD_20)
    (h_branch20 : oldMemD_21 = oldMemD_22)
    (h_branch21 : oldMemD_23 = oldMemD_14)
    (h_branch22 : oldMemD_24 = oldMemD_16)
    (h_branch23 : oldMemD_25 = oldMemD_19)
    (h_branch24 : oldMemD_26 = oldMemD_21)
    (h_branch25 : oldMemB_27 % 256 = toU64 1)
    (h_branch26 : oldMemB_28 % 256 ≠ oldMemB_29 % 256)
    (h_branch27 : ¬ toSigned64 ((((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) > toSigned64 (toU64 12))
    (h_branch28 : toSigned64 ((((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) ≤ toSigned64 (toU64 5))
    (h_branch29 : ¬ toSigned64 ((((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) > toSigned64 (toU64 2))
    (h_branch30 : (((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64) = toU64 0)
    (h_branch31 : (((toU64 18) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64) < toU64 20)
    (h_branch32 : ((((((toU64 18) <<< (toU64 32 % 64)) % U64_MODULUS) ||| toU64 26) % U64_MODULUS) &&& toU64 27) % U64_MODULUS = toU64 26)
    (h_branch33 : ¬ toSigned64 ((((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) > toSigned64 (toU64 12))
    (h_branch34 : toSigned64 ((((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) ≤ toSigned64 (toU64 5))
    (h_branch35 : ¬ toSigned64 ((((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) > toSigned64 (toU64 2))
    (h_branch36 : (((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64) = toU64 0)
    (h_branch37 : (((toU64 18) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64) ≠ toU64 0)
    (nCuLog32 : Nat)
    (hCuLog32 : ∀ s : State, (step (.call .sol_log_) s).cuConsumed ≤ s.cuConsumed + nCuLog32)
    : SVM.Solana.Patterns.EnforcedError (122 + 1) nCuLog32 198
      ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((CodeReq.singleton 198 (.ldx .byte .r2 .r1 0)).union
        (CodeReq.singleton 199 (.jeq .r2 (.imm (3)) 304))).union
        (CodeReq.singleton 200 (.jne .r2 (.imm (4)) 312))).union
        (CodeReq.singleton 201 (.ldx .dword .r2 .r1 88))).union
        (CodeReq.singleton 202 (.jne .r2 (.imm (165)) 312))).union
        (CodeReq.singleton 203 (.ldx .byte .r2 .r1 10512))).union
        (CodeReq.singleton 204 (.jne .r2 (.imm (255)) 312))).union
        (CodeReq.singleton 205 (.ldx .dword .r2 .r1 10592))).union
        (CodeReq.singleton 206 (.jne .r2 (.imm (82)) 312))).union
        (CodeReq.singleton 207 (.ldx .byte .r2 .r1 20936))).union
        (CodeReq.singleton 208 (.jne .r2 (.imm (255)) 312))).union
        (CodeReq.singleton 209 (.ldx .dword .r2 .r1 21016))).union
        (CodeReq.singleton 210 (.jne .r2 (.imm (165)) 312))).union
        (CodeReq.singleton 211 (.ldx .byte .r2 .r1 31440))).union
        (CodeReq.singleton 212 (.jne .r2 (.imm (255)) 312))).union
        (CodeReq.singleton 213 (.ldx .dword .r4 .r1 31520))).union
        (CodeReq.singleton 214 (.mov64 .r2 (.reg .r4)))).union
        (CodeReq.singleton 215 (.add64 .r2 (.imm (7))))).union
        (CodeReq.singleton 216 (.and64 .r2 (.imm (-8))))).union
        (CodeReq.singleton 217 (.mov64 .r5 (.reg .r1)))).union
        (CodeReq.singleton 218 (.add64 .r5 (.reg .r2)))).union
        (CodeReq.singleton 219 (.mov64 .r2 (.reg .r5)))).union
        (CodeReq.singleton 220 (.add64 .r2 (.imm (41776))))).union
        (CodeReq.singleton 221 (.ldx .dword .r2 .r2 0))).union
        (CodeReq.singleton 222 (.jlt .r2 (.imm (10)) 312))).union
        (CodeReq.singleton 223 (.mov64 .r2 (.reg .r5)))).union
        (CodeReq.singleton 224 (.add64 .r2 (.imm (41784))))).union
        (CodeReq.singleton 225 (.ldx .byte .r2 .r2 0))).union
        (CodeReq.singleton 226 (.jne .r2 (.imm (12)) 312))).union
        (CodeReq.singleton 227 (.mov64 .r6 (.imm (3))))).union
        (CodeReq.singleton 228 (.mov64 .r7 (.imm (0))))).union
        (CodeReq.singleton 229 (.ldx .byte .r2 .r1 204))).union
        (CodeReq.singleton 230 (.jgt .r2 (.imm (2)) 4725))).union
        (CodeReq.singleton 231 (.jeq .r2 (.imm (0)) 5080))).union
        (CodeReq.singleton 232 (.ldx .byte .r3 .r1 21132))).union
        (CodeReq.singleton 233 (.jgt .r3 (.imm (2)) 4725))).union
        (CodeReq.singleton 234 (.jeq .r3 (.imm (0)) 5080))).union
        (CodeReq.singleton 235 (.mov64 .r6 (.imm (0))))).union
        (CodeReq.singleton 236 (.mov64 .r7 (.imm (17))))).union
        (CodeReq.singleton 237 (.jeq .r2 (.imm (2)) 4725))).union
        (CodeReq.singleton 238 (.jeq .r3 (.imm (2)) 4725))).union
        (CodeReq.singleton 239 (.mov64 .r2 (.reg .r5)))).union
        (CodeReq.singleton 240 (.add64 .r2 (.imm (41785))))).union
        (CodeReq.singleton 241 (.ldx .dword .r2 .r2 0))).union
        (CodeReq.singleton 242 (.mov64 .r7 (.imm (1))))).union
        (CodeReq.singleton 243 (.ldx .dword .r3 .r1 160))).union
        (CodeReq.singleton 244 (.jlt .r3 (.reg .r2) 4725))).union
        (CodeReq.singleton 245 (.mov64 .r7 (.imm (3))))).union
        (CodeReq.singleton 246 (.ldx .dword .r0 .r1 96))).union
        (CodeReq.singleton 247 (.ldx .dword .r6 .r1 21024))).union
        (CodeReq.singleton 248 (.jne .r0 (.reg .r6) 5475))).union
        (CodeReq.singleton 249 (.ldx .dword .r8 .r1 104))).union
        (CodeReq.singleton 250 (.ldx .dword .r6 .r1 21032))).union
        (CodeReq.singleton 251 (.jne .r8 (.reg .r6) 5475))).union
        (CodeReq.singleton 252 (.stx .dword .r10 (-2080) .r3))).union
        (CodeReq.singleton 253 (.ldx .dword .r6 .r1 112))).union
        (CodeReq.singleton 254 (.ldx .dword .r9 .r1 21040))).union
        (CodeReq.singleton 255 (.jne .r6 (.reg .r9) 5475))).union
        (CodeReq.singleton 256 (.ldx .dword .r9 .r1 120))).union
        (CodeReq.singleton 257 (.ldx .dword .r3 .r1 21048))).union
        (CodeReq.singleton 258 (.jne .r9 (.reg .r3) 5475))).union
        (CodeReq.singleton 259 (.ldx .dword .r3 .r1 10520))).union
        (CodeReq.singleton 260 (.jne .r3 (.reg .r0) 5475))).union
        (CodeReq.singleton 261 (.ldx .dword .r3 .r1 10528))).union
        (CodeReq.singleton 262 (.jne .r3 (.reg .r8) 5475))).union
        (CodeReq.singleton 263 (.ldx .dword .r3 .r1 10536))).union
        (CodeReq.singleton 264 (.jne .r3 (.reg .r6) 5475))).union
        (CodeReq.singleton 265 (.ldx .dword .r3 .r1 10544))).union
        (CodeReq.singleton 266 (.mov64 .r6 (.imm (0))))).union
        (CodeReq.singleton 267 (.jne .r3 (.reg .r9) 4725))).union
        (CodeReq.singleton 268 (.ldx .byte .r0 .r1 10645))).union
        (CodeReq.singleton 269 (.jne .r0 (.imm (1)) 5078))).union
        (CodeReq.singleton 270 (.add64 .r5 (.imm (41793))))).union
        (CodeReq.singleton 271 (.ldx .byte .r3 .r5 0))).union
        (CodeReq.singleton 272 (.ldx .byte .r5 .r1 10644))).union
        (CodeReq.singleton 273 (.jne .r3 (.reg .r5) 5990))).union
        (CodeReq.singleton 5990 (.mov64 .r7 (.imm (18))))).union
        (CodeReq.singleton 5991 (.ja 4725))).union
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
      (effectiveAddr baseAddr 20936 ↦ₘ oldMemB_4) **
      (effectiveAddr baseAddr 21016 ↦U64 oldMemD_5) **
      (effectiveAddr baseAddr 31440 ↦ₘ oldMemB_6) **
      (effectiveAddr baseAddr 31520 ↦U64 oldMemD_7) **
      (.r4 ↦ᵣ vR4Old) **
      (.r5 ↦ᵣ vR5Old) **
      (effectiveAddr addr0 0 ↦U64 oldMemD_8) **
      (effectiveAddr addr1 0 ↦ₘ oldMemB_9) **
      (.r6 ↦ᵣ vR6Old) **
      (.r7 ↦ᵣ vR7Old) **
      (effectiveAddr baseAddr 204 ↦ₘ oldMemB_10) **
      (effectiveAddr baseAddr 21132 ↦ₘ oldMemB_11) **
      (.r3 ↦ᵣ vR3Old) **
      (effectiveAddr addr2 0 ↦U64 oldMemD_12) **
      (effectiveAddr baseAddr 160 ↦U64 oldMemD_13) **
      (effectiveAddr baseAddr 96 ↦U64 oldMemD_14) **
      (.r0 ↦ᵣ vR0Old) **
      (effectiveAddr baseAddr 21024 ↦U64 oldMemD_15) **
      (effectiveAddr baseAddr 104 ↦U64 oldMemD_16) **
      (.r8 ↦ᵣ vR8Old) **
      (effectiveAddr baseAddr 21032 ↦U64 oldMemD_17) **
      (.r10 ↦ᵣ vR10Old) **
      (effectiveAddr vR10Old (-2080) ↦U64 oldMemD_18) **
      (effectiveAddr baseAddr 112 ↦U64 oldMemD_19) **
      (effectiveAddr baseAddr 21040 ↦U64 oldMemD_20) **
      (.r9 ↦ᵣ vR9Old) **
      (effectiveAddr baseAddr 120 ↦U64 oldMemD_21) **
      (effectiveAddr baseAddr 21048 ↦U64 oldMemD_22) **
      (effectiveAddr baseAddr 10520 ↦U64 oldMemD_23) **
      (effectiveAddr baseAddr 10528 ↦U64 oldMemD_24) **
      (effectiveAddr baseAddr 10536 ↦U64 oldMemD_25) **
      (effectiveAddr baseAddr 10544 ↦U64 oldMemD_26) **
      (effectiveAddr baseAddr 10645 ↦ₘ oldMemB_27) **
      (effectiveAddr addr3 0 ↦ₘ oldMemB_28) **
      (effectiveAddr baseAddr 10644 ↦ₘ oldMemB_29) **
      (effectiveAddr addr4 0 ↦U64 oldMemD_30) **
      (effectiveAddr addr5 0 ↦U64 oldMemD_31) ** callStackIs [])
      ((.r0 ↦ᵣ 18) ** callStackIs [] **
      (.r1 ↦ᵣ 0) **
      (effectiveAddr baseAddr 0 ↦ₘ oldMemB_0) **
      (.r2 ↦ᵣ toU64 18) **
      (effectiveAddr baseAddr 88 ↦U64 oldMemD_1) **
      (effectiveAddr baseAddr 10512 ↦ₘ oldMemB_2) **
      (effectiveAddr baseAddr 10592 ↦U64 oldMemD_3) **
      (effectiveAddr baseAddr 20936 ↦ₘ oldMemB_4) **
      (effectiveAddr baseAddr 21016 ↦U64 oldMemD_5) **
      (effectiveAddr baseAddr 31440 ↦ₘ oldMemB_6) **
      (effectiveAddr baseAddr 31520 ↦U64 oldMemD_7) **
      (.r4 ↦ᵣ oldMemD_7) **
      (.r5 ↦ᵣ oldMemB_29 % 256) **
      (effectiveAddr addr0 0 ↦U64 oldMemD_8) **
      (effectiveAddr addr1 0 ↦ₘ oldMemB_9) **
      (.r6 ↦ᵣ toU64 0) **
      (.r7 ↦ᵣ toU64 18) **
      (effectiveAddr baseAddr 204 ↦ₘ oldMemB_10) **
      (effectiveAddr baseAddr 21132 ↦ₘ oldMemB_11) **
      (.r3 ↦ᵣ addr5) **
      (effectiveAddr addr2 0 ↦U64 oldMemD_12) **
      (effectiveAddr baseAddr 160 ↦U64 oldMemD_13) **
      (effectiveAddr baseAddr 96 ↦U64 oldMemD_14) **
      (effectiveAddr baseAddr 21024 ↦U64 oldMemD_15) **
      (effectiveAddr baseAddr 104 ↦U64 oldMemD_16) **
      (.r8 ↦ᵣ oldMemD_16) **
      (effectiveAddr baseAddr 21032 ↦U64 oldMemD_17) **
      (.r10 ↦ᵣ vR10Old) **
      (effectiveAddr vR10Old (-2080) ↦U64 oldMemD_13) **
      (effectiveAddr baseAddr 112 ↦U64 oldMemD_19) **
      (effectiveAddr baseAddr 21040 ↦U64 oldMemD_20) **
      (.r9 ↦ᵣ oldMemD_21) **
      (effectiveAddr baseAddr 120 ↦U64 oldMemD_21) **
      (effectiveAddr baseAddr 21048 ↦U64 oldMemD_22) **
      (effectiveAddr baseAddr 10520 ↦U64 oldMemD_23) **
      (effectiveAddr baseAddr 10528 ↦U64 oldMemD_24) **
      (effectiveAddr baseAddr 10536 ↦U64 oldMemD_25) **
      (effectiveAddr baseAddr 10544 ↦U64 oldMemD_26) **
      (effectiveAddr baseAddr 10645 ↦ₘ oldMemB_27) **
      (effectiveAddr addr3 0 ↦ₘ oldMemB_28) **
      (effectiveAddr baseAddr 10644 ↦ₘ oldMemB_29) **
      (effectiveAddr addr4 0 ↦U64 oldMemD_30) **
      (effectiveAddr addr5 0 ↦U64 oldMemD_31))
      (fun rt => ((((((((((((((((((((((((((((((((rt.containsRange (effectiveAddr baseAddr 0) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 88) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10512) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10592) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 20936) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 21016) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 31440) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 31520) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr0 0) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr1 0) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 204) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 21132) 1 = true) ∧
                  rt.containsRange (effectiveAddr addr2 0) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 160) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 96) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 21024) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 104) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 21032) 8 = true) ∧
                  rt.containsWritable (effectiveAddr vR10Old (-2080)) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 112) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 21040) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 120) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 21048) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10520) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10528) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10536) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10544) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10645) 1 = true) ∧
                  rt.containsRange (effectiveAddr addr3 0) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10644) 1 = true) ∧
                  rt.containsRange (effectiveAddr addr4 0) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr5 0) 8 = true) ∧
                  rt.containsRange (oldMemD_30) (oldMemD_31) = true)
      18 := by
  refine ⟨by decide, ?_⟩
  have h := PTokenTransferCheckedDecimalsMismatch_lifted_spec baseAddr oldMemB_0 vR2Old oldMemD_1 oldMemB_2 oldMemD_3 oldMemB_4 oldMemD_5 oldMemB_6 oldMemD_7 vR4Old vR5Old oldMemD_8 oldMemB_9 vR6Old vR7Old oldMemB_10 oldMemB_11 vR3Old oldMemD_12 oldMemD_13 oldMemD_14 vR0Old oldMemD_15 oldMemD_16 vR8Old oldMemD_17 vR10Old oldMemD_18 oldMemD_19 oldMemD_20 vR9Old oldMemD_21 oldMemD_22 oldMemD_23 oldMemD_24 oldMemD_25 oldMemD_26 oldMemB_27 oldMemB_28 oldMemB_29 oldMemD_30 oldMemD_31 addr0 addr1 addr2 addr3 addr4 addr5 h_addr0 h_addr1 h_addr2 h_addr3 h_addr4 h_addr5 holdMemD_1_lt holdMemD_3_lt holdMemD_5_lt holdMemD_7_lt holdMemD_8_lt holdMemD_12_lt holdMemD_13_lt holdMemD_14_lt holdMemD_15_lt holdMemD_16_lt holdMemD_17_lt holdMemD_19_lt holdMemD_20_lt holdMemD_21_lt holdMemD_22_lt holdMemD_23_lt holdMemD_24_lt holdMemD_25_lt holdMemD_26_lt holdMemD_30_lt holdMemD_31_lt h_branch0 h_branch1 h_branch2 h_branch3 h_branch4 h_branch5 h_branch6 h_branch7 h_branch8 h_branch9 h_branch10 h_branch11 h_branch12 h_branch13 h_branch14 h_branch15 h_branch16 h_branch17 h_branch18 h_branch19 h_branch20 h_branch21 h_branch22 h_branch23 h_branch24 h_branch25 h_branch26 h_branch27 h_branch28 h_branch29 h_branch30 h_branch31 h_branch32 h_branch33 h_branch34 h_branch35 h_branch36 h_branch37 nCuLog32 hCuLog32
  rw [show (((toU64 18) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)
        = 18 from by decide,
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

#assert_std_axioms_local Examples.Lifted.PTokenTransferCheckedDecimalsMismatch.PTokenTransferCheckedDecimalsMismatch_lifted_spec
#assert_std_axioms_local Examples.PTokenTransferCheckedDecimalsMismatchGuard.p_token_transfer_checked_decimals_mismatch_enforced

end Examples.PTokenTransferCheckedDecimalsMismatchGuard
