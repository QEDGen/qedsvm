/-
  Pattern library Layer 3 — the SUPPLY-OVERFLOW guard on the real p-token
  MintTo arm: the load-bearing side of the supply invariant. Transfer's
  destination add is UNCHECKED (it wraps — see the pinned non-guard
  `p_token_transfer_dest_overflow_wraps_on_both`), which is sound only
  because balances sum to the supply and THIS check keeps the supply below
  2^64. Both sides of that invariant are now in the catalog: the absent
  check is pinned, the enforcing check is proven.

  From a pre where supply + amount does not fit u64 (the VIOLATION as
  hypothesis), the lifted error path runs from the shared dispatch entry
  through the MintTo arm to the shared exit with r0 = 14
  (TokenError::Overflow), mint and account cells untouched.
-/

import Generated.PTokenMintToSupplyOverflowLifted
import Lean
import SVM.Solana.Patterns.Guards

namespace Examples.PTokenMintToSupplyOverflowGuard

open SVM.SBPF
open Memory
open Examples.Lifted.PTokenMintToSupplyOverflow

set_option maxHeartbeats 1600000 in
/-- From a mint whose supply + amount does not fit u64, the real p-token
    MintTo HALTS with `exitCode = some 14` (TokenError::Overflow), the mint
    supply untouched — the supply-overflow check is ENFORCED. This is the
    check the unchecked Transfer destination add relies on. -/
theorem p_token_mint_to_supply_overflow_enforced
    (baseAddr oldMemB_0 vR2Old oldMemD_1 vR0Old oldMemB_2 oldMemB_3 oldMemB_4 oldMemB_5 oldMemB_6 oldMemB_7 oldMemB_8 vR7Old vR10Old oldMemD_9 vR3Old oldMemB_10 oldMemD_11 oldMemD_12 oldMemB_13 oldMemD_14 oldMemD_15 vR4Old oldMemD_16 vR9Old oldMemB_17 vR5Old vR8Old vR6Old oldMemB_18 oldMemB_19 oldMemD_20 oldMemD_21 oldMemD_22 oldMemD_23 oldMemD_24 oldMemD_25 oldMemD_26 oldMemD_27 oldMemB_28 oldMemB_29 oldMemD_30 oldMemD_31 oldMemD_32 oldMemD_33 oldMemD_34 oldMemD_35 oldMemD_36 oldMemD_37 oldMemD_38 oldMemB_39 oldMemD_40 oldMemD_41 oldMemD_42 : Nat)
    (addr0 : Nat)
    (addr1 : Nat)
    (addr2 : Nat)
    (addr3 : Nat)
    (addr4 : Nat)
    (addr5 : Nat)
    (addr6 : Nat)
    (addr7 : Nat)
    (h_addr0 : addr0 = ((wrapAdd (wrapAdd baseAddr oldMemD_1) (toU64 10351)) &&& toU64 (-8)) % U64_MODULUS)
    (h_addr1 : addr1 = wrapAdd vR10Old (toU64 (-2072)))
    (h_addr2 : addr2 = ((wrapAdd (wrapAdd (addr0) oldMemD_12) (toU64 10343)) &&& toU64 (-8)) % U64_MODULUS)
    (h_addr3 : addr3 = ((wrapAdd (wrapAdd (addr2) oldMemD_15) (toU64 10343)) &&& toU64 (-8)) % U64_MODULUS)
    (h_addr4 : addr4 = wrapAdd baseAddr (toU64 8))
    (h_addr5 : addr5 = wrapAdd (addr3) (toU64 9))
    (h_addr6 : addr6 = wrapAdd (toU64 4295072816) ((((let shift := toU64 56 % 64; if (((((((toU64 14) <<< (toU64 32 % 64)) % U64_MODULUS) ||| toU64 26) % U64_MODULUS) <<< (toU64 24 % 64)) % U64_MODULUS) < U64_MODULUS / 2 then (((((((toU64 14) <<< (toU64 32 % 64)) % U64_MODULUS) ||| toU64 26) % U64_MODULUS) <<< (toU64 24 % 64)) % U64_MODULUS) >>> shift else (let shifted := (((((((toU64 14) <<< (toU64 32 % 64)) % U64_MODULUS) ||| toU64 26) % U64_MODULUS) <<< (toU64 24 % 64)) % U64_MODULUS) >>> shift; let highBits := (U64_MODULUS - 1) - (U64_MODULUS / (2 ^ shift) - 1); (shifted ||| highBits) % U64_MODULUS))) <<< (toU64 3 % 64)) % U64_MODULUS))
    (h_addr7 : addr7 = wrapAdd (toU64 4295071984) ((((let shift := toU64 56 % 64; if (((((((toU64 14) <<< (toU64 32 % 64)) % U64_MODULUS) ||| toU64 26) % U64_MODULUS) <<< (toU64 24 % 64)) % U64_MODULUS) < U64_MODULUS / 2 then (((((((toU64 14) <<< (toU64 32 % 64)) % U64_MODULUS) ||| toU64 26) % U64_MODULUS) <<< (toU64 24 % 64)) % U64_MODULUS) >>> shift else (let shifted := (((((((toU64 14) <<< (toU64 32 % 64)) % U64_MODULUS) ||| toU64 26) % U64_MODULUS) <<< (toU64 24 % 64)) % U64_MODULUS) >>> shift; let highBits := (U64_MODULUS - 1) - (U64_MODULUS / (2 ^ shift) - 1); (shifted ||| highBits) % U64_MODULUS))) <<< (toU64 3 % 64)) % U64_MODULUS))
    (holdMemD_1_lt : oldMemD_1 < 2 ^ 64)
    (holdMemB_0_lt : oldMemB_0 < 2 ^ 8)
    (holdMemB_2_lt : oldMemB_2 < 2 ^ 8)
    (holdMemB_3_lt : oldMemB_3 < 2 ^ 8)
    (holdMemB_4_lt : oldMemB_4 < 2 ^ 8)
    (holdMemB_5_lt : oldMemB_5 < 2 ^ 8)
    (holdMemB_6_lt : oldMemB_6 < 2 ^ 8)
    (holdMemB_7_lt : oldMemB_7 < 2 ^ 8)
    (holdMemB_8_lt : oldMemB_8 < 2 ^ 8)
    (holdMemD_12_lt : oldMemD_12 < 2 ^ 64)
    (holdMemD_15_lt : oldMemD_15 < 2 ^ 64)
    (holdMemD_16_lt : oldMemD_16 < 2 ^ 64)
    (holdMemD_20_lt : oldMemD_20 < 2 ^ 64)
    (holdMemD_21_lt : oldMemD_21 < 2 ^ 64)
    (holdMemD_22_lt : oldMemD_22 < 2 ^ 64)
    (holdMemD_23_lt : oldMemD_23 < 2 ^ 64)
    (holdMemD_24_lt : oldMemD_24 < 2 ^ 64)
    (holdMemD_25_lt : oldMemD_25 < 2 ^ 64)
    (holdMemD_26_lt : oldMemD_26 < 2 ^ 64)
    (holdMemD_27_lt : oldMemD_27 < 2 ^ 64)
    (holdMemD_30_lt : oldMemD_30 < 2 ^ 64)
    (holdMemD_31_lt : oldMemD_31 < 2 ^ 64)
    (holdMemD_32_lt : oldMemD_32 < 2 ^ 64)
    (holdMemD_33_lt : oldMemD_33 < 2 ^ 64)
    (holdMemD_34_lt : oldMemD_34 < 2 ^ 64)
    (holdMemD_35_lt : oldMemD_35 < 2 ^ 64)
    (holdMemD_36_lt : oldMemD_36 < 2 ^ 64)
    (holdMemD_37_lt : oldMemD_37 < 2 ^ 64)
    (holdMemD_38_lt : oldMemD_38 < 2 ^ 64)
    (holdMemD_40_lt : oldMemD_40 < 2 ^ 64)
    (holdMemD_41_lt : oldMemD_41 < 2 ^ 64)
    (holdMemD_42_lt : oldMemD_42 < 2 ^ 64)
    (h_branch0 : oldMemB_0 % 256 = toU64 3)
    (h_branch1 : oldMemD_1 ≠ toU64 165)
    (h_branch2 : oldMemB_0 + 256 * (oldMemB_2 + 256 * (oldMemB_3 + 256 * (oldMemB_4 + 256 * (oldMemB_5 + 256 * (oldMemB_6 + 256 * (oldMemB_7 + 256 * oldMemB_8)))))) ≠ toU64 0)
    (h_branch3 : oldMemB_0 + 256 * (oldMemB_2 + 256 * (oldMemB_3 + 256 * (oldMemB_4 + 256 * (oldMemB_5 + 256 * (oldMemB_6 + 256 * (oldMemB_7 + 256 * oldMemB_8)))))) ≠ toU64 1)
    (h_branch4 : oldMemB_0 + 256 * (oldMemB_2 + 256 * (oldMemB_3 + 256 * (oldMemB_4 + 256 * (oldMemB_5 + 256 * (oldMemB_6 + 256 * (oldMemB_7 + 256 * oldMemB_8)))))) ≠ toU64 2)
    (h_branch5 : oldMemB_0 + 256 * (oldMemB_2 + 256 * (oldMemB_3 + 256 * (oldMemB_4 + 256 * (oldMemB_5 + 256 * (oldMemB_6 + 256 * (oldMemB_7 + 256 * oldMemB_8)))))) < toU64 6)
    (h_branch6 : ¬ toSigned64 (oldMemB_0 + 256 * (oldMemB_2 + 256 * (oldMemB_3 + 256 * (oldMemB_4 + 256 * (oldMemB_5 + 256 * (oldMemB_6 + 256 * (oldMemB_7 + 256 * oldMemB_8))))))) ≤ toSigned64 (toU64 2))
    (h_branch7 : oldMemB_0 + 256 * (oldMemB_2 + 256 * (oldMemB_3 + 256 * (oldMemB_4 + 256 * (oldMemB_5 + 256 * (oldMemB_6 + 256 * (oldMemB_7 + 256 * oldMemB_8)))))) = toU64 3)
    (h_branch8 : oldMemB_10 % 256 = toU64 255)
    (h_branch9 : oldMemB_13 % 256 = toU64 255)
    (h_branch10 : oldMemD_16 ≠ toU64 0)
    (h_branch11 : oldMemB_17 % 256 ≠ toU64 255)
    (h_branch12 : ¬ toSigned64 (oldMemB_17 % 256) > toSigned64 (toU64 11))
    (h_branch13 : toSigned64 (oldMemB_17 % 256) > toSigned64 (toU64 6))
    (h_branch14 : oldMemB_17 % 256 = toU64 7)
    (h_branch15 : ¬ wrapAdd oldMemD_16 (toU64 (-1)) < toU64 8)
    (h_branch16 : ¬ oldMemB_0 + 256 * (oldMemB_2 + 256 * (oldMemB_3 + 256 * (oldMemB_4 + 256 * (oldMemB_5 + 256 * (oldMemB_6 + 256 * (oldMemB_7 + 256 * oldMemB_8)))))) < toU64 3)
    (h_branch17 : oldMemD_12 = toU64 165)
    (h_branch18 : ¬ oldMemB_18 % 256 > toU64 2)
    (h_branch19 : oldMemB_18 % 256 ≠ toU64 2)
    (h_branch20 : oldMemB_18 % 256 ≠ toU64 0)
    (h_branch21 : oldMemB_19 % 256 ≠ toU64 1)
    (h_branch22 : oldMemD_21 = oldMemD_20)
    (h_branch23 : oldMemD_23 = oldMemD_22)
    (h_branch24 : oldMemD_25 = oldMemD_24)
    (h_branch25 : oldMemD_27 = oldMemD_26)
    (h_branch26 : oldMemD_1 = toU64 82)
    (h_branch27 : oldMemB_28 % 256 = toU64 1)
    (h_branch28 : oldMemB_29 % 256 = toU64 1)
    (h_branch29 : oldMemD_31 = oldMemD_30)
    (h_branch30 : oldMemD_33 = oldMemD_32)
    (h_branch31 : oldMemD_35 = oldMemD_34)
    (h_branch32 : oldMemD_37 = oldMemD_36)
    (h_branch33 : oldMemD_15 ≠ toU64 355)
    (h_branch34 : oldMemB_39 % 256 ≠ toU64 0)
    (h_branch35 : oldMemD_38 ≠ toU64 0)
    (h_branch36 : wrapAdd oldMemD_40 oldMemD_38 < oldMemD_40)
    (h_branch37 : ((toU64 1) &&& toU64 1) % U64_MODULUS ≠ toU64 0)
    (h_branch38 : ¬ toSigned64 ((((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) > toSigned64 (toU64 12))
    (h_branch39 : toSigned64 ((((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) ≤ toSigned64 (toU64 5))
    (h_branch40 : ¬ toSigned64 ((((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) > toSigned64 (toU64 2))
    (h_branch41 : (((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64) = toU64 0)
    (h_branch42 : (((toU64 14) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64) < toU64 20)
    (h_branch43 : ((((((toU64 14) <<< (toU64 32 % 64)) % U64_MODULUS) ||| toU64 26) % U64_MODULUS) &&& toU64 27) % U64_MODULUS = toU64 26)
    (h_branch44 : ¬ toSigned64 ((((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) > toSigned64 (toU64 12))
    (h_branch45 : toSigned64 ((((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) ≤ toSigned64 (toU64 5))
    (h_branch46 : ¬ toSigned64 ((((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) > toSigned64 (toU64 2))
    (h_branch47 : (((toU64 0) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64) = toU64 0)
    (h_branch48 : (((toU64 14) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64) ≠ toU64 0)
    (hReloadLt_3658 : ((wrapAdd (wrapAdd baseAddr oldMemD_1) (toU64 10351)) &&& toU64 (-8)) % U64_MODULUS < 2 ^ 64)
    (h_alias_3658 : effectiveAddr (vR10Old) (-2064) = effectiveAddr (wrapAdd vR10Old (toU64 (-2072))) (8))
    (h_alias_3685 : effectiveAddr (wrapAdd baseAddr (toU64 8)) (80) = effectiveAddr (baseAddr) (88))
    (hReloadLt_3692 : ((wrapAdd (wrapAdd (((wrapAdd (wrapAdd baseAddr oldMemD_1) (toU64 10351)) &&& toU64 (-8)) % U64_MODULUS) oldMemD_12) (toU64 10343)) &&& toU64 (-8)) % U64_MODULUS < 2 ^ 64)
    (h_alias_3692 : effectiveAddr (vR10Old) (-2056) = effectiveAddr (wrapAdd vR10Old (toU64 (-2072))) (16))
    (nCuLog43 : Nat)
    (hCuLog43 : ∀ s : State, (step (.call .sol_log_) s).cuConsumed ≤ s.cuConsumed + nCuLog43)
    : SVM.Solana.Patterns.EnforcedError (158 + 1) nCuLog43 198
      ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((CodeReq.singleton 198 (.ldx .byte .r2 .r1 0)).union
        (CodeReq.singleton 199 (.jeq .r2 (.imm (3)) 304))).union
        (CodeReq.singleton 304 (.ldx .dword .r2 .r1 88))).union
        (CodeReq.singleton 305 (.jne .r2 (.imm (165)) 312))).union
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
        (CodeReq.singleton 3543 (.jeq .r5 (.imm (7)) 3654))).union
        (CodeReq.singleton 3654 (.jlt .r9 (.imm (8)) 3944))).union
        (CodeReq.singleton 3655 (.jlt .r7 (.imm (3)) 3947))).union
        (CodeReq.singleton 3656 (.mov64 .r6 (.imm (3))))).union
        (CodeReq.singleton 3657 (.mov64 .r9 (.imm (0))))).union
        (CodeReq.singleton 3658 (.ldx .dword .r3 .r10 (-2064)))).union
        (CodeReq.singleton 3659 (.ldx .dword .r1 .r3 80))).union
        (CodeReq.singleton 3660 (.jne .r1 (.imm (165)) 3536))).union
        (CodeReq.singleton 3661 (.ldx .byte .r1 .r3 196))).union
        (CodeReq.singleton 3662 (.jgt .r1 (.imm (2)) 3536))).union
        (CodeReq.singleton 3663 (.jeq .r1 (.imm (2)) 3974))).union
        (CodeReq.singleton 3664 (.jeq .r1 (.imm (0)) 4916))).union
        (CodeReq.singleton 3665 (.mov64 .r6 (.imm (0))))).union
        (CodeReq.singleton 3666 (.ldx .byte .r1 .r3 197))).union
        (CodeReq.singleton 3667 (.jeq .r1 (.imm (1)) 5361))).union
        (CodeReq.singleton 3668 (.mov64 .r9 (.imm (3))))).union
        (CodeReq.singleton 3669 (.ldx .dword .r1 .r3 88))).union
        (CodeReq.singleton 3670 (.ldx .dword .r2 .r4 8))).union
        (CodeReq.singleton 3671 (.jne .r2 (.reg .r1) 3536))).union
        (CodeReq.singleton 3672 (.ldx .dword .r1 .r3 96))).union
        (CodeReq.singleton 3673 (.ldx .dword .r2 .r4 16))).union
        (CodeReq.singleton 3674 (.jne .r2 (.reg .r1) 3536))).union
        (CodeReq.singleton 3675 (.mov64 .r0 (.reg .r7)))).union
        (CodeReq.singleton 3676 (.ldx .dword .r1 .r3 104))).union
        (CodeReq.singleton 3677 (.ldx .dword .r2 .r4 24))).union
        (CodeReq.singleton 3678 (.jne .r2 (.reg .r1) 3536))).union
        (CodeReq.singleton 3679 (.ldx .dword .r1 .r3 112))).union
        (CodeReq.singleton 3680 (.mov64 .r7 (.reg .r4)))).union
        (CodeReq.singleton 3681 (.ldx .dword .r2 .r4 32))).union
        (CodeReq.singleton 3682 (.jne .r2 (.reg .r1) 3536))).union
        (CodeReq.singleton 3683 (.mov64 .r9 (.imm (0))))).union
        (CodeReq.singleton 3684 (.mov64 .r4 (.reg .r7)))).union
        (CodeReq.singleton 3685 (.ldx .dword .r1 .r4 80))).union
        (CodeReq.singleton 3686 (.jne .r1 (.imm (82)) 4800))).union
        (CodeReq.singleton 3687 (.ldx .byte .r1 .r4 133))).union
        (CodeReq.singleton 3688 (.jne .r1 (.imm (1)) 4799))).union
        (CodeReq.singleton 3689 (.ldx .byte .r1 .r4 88))).union
        (CodeReq.singleton 3690 (.jne .r1 (.imm (1)) 4911))).union
        (CodeReq.singleton 3691 (.mov64 .r9 (.imm (4))))).union
        (CodeReq.singleton 3692 (.ldx .dword .r5 .r10 (-2056)))).union
        (CodeReq.singleton 3693 (.ldx .dword .r1 .r5 8))).union
        (CodeReq.singleton 3694 (.ldx .dword .r2 .r4 92))).union
        (CodeReq.singleton 3695 (.jne .r2 (.reg .r1) 3536))).union
        (CodeReq.singleton 3696 (.ldx .dword .r1 .r5 16))).union
        (CodeReq.singleton 3697 (.ldx .dword .r2 .r4 100))).union
        (CodeReq.singleton 3698 (.jne .r2 (.reg .r1) 3536))).union
        (CodeReq.singleton 3699 (.ldx .dword .r1 .r5 24))).union
        (CodeReq.singleton 3700 (.ldx .dword .r2 .r4 108))).union
        (CodeReq.singleton 3701 (.jne .r2 (.reg .r1) 3536))).union
        (CodeReq.singleton 3702 (.ldx .dword .r1 .r5 32))).union
        (CodeReq.singleton 3703 (.ldx .dword .r2 .r4 116))).union
        (CodeReq.singleton 3704 (.jne .r2 (.reg .r1) 3536))).union
        (CodeReq.singleton 3705 (.ldx .dword .r4 .r8 0))).union
        (CodeReq.singleton 3706 (.ldx .dword .r1 .r5 80))).union
        (CodeReq.singleton 3707 (.jne .r1 (.imm (355)) 4743))).union
        (CodeReq.singleton 4743 (.ldx .byte .r1 .r5 1))).union
        (CodeReq.singleton 4744 (.jeq .r1 (.imm (0)) 6337))).union
        (CodeReq.singleton 4745 (.jeq .r4 (.imm (0)) 4760))).union
        (CodeReq.singleton 4746 (.ldx .dword .r5 .r7 124))).union
        (CodeReq.singleton 4747 (.mov64 .r1 (.reg .r5)))).union
        (CodeReq.singleton 4748 (.add64 .r1 (.reg .r4)))).union
        (CodeReq.singleton 4749 (.mov64 .r2 (.imm (1))))).union
        (CodeReq.singleton 4750 (.jlt .r1 (.reg .r5) 4752))).union
        (CodeReq.singleton 4752 (.and64 .r2 (.imm (1))))).union
        (CodeReq.singleton 4753 (.jne .r2 (.imm (0)) 4771))).union
        (CodeReq.singleton 4771 (.mov64 .r6 (.imm (0))))).union
        (CodeReq.singleton 4772 (.mov64 .r9 (.imm (14))))).union
        (CodeReq.singleton 4773 (.ja 3536))).union
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
      (effectiveAddr addr6 0 ↦U64 oldMemD_41) **
      (effectiveAddr addr7 0 ↦U64 oldMemD_42) ** callStackIs [])
      ((.r0 ↦ᵣ 14) ** callStackIs [] **
      (.r1 ↦ᵣ 0) **
      (effectiveAddr baseAddr 0 ↦ₘ oldMemB_0) **
      (.r2 ↦ᵣ toU64 14) **
      (effectiveAddr baseAddr 88 ↦U64 oldMemD_1) **
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
      (.r3 ↦ᵣ addr7) **
      (effectiveAddr addr0 0 ↦ₘ oldMemB_10) **
      (effectiveAddr addr1 8 ↦U64 addr0) **
      (effectiveAddr addr0 80 ↦U64 oldMemD_12) **
      (effectiveAddr addr2 0 ↦ₘ oldMemB_13) **
      (effectiveAddr addr1 16 ↦U64 addr2) **
      (effectiveAddr addr2 80 ↦U64 oldMemD_15) **
      (.r4 ↦ᵣ oldMemD_38) **
      (effectiveAddr addr3 0 ↦U64 oldMemD_16) **
      (.r9 ↦ᵣ toU64 14) **
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
      (effectiveAddr addr4 124 ↦U64 oldMemD_40) **
      (effectiveAddr addr6 0 ↦U64 oldMemD_41) **
      (effectiveAddr addr7 0 ↦U64 oldMemD_42))
      (fun rt => (((((((((((((((((((((((((((((((((((((((((((rt.containsRange (effectiveAddr baseAddr 0) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 88) 8 = true) ∧
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
                  rt.containsRange (effectiveAddr addr1 8) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr0 80) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr0 196) 1 = true) ∧
                  rt.containsRange (effectiveAddr addr0 197) 1 = true) ∧
                  rt.containsRange (effectiveAddr addr0 88) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr4 8) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr0 96) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr4 16) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr0 104) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr4 24) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr0 112) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr4 32) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 88) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr4 133) 1 = true) ∧
                  rt.containsRange (effectiveAddr addr4 88) 1 = true) ∧
                  rt.containsRange (effectiveAddr addr1 16) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr2 8) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr4 92) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr2 16) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr4 100) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr2 24) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr4 108) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr2 32) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr4 116) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr5 0) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr2 80) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr2 1) 1 = true) ∧
                  rt.containsRange (effectiveAddr addr4 124) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr6 0) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr7 0) 8 = true) ∧
                  rt.containsRange (oldMemD_41) (oldMemD_42) = true)
      14 := by
  refine ⟨by decide, ?_⟩
  have h := PTokenMintToSupplyOverflow_lifted_spec baseAddr oldMemB_0 vR2Old oldMemD_1 vR0Old oldMemB_2 oldMemB_3 oldMemB_4 oldMemB_5 oldMemB_6 oldMemB_7 oldMemB_8 vR7Old vR10Old oldMemD_9 vR3Old oldMemB_10 oldMemD_11 oldMemD_12 oldMemB_13 oldMemD_14 oldMemD_15 vR4Old oldMemD_16 vR9Old oldMemB_17 vR5Old vR8Old vR6Old oldMemB_18 oldMemB_19 oldMemD_20 oldMemD_21 oldMemD_22 oldMemD_23 oldMemD_24 oldMemD_25 oldMemD_26 oldMemD_27 oldMemB_28 oldMemB_29 oldMemD_30 oldMemD_31 oldMemD_32 oldMemD_33 oldMemD_34 oldMemD_35 oldMemD_36 oldMemD_37 oldMemD_38 oldMemB_39 oldMemD_40 oldMemD_41 oldMemD_42 addr0 addr1 addr2 addr3 addr4 addr5 addr6 addr7 h_addr0 h_addr1 h_addr2 h_addr3 h_addr4 h_addr5 h_addr6 h_addr7 holdMemD_1_lt holdMemB_0_lt holdMemB_2_lt holdMemB_3_lt holdMemB_4_lt holdMemB_5_lt holdMemB_6_lt holdMemB_7_lt holdMemB_8_lt holdMemD_12_lt holdMemD_15_lt holdMemD_16_lt holdMemD_20_lt holdMemD_21_lt holdMemD_22_lt holdMemD_23_lt holdMemD_24_lt holdMemD_25_lt holdMemD_26_lt holdMemD_27_lt holdMemD_30_lt holdMemD_31_lt holdMemD_32_lt holdMemD_33_lt holdMemD_34_lt holdMemD_35_lt holdMemD_36_lt holdMemD_37_lt holdMemD_38_lt holdMemD_40_lt holdMemD_41_lt holdMemD_42_lt h_branch0 h_branch1 h_branch2 h_branch3 h_branch4 h_branch5 h_branch6 h_branch7 h_branch8 h_branch9 h_branch10 h_branch11 h_branch12 h_branch13 h_branch14 h_branch15 h_branch16 h_branch17 h_branch18 h_branch19 h_branch20 h_branch21 h_branch22 h_branch23 h_branch24 h_branch25 h_branch26 h_branch27 h_branch28 h_branch29 h_branch30 h_branch31 h_branch32 h_branch33 h_branch34 h_branch35 h_branch36 h_branch37 h_branch38 h_branch39 h_branch40 h_branch41 h_branch42 h_branch43 h_branch44 h_branch45 h_branch46 h_branch47 h_branch48 hReloadLt_3658 h_alias_3658 h_alias_3685 hReloadLt_3692 h_alias_3692 nCuLog43 hCuLog43
  rw [show (((toU64 14) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)
        = 14 from by decide,
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

#assert_std_axioms_local Examples.Lifted.PTokenMintToSupplyOverflow.PTokenMintToSupplyOverflow_lifted_spec
#assert_std_axioms_local Examples.PTokenMintToSupplyOverflowGuard.p_token_mint_to_supply_overflow_enforced

end Examples.PTokenMintToSupplyOverflowGuard
