/-
  Pattern library Layer 3 — the UNINITIALIZED-DESTINATION guard's full
  ENFORCES composition on the real p-token binary (sibling of
  `SrcUninitGuardEnforced.lean`: the source's `jeq state, 0` at 4005 falls
  through, the dest's at 4008 takes). r0 = 42949672960
  (ProgramError::UninitializedAccount, builtin high-32 encoding).
-/

import Generated.PTokenTransferDestUninitLifted
import Lean
import SVM.Solana.Patterns.Guards

namespace Examples.PTokenDestUninitGuardEnforced

open SVM.SBPF
open Memory
open Examples.Lifted.PTokenTransferDestUninit

set_option maxHeartbeats 1600000 in
/-- From an uninitialized destination account, the real p-token Transfer
    HALTS with `exitCode = some (10 <<< 32)`
    (ProgramError::UninitializedAccount), the token cells untouched — the
    initialized check is ENFORCED on the destination too. -/
theorem p_token_dest_uninit_enforced
    (baseAddr oldMemB_0 vR2Old oldMemD_1 oldMemB_2 oldMemD_3 oldMemB_4 oldMemD_5 vR4Old vR3Old oldMemD_6 oldMemB_7 vR6Old vR7Old oldMemB_8 oldMemB_9 vR5Old vR8Old vR9Old vR10Old vR0Old : Nat)
    (addr0 : Nat)
    (h_addr0 : addr0 = wrapAdd baseAddr (((wrapAdd oldMemD_5 (toU64 7)) &&& toU64 (-8)) % U64_MODULUS))
    (holdMemD_1_lt : oldMemD_1 < 2 ^ 64)
    (holdMemD_3_lt : oldMemD_3 < 2 ^ 64)
    (holdMemD_5_lt : oldMemD_5 < 2 ^ 64)
    (holdMemD_6_lt : oldMemD_6 < 2 ^ 64)
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
    (h_branch10 : oldMemB_9 % 256 = toU64 0)
    (h_branch11 : ¬ toSigned64 ((((toU64 9) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) > toSigned64 (toU64 12))
    (h_branch12 : ¬ toSigned64 ((((toU64 9) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) ≤ toSigned64 (toU64 5))
    (h_branch13 : ¬ toSigned64 ((((toU64 9) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) ≤ toSigned64 (toU64 8))
    (h_branch14 : ¬ toSigned64 ((((toU64 9) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) > toSigned64 (toU64 10))
    (h_branch15 : (((toU64 9) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64) = toU64 9)
    (h_branch16 : ¬ toSigned64 ((((toU64 9) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) > toSigned64 (toU64 12))
    (h_branch17 : ¬ toSigned64 ((((toU64 9) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) ≤ toSigned64 (toU64 5))
    (h_branch18 : ¬ toSigned64 ((((toU64 9) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) ≤ toSigned64 (toU64 8))
    (h_branch19 : ¬ toSigned64 ((((toU64 9) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) > toSigned64 (toU64 10))
    (h_branch20 : (((toU64 9) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64) = toU64 9)
    (nCuLog10 : Nat)
    (hCuLog10 : ∀ s : State, (step (.call .sol_log_) s).cuConsumed ≤ s.cuConsumed + nCuLog10)
    : SVM.Solana.Patterns.EnforcedError (60 + 1) nCuLog10 198
      ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((CodeReq.singleton 198 (.ldx .byte .r2 .r1 0)).union
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
        (CodeReq.singleton 5080 (.mov64 .r6 (.imm (9))))).union
        (CodeReq.singleton 5081 (.ja 4725))).union
        (CodeReq.singleton 4725 (.mov64 .r1 (.reg .r6)))).union
        (CodeReq.singleton 4726 (.mov64 .r2 (.reg .r7)))).union
        (CodeReq.singleton 4727 (.call_local 6864))).union
        (CodeReq.singleton 6864 (.lsh64 .r1 (.imm (32))))).union
        (CodeReq.singleton 6865 (.rsh64 .r1 (.imm (32))))).union
        (CodeReq.singleton 6866 (.jsgt .r1 (.imm (12)) 6874))).union
        (CodeReq.singleton 6867 (.jsle .r1 (.imm (5)) 6881))).union
        (CodeReq.singleton 6868 (.jsle .r1 (.imm (8)) 6893))).union
        (CodeReq.singleton 6869 (.jsgt .r1 (.imm (10)) 6913))).union
        (CodeReq.singleton 6870 (.jne .r1 (.imm (9)) 6948))).union
        (CodeReq.singleton 6871 (.lddw .r1 (4295070712)))).union
        (CodeReq.singleton 6872 (.mov64 .r2 (.imm (27))))).union
        (CodeReq.singleton 6873 (.ja 6988))).union
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
        (CodeReq.singleton 122 (.jsgt .r1 (.imm (10)) 159))).union
        (CodeReq.singleton 123 (.jne .r1 (.imm (9)) 184))).union
        (CodeReq.singleton 124 (.lddw .r0 (42949672960)))).union
        (CodeReq.singleton 125 (.ja 197))).union
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
      (.r8 ↦ᵣ vR8Old) **
      (.r9 ↦ᵣ vR9Old) **
      (.r10 ↦ᵣ vR10Old) **
      (.r0 ↦ᵣ vR0Old) ** callStackIs [])
      ((.r0 ↦ᵣ 42949672960) ** callStackIs [] **
      (.r1 ↦ᵣ (((toU64 9) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) **
      (effectiveAddr baseAddr 0 ↦ₘ oldMemB_0) **
      (.r2 ↦ᵣ toU64 0) **
      (effectiveAddr baseAddr 88 ↦U64 oldMemD_1) **
      (effectiveAddr baseAddr 10512 ↦ₘ oldMemB_2) **
      (effectiveAddr baseAddr 10592 ↦U64 oldMemD_3) **
      (effectiveAddr baseAddr 21016 ↦ₘ oldMemB_4) **
      (effectiveAddr baseAddr 21096 ↦U64 oldMemD_5) **
      (.r4 ↦ᵣ oldMemD_5) **
      (.r3 ↦ᵣ oldMemB_8 % 256) **
      (effectiveAddr addr0 31352 ↦U64 oldMemD_6) **
      (effectiveAddr addr0 31360 ↦ₘ oldMemB_7) **
      (.r6 ↦ᵣ toU64 9) **
      (.r7 ↦ᵣ toU64 0) **
      (effectiveAddr baseAddr 204 ↦ₘ oldMemB_8) **
      (effectiveAddr baseAddr 10708 ↦ₘ oldMemB_9) **
      (.r5 ↦ᵣ oldMemB_9 % 256) **
      (.r8 ↦ᵣ vR8Old) **
      (.r9 ↦ᵣ vR9Old) **
      (.r10 ↦ᵣ vR10Old))
      (fun rt => ((((((((((rt.containsRange (effectiveAddr baseAddr 0) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 88) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10512) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10592) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 21016) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 21096) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr0 31352) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr0 31360) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 204) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10708) 1 = true) ∧
                  rt.containsRange (toU64 4295070712) (toU64 27) = true)
      42949672960 := by
  refine ⟨by decide, ?_⟩
  have h := PTokenTransferDestUninit_lifted_spec baseAddr oldMemB_0 vR2Old oldMemD_1 oldMemB_2 oldMemD_3 oldMemB_4 oldMemD_5 vR4Old vR3Old oldMemD_6 oldMemB_7 vR6Old vR7Old oldMemB_8 oldMemB_9 vR5Old vR8Old vR9Old vR10Old vR0Old addr0 h_addr0 holdMemD_1_lt holdMemD_3_lt holdMemD_5_lt holdMemD_6_lt h_branch0 h_branch1 h_branch2 h_branch3 h_branch4 h_branch5 h_branch6 h_branch7 h_branch8 h_branch9 h_branch10 h_branch11 h_branch12 h_branch13 h_branch14 h_branch15 h_branch16 h_branch17 h_branch18 h_branch19 h_branch20 nCuLog10 hCuLog10
  rw [show toU64 42949672960 = 42949672960 from by decide] at h
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

#assert_std_axioms_local Examples.Lifted.PTokenTransferDestUninit.PTokenTransferDestUninit_lifted_spec
#assert_std_axioms_local Examples.PTokenDestUninitGuardEnforced.p_token_dest_uninit_enforced

end Examples.PTokenDestUninitGuardEnforced
