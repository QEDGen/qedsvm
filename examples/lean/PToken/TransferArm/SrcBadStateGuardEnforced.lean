/-
  Pattern library Layer 3 — the INVALID-STATE-BYTE guard (source) on the
  real p-token binary: the account-data SHAPE check (a state byte outside
  the AccountState tag range 0..2 means the blob is not a token account —
  the type-confusion bug class).

  From a source state byte > 2 (the VIOLATION as hypothesis), the lifted
  error path runs through the taken `jgt state, 2` at pc 4004 and the
  BUILTIN encoder to the shared exit with r0 = 4 <<< 32 = 17179869184
  (ProgramError::InvalidAccountData), token cells untouched.
-/

import Generated.PTokenTransferSrcBadStateLifted
import Lean
import SVM.Solana.Patterns.Guards

namespace Examples.PTokenSrcBadStateGuardEnforced

open SVM.SBPF
open Memory
open Examples.Lifted.PTokenTransferSrcBadState

set_option maxHeartbeats 1600000 in
/-- From a source account whose state byte is outside the AccountState tag
    range (> 2), the real p-token Transfer HALTS with
    `exitCode = some (4 <<< 32)` (ProgramError::InvalidAccountData) — the
    account-shape check is ENFORCED. -/
theorem p_token_src_bad_state_enforced
    (baseAddr oldMemB_0 vR2Old oldMemD_1 oldMemB_2 oldMemD_3 oldMemB_4 oldMemD_5 vR4Old vR3Old oldMemD_6 oldMemB_7 vR6Old vR7Old oldMemB_8 vR8Old vR9Old vR10Old vR0Old : Nat)
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
    (h_branch7 : oldMemB_8 % 256 > toU64 2)
    (h_branch8 : ¬ toSigned64 ((((toU64 3) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) > toSigned64 (toU64 12))
    (h_branch9 : toSigned64 ((((toU64 3) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) ≤ toSigned64 (toU64 5))
    (h_branch10 : toSigned64 ((((toU64 3) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) > toSigned64 (toU64 2))
    (h_branch11 : (((toU64 3) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64) = toU64 3)
    (h_branch12 : ¬ toSigned64 ((((toU64 3) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) > toSigned64 (toU64 12))
    (h_branch13 : toSigned64 ((((toU64 3) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) ≤ toSigned64 (toU64 5))
    (h_branch14 : toSigned64 ((((toU64 3) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) > toSigned64 (toU64 2))
    (h_branch15 : (((toU64 3) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64) = toU64 3)
    (nCuLog9 : Nat)
    (hCuLog9 : ∀ s : State, (step (.call .sol_log_) s).cuConsumed ≤ s.cuConsumed + nCuLog9)
    : SVM.Solana.Patterns.EnforcedError (52 + 1) nCuLog9 198
      ((((((((((((((((((((((((((((((((((((((((((((((((((((((CodeReq.singleton 198 (.ldx .byte .r2 .r1 0)).union
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
        (CodeReq.singleton 4725 (.mov64 .r1 (.reg .r6)))).union
        (CodeReq.singleton 4726 (.mov64 .r2 (.reg .r7)))).union
        (CodeReq.singleton 4727 (.call_local 6864))).union
        (CodeReq.singleton 6864 (.lsh64 .r1 (.imm (32))))).union
        (CodeReq.singleton 6865 (.rsh64 .r1 (.imm (32))))).union
        (CodeReq.singleton 6866 (.jsgt .r1 (.imm (12)) 6874))).union
        (CodeReq.singleton 6867 (.jsle .r1 (.imm (5)) 6881))).union
        (CodeReq.singleton 6881 (.jsgt .r1 (.imm (2)) 6903))).union
        (CodeReq.singleton 6903 (.jeq .r1 (.imm (3)) 6936))).union
        (CodeReq.singleton 6936 (.lddw .r1 (4295070447)))).union
        (CodeReq.singleton 6937 (.mov64 .r2 (.imm (25))))).union
        (CodeReq.singleton 6938 (.ja 6988))).union
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
        (CodeReq.singleton 151 (.jeq .r1 (.imm (3)) 176))).union
        (CodeReq.singleton 176 (.lddw .r0 (17179869184)))).union
        (CodeReq.singleton 177 (.ja 197))).union
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
      (.r8 ↦ᵣ vR8Old) **
      (.r9 ↦ᵣ vR9Old) **
      (.r10 ↦ᵣ vR10Old) **
      (.r0 ↦ᵣ vR0Old) ** callStackIs [])
      ((.r0 ↦ᵣ 17179869184) ** callStackIs [] **
      (.r1 ↦ᵣ (((toU64 3) <<< (toU64 32 % 64)) % U64_MODULUS) >>> (toU64 32 % 64)) **
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
      (.r6 ↦ᵣ toU64 3) **
      (.r7 ↦ᵣ toU64 0) **
      (effectiveAddr baseAddr 204 ↦ₘ oldMemB_8) **
      (.r8 ↦ᵣ vR8Old) **
      (.r9 ↦ᵣ vR9Old) **
      (.r10 ↦ᵣ vR10Old))
      (fun rt => (((((((((rt.containsRange (effectiveAddr baseAddr 0) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 88) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10512) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 10592) 8 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 21016) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 21096) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr0 31352) 8 = true) ∧
                  rt.containsRange (effectiveAddr addr0 31360) 1 = true) ∧
                  rt.containsRange (effectiveAddr baseAddr 204) 1 = true) ∧
                  rt.containsRange (toU64 4295070447) (toU64 25) = true)
      17179869184 := by
  refine ⟨by decide, ?_⟩
  have h := PTokenTransferSrcBadState_lifted_spec baseAddr oldMemB_0 vR2Old oldMemD_1 oldMemB_2 oldMemD_3 oldMemB_4 oldMemD_5 vR4Old vR3Old oldMemD_6 oldMemB_7 vR6Old vR7Old oldMemB_8 vR8Old vR9Old vR10Old vR0Old addr0 h_addr0 holdMemD_1_lt holdMemD_3_lt holdMemD_5_lt holdMemD_6_lt h_branch0 h_branch1 h_branch2 h_branch3 h_branch4 h_branch5 h_branch6 h_branch7 h_branch8 h_branch9 h_branch10 h_branch11 h_branch12 h_branch13 h_branch14 h_branch15 nCuLog9 hCuLog9
  rw [show toU64 17179869184 = 17179869184 from by decide] at h
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

#assert_std_axioms_local Examples.Lifted.PTokenTransferSrcBadState.PTokenTransferSrcBadState_lifted_spec
#assert_std_axioms_local Examples.PTokenSrcBadStateGuardEnforced.p_token_src_bad_state_enforced

end Examples.PTokenSrcBadStateGuardEnforced
