-- Native program dispatch.
--
-- Native programs aren't BPF: agave runs them as Rust closures inside
-- `solana-bpf-loader-program`, not via the sBPF VM. ATA's `Create`,
-- vault programs, and most real CPI chains eventually invoke System
-- (transfer, create_account, allocate, …). Without native dispatch
-- our CPI handler hits "unknown program" and returns `r0 := 1` —
-- diverging from agave on every real fixture.
--
-- This module exposes a single dispatch entry point:
--
--   Native.dispatch (pid : Nat) (ixData : ByteArray)
--                   (accts : List AcctInput) (mem : Mem) :
--     Option NativeResult
--
-- A `some result` tells the CPI handler the callee was a native
-- program; the caller's memory is updated to `result.mem`, `r0`
-- becomes `result.r0`, and `result.cu` is added to the caller's
-- `cuConsumed`.
--
-- A `none` result means the program-id isn't a known native
-- program and the CPI handler should fall through to its BPF
-- registry lookup. (Note: System's own `unimplemented` variants
-- still return `some` so the failure surfaces deterministically —
-- only program-ids we don't recognize at all yield `none`.)
--
-- Architecturally each native program lives in its own
-- `SVM/Native/<Name>.lean` module with its own `PROGRAM_ID` and
-- `dispatch`. This file aggregates the dispatchers in priority
-- order (System first; ComputeBudget / Stake / Vote as future
-- adds).

import SVM.Native.AcctInput
import SVM.Native.System
import SVM.Native.ComputeBudget
import SVM.Native.Precompiles
import SVM.Native.BpfLoaderUpgradeable

namespace SVM.Native

open SVM.SBPF.Memory

/-- Top-level native dispatch. Tries each native program in priority
    order; returns the first match.

    ## Scope alignment with Firedancer

    Firedancer's builtin program registry
    (`src/flamenco/runtime/program/fd_builtin_programs.c`) is the
    second-client gauge of which native programs are still
    load-bearing:

    ```
    SYSTEM_PROGRAM_BUILTIN,
    VOTE_PROGRAM_BUILTIN,
    LOADER_V4_BUILTIN,
    BPF_LOADER_DEPRECATED_BUILTIN,
    BPF_LOADER_BUILTIN,
    BPF_LOADER_UPGRADEABLE_BUILTIN,
    COMPUTE_BUDGET_PROGRAM_BUILTIN,
    ZK_TOKEN_PROOF_PROGRAM_BUILTIN,
    ZK_ELGAMAL_PROOF_PROGRAM_BUILTIN
    ```

    Native programs *absent* from this list (Stake, Config,
    AddressLookupTable) have been migrated to Core BPF on mainnet:
    the canonical semantics now live in the deployed BPF program
    owned by `BPFLoaderUpgradeab1e…`, dispatched through the
    standard BPF VM path — which is already covered by our BPF
    interpreter + BPF Loader v3 Upgradeable native. Modeling them as
    natives would be modeling dead code. We mirror Firedancer's
    decision and don't ship native dispatchers for them.

    ## Implemented

      - System (all 13 variants)
      - ComputeBudget (no-op + 150 CU)
      - BPF Loader v3 Upgradeable (all 8 variants)
      - The three sig-verify precompiles (ed25519, secp256k1,
        secp256r1) — Firedancer's `fd_precompiles.c` mirror

    ## Not modeled (intentionally — see
    [[native-programs-scope-decision]])

      - **Stake, Config, AddressLookupTable** — migrated to Core
        BPF; Firedancer doesn't ship native dispatchers either. Real
        semantics live in the deployed BPF program at their
        respective on-chain program-ids, handled by our BPF VM.
      - **Vote** — SIMD-0387 is migrating it out of builtins.
        Firedancer still has `VOTE_PROGRAM_BUILTIN` but the migration
        is in progress; we skip until the dust settles.
      - **ZK ElGamal Proof** — Token-2022 confidential transfers;
        narrow utility, large math surface. Firedancer ships it
        but our scope skips for now.

    Not yet covered: BPF Loader v1 (deprecated), v2, v4. -/
def dispatch (pid : Nat) (ixData : ByteArray) (accts : List AcctInput)
    (mem : Mem) : Option NativeResult :=
  if pid = System.PROGRAM_ID then
    System.dispatch ixData accts mem
  else if pid = ComputeBudget.PROGRAM_ID then
    ComputeBudget.dispatch ixData accts mem
  else if pid = BpfLoaderUpgradeable.PROGRAM_ID then
    BpfLoaderUpgradeable.dispatch ixData accts mem
  else
    Precompiles.dispatch pid ixData accts mem

/-! ## Boundedness — the full `hnative` discharge (audit L5/L3, cross-CPI
`StateBounded` closure in `SVM/SBPF/BoundedCpi.lean`): any successful native
dispatch returns a u64 `r0` and byte-bounded caller memory. System and
BpfLoaderUpgradeable prove their legs in-file (private helpers); the two
remaining modules are external sweeps here. -/

theorem ComputeBudget.dispatch_bounded {ixData : ByteArray}
    {accts : List AcctInput} {mem : Mem} {nr : NativeResult}
    (hm : ∀ a, mem a < 256)
    (h : ComputeBudget.dispatch ixData accts mem = some nr) :
    nr.r0 < SVM.SBPF.U64_MODULUS ∧ ∀ a, nr.mem a < 256 := by
  unfold ComputeBudget.dispatch at h
  injection h with h
  subst h
  exact ⟨(by decide : (0 : Nat) < SVM.SBPF.U64_MODULUS), hm⟩

set_option linter.unusedSimpArgs false in
theorem Precompiles.dispatch_bounded {pid : Nat} {ixData : ByteArray}
    {accts : List AcctInput} {mem : Mem} {nr : NativeResult}
    (hm : ∀ a, mem a < 256)
    (h : Precompiles.dispatch pid ixData accts mem = some nr) :
    nr.r0 < SVM.SBPF.U64_MODULUS ∧ ∀ a, nr.mem a < 256 := by
  have hzero : (0 : Nat) < SVM.SBPF.U64_MODULUS := by decide
  have hone : (1 : Nat) < SVM.SBPF.U64_MODULUS := by decide
  unfold Precompiles.dispatch at h
  repeat' split at h
  all_goals first
    | (injection h with h; subst h
       simp only [Precompiles.dispatchEd25519, Precompiles.dispatchSecp256k1,
         Precompiles.dispatchSecp256r1]
       refine ⟨?_, ?_⟩
       · repeat' split
         all_goals first | exact hzero | exact hone
       · intro a
         repeat' split
         all_goals exact hm _)
    | exact nomatch h

/-- The full `hnative` obligation. -/
theorem dispatch_bounded {pid : Nat} {ixData : ByteArray}
    {accts : List AcctInput} {mem : Mem} {nr : NativeResult}
    (hm : ∀ a, mem a < 256)
    (h : dispatch pid ixData accts mem = some nr) :
    nr.r0 < SVM.SBPF.U64_MODULUS ∧ ∀ a, nr.mem a < 256 := by
  unfold dispatch at h
  repeat' split at h
  all_goals
    first
      | exact System.dispatch_bounded hm h
      | exact ComputeBudget.dispatch_bounded hm h
      | exact BpfLoaderUpgradeable.dispatch_bounded hm h
      | exact Precompiles.dispatch_bounded hm h

end SVM.Native
