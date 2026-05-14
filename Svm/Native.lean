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
-- `Svm/Native/<Name>.lean` module with its own `PROGRAM_ID` and
-- `dispatch`. This file aggregates the dispatchers in priority
-- order (System first; ComputeBudget / Stake / Vote as future
-- adds).

import Svm.Native.AcctInput
import Svm.Native.System
import Svm.Native.ComputeBudget
import Svm.Native.AddressLookupTable
import Svm.Native.Config
import Svm.Native.Precompiles

namespace Svm.Native

open Svm.SBPF.Memory

/-- Top-level native dispatch. Tries each native program in priority
    order; returns the first match.

    Implemented: System (all 13 variants), ComputeBudget (no-op +
    150 CU), AddressLookupTable (all 5 variants), Config (the single
    `Store` instruction), and the three sig-verify precompiles
    (ed25519, secp256k1, secp256r1). Still missing: Stake, Vote, the
    BPF Loaders, ZK ElGamal Proof. -/
def dispatch (pid : Nat) (ixData : ByteArray) (accts : List AcctInput)
    (mem : Mem) : Option NativeResult :=
  if pid = System.PROGRAM_ID then
    System.dispatch ixData accts mem
  else if pid = ComputeBudget.PROGRAM_ID then
    ComputeBudget.dispatch ixData accts mem
  else if pid = AddressLookupTable.PROGRAM_ID then
    AddressLookupTable.dispatch ixData accts mem
  else if pid = Config.PROGRAM_ID then
    some (Config.dispatch ixData accts mem)
  else
    Precompiles.dispatch pid ixData accts mem

end Svm.Native
