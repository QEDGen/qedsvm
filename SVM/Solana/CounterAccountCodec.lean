/-
  Bridge between the abstract `CounterAccount` record (`Abstract/State.lean`)
  and its byte-level SL predicate — the bare `u64` at the account-data offset.

  Non-token analogue of `TokenAccountCodec.lean`: a counter decodes to one
  `u64`, so `counterValOf` is just `memU64Is` keyed on the record — no field
  aggregation, the coarse field IS the single dword cell. Exists to keep the
  import graph parallel and give the refinement bridge a record-keyed atom.
-/

import SVM.SBPF.SepLogic
import SVM.Solana.Abstract.State

namespace SVM.Solana

open SVM.SBPF
open SVM.Solana.Abstract

/-- SL atom for a counter account at `addr` matching record `c`. The single
    `counter` field sits at offset 0, so the coarse atom is one `↦U64`. -/
def counterValOf (addr : Nat) (c : Abstract.CounterAccount) : Assertion :=
  memU64Is addr c.counter

/-- Definitional unfold for `simp` chains. -/
@[simp] theorem counterValOf_eq (addr : Nat) (c : Abstract.CounterAccount) :
    counterValOf addr c = memU64Is addr c.counter := rfl

/-- A `withCounter` shift rewrites the SL atom to the new value. Load-bearing:
    the refinement bridge applies this to convert the abstract post-state to the
    asm-side predicate. -/
@[simp] theorem counterValOf_withCounter
    (addr : Nat) (c : Abstract.CounterAccount) (n : Nat) :
    counterValOf addr (c.withCounter n) = memU64Is addr n := by
  unfold counterValOf Abstract.CounterAccount.withCounter
  rfl

end SVM.Solana
