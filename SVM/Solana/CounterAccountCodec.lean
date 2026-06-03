/-
  Bridge between the abstract `CounterAccount` record (decoded form,
  defined in `SVM/Solana/Abstract/State.lean`) and the byte-level SL
  predicate — for a counter, the bare `u64` at the account-data offset.

  The non-token analogue of `SVM/Solana/TokenAccountCodec.lean`: where a
  token account decodes to mint/owner/amount/rest, a counter account
  decodes to a single `u64` field. `counterValOf` is therefore just
  `memU64Is` keyed on the abstract record — no field aggregation, since
  the coarse field IS the single dword cell the lift owns. This file
  exists to keep the import graph parallel to the token codec and to
  give the refinement bridge a record-keyed SL atom to target.
-/

import SVM.SBPF.SepLogic
import SVM.Solana.Abstract.State

namespace SVM.Solana

open SVM.SBPF
open SVM.Solana.Abstract

/-- Record-keyed view of the counter cell: the SL atom for a counter
    account at byte address `addr`, with contents matching the abstract
    record `c`. The single `counter` field sits at offset 0, so the
    coarse atom is exactly one `↦U64`. -/
def counterValOf (addr : Nat) (c : Abstract.CounterAccount) : Assertion :=
  memU64Is addr c.counter

/-- Definitional unfold for `simp` chains. -/
@[simp] theorem counterValOf_eq (addr : Nat) (c : Abstract.CounterAccount) :
    counterValOf addr c = memU64Is addr c.counter := rfl

/-- A `withCounter` shift on the abstract record rewrites the SL atom to
    one with the new counter value. The load-bearing lemma the
    refinement bridge applies to convert the abstract counter's
    post-state to the asm-side predicate. -/
@[simp] theorem counterValOf_withCounter
    (addr : Nat) (c : Abstract.CounterAccount) (n : Nat) :
    counterValOf addr (c.withCounter n) = memU64Is addr n := by
  unfold counterValOf Abstract.CounterAccount.withCounter
  rfl

end SVM.Solana
