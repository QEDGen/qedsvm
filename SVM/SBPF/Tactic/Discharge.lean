/-
  `qedsvm_discharge` — the accessor-projection tactic.

  A program's state-mutation contract, as qedgen states it
  (QEDGen/solana-skills: crates/qedgen/data/proofs/spl/Token.lean), is
  parametric over an opaque `State` and an accessor `State → Nat`:

      (from_balance post) = (from_balance pre) ± amount

  The `qedsvm_discharge` direction (QEDGen/qedsvm#24) discharges that
  obligation against pinned bytecode. The chain is: decode the ELF, lift
  via `sl_block_auto`, reshape the account bytes coarse→fine via
  `account_agg` (keystone #2). All of that is upstream and produces an
  `AsmRefines…` obligation carrying the decoded field list
  (`List (Nat × FieldVal)`). What remains — the part this file packages as
  a tactic — is the ACCESSOR PROJECTION: read the mutated field's value out
  of that field list, so qedgen's `ensures` equation falls out.

  Instantiating qedgen's `State` as the field list and `from_balance` as
  `u64FieldAt off` makes the projection a pure lookup — no raw `readU64` /
  `Mem` bridge, because the field-list route (via `account_agg`) sidesteps
  it.
-/

import SVM.SBPF.AccountCodec

namespace SVM.SBPF

/-- qedgen's `from_balance : State → Nat`, instantiated: read the `u64`
    field at byte offset `off` from a decoded account (the field list the
    lift produces). `State := List (Nat × FieldVal)`. -/
def u64FieldAt (off : Nat) : List (Nat × FieldVal) → Nat
  | [] => 0
  | (o, .u64 v) :: rest => if o = off then v else u64FieldAt off rest
  | _ :: rest => u64FieldAt off rest

/-- Generic accessor evaluation: a `.u64` field at `off` reads its value
    when the entries before it carry other offsets (true of the lift's
    sorted, distinct-offset field lists). The reusable projection the
    discharge applies, beyond per-literal `simp`. -/
theorem u64FieldAt_found (off v : Nat) (before after : List (Nat × FieldVal))
    (hb : ∀ e ∈ before, e.1 ≠ off) :
    u64FieldAt off (before ++ (off, .u64 v) :: after) = v := by
  induction before with
  | nil => simp [u64FieldAt]
  | cons e es ih =>
    have ho : e.1 ≠ off := hb e (by simp)
    have ih' := ih (fun x hx => hb x (by simp [hx]))
    obtain ⟨o, fv⟩ := e
    simp only [List.cons_append]
    cases fv <;> simp_all [u64FieldAt]

/-- Close a field-list accessor obligation — qedgen's `ensures` shape,
    `u64FieldAt off post = u64FieldAt off pre ± k` — by evaluating the
    projection on the lift's field lists. The decode / lift / reshape are
    upstream (the `AsmRefines…` obligation); this discharges the accessor
    read on top.

    Field accessors keyed to a specific layout (e.g. the SPL token
    `amount`) should be tagged `@[simp]` so they fire here. -/
macro "qedsvm_discharge" : tactic =>
  `(tactic| simp [u64FieldAt])

end SVM.SBPF
