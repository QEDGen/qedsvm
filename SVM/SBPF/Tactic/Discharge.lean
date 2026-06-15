/-
  `qedsvm_discharge` — the accessor-projection tactic.

  qedgen states a mutation contract parametric over an opaque `State` and
  accessor `State → Nat`:  `from_balance post = from_balance pre ± amount`.
  The upstream chain (decode ELF → lift via `sl_block_auto` → reshape
  coarse→fine via `account_agg`) produces an `AsmRefines…` obligation
  carrying the decoded field list `List (Nat × FieldVal)`. What this file
  packages is the remaining ACCESSOR PROJECTION: read the mutated field's
  value out of that list so qedgen's `ensures` falls out.

  Instantiating `State` as the field list and `from_balance` as
  `u64FieldAt off` makes the projection a pure lookup — no raw
  `readU64`/`Mem` bridge (the field-list route sidesteps it).
-/

import SVM.SBPF.AccountCodec

namespace SVM.SBPF

/-- qedgen's `from_balance : State → Nat` instantiated at
    `State := List (Nat × FieldVal)`: read the `u64` field at offset `off`
    from the lift's decoded field list. -/
def u64FieldAt (off : Nat) : List (Nat × FieldVal) → Nat
  | [] => 0
  | (o, .u64 v) :: rest => if o = off then v else u64FieldAt off rest
  | _ :: rest => u64FieldAt off rest

/-- Generic accessor evaluation: a `.u64` field at `off` reads its value
    when earlier entries carry other offsets (true of the lift's sorted,
    distinct-offset lists). The reusable projection beyond per-literal `simp`. -/
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

/-- Close a field-list accessor obligation (qedgen's `ensures` shape
    `u64FieldAt off post = u64FieldAt off pre ± k`) by evaluating the
    projection on the lift's lists; decode/lift/reshape are upstream.
    Layout-specific accessors (e.g. SPL token `amount`) should be `@[simp]`
    so they fire here. -/
macro "qedsvm_discharge" : tactic =>
  `(tactic| simp [u64FieldAt])

end SVM.SBPF
