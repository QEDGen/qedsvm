/-
  What a proof gets from the runtime's account-change rules (#144).

  Nothing here looks at bytecode. Whatever a program does, once the runtime accepts
  the instruction these facts hold, so a proof about one program can rely on them
  for every account that program does not own. #146 connects acceptance to the
  runner's result.
-/
import SVM.Lib.Runtime.Checks

namespace Examples.AccountGuarantees

open SVM.Runtime
open SVM.Pubkey (Pubkey)

/-- However the program behaves after its last CPI returned, an account it does
    not own keeps its existing bytes, length and owner, and can only gain lamports. -/
theorem foreign_account_safe {programId : Pubkey} {refs : List AccountChange} {c : AccountChange}
    (h : postInstructionCheck programId refs = .ok ())
    (hc : c ∈ uniqueChanges refs) (hforeign : c.pre.owner ≠ programId) :
    c.pre.lamports ≤ c.post.lamports ∧ c.contentChanged = false ∧
      c.post.dataLen = c.pre.data.length ∧ c.post.owner = c.pre.owner := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Classical.byContradiction
    intro hlt
    exact hforeign (debit_requires_owner h hc (by omega))
  · cases hd : c.contentChanged with
    | false => rfl
    | true => exact absurd (content_change_authorized h hc hd).2 hforeign
  · apply Classical.byContradiction
    intro hn
    exact hforeign (resize_authorized h hc hn).2
  · apply Classical.byContradiction
    intro hn
    exact hforeign (owner_change_authorized h hc hn).1

/-- A pool that holds every account of an instruction keeps its lamport total, and
    listing a pool account twice does not create lamports to spend. -/
theorem pool_total_conserved {programId : Pubkey} {refs : List AccountChange}
    (h : postInstructionCheck programId refs = .ok ()) :
    ((uniqueChanges refs).map (·.post.lamports)).sum =
      ((uniqueChanges refs).map (·.entry.lamports)).sum :=
  lamports_conserved h

/-! ## The checker on concrete instructions

Each program here exits 0. Acceptance is a further question. -/

private def program : Pubkey := ⟨7, 0, 0, 0⟩
private def other : Pubkey := ⟨8, 0, 0, 0⟩

/-- An account `program` owns, with 16 lamports and no data. -/
private def state (owner : Pubkey := program) : AccountState :=
  { owner, lamports := 16, data := [], executable := false, rentEpoch := 0 }

private def change (key : Nat) (lamports : Nat) (owner : Pubkey := program)
    (isWritable : Bool := true) : AccountChange :=
  { key := ⟨key, 0, 0, 0⟩, isWritable, entry := state owner, pre := state owner
    post := { owner, lamports, dataLen := 0, data := [] } }

example : postInstructionCheck program [change 1 15, change 2 17] = .ok () := rfl

example : postInstructionCheck program [change 1 17] = .error .unbalancedInstruction := rfl

/-- The non-owner debit is reported even though the balance holds. -/
example : postInstructionCheck program [change 1 15 (owner := other), change 2 17] =
    .error .externalAccountLamportSpend := rfl

/-- A duplicate reference does not count twice. -/
example : postInstructionCheck program [change 1 15, change 1 15, change 2 17] = .ok () := rfl

/-- A duplicate's writable flag counts: writable in any reference is writable. -/
example : postInstructionCheck program
    [change 1 15 (isWritable := false), change 1 15, change 2 17] = .ok () := rfl

end Examples.AccountGuarantees
