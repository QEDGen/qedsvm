/-
  The runtime's account-change rules for one top-level instruction (#144).

  Agave 4.3 has no single post-execution pass. The rules fire while it reads the
  input buffer back after the program exits 0 (`deserialize_parameters_for_abiv1`
  and `BorrowedInstructionAccount`), and the balance check fires at instruction
  pop. Under `account_data_direct_mapping`, which Mollusk's `all_enabled` turns
  on, data writes are refused earlier still, at the store. So the order here is:

      1. data writes, across all accounts (agave: at the store)
      2. per unique account, in instruction order:
         lamports, then realloc bounds, then resize, then owner
      3. the lamport balance across unique accounts

  A callee's changes are not the caller's, so the comparison points differ by rule.
  Authorization compares against the account when the last CPI returned (`pre`),
  which is agave's current account as it reads the buffer back. The realloc bound
  and the balance look back to instruction entry (`entry`). With no CPI, the two
  are the same state.

  This is a statement about states and a buffer, separate from whether the bytecode
  returned zero. #146 connects it to the runner.

  What this does not say:
  - Rent-state transitions are transaction-level and live elsewhere.
  - `MaxAccountsDataAllocationsExceeded` (20 MiB growth per transaction) cannot
    fire for one top-level instruction: 255 accounts grow by at most 10 KiB each.
  - Accepting does not imply agave accepts. A program that writes read-only data
    and restores it faults on agave at the store, but leaves no trace in the
    pre/post pair (#158). The other direction holds: agave accepting implies the
    checker accepts.
  - Agave also applies these rules to a caller's pending changes at CPI entry, and
    to a callee's changes at its own return. This file judges only what follows the
    last return to the top-level program; the rest belongs to #112.
  - Duplicates are explicit: `uniqueChanges` merges references by key, and a key's
    writable flag is the OR of its references (Mollusk compiles a message, so
    `[a readonly, a writable]` is writable; see `dup_mixed_*` in `diff_mollusk.rs`).
-/
import SVM.Pubkey

namespace SVM.Runtime

open SVM.Pubkey (Pubkey)

/-- `MAX_PERMITTED_DATA_INCREASE`: per-instruction growth of one account. -/
def MAX_PERMITTED_DATA_INCREASE : Nat := 10240

/-- `MAX_PERMITTED_DATA_LENGTH`: the largest account. -/
def MAX_PERMITTED_DATA_LENGTH : Nat := 10 * 1024 * 1024

/-- An account as the runtime holds it. -/
structure AccountState where
  owner      : Pubkey
  lamports   : Nat
  data       : List UInt8
  executable : Bool
  rentEpoch  : Nat
  deriving Repr, DecidableEq

/-- What the runtime reads back from the buffer for one account. This is every
    field a program can influence: the serialized key, executable, is_signer,
    is_writable and rent_epoch are never read back, so a write to them has no
    effect (`commit_executable`).

    `dataLen` is the raw length field, which a program may set to anything.
    `data` is the bytes behind it, at most `pre + MAX_PERMITTED_DATA_INCREASE` of
    them, so it is shorter than `dataLen` only when the realloc rule rejects. -/
structure AccountWrites where
  owner    : Pubkey
  lamports : Nat
  dataLen  : Nat
  data     : List UInt8
  deriving Repr, DecidableEq

/-- One instruction reference to an account: its state at instruction entry, its
    state when control last returned to this program, and what the buffer holds. -/
structure AccountChange where
  key        : Pubkey
  isWritable : Bool
  entry      : AccountState
  pre        : AccountState
  post       : AccountWrites
  deriving Repr, DecidableEq

/-- Agave's `InstructionError` names, for the rules this file covers. -/
inductive AccountChangeError where
  | externalAccountLamportSpend
  | readonlyLamportChange
  | invalidRealloc
  | readonlyDataModified
  | externalAccountDataModified
  | modifiedProgramId
  | unbalancedInstruction
  deriving Repr, DecidableEq

/-! ## Unique accounts -/

/-- Add one reference to the accounts seen so far: a known key only widens its
    writable flag, and the first reference's states stand (agave skips a duplicate
    slot's buffer record, so no other states exist). -/
def mergeRef (acc : List AccountChange) (c : AccountChange) : List AccountChange :=
  if acc.any (fun a => decide (a.key = c.key)) then
    acc.map fun a => if a.key = c.key then { a with isWritable := a.isWritable || c.isWritable } else a
  else
    acc ++ [c]

/-- The unique accounts of an instruction, in first-reference order. -/
def uniqueChanges (refs : List AccountChange) : List AccountChange :=
  refs.foldl mergeRef []

/-! ## The rules -/

/-- `is_owned_by_current_program`: decided on the pre-state owner, because agave
    applies an owner change last. -/
def AccountChange.owned (c : AccountChange) (programId : Pubkey) : Bool :=
  decide (c.pre.owner = programId)

/-- `can_data_be_changed`. -/
def canDataBeChanged (programId : Pubkey) (c : AccountChange) : Except AccountChangeError Unit :=
  if !c.isWritable then .error .readonlyDataModified
  else if !c.owned programId then .error .externalAccountDataModified
  else .ok ()

/-- Whether two byte strings differ on their common prefix. Tail recursive: this
    runs over accounts of up to 10 MiB. -/
def prefixDiffers : List UInt8 → List UInt8 → Bool
  | a :: as, b :: bs => if a != b then true else prefixDiffers as bs
  | _, _ => false

/-- A store into existing account data. Bytes past the old length belong to the
    resize rule. -/
def AccountChange.contentChanged (c : AccountChange) : Bool :=
  prefixDiffers c.pre.data c.post.data

/-- Step 1: the data write rule, enforced at the store under direct mapping. -/
def checkDataWrite (programId : Pubkey) (c : AccountChange) : Except AccountChangeError Unit :=
  if c.contentChanged then canDataBeChanged programId c else .ok ()

/-- `set_lamports`, which runs only when the value changed. -/
def checkLamports (programId : Pubkey) (c : AccountChange) : Except AccountChangeError Unit :=
  if c.post.lamports == c.pre.lamports then .ok ()
  else if !c.owned programId && decide (c.post.lamports < c.pre.lamports) then
    .error .externalAccountLamportSpend
  else if !c.isWritable then .error .readonlyLamportChange
  else .ok ()

/-- The realloc bounds, from the entry length, then `set_data_length`'s `can_data_be_resized`. -/
def checkDataLen (programId : Pubkey) (c : AccountChange) : Except AccountChangeError Unit :=
  if decide (c.post.dataLen - c.entry.data.length > MAX_PERMITTED_DATA_INCREASE)
      || decide (c.post.dataLen > MAX_PERMITTED_DATA_LENGTH) then
    .error .invalidRealloc
  else if c.post.dataLen == c.pre.data.length then .ok ()
  else canDataBeChanged programId c

/-- `set_owner`, which runs only when the value changed. Zeroing is judged on the
    post-state data: agave applies the owner last so that a program can clear an
    account and hand it over in one instruction. -/
def checkOwner (programId : Pubkey) (c : AccountChange) : Except AccountChangeError Unit :=
  if c.post.owner = c.pre.owner then .ok ()
  else if !c.owned programId then .error .modifiedProgramId
  else if !c.isWritable then .error .modifiedProgramId
  else if !c.post.data.all (· == 0) then .error .modifiedProgramId
  else .ok ()

/-- Step 2, for one account. -/
def checkAccount (programId : Pubkey) (c : AccountChange) : Except AccountChangeError Unit :=
  match checkLamports programId c with
  | .error e => .error e
  | .ok () =>
    match checkDataLen programId c with
    | .error e => .error e
    | .ok () => checkOwner programId c

/-- Apply `f` in order, stopping at the first error. -/
def checkAll {α : Type} (f : α → Except AccountChangeError Unit) :
    List α → Except AccountChangeError Unit
  | [] => .ok ()
  | x :: xs =>
    match f x with
    | .error e => .error e
    | .ok () => checkAll f xs

def entryLamports (xs : List AccountChange) : Nat :=
  (xs.map (·.entry.lamports)).sum

def postLamports (xs : List AccountChange) : Nat :=
  (xs.map (·.post.lamports)).sum

/-- Does the runtime accept this instruction's account changes? `refs` holds one
    entry per instruction reference, duplicates included. -/
def postInstructionCheck (programId : Pubkey) (refs : List AccountChange) :
    Except AccountChangeError Unit :=
  let xs := uniqueChanges refs
  match checkAll (checkDataWrite programId) xs with
  | .error e => .error e
  | .ok () =>
    match checkAll (checkAccount programId) xs with
    | .error e => .error e
    | .ok () =>
      if postLamports xs == entryLamports xs then .ok () else .error .unbalancedInstruction

/-- The account the runtime stores on acceptance. -/
def commit (c : AccountChange) : AccountState :=
  { owner      := c.post.owner
    lamports   := c.post.lamports
    data       := c.post.data
    executable := c.entry.executable
    rentEpoch  := c.entry.rentEpoch }

/-! ## Unpacking acceptance -/

theorem checkAll_ok {α : Type} {f : α → Except AccountChangeError Unit} :
    ∀ {xs : List α}, checkAll f xs = .ok () → ∀ x ∈ xs, f x = .ok ()
  | [], _, _, hx => by cases hx
  | x :: xs, h, y, hy => by
    unfold checkAll at h
    cases hf : f x with
    | error e => simp [hf] at h
    | ok u =>
      rw [hf] at h
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hf
      · exact checkAll_ok h y hy

/-- Acceptance, as the three steps it is made of. -/
theorem postInstructionCheck_ok {programId : Pubkey} {refs : List AccountChange}
    (h : postInstructionCheck programId refs = .ok ()) :
    (∀ c ∈ uniqueChanges refs, checkDataWrite programId c = .ok ()) ∧
    (∀ c ∈ uniqueChanges refs, checkAccount programId c = .ok ()) ∧
    postLamports (uniqueChanges refs) = entryLamports (uniqueChanges refs) := by
  unfold postInstructionCheck at h
  cases h1 : checkAll (checkDataWrite programId) (uniqueChanges refs) with
  | error e => simp [h1] at h
  | ok u1 =>
    cases h2 : checkAll (checkAccount programId) (uniqueChanges refs) with
    | error e => simp [h1, h2] at h
    | ok u2 =>
      simp only [h1, h2] at h
      refine ⟨checkAll_ok h1, checkAll_ok h2, ?_⟩
      by_cases hb : postLamports (uniqueChanges refs) == entryLamports (uniqueChanges refs)
      · exact beq_iff_eq.mp hb
      · simp [hb] at h

/-- Acceptance of one account, as its three rules. -/
theorem checkAccount_ok {programId : Pubkey} {c : AccountChange}
    (h : checkAccount programId c = .ok ()) :
    checkLamports programId c = .ok () ∧ checkDataLen programId c = .ok () ∧
      checkOwner programId c = .ok () := by
  unfold checkAccount at h
  cases h1 : checkLamports programId c with
  | error e => simp [h1] at h
  | ok u1 =>
    cases h2 : checkDataLen programId c with
    | error e => simp [h1, h2] at h
    | ok u2 =>
      simp only [h1, h2] at h
      exact ⟨rfl, rfl, h⟩

theorem canDataBeChanged_ok {programId : Pubkey} {c : AccountChange}
    (h : canDataBeChanged programId c = .ok ()) :
    c.isWritable = true ∧ c.owned programId = true := by
  unfold canDataBeChanged at h
  cases hw : c.isWritable <;> cases ho : c.owned programId <;> simp_all

/-! ## One guarantee per rule

Each takes acceptance of the whole instruction and speaks of one unique account. -/

section Guarantees

variable {programId : Pubkey} {refs : List AccountChange} {c : AccountChange}

/-- Only the owning program can debit an account. -/
theorem debit_requires_owner (h : postInstructionCheck programId refs = .ok ())
    (hc : c ∈ uniqueChanges refs) (hd : c.post.lamports < c.pre.lamports) :
    c.pre.owner = programId := by
  have hl := (checkAccount_ok ((postInstructionCheck_ok h).2.1 c hc)).1
  unfold checkLamports at hl
  have hne : (c.post.lamports == c.pre.lamports) = false := by
    simp; omega
  cases ho : c.owned programId with
  | true => simpa [AccountChange.owned] using ho
  | false => simp [hne, ho, hd] at hl

/-- A read-only account's balance does not change. -/
theorem readonly_lamports_unchanged (h : postInstructionCheck programId refs = .ok ())
    (hc : c ∈ uniqueChanges refs) (hr : c.isWritable = false) :
    c.post.lamports = c.pre.lamports := by
  have hl := (checkAccount_ok ((postInstructionCheck_ok h).2.1 c hc)).1
  unfold checkLamports at hl
  by_cases he : c.post.lamports = c.pre.lamports
  · exact he
  · have hne : (c.post.lamports == c.pre.lamports) = false := by simpa using he
    cases ho : c.owned programId <;> cases hlt : decide (c.post.lamports < c.pre.lamports) <;>
      simp [hne, ho, hlt, hr] at hl

/-- Lamports are conserved across unique accounts. -/
theorem lamports_conserved (h : postInstructionCheck programId refs = .ok ()) :
    postLamports (uniqueChanges refs) = entryLamports (uniqueChanges refs) :=
  (postInstructionCheck_ok h).2.2

/-- Existing data changes only in a writable account the program owns. -/
theorem content_change_authorized (h : postInstructionCheck programId refs = .ok ())
    (hc : c ∈ uniqueChanges refs) (hd : c.contentChanged = true) :
    c.isWritable = true ∧ c.pre.owner = programId := by
  have hw := (postInstructionCheck_ok h).1 c hc
  unfold checkDataWrite at hw
  simp only [hd, if_true] at hw
  obtain ⟨h1, h2⟩ := canDataBeChanged_ok hw
  exact ⟨h1, by simpa [AccountChange.owned] using h2⟩

/-- An account grows by at most `MAX_PERMITTED_DATA_INCREASE`. -/
theorem realloc_within_increase (h : postInstructionCheck programId refs = .ok ())
    (hc : c ∈ uniqueChanges refs) :
    c.post.dataLen ≤ c.entry.data.length + MAX_PERMITTED_DATA_INCREASE := by
  have hl := (checkAccount_ok ((postInstructionCheck_ok h).2.1 c hc)).2.1
  unfold checkDataLen at hl
  by_cases hb : c.post.dataLen - c.entry.data.length > MAX_PERMITTED_DATA_INCREASE
  · simp [hb] at hl
  · omega

/-- No account exceeds `MAX_PERMITTED_DATA_LENGTH`. -/
theorem realloc_within_max (h : postInstructionCheck programId refs = .ok ())
    (hc : c ∈ uniqueChanges refs) :
    c.post.dataLen ≤ MAX_PERMITTED_DATA_LENGTH := by
  have hl := (checkAccount_ok ((postInstructionCheck_ok h).2.1 c hc)).2.1
  unfold checkDataLen at hl
  by_cases hb : c.post.dataLen > MAX_PERMITTED_DATA_LENGTH
  · simp [hb] at hl
  · omega

/-- An account's length changes only if it is writable and the program owns it. -/
theorem resize_authorized (h : postInstructionCheck programId refs = .ok ())
    (hc : c ∈ uniqueChanges refs) (hn : c.post.dataLen ≠ c.pre.data.length) :
    c.isWritable = true ∧ c.pre.owner = programId := by
  have hl := (checkAccount_ok ((postInstructionCheck_ok h).2.1 c hc)).2.1
  unfold checkDataLen at hl
  have hne : (c.post.dataLen == c.pre.data.length) = false := by simpa using hn
  split at hl
  · cases hl
  · simp only [hne] at hl
    obtain ⟨h1, h2⟩ := canDataBeChanged_ok (by simpa using hl)
    exact ⟨h1, by simpa [AccountChange.owned] using h2⟩

/-- An owner change needs the old owner to be this program, a writable account,
    and zeroed post-state data. -/
theorem owner_change_authorized (h : postInstructionCheck programId refs = .ok ())
    (hc : c ∈ uniqueChanges refs) (hn : c.post.owner ≠ c.pre.owner) :
    c.pre.owner = programId ∧ c.isWritable = true ∧ ∀ b ∈ c.post.data, b = 0 := by
  have hl := (checkAccount_ok ((postInstructionCheck_ok h).2.1 c hc)).2.2
  unfold checkOwner at hl
  cases ho : c.owned programId <;> cases hw : c.isWritable <;>
    cases hz : c.post.data.all (· == 0) <;> simp [hn, ho, hw, hz] at hl
  refine ⟨by simpa [AccountChange.owned] using ho, rfl, ?_⟩
  intro b hb
  simpa using List.all_eq_true.mp hz b hb

/-- A read-only account keeps its balance, length, existing bytes and owner. -/
theorem readonly_unchanged (h : postInstructionCheck programId refs = .ok ())
    (hc : c ∈ uniqueChanges refs) (hr : c.isWritable = false) :
    c.post.lamports = c.pre.lamports ∧ c.post.dataLen = c.pre.data.length ∧
      c.contentChanged = false ∧ c.post.owner = c.pre.owner := by
  refine ⟨readonly_lamports_unchanged h hc hr, ?_, ?_, ?_⟩
  · apply Classical.byContradiction
    intro hn
    have := (resize_authorized h hc hn).1
    simp [hr] at this
  · cases hd : c.contentChanged with
    | false => rfl
    | true =>
      have := (content_change_authorized h hc hd).1
      simp [hr] at this
  · apply Classical.byContradiction
    intro hn
    have := (owner_change_authorized h hc hn).2.1
    simp [hr] at this

/-- The runtime never takes the executable flag from the program. -/
theorem commit_executable (c : AccountChange) : (commit c).executable = c.entry.executable := rfl

/-- The runtime never takes the rent epoch from the program. -/
theorem commit_rentEpoch (c : AccountChange) : (commit c).rentEpoch = c.entry.rentEpoch := rfl

end Guarantees

/-! ## Common-prefix comparison -/

/-- `contentChanged` means what it says: no difference, no store visible in the
    bytes both states have. -/
theorem prefixDiffers_false_iff :
    ∀ (a b : List UInt8), prefixDiffers a b = false ↔
      a.take (min a.length b.length) = b.take (min a.length b.length)
  | [], b => by simp [prefixDiffers]
  | _ :: _, [] => by simp [prefixDiffers]
  | x :: as, y :: bs => by
    have ih := prefixDiffers_false_iff as bs
    have hmin : min (x :: as).length (y :: bs).length = min as.length bs.length + 1 := by
      simp only [List.length_cons]; omega
    rw [hmin]
    simp only [List.take_succ_cons, List.cons.injEq]
    unfold prefixDiffers
    by_cases hxy : x = y
    · subst hxy; simpa using ih
    · simp [hxy]

/-! ## Duplicate references -/

theorem mergeRef_keys_of_mem {acc : List AccountChange} {c : AccountChange}
    (hk : acc.any (fun a => decide (a.key = c.key)) = true) :
    (mergeRef acc c).map (·.key) = acc.map (·.key) := by
  unfold mergeRef
  simp only [hk, if_true, List.map_map]
  apply List.map_congr_left
  intro a _
  by_cases he : a.key = c.key <;> simp [he]

theorem mergeRef_keys_of_not_mem {acc : List AccountChange} {c : AccountChange}
    (hk : acc.any (fun a => decide (a.key = c.key)) = false) :
    (mergeRef acc c).map (·.key) = acc.map (·.key) ++ [c.key] := by
  unfold mergeRef
  simp [hk]

theorem mergeRef_nodup {acc : List AccountChange} {c : AccountChange}
    (h : (acc.map (·.key)).Nodup) : ((mergeRef acc c).map (·.key)).Nodup := by
  cases hk : acc.any (fun a => decide (a.key = c.key)) with
  | true => rw [mergeRef_keys_of_mem hk]; exact h
  | false =>
    rw [mergeRef_keys_of_not_mem hk]
    refine List.nodup_append.mpr ⟨h, by simp, ?_⟩
    intro a ha b hb hab
    simp only [List.mem_singleton] at hb
    subst hb
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
    have : d.key = c.key := hab
    have hany : acc.any (fun a => decide (a.key = c.key)) = true :=
      List.any_eq_true.mpr ⟨d, hd, by simpa using this⟩
    simp [hk] at hany

/-- Uniqueness: `uniqueChanges` never holds a key twice. -/
theorem uniqueChanges_nodup (refs : List AccountChange) :
    ((uniqueChanges refs).map (·.key)).Nodup := by
  unfold uniqueChanges
  have : ∀ (rs acc : List AccountChange), (acc.map (·.key)).Nodup →
      ((rs.foldl mergeRef acc).map (·.key)).Nodup := by
    intro rs
    induction rs with
    | nil => intro acc h; exact h
    | cons r rs ih => intro acc h; exact ih _ (mergeRef_nodup h)
  exact this refs [] (by simp)

/-- A reference to a known key changes neither lamport total: conservation counts
    accounts, not references. -/
theorem mergeRef_dup_lamports {acc : List AccountChange} {c : AccountChange}
    (hk : acc.any (fun a => decide (a.key = c.key)) = true) :
    entryLamports (mergeRef acc c) = entryLamports acc ∧
      postLamports (mergeRef acc c) = postLamports acc := by
  have hmap : ∀ a : AccountChange,
      (if a.key = c.key then { a with isWritable := a.isWritable || c.isWritable } else a).entry = a.entry ∧
      (if a.key = c.key then { a with isWritable := a.isWritable || c.isWritable } else a).post = a.post := by
    intro a; by_cases he : a.key = c.key <;> simp [he]
  unfold mergeRef entryLamports postLamports
  simp only [hk, if_true, List.map_map]
  constructor
  · congr 1
    apply List.map_congr_left
    intro a _
    simp [(hmap a).1]
  · congr 1
    apply List.map_congr_left
    intro a _
    simp [(hmap a).2]

/-- Every reference's key has its one entry among the unique accounts. -/
theorem key_mem_uniqueChanges {refs : List AccountChange} {r : AccountChange} (hr : r ∈ refs) :
    r.key ∈ (uniqueChanges refs).map (·.key) := by
  unfold uniqueChanges
  have keep : ∀ (acc : List AccountChange) (c : AccountChange) (k : Pubkey),
      k ∈ acc.map (·.key) → k ∈ (mergeRef acc c).map (·.key) := by
    intro acc c k hk
    cases ha : acc.any (fun a => decide (a.key = c.key)) with
    | true => rw [mergeRef_keys_of_mem ha]; exact hk
    | false => rw [mergeRef_keys_of_not_mem ha]; exact List.mem_append_left _ hk
  have adds : ∀ (acc : List AccountChange) (c : AccountChange),
      c.key ∈ (mergeRef acc c).map (·.key) := by
    intro acc c
    cases ha : acc.any (fun a => decide (a.key = c.key)) with
    | true =>
      rw [mergeRef_keys_of_mem ha]
      obtain ⟨d, hd, he⟩ := List.any_eq_true.mp ha
      exact List.mem_map.mpr ⟨d, hd, by simpa using he⟩
    | false => rw [mergeRef_keys_of_not_mem ha]; simp
  have keepAll : ∀ (rs acc : List AccountChange) (k : Pubkey),
      k ∈ acc.map (·.key) → k ∈ (rs.foldl mergeRef acc).map (·.key) := by
    intro rs
    induction rs with
    | nil => intro acc k h; exact h
    | cons x rs ih => intro acc k h; exact ih _ _ (keep _ _ _ h)
  have main : ∀ (rs acc : List AccountChange), r ∈ rs →
      r.key ∈ (rs.foldl mergeRef acc).map (·.key) := by
    intro rs
    induction rs with
    | nil => intro acc h; cases h
    | cons x rs ih =>
      intro acc h
      rw [List.foldl_cons]
      rcases List.mem_cons.mp h with he | h
      · subst he; exact keepAll rs _ _ (adds acc r)
      · exact ih _ h
  exact main refs [] hr

end SVM.Runtime
