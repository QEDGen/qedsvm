/-
  Solana-native MIR — Direction A (qedgen issue #66).

  Pilot scope: a single intrinsic, `tokenTransfer`. The MIR grows by
  adding constructors here + abstract triples in
  `Svm/Solana/Abstract/Triples.lean` + refinement lemmas in
  `Svm/Solana/Abstract/Refinement.lean`. Each addition is local: the
  surrounding machinery (`runMir`'s sequencing, the SL frame rule)
  doesn't change.

  Soundness invariant for every intrinsic added here: MIR's failure
  modes must be a **subset** of the asm-side failure modes for the
  refining codegen pattern. If MIR fails on case X but the asm
  silently succeeds, refinement is unsound — the user-facing triple
  needs to declare X as a precondition rather than have MIR error
  on it.

  Why `tokenTransfer` errors on `src = dst`: SPL Token's unchecked
  Transfer would silently no-op the self case, but modeling that
  cleanly requires the second update to re-read state instead of
  reusing the captured `tTo`. The pilot's downstream proof has a
  disjointness precondition (`h_disjoint`) that implies `src ≠ dst`,
  so the self case is excluded by the caller; we surface it as an
  explicit MIR error so the precondition is visible in the spec.
  A future `TokenTransferAllowingSelf` intrinsic can model the
  no-op semantics if a user-spec actually needs it.
-/

import Svm.Solana.Abstract.State

namespace Svm.Solana.Abstract

open Svm.Account

/-! ## MirError -/

/-- Failure modes of `runMir`. Each constructor names the offending
    key (or the impossible-state shape) so error-case proofs and
    counterexamples are localised. -/
inductive MirError where
  | accountMissing    (key : Pubkey)
  | selfTransfer
  | insufficientFunds (key : Pubkey) (have_ : Nat) (want : Nat)
  | overflow          (key : Pubkey)
  deriving Inhabited

/-! ## MirStmt — one intrinsic per constructor

Add new intrinsics here. Each addition needs:
  1. A constructor below.
  2. A clause in `runStep`.
  3. An abstract triple in `Svm/Solana/Abstract/Triples.lean`.
  4. A refinement lemma in `Svm/Solana/Abstract/Refinement.lean`
     before the intrinsic can be cited from user-facing theorems. -/

inductive MirStmt where
  /-- Transfer `amount` units of a fungible token from the account at
      `src` to the account at `dst`. Errors on missing accounts,
      self-transfer (`src = dst`; see file docstring), insufficient
      funds, or u64 overflow on the destination. Mint equality is
      *not* enforced — matches the on-chain semantics of SPL Token's
      unchecked Transfer. -/
  | tokenTransfer (src dst : Pubkey) (amount : Nat)
  deriving Inhabited

/-! ## runStep — operational semantics for one MIR statement -/

/-- Execute a single MIR statement against the abstract heap.
    Pure function — no syscalls, no CU. -/
def runStep (stmt : MirStmt) (s : AbstractState) :
    Except MirError AbstractState :=
  match stmt with
  | .tokenTransfer src dst amount =>
    match s.get src, s.get dst with
    | none,        _           => .error (.accountMissing src)
    | some _,      none        => .error (.accountMissing dst)
    | some tSrc,   some tDst   =>
      if src = dst then .error .selfTransfer
      else if amount > tSrc.amount then
        .error (.insufficientFunds src tSrc.amount amount)
      else if tDst.amount + amount ≥ 2 ^ 64 then
        .error (.overflow dst)
      else
        let s1 := s.set src (tSrc.withAmount (tSrc.amount - amount))
        let s2 := s1.set dst (tDst.withAmount (tDst.amount + amount))
        .ok s2

/-! ## runMir — sequence of statements

Sequencing is "stop on first error" — standard Except-monad semantics.
The shape `match runStep ... | .ok | .error` keeps the recursion
structurally obvious to Lean's termination checker. -/

def runMir : List MirStmt → AbstractState → Except MirError AbstractState
  | [],        s => .ok s
  | stmt :: rest, s =>
    match runStep stmt s with
    | .ok s'   => runMir rest s'
    | .error e => .error e

/-! ## Basic equational lemmas -/

@[simp] theorem runMir_nil (s : AbstractState) :
    runMir [] s = .ok s := rfl

@[simp] theorem runMir_cons_ok (stmt : MirStmt) (rest : List MirStmt)
    (s s' : AbstractState) (h : runStep stmt s = .ok s') :
    runMir (stmt :: rest) s = runMir rest s' := by
  show (match runStep stmt s with
        | .ok s' => runMir rest s'
        | .error e => .error e) = runMir rest s'
  rw [h]

@[simp] theorem runMir_cons_error (stmt : MirStmt) (rest : List MirStmt)
    (s : AbstractState) (e : MirError) (h : runStep stmt s = .error e) :
    runMir (stmt :: rest) s = .error e := by
  show (match runStep stmt s with
        | .ok s' => runMir rest s'
        | .error e => .error e) = .error e
  rw [h]

@[simp] theorem runMir_singleton (stmt : MirStmt) (s : AbstractState) :
    runMir [stmt] s = runStep stmt s := by
  show (match runStep stmt s with
        | .ok s' => runMir [] s'
        | .error e => .error e) = runStep stmt s
  cases runStep stmt s <;> rfl

end Svm.Solana.Abstract
