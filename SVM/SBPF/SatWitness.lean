/-
  Satisfiability witnesses for qedlift-emitted preconditions.

  H8 hardening: a lifted Hoare triple with an UNSATISFIABLE precondition
  (overlapping ownership atoms) is vacuously true — type-checks, claims nothing.
  qedlift's Rust-side overlap detector is itself unverified; this module closes
  the loop KERNEL-side by emitting, per lift, an

      example : ∃ s, (pre at a concrete assignment) s :=
        SatWitness.sat_witness [reflected atoms] (by native_decide)

  so an unsatisfiable precondition fails `lake build` rather than shipping
  silently — even for overlap classes the Rust detector misses.

  Design: every pre atom is an EXACT-state predicate, so the canonical witness
  is the right-nested union of singleton states and satisfiability reduces to a
  decidable pairwise footprint-disjointness check (`satCheck`), made sound by
  `sat_witness`. The link to the REAL precondition is the elaborator's defeq
  check: `interp atoms` must unify with the rendered pre, so any divergence is a
  type error.

  SCOPE: covers the heap predicate (the sepConj) at one assignment respecting
  the address-defining `h_addr` equations. Value-level path hypotheses
  (`h_branch*`, `h*_lt`) are NOT certified consistent — outside the
  overlap-vacuity class this guards against.
-/

import SVM.SBPF.SepLogic

namespace SVM.SBPF
namespace SatWitness

open PartialState

/-- Reflected form of one qedlift precondition atom (one constructor per
    exact-state assertion the emitter produces). -/
inductive SatAtom where
  | reg (r : Reg) (v : Nat)
  | byte (a v : Nat)
  | u16 (a v : Nat)
  | u32 (a v : Nat)
  | u64 (a v : Nat)
  | bytes32 (a : Nat) (bs : ByteArray)
  | bytes (a : Nat) (bs : ByteArray)
  | pcAt (v : Nat)
  | retData (bs : ByteArray)
  | callStack (cs : List CallFrame)

/-- The assertion a reflected atom denotes. Mirrors the assertion definitions
    exactly (each `fun h => h = SatAtom.state _`), so `pred_state` is `rfl` and
    `interp` is defeq to the rendered pre. -/
def SatAtom.pred : SatAtom → Assertion
  | .reg r v      => regIs r v
  | .byte a v     => memByteIs a v
  | .u16 a v      => memU16Is a v
  | .u32 a v      => memU32Is a v
  | .u64 a v      => memU64Is a v
  | .bytes32 a bs => memBytes32Is a bs
  | .bytes a bs   => memBytesIs a bs
  | .pcAt v       => pcIs v
  | .retData bs   => returnDataIs bs
  | .callStack cs => callStackIs cs

/-- The unique partial state satisfying the atom's assertion. -/
def SatAtom.state : SatAtom → PartialState
  | .reg r v      => singletonReg r v
  | .byte a v     => singletonMem a v
  | .u16 a v      => singletonMemU16 a v
  | .u32 a v      => singletonMemU32 a v
  | .u64 a v      => singletonMemU64 a v
  | .bytes32 a bs => singletonMem32Bytes a bs
  | .bytes a bs   => singletonMemBytes a bs
  | .pcAt v       => singletonPC v
  | .retData bs   => singletonReturnData bs
  | .callStack cs => singletonCallStack cs

theorem SatAtom.pred_state (x : SatAtom) : x.pred x.state := by
  cases x <;> rfl

/-! ## Footprints

One footprint projection per `PartialState` field; the domain lemmas tie them
to the singleton definitions. -/

/-- Memory footprint `(start, length)`; `(0, 0)` for non-memory atoms
    (and the empty blob, which owns nothing). -/
def SatAtom.memFoot : SatAtom → Nat × Nat
  | .byte a _     => (a, 1)
  | .u16 a _      => (a, 2)
  | .u32 a _      => (a, 4)
  | .u64 a _      => (a, 8)
  | .bytes32 a _  => (a, 32)
  | .bytes a bs   => (a, bs.size)
  | _             => (0, 0)

/-- Register footprint. -/
def SatAtom.regFoot : SatAtom → Option Reg
  | .reg r _ => some r
  | _        => none

def SatAtom.pcFoot : SatAtom → Bool
  | .pcAt _ => true
  | _       => false

def SatAtom.rdFoot : SatAtom → Bool
  | .retData _ => true
  | _          => false

def SatAtom.csFoot : SatAtom → Bool
  | .callStack _ => true
  | _            => false

/-! ## Domain lemmas: owned resources lie inside the footprint -/

theorem SatAtom.mem_dom (x : SatAtom) (n : Nat)
    (h : x.state.mem n ≠ none) :
    x.memFoot.1 ≤ n ∧ n < x.memFoot.1 + x.memFoot.2 := by
  cases x with
  | reg r v       => exact absurd rfl h
  | pcAt v        => exact absurd rfl h
  | retData bs    => exact absurd rfl h
  | callStack cs  => exact absurd rfl h
  | byte a v =>
      simp only [state, singletonMem, memFoot] at h ⊢
      split at h
      · omega
      · exact absurd rfl h
  | u16 a v =>
      simp only [state, singletonMemU16, memFoot] at h ⊢
      repeat' split at h
      all_goals first | omega | exact absurd rfl h
  | u32 a v =>
      simp only [state, singletonMemU32, memFoot] at h ⊢
      repeat' split at h
      all_goals first | omega | exact absurd rfl h
  | u64 a v =>
      simp only [state, singletonMemU64, memFoot] at h ⊢
      repeat' split at h
      all_goals first | omega | exact absurd rfl h
  | bytes32 a bs =>
      simp only [state, singletonMem32Bytes, memFoot] at h ⊢
      split at h
      · next hin => omega
      · exact absurd rfl h
  | bytes a bs =>
      simp only [state, singletonMemBytes, memFoot] at h ⊢
      split at h
      · next hin => omega
      · exact absurd rfl h

theorem SatAtom.reg_dom (x : SatAtom) (r : Reg)
    (h : x.state.regs r ≠ none) : x.regFoot = some r := by
  cases x with
  | reg r' v =>
      simp only [state, singletonReg, regFoot] at h ⊢
      split at h
      · next heq => rw [heq]
      · exact absurd rfl h
  | byte a v      => exact absurd rfl h
  | u16 a v       => exact absurd rfl h
  | u32 a v       => exact absurd rfl h
  | u64 a v       => exact absurd rfl h
  | bytes32 a bs  => exact absurd rfl h
  | bytes a bs    => exact absurd rfl h
  | pcAt v        => exact absurd rfl h
  | retData bs    => exact absurd rfl h
  | callStack cs  => exact absurd rfl h

theorem SatAtom.pc_dom (x : SatAtom) (h : x.state.pc ≠ none) :
    x.pcFoot = true := by
  cases x <;> first | rfl | exact absurd rfl h

theorem SatAtom.rd_dom (x : SatAtom) (h : x.state.returnData ≠ none) :
    x.rdFoot = true := by
  cases x <;> first | rfl | exact absurd rfl h

theorem SatAtom.cs_dom (x : SatAtom) (h : x.state.callStack ≠ none) :
    x.csFoot = true := by
  cases x <;> first | rfl | exact absurd rfl h

/-! ## The decidable pairwise check -/

/-- Memory footprints don't overlap (empty footprints never overlap). -/
def memSep (x y : SatAtom) : Bool :=
  x.memFoot.2 == 0 || y.memFoot.2 == 0 ||
  decide (x.memFoot.1 + x.memFoot.2 ≤ y.memFoot.1) ||
  decide (y.memFoot.1 + y.memFoot.2 ≤ x.memFoot.1)

/-- Register footprints differ (or at least one atom owns no register). -/
def regSep (x y : SatAtom) : Bool :=
  match x.regFoot, y.regFoot with
  | some ra, some rb => decide (ra ≠ rb)
  | _, _ => true

/-- Two atoms own disjoint resources. -/
def pairOk (x y : SatAtom) : Bool :=
  memSep x y && regSep x y &&
  !(x.pcFoot && y.pcFoot) && !(x.rdFoot && y.rdFoot) &&
  !(x.csFoot && y.csFoot)

/-- Every pair of atoms in the list is disjoint. -/
def satCheck : List SatAtom → Bool
  | [] => true
  | x :: rest => rest.all (pairOk x) && satCheck rest

/-! ## Soundness -/

theorem disjoint_of_pairOk {x y : SatAtom} (h : pairOk x y = true) :
    x.state.Disjoint y.state := by
  simp only [pairOk, Bool.and_eq_true, Bool.not_eq_true',
             Bool.and_eq_false_iff] at h
  obtain ⟨⟨⟨⟨hmem, hreg⟩, hpc⟩, hrd⟩, hcs⟩ := h
  constructor
  · -- regs
    intro r
    cases h1 : x.state.regs r with
    | none => exact .inl rfl
    | some v =>
      cases h2 : y.state.regs r with
      | none => exact .inr rfl
      | some w =>
        have d1 := x.reg_dom r (by simp [h1])
        have d2 := y.reg_dom r (by simp [h2])
        rw [regSep, d1, d2] at hreg
        simp only [decide_eq_true_eq] at hreg
        exact absurd rfl hreg
  · -- mem
    intro a
    cases h1 : x.state.mem a with
    | none => exact .inl rfl
    | some v =>
      cases h2 : y.state.mem a with
      | none => exact .inr rfl
      | some w =>
        have d1 := x.mem_dom a (by simp [h1])
        have d2 := y.mem_dom a (by simp [h2])
        simp only [memSep, Bool.or_eq_true, beq_iff_eq,
                   decide_eq_true_eq] at hmem
        omega
  · -- pc
    cases h1 : x.state.pc with
    | none => exact .inl rfl
    | some v =>
      cases h2 : y.state.pc with
      | none => exact .inr rfl
      | some w =>
        have d1 := x.pc_dom (by simp [h1])
        have d2 := y.pc_dom (by simp [h2])
        rw [d1, d2] at hpc
        simp at hpc
  · -- returnData
    cases h1 : x.state.returnData with
    | none => exact .inl rfl
    | some v =>
      cases h2 : y.state.returnData with
      | none => exact .inr rfl
      | some w =>
        have d1 := x.rd_dom (by simp [h1])
        have d2 := y.rd_dom (by simp [h2])
        rw [d1, d2] at hrd
        simp at hrd
  · -- callStack
    cases h1 : x.state.callStack with
    | none => exact .inl rfl
    | some v =>
      cases h2 : y.state.callStack with
      | none => exact .inr rfl
      | some w =>
        have d1 := x.cs_dom (by simp [h1])
        have d2 := y.cs_dom (by simp [h2])
        rw [d1, d2] at hcs
        simp at hcs

/-- Right-nested union of the atoms' singleton states — the canonical satisfying
    heap, mirroring `interp`'s nesting. -/
def statesUnion : List SatAtom → PartialState
  | [] => PartialState.empty
  | [x] => x.state
  | x :: rest => x.state.union (statesUnion rest)

theorem disjoint_statesUnion {x : SatAtom} :
    {rest : List SatAtom} → rest.all (pairOk x) = true →
    x.state.Disjoint (statesUnion rest)
  | [], _ => Disjoint_empty_right
  | [y], h => by
      simp only [List.all_cons, List.all_nil, Bool.and_eq_true] at h
      exact disjoint_of_pairOk h.1
  | y :: z :: rest, h => by
      simp only [List.all_cons, Bool.and_eq_true] at h
      have h1 := disjoint_of_pairOk h.1
      have h2 : ((z :: rest).all (pairOk x)) = true := by
        simp only [List.all_cons, Bool.and_eq_true]
        exact ⟨h.2.1, h.2.2⟩
      exact (Disjoint_union_of_both h1.symm
              (disjoint_statesUnion h2).symm).symm

/-- The assertion a reflected atom LIST denotes: the right-nested separating
    conjunction. Defeq to the qedlift-rendered precondition at a concrete
    assignment. -/
def interp : List SatAtom → Assertion
  | [] => emp
  | [x] => x.pred
  | x :: rest => x.pred ** interp rest

theorem sat_sound : (atoms : List SatAtom) → satCheck atoms = true →
    interp atoms (statesUnion atoms)
  | [], _ => rfl
  | [x], _ => x.pred_state
  | x :: y :: rest, h => by
      -- `satCheck (x :: y :: rest)` is DEFEQ to the `&&`; `simp [satCheck]`
      -- would unfold the recursion all the way, so avoid it.
      have h' : ((y :: rest).all (pairOk x) && satCheck (y :: rest)) = true := h
      rw [Bool.and_eq_true] at h'
      exact ⟨x.state, statesUnion (y :: rest),
             disjoint_statesUnion h'.1, rfl,
             x.pred_state, sat_sound (y :: rest) h'.2⟩

/-- The H8 vacuity gate: a `true` pairwise-disjointness check yields a satisfying
    heap for the whole sepConj. qedlift emits one per lift; the elaborator's defeq
    check ties `interp atoms` to the rendered precondition. -/
theorem sat_witness (atoms : List SatAtom) (h : satCheck atoms = true) :
    ∃ s, interp atoms s :=
  ⟨statesUnion atoms, sat_sound atoms h⟩

/-! ## Shape self-tests

Pin the defeq bridge `interp [..] =?= (rendered pre)` on each atom form
(incl. `effectiveAddr`-shaped addresses reducing against the reflected
literal). -/

open Memory in
example : ∃ s,
    ((.r1 ↦ᵣ 5) **
      ((effectiveAddr 4096 8 ↦U64 7) **
        ((effectiveAddr 4096 (-8) ↦ₘ 3) **
          (callStackIs [])))) s :=
  sat_witness [.reg .r1 5, .u64 4104 7, .byte 4088 3, .callStack []]
    (by native_decide)

open Memory in
example : ∃ s, ((effectiveAddr 4096 0 + 2 ↦U16 9) ** (8192 ↦Bytes ByteArray.empty)) s :=
  sat_witness [.u16 4098 9, .bytes 8192 ByteArray.empty] (by native_decide)

/-- Overlap is rejected: two dword cells 4 bytes apart fail `satCheck` (the H8
    vacuity class). -/
example : satCheck [.u64 4096 0, .u64 4100 0] = false := by native_decide

end SatWitness
end SVM.SBPF
