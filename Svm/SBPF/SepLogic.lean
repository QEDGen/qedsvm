/-
  Separation logic over sBPF machine state.

  Following Kennedy et al. (2013) and the EvmAsm.Rv64.SepLogic adaptation
  in Verified-zkEVM/evm-asm: registers, memory bytes, and the program
  counter are separable resources. An `Assertion` is a predicate on a
  `PartialState` (a partial heap that owns some subset of those resources).
  The separating conjunction `P ** Q` holds when the partial state splits
  into two disjoint pieces, with `P` holding on one and `Q` on the other.

  The bridge to the executable `State` from `Svm.SBPF.Execute` is
  `Assertion.holdsFor`: an assertion holds for a full machine state when
  some partial state compatible with the full state satisfies it.

  Memory is byte-level. Multi-byte (u64) assertions are built from byte
  points-to via `**`.
-/

import Svm.SBPF.Execute

namespace Svm.SBPF

/-! ## PartialState — partial ownership of registers, memory, PC -/

/-- A partial view of an sBPF machine state. `some v` means we own the
    resource and assert its value is `v`; `none` means we don't own it. -/
structure PartialState where
  regs : Reg → Option Nat
  mem  : Nat → Option Nat
  pc   : Option Nat
  deriving Inhabited

namespace PartialState

/-- The empty partial state owns nothing. -/
def empty : PartialState :=
  { regs := fun _ => none, mem := fun _ => none, pc := none }

/-- Partial state owning exactly one register. -/
def singletonReg (r : Reg) (v : Nat) : PartialState :=
  { regs := fun r' => if r' = r then some v else none
    mem  := fun _ => none
    pc   := none }

/-- Partial state owning exactly one memory byte. -/
def singletonMem (a v : Nat) : PartialState :=
  { regs := fun _ => none
    mem  := fun a' => if a' = a then some v else none
    pc   := none }

/-- Partial state owning exactly the PC. -/
def singletonPC (v : Nat) : PartialState :=
  { regs := fun _ => none
    mem  := fun _ => none
    pc   := some v }

/-- Two partial states are disjoint if they never both own the same resource. -/
def Disjoint (h1 h2 : PartialState) : Prop :=
  (∀ r, h1.regs r = none ∨ h2.regs r = none) ∧
  (∀ a, h1.mem  a = none ∨ h2.mem  a = none) ∧
  (h1.pc = none ∨ h2.pc = none)

/-- Left-biased union of two partial states. -/
def union (h1 h2 : PartialState) : PartialState where
  regs := fun r => match h1.regs r with | some v => some v | none => h2.regs r
  mem  := fun a => match h1.mem  a with | some v => some v | none => h2.mem  a
  pc   := match h1.pc with | some v => some v | none => h2.pc

/-- A partial state is compatible with a full machine state if every
    owned resource agrees with the full state. -/
def CompatibleWith (h : PartialState) (s : State) : Prop :=
  (∀ r v, h.regs r = some v → s.regs.get r = v) ∧
  (∀ a v, h.mem  a = some v → s.mem a = v) ∧
  (∀ v,   h.pc   = some v → s.pc = v)

/-! ## Disjoint lemmas -/

theorem Disjoint.symm {h1 h2 : PartialState} (hd : h1.Disjoint h2) :
    h2.Disjoint h1 := by
  obtain ⟨hr, hm, hpc⟩ := hd
  exact ⟨fun r => (hr r).symm, fun a => (hm a).symm, hpc.symm⟩

/-! ## Singleton projection lemmas -/

@[simp] theorem singletonReg_regs_self {r : Reg} {v : Nat} :
    (singletonReg r v).regs r = some v := by
  unfold singletonReg; simp

@[simp] theorem singletonReg_regs_other {r r' : Reg} {v : Nat} (h : r' ≠ r) :
    (singletonReg r v).regs r' = none := by
  unfold singletonReg; simp [h]

@[simp] theorem singletonReg_mem {r : Reg} {v : Nat} (a : Nat) :
    (singletonReg r v).mem a = none := rfl

@[simp] theorem singletonReg_pc {r : Reg} {v : Nat} :
    (singletonReg r v).pc = none := rfl

@[simp] theorem singletonMem_regs {a v : Nat} (r : Reg) :
    (singletonMem a v).regs r = none := rfl

@[simp] theorem singletonMem_mem_self {a v : Nat} :
    (singletonMem a v).mem a = some v := by
  unfold singletonMem; simp

@[simp] theorem singletonMem_mem_other {a a' v : Nat} (h : a' ≠ a) :
    (singletonMem a v).mem a' = none := by
  unfold singletonMem; simp [h]

@[simp] theorem singletonMem_pc {a v : Nat} :
    (singletonMem a v).pc = none := rfl

@[simp] theorem empty_regs (r : Reg) : empty.regs r = none := rfl
@[simp] theorem empty_mem (a : Nat) : empty.mem a = none := rfl
@[simp] theorem empty_pc : empty.pc = none := rfl

theorem Disjoint_empty_left {h : PartialState} : empty.Disjoint h := by
  refine ⟨fun _ => Or.inl rfl, fun _ => Or.inl rfl, Or.inl rfl⟩

theorem Disjoint_empty_right {h : PartialState} : h.Disjoint empty :=
  Disjoint_empty_left.symm

/-! ## Field-projection helpers for `union`.

These extract the value of each field of `union h1 h2` under known
field-level conditions, sidestepping the need to reduce a `match` by
hand in larger proofs. -/

theorem union_regs_of_left_none {h1 h2 : PartialState} {r : Reg}
    (h : h1.regs r = none) : (h1.union h2).regs r = h2.regs r := by
  show (match h1.regs r with | some v => some v | none => h2.regs r) = h2.regs r
  rw [h]

theorem union_regs_of_left_some {h1 h2 : PartialState} {r : Reg} {v : Nat}
    (h : h1.regs r = some v) : (h1.union h2).regs r = some v := by
  show (match h1.regs r with | some v => some v | none => h2.regs r) = some v
  rw [h]

theorem union_mem_of_left_none {h1 h2 : PartialState} {a : Nat}
    (h : h1.mem a = none) : (h1.union h2).mem a = h2.mem a := by
  show (match h1.mem a with | some v => some v | none => h2.mem a) = h2.mem a
  rw [h]

theorem union_mem_of_left_some {h1 h2 : PartialState} {a v : Nat}
    (h : h1.mem a = some v) : (h1.union h2).mem a = some v := by
  show (match h1.mem a with | some v => some v | none => h2.mem a) = some v
  rw [h]

theorem union_pc_of_left_none {h1 h2 : PartialState}
    (h : h1.pc = none) : (h1.union h2).pc = h2.pc := by
  show (match h1.pc with | some v => some v | none => h2.pc) = h2.pc
  rw [h]

theorem union_pc_of_left_some {h1 h2 : PartialState} {v : Nat}
    (h : h1.pc = some v) : (h1.union h2).pc = some v := by
  show (match h1.pc with | some v => some v | none => h2.pc) = some v
  rw [h]

/-! ## Union lemmas -/

theorem union_empty_left {h : PartialState} : empty.union h = h := by
  cases h
  rfl

theorem union_empty_right {h : PartialState} : h.union empty = h := by
  obtain ⟨regs, mem, pc⟩ := h
  show PartialState.mk _ _ _ = _
  simp only [PartialState.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext r; cases regs r <;> rfl
  · funext a; cases mem  a <;> rfl
  · cases pc <;> rfl

theorem union_comm_of_disjoint {h1 h2 : PartialState} (hd : h1.Disjoint h2) :
    h1.union h2 = h2.union h1 := by
  obtain ⟨hr, hm, hpc⟩ := hd
  show PartialState.mk _ _ _ = PartialState.mk _ _ _
  simp only [PartialState.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext r
    rcases hr r with h | h
    · rw [h]; cases h2.regs r <;> rfl
    · rw [h]; cases h1.regs r <;> rfl
  · funext a
    rcases hm a with h | h
    · rw [h]; cases h2.mem a <;> rfl
    · rw [h]; cases h1.mem a <;> rfl
  · rcases hpc with h | h
    · rw [h]; cases h2.pc <;> rfl
    · rw [h]; cases h1.pc <;> rfl

/-! ## Field-level "owned by union iff owned by either" lemmas -/

theorem union_regs_eq_none_iff {h1 h2 : PartialState} {r : Reg} :
    (h1.union h2).regs r = none ↔ h1.regs r = none ∧ h2.regs r = none := by
  show (match h1.regs r with | some v => some v | none => h2.regs r) = none ↔ _
  cases h1.regs r
  · cases h2.regs r <;> simp
  · simp

theorem union_mem_eq_none_iff {h1 h2 : PartialState} {a : Nat} :
    (h1.union h2).mem a = none ↔ h1.mem a = none ∧ h2.mem a = none := by
  show (match h1.mem a with | some v => some v | none => h2.mem a) = none ↔ _
  cases h1.mem a
  · cases h2.mem a <;> simp
  · simp

theorem union_pc_eq_none_iff {h1 h2 : PartialState} :
    (h1.union h2).pc = none ↔ h1.pc = none ∧ h2.pc = none := by
  show (match h1.pc with | some v => some v | none => h2.pc) = none ↔ _
  cases h1.pc
  · cases h2.pc <;> simp
  · simp

/-! ## Union associativity -/

theorem union_assoc {h1 h2 h3 : PartialState} :
    h1.union (h2.union h3) = (h1.union h2).union h3 := by
  obtain ⟨r1, m1, p1⟩ := h1
  obtain ⟨r2, m2, p2⟩ := h2
  obtain ⟨r3, m3, p3⟩ := h3
  show PartialState.mk _ _ _ = PartialState.mk _ _ _
  simp only [PartialState.mk.injEq, union]
  refine ⟨?_, ?_, ?_⟩
  · funext r; cases r1 r <;> cases r2 r <;> cases r3 r <;> rfl
  · funext a; cases m1 a <;> cases m2 a <;> cases m3 a <;> rfl
  · cases p1 <;> cases p2 <;> cases p3 <;> rfl

/-! ## Disjoint redistribution under union -/

theorem Disjoint_of_union_left {h1 h2 h3 : PartialState}
    (hd : (h1.union h2).Disjoint h3) : h1.Disjoint h3 := by
  obtain ⟨hr, hm, hpc⟩ := hd
  refine ⟨fun r => ?_, fun a => ?_, ?_⟩
  · rcases hr r with hl | hl
    · left; exact (union_regs_eq_none_iff.mp hl).1
    · right; exact hl
  · rcases hm a with hl | hl
    · left; exact (union_mem_eq_none_iff.mp hl).1
    · right; exact hl
  · rcases hpc with hl | hl
    · left; exact union_pc_eq_none_iff.mp hl |>.1
    · right; exact hl

theorem Disjoint_of_union_right {h1 h2 h3 : PartialState}
    (hd : (h1.union h2).Disjoint h3) : h2.Disjoint h3 := by
  obtain ⟨hr, hm, hpc⟩ := hd
  refine ⟨fun r => ?_, fun a => ?_, ?_⟩
  · rcases hr r with hl | hl
    · left; exact (union_regs_eq_none_iff.mp hl).2
    · right; exact hl
  · rcases hm a with hl | hl
    · left; exact (union_mem_eq_none_iff.mp hl).2
    · right; exact hl
  · rcases hpc with hl | hl
    · left; exact union_pc_eq_none_iff.mp hl |>.2
    · right; exact hl

theorem Disjoint_union_of_both {h1 h2 h3 : PartialState}
    (hd1 : h1.Disjoint h3) (hd2 : h2.Disjoint h3) : (h1.union h2).Disjoint h3 := by
  obtain ⟨hr1, hm1, hpc1⟩ := hd1
  obtain ⟨hr2, hm2, hpc2⟩ := hd2
  refine ⟨fun r => ?_, fun a => ?_, ?_⟩
  · rcases hr1 r with hl | hl <;> rcases hr2 r with hl' | hl'
    · left; exact union_regs_eq_none_iff.mpr ⟨hl, hl'⟩
    · right; exact hl'
    · right; exact hl
    · right; exact hl
  · rcases hm1 a with hl | hl <;> rcases hm2 a with hl' | hl'
    · left; exact union_mem_eq_none_iff.mpr ⟨hl, hl'⟩
    · right; exact hl'
    · right; exact hl
    · right; exact hl
  · rcases hpc1 with hl | hl <;> rcases hpc2 with hl' | hl'
    · left; exact union_pc_eq_none_iff.mpr ⟨hl, hl'⟩
    · right; exact hl'
    · right; exact hl
    · right; exact hl

theorem Disjoint_symm_of_union_left {h1 h2 h3 : PartialState}
    (hd : h1.Disjoint (h2.union h3)) : h1.Disjoint h2 :=
  (Disjoint_of_union_left hd.symm).symm

theorem Disjoint_symm_of_union_right {h1 h2 h3 : PartialState}
    (hd : h1.Disjoint (h2.union h3)) : h1.Disjoint h3 :=
  (Disjoint_of_union_right hd.symm).symm

end PartialState

/-! ## Assertions -/

/-- An assertion is a predicate on partial states. -/
abbrev Assertion := PartialState → Prop

/-- Separating conjunction: `P ** Q` holds on a partial state that splits
    into two disjoint pieces satisfying `P` and `Q` respectively. -/
def sepConj (P Q : Assertion) : Assertion :=
  fun h => ∃ h1 h2, h1.Disjoint h2 ∧ h1.union h2 = h ∧ P h1 ∧ Q h2

@[inherit_doc] infixr:35 " ** " => sepConj

/-- The empty assertion: holds only on the empty partial state. -/
def emp : Assertion := fun h => h = PartialState.empty

/-- Register `r` holds value `v`, and that's all we own. -/
def regIs (r : Reg) (v : Nat) : Assertion :=
  fun h => h = PartialState.singletonReg r v

@[inherit_doc] notation:50 r " ↦ᵣ " v => regIs r v

/-- Memory byte at `a` holds value `v` (treated mod 256), and that's all we own. -/
def memByteIs (a v : Nat) : Assertion :=
  fun h => h = PartialState.singletonMem a v

@[inherit_doc] notation:50 a " ↦ₘ " v => memByteIs a v

/-- The PC holds value `v`, and that's all we own. -/
def pcIs (v : Nat) : Assertion :=
  fun h => h = PartialState.singletonPC v

/-! ## Structural lemmas for `**` -/

theorem sepConj_comm {P Q : Assertion} :
    ∀ h, (P ** Q) h ↔ (Q ** P) h := by
  intro h
  constructor
  · rintro ⟨h1, h2, hd, hu, hP, hQ⟩
    refine ⟨h2, h1, hd.symm, ?_, hQ, hP⟩
    rw [← hu]; exact (PartialState.union_comm_of_disjoint hd).symm
  · rintro ⟨h1, h2, hd, hu, hQ, hP⟩
    refine ⟨h2, h1, hd.symm, ?_, hP, hQ⟩
    rw [← hu]; exact (PartialState.union_comm_of_disjoint hd).symm

theorem sepConj_emp_left {P : Assertion} :
    ∀ h, (emp ** P) h ↔ P h := by
  intro h
  constructor
  · rintro ⟨h1, h2, _, hu, hemp, hP⟩
    rw [show h1 = PartialState.empty from hemp] at hu
    rw [PartialState.union_empty_left] at hu
    rwa [← hu]
  · intro hP
    exact ⟨PartialState.empty, h, PartialState.Disjoint_empty_left,
           PartialState.union_empty_left, rfl, hP⟩

theorem sepConj_emp_right {P : Assertion} :
    ∀ h, (P ** emp) h ↔ P h := by
  intro h
  rw [sepConj_comm]
  exact sepConj_emp_left h

/-- Separating conjunction is associative: `(P ** Q) ** R ↔ P ** (Q ** R)`. -/
theorem sepConj_assoc {P Q R : Assertion} :
    ∀ h, ((P ** Q) ** R) h ↔ (P ** (Q ** R)) h := by
  intro h
  constructor
  · rintro ⟨h_PQ, h_R, hd_PQR, hu_PQR, ⟨h_P, h_Q, hd_PQ, hu_PQ, hP, hQ⟩, hR⟩
    -- h_PQ = h_P ⊎ h_Q. Build h_QR := h_Q ⊎ h_R.
    have hd_PQR' : (h_P.union h_Q).Disjoint h_R := hu_PQ ▸ hd_PQR
    have hd_PR : h_P.Disjoint h_R := PartialState.Disjoint_of_union_left hd_PQR'
    have hd_QR : h_Q.Disjoint h_R := PartialState.Disjoint_of_union_right hd_PQR'
    have hd_P_QR : h_P.Disjoint (h_Q.union h_R) :=
      (PartialState.Disjoint_union_of_both hd_PQ.symm hd_PR.symm).symm
    refine ⟨h_P, h_Q.union h_R, hd_P_QR, ?_, hP,
            ⟨h_Q, h_R, hd_QR, rfl, hQ, hR⟩⟩
    rw [PartialState.union_assoc, hu_PQ]; exact hu_PQR
  · rintro ⟨h_P, h_QR, hd_P_QR, hu_P_QR, hP, ⟨h_Q, h_R, hd_QR, hu_QR, hQ, hR⟩⟩
    have hd_P_QR' : h_P.Disjoint (h_Q.union h_R) := hu_QR ▸ hd_P_QR
    have hd_PQ : h_P.Disjoint h_Q := PartialState.Disjoint_symm_of_union_left hd_P_QR'
    have hd_PR : h_P.Disjoint h_R := PartialState.Disjoint_symm_of_union_right hd_P_QR'
    have hd_PQ_R : (h_P.union h_Q).Disjoint h_R :=
      PartialState.Disjoint_union_of_both hd_PR hd_QR
    refine ⟨h_P.union h_Q, h_R, hd_PQ_R, ?_, ⟨h_P, h_Q, hd_PQ, rfl, hP, hQ⟩, hR⟩
    rw [← PartialState.union_assoc, hu_QR]; exact hu_P_QR

/-! ## holdsFor — bridge from Assertion to full State -/

/-- An assertion `P` holds for full state `s` when some partial state
    compatible with `s` satisfies `P`. -/
def Assertion.holdsFor (P : Assertion) (s : State) : Prop :=
  ∃ h : PartialState, h.CompatibleWith s ∧ P h

/-- `holdsFor` respects pointwise equivalence: if two assertions are
    equivalent on every partial state, they hold for the same full states. -/
theorem holdsFor_iff_pointwise {P Q : Assertion} {s : State}
    (h : ∀ h, P h ↔ Q h) : P.holdsFor s ↔ Q.holdsFor s := by
  unfold Assertion.holdsFor
  exact ⟨fun ⟨hp, hc, hP⟩ => ⟨hp, hc, (h hp).mp hP⟩,
         fun ⟨hp, hc, hQ⟩ => ⟨hp, hc, (h hp).mpr hQ⟩⟩

/-- `holdsFor` lifts `sepConj_assoc`. -/
theorem holdsFor_sepConj_assoc {P Q R : Assertion} {s : State} :
    ((P ** Q) ** R).holdsFor s ↔ (P ** (Q ** R)).holdsFor s :=
  holdsFor_iff_pointwise sepConj_assoc

/-- `holdsFor` lifts `sepConj_comm`. -/
theorem holdsFor_sepConj_comm {P Q : Assertion} {s : State} :
    (P ** Q).holdsFor s ↔ (Q ** P).holdsFor s :=
  holdsFor_iff_pointwise sepConj_comm

/-! ## pcFree — assertion does not own the PC -/

/-- An assertion is *pc-free* when no satisfying partial state owns the PC.
    This is the side-condition used as a frame in `cuTripleWithin` so that
    incrementing the PC doesn't invalidate the frame. -/
def Assertion.pcFree (P : Assertion) : Prop :=
  ∀ h, P h → h.pc = none

theorem pcFree_emp : (emp : Assertion).pcFree := by
  intro h heq; rw [heq]; rfl

theorem pcFree_regIs (r : Reg) (v : Nat) : (regIs r v).pcFree := by
  intro h heq; rw [heq]; rfl

theorem pcFree_memByteIs (a v : Nat) : (memByteIs a v).pcFree := by
  intro h heq; rw [heq]; rfl

theorem pcFree_sepConj {P Q : Assertion} (hP : P.pcFree) (hQ : Q.pcFree) :
    (P ** Q).pcFree := by
  rintro h ⟨h1, h2, _, hu, hP1, hQ2⟩
  rw [← hu, PartialState.union_pc_of_left_none (hP _ hP1)]
  exact hQ _ hQ2

end Svm.SBPF
