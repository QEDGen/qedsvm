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

/-! ### singletonMemU64 — 8 consecutive bytes encoding a u64 value

The partial state owns 8 bytes starting at `addr`, whose little-endian
decode is `v % 2^64`. Used as the building block for the `↦U64`
assertion that ldxdw/stxdw specs need. -/

/-- Partial state owning 8 consecutive memory bytes whose little-endian
    decode equals `v % 2^64`. -/
def singletonMemU64 (addr v : Nat) : PartialState :=
  { regs := fun _ => none
    mem := fun a =>
      if a = addr then some (v % 256)
      else if a = addr + 1 then some (v / 0x100 % 256)
      else if a = addr + 2 then some (v / 0x10000 % 256)
      else if a = addr + 3 then some (v / 0x1000000 % 256)
      else if a = addr + 4 then some (v / 0x100000000 % 256)
      else if a = addr + 5 then some (v / 0x10000000000 % 256)
      else if a = addr + 6 then some (v / 0x1000000000000 % 256)
      else if a = addr + 7 then some (v / 0x100000000000000 % 256)
      else none
    pc := none }

@[simp] theorem singletonMemU64_regs {addr v : Nat} (r : Reg) :
    (singletonMemU64 addr v).regs r = none := rfl

@[simp] theorem singletonMemU64_pc {addr v : Nat} :
    (singletonMemU64 addr v).pc = none := rfl

theorem singletonMemU64_mem_0 (addr v : Nat) :
    (singletonMemU64 addr v).mem addr = some (v % 256) := by
  unfold singletonMemU64; simp

theorem singletonMemU64_mem_1 (addr v : Nat) :
    (singletonMemU64 addr v).mem (addr + 1) = some (v / 0x100 % 256) := by
  unfold singletonMemU64
  show (if addr + 1 = addr then _
        else if addr + 1 = addr + 1 then some (v / 0x100 % 256)
        else _) = _
  rw [if_neg (by omega : addr + 1 ≠ addr), if_pos rfl]

theorem singletonMemU64_mem_2 (addr v : Nat) :
    (singletonMemU64 addr v).mem (addr + 2) = some (v / 0x10000 % 256) := by
  show (singletonMemU64 addr v).mem (addr + 2) = _
  unfold singletonMemU64
  show (if addr + 2 = addr then some (v % 256)
        else if addr + 2 = addr + 1 then some (v / 0x100 % 256)
        else if addr + 2 = addr + 2 then some (v / 0x10000 % 256)
        else _) = _
  rw [if_neg (by omega : addr + 2 ≠ addr),
      if_neg (by omega : addr + 2 ≠ addr + 1),
      if_pos rfl]

theorem singletonMemU64_mem_3 (addr v : Nat) :
    (singletonMemU64 addr v).mem (addr + 3) = some (v / 0x1000000 % 256) := by
  unfold singletonMemU64
  show (if addr + 3 = addr then _
        else if addr + 3 = addr + 1 then _
        else if addr + 3 = addr + 2 then _
        else if addr + 3 = addr + 3 then some (v / 0x1000000 % 256)
        else _) = _
  rw [if_neg (by omega : addr + 3 ≠ addr),
      if_neg (by omega : addr + 3 ≠ addr + 1),
      if_neg (by omega : addr + 3 ≠ addr + 2),
      if_pos rfl]

theorem singletonMemU64_mem_4 (addr v : Nat) :
    (singletonMemU64 addr v).mem (addr + 4) = some (v / 0x100000000 % 256) := by
  unfold singletonMemU64
  show (if addr + 4 = addr then _
        else if addr + 4 = addr + 1 then _
        else if addr + 4 = addr + 2 then _
        else if addr + 4 = addr + 3 then _
        else if addr + 4 = addr + 4 then some (v / 0x100000000 % 256)
        else _) = _
  rw [if_neg (by omega : addr + 4 ≠ addr),
      if_neg (by omega : addr + 4 ≠ addr + 1),
      if_neg (by omega : addr + 4 ≠ addr + 2),
      if_neg (by omega : addr + 4 ≠ addr + 3),
      if_pos rfl]

theorem singletonMemU64_mem_5 (addr v : Nat) :
    (singletonMemU64 addr v).mem (addr + 5) = some (v / 0x10000000000 % 256) := by
  unfold singletonMemU64
  show (if addr + 5 = addr then _
        else if addr + 5 = addr + 1 then _
        else if addr + 5 = addr + 2 then _
        else if addr + 5 = addr + 3 then _
        else if addr + 5 = addr + 4 then _
        else if addr + 5 = addr + 5 then some (v / 0x10000000000 % 256)
        else _) = _
  rw [if_neg (by omega : addr + 5 ≠ addr),
      if_neg (by omega : addr + 5 ≠ addr + 1),
      if_neg (by omega : addr + 5 ≠ addr + 2),
      if_neg (by omega : addr + 5 ≠ addr + 3),
      if_neg (by omega : addr + 5 ≠ addr + 4),
      if_pos rfl]

theorem singletonMemU64_mem_6 (addr v : Nat) :
    (singletonMemU64 addr v).mem (addr + 6) = some (v / 0x1000000000000 % 256) := by
  unfold singletonMemU64
  show (if addr + 6 = addr then _
        else if addr + 6 = addr + 1 then _
        else if addr + 6 = addr + 2 then _
        else if addr + 6 = addr + 3 then _
        else if addr + 6 = addr + 4 then _
        else if addr + 6 = addr + 5 then _
        else if addr + 6 = addr + 6 then some (v / 0x1000000000000 % 256)
        else _) = _
  rw [if_neg (by omega : addr + 6 ≠ addr),
      if_neg (by omega : addr + 6 ≠ addr + 1),
      if_neg (by omega : addr + 6 ≠ addr + 2),
      if_neg (by omega : addr + 6 ≠ addr + 3),
      if_neg (by omega : addr + 6 ≠ addr + 4),
      if_neg (by omega : addr + 6 ≠ addr + 5),
      if_pos rfl]

theorem singletonMemU64_mem_7 (addr v : Nat) :
    (singletonMemU64 addr v).mem (addr + 7) = some (v / 0x100000000000000 % 256) := by
  unfold singletonMemU64
  show (if addr + 7 = addr then _
        else if addr + 7 = addr + 1 then _
        else if addr + 7 = addr + 2 then _
        else if addr + 7 = addr + 3 then _
        else if addr + 7 = addr + 4 then _
        else if addr + 7 = addr + 5 then _
        else if addr + 7 = addr + 6 then _
        else if addr + 7 = addr + 7 then some (v / 0x100000000000000 % 256)
        else _) = _
  rw [if_neg (by omega : addr + 7 ≠ addr),
      if_neg (by omega : addr + 7 ≠ addr + 1),
      if_neg (by omega : addr + 7 ≠ addr + 2),
      if_neg (by omega : addr + 7 ≠ addr + 3),
      if_neg (by omega : addr + 7 ≠ addr + 4),
      if_neg (by omega : addr + 7 ≠ addr + 5),
      if_neg (by omega : addr + 7 ≠ addr + 6),
      if_pos rfl]

/-! ### singletonMemU16 / singletonMemU32 — narrower-width variants

Same shape as `singletonMemU64` but for 2-byte (`u16`) and 4-byte
(`u32`) ownership. Used by `ldxh`/`stxh` and `ldxw`/`stxw`. -/

/-- Partial state owning 2 consecutive memory bytes whose little-endian
    decode equals `v % 2^16`. -/
def singletonMemU16 (addr v : Nat) : PartialState :=
  { regs := fun _ => none
    mem := fun a =>
      if a = addr then some (v % 256)
      else if a = addr + 1 then some (v / 0x100 % 256)
      else none
    pc := none }

@[simp] theorem singletonMemU16_regs {addr v : Nat} (r : Reg) :
    (singletonMemU16 addr v).regs r = none := rfl

@[simp] theorem singletonMemU16_pc {addr v : Nat} :
    (singletonMemU16 addr v).pc = none := rfl

theorem singletonMemU16_mem_0 (addr v : Nat) :
    (singletonMemU16 addr v).mem addr = some (v % 256) := by
  unfold singletonMemU16; simp

theorem singletonMemU16_mem_1 (addr v : Nat) :
    (singletonMemU16 addr v).mem (addr + 1) = some (v / 0x100 % 256) := by
  unfold singletonMemU16
  show (if addr + 1 = addr then _
        else if addr + 1 = addr + 1 then some (v / 0x100 % 256)
        else _) = _
  rw [if_neg (by omega : addr + 1 ≠ addr), if_pos rfl]

theorem singletonMemU16_mem_outside (addr v : Nat) (a : Nat)
    (h : a < addr ∨ a ≥ addr + 2) :
    (singletonMemU16 addr v).mem a = none := by
  unfold singletonMemU16
  show (if a = addr then some (v % 256)
        else if a = addr + 1 then some (v / 0x100 % 256)
        else none) = none
  rw [if_neg (by omega : a ≠ addr),
      if_neg (by omega : a ≠ addr + 1)]

/-- Partial state owning 4 consecutive memory bytes whose little-endian
    decode equals `v % 2^32`. -/
def singletonMemU32 (addr v : Nat) : PartialState :=
  { regs := fun _ => none
    mem := fun a =>
      if a = addr then some (v % 256)
      else if a = addr + 1 then some (v / 0x100 % 256)
      else if a = addr + 2 then some (v / 0x10000 % 256)
      else if a = addr + 3 then some (v / 0x1000000 % 256)
      else none
    pc := none }

@[simp] theorem singletonMemU32_regs {addr v : Nat} (r : Reg) :
    (singletonMemU32 addr v).regs r = none := rfl

@[simp] theorem singletonMemU32_pc {addr v : Nat} :
    (singletonMemU32 addr v).pc = none := rfl

theorem singletonMemU32_mem_0 (addr v : Nat) :
    (singletonMemU32 addr v).mem addr = some (v % 256) := by
  unfold singletonMemU32; simp

theorem singletonMemU32_mem_1 (addr v : Nat) :
    (singletonMemU32 addr v).mem (addr + 1) = some (v / 0x100 % 256) := by
  unfold singletonMemU32
  show (if addr + 1 = addr then _
        else if addr + 1 = addr + 1 then some (v / 0x100 % 256)
        else _) = _
  rw [if_neg (by omega : addr + 1 ≠ addr), if_pos rfl]

theorem singletonMemU32_mem_2 (addr v : Nat) :
    (singletonMemU32 addr v).mem (addr + 2) = some (v / 0x10000 % 256) := by
  unfold singletonMemU32
  show (if addr + 2 = addr then _
        else if addr + 2 = addr + 1 then _
        else if addr + 2 = addr + 2 then some (v / 0x10000 % 256)
        else _) = _
  rw [if_neg (by omega : addr + 2 ≠ addr),
      if_neg (by omega : addr + 2 ≠ addr + 1),
      if_pos rfl]

theorem singletonMemU32_mem_3 (addr v : Nat) :
    (singletonMemU32 addr v).mem (addr + 3) = some (v / 0x1000000 % 256) := by
  unfold singletonMemU32
  show (if addr + 3 = addr then _
        else if addr + 3 = addr + 1 then _
        else if addr + 3 = addr + 2 then _
        else if addr + 3 = addr + 3 then some (v / 0x1000000 % 256)
        else _) = _
  rw [if_neg (by omega : addr + 3 ≠ addr),
      if_neg (by omega : addr + 3 ≠ addr + 1),
      if_neg (by omega : addr + 3 ≠ addr + 2),
      if_pos rfl]

theorem singletonMemU32_mem_outside (addr v : Nat) (a : Nat)
    (h : a < addr ∨ a ≥ addr + 4) :
    (singletonMemU32 addr v).mem a = none := by
  unfold singletonMemU32
  show (if a = addr then some (v % 256)
        else if a = addr + 1 then some (v / 0x100 % 256)
        else if a = addr + 2 then some (v / 0x10000 % 256)
        else if a = addr + 3 then some (v / 0x1000000 % 256)
        else none) = none
  rw [if_neg (by omega : a ≠ addr),
      if_neg (by omega : a ≠ addr + 1),
      if_neg (by omega : a ≠ addr + 2),
      if_neg (by omega : a ≠ addr + 3)]

/-- Address outside the 8-byte range owns nothing in `singletonMemU64`. -/
theorem singletonMemU64_mem_outside (addr v : Nat) (a : Nat)
    (h : a < addr ∨ a ≥ addr + 8) :
    (singletonMemU64 addr v).mem a = none := by
  unfold singletonMemU64
  show (if a = addr then some (v % 256)
        else if a = addr + 1 then some (v / 0x100 % 256)
        else if a = addr + 2 then some (v / 0x10000 % 256)
        else if a = addr + 3 then some (v / 0x1000000 % 256)
        else if a = addr + 4 then some (v / 0x100000000 % 256)
        else if a = addr + 5 then some (v / 0x10000000000 % 256)
        else if a = addr + 6 then some (v / 0x1000000000000 % 256)
        else if a = addr + 7 then some (v / 0x100000000000000 % 256)
        else none) = none
  rw [if_neg (by omega : a ≠ addr),
      if_neg (by omega : a ≠ addr + 1),
      if_neg (by omega : a ≠ addr + 2),
      if_neg (by omega : a ≠ addr + 3),
      if_neg (by omega : a ≠ addr + 4),
      if_neg (by omega : a ≠ addr + 5),
      if_neg (by omega : a ≠ addr + 6),
      if_neg (by omega : a ≠ addr + 7)]

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

/-- 2 consecutive memory bytes at `addr` whose little-endian decode is
    `v % 2^16`. Used by `ldxh` / `stxh` specs. -/
def memU16Is (addr v : Nat) : Assertion :=
  fun h => h = PartialState.singletonMemU16 addr v

@[inherit_doc] notation:50 a " ↦U16 " v => memU16Is a v

/-- 4 consecutive memory bytes at `addr` whose little-endian decode is
    `v % 2^32`. Used by `ldxw` / `stxw` specs. -/
def memU32Is (addr v : Nat) : Assertion :=
  fun h => h = PartialState.singletonMemU32 addr v

@[inherit_doc] notation:50 a " ↦U32 " v => memU32Is a v

/-- 8 consecutive memory bytes at `addr` whose little-endian decode is
    `v % 2^64`. Used by `ldxdw` / `stxdw` specs. -/
def memU64Is (addr v : Nat) : Assertion :=
  fun h => h = PartialState.singletonMemU64 addr v

@[inherit_doc] notation:50 a " ↦U64 " v => memU64Is a v

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

/-- Swap the first two atoms of a 3-fold separating conjunction.
    Useful when composing specs whose natural assertion orders differ
    (e.g. `ldxb` produces `dst ** src ** mem` while `stxb` consumes
    `baseReg ** valReg ** mem`). Chain: assoc-back, comm inner, assoc-forward. -/
theorem sepConj_swap_first_two {P Q R : Assertion} :
    ∀ h, (P ** Q ** R) h ↔ (Q ** P ** R) h := by
  intro h
  constructor
  · intro hPQR
    have h1 : ((P ** Q) ** R) h := (sepConj_assoc h).mpr hPQR
    obtain ⟨a, c, hd, hu, hpq, hr⟩ := h1
    have hQP : (Q ** P) a := (sepConj_comm a).mp hpq
    exact (sepConj_assoc h).mp ⟨a, c, hd, hu, hQP, hr⟩
  · intro hQPR
    have h1 : ((Q ** P) ** R) h := (sepConj_assoc h).mpr hQPR
    obtain ⟨a, c, hd, hu, hqp, hr⟩ := h1
    have hPQ : (P ** Q) a := (sepConj_comm a).mp hqp
    exact (sepConj_assoc h).mp ⟨a, c, hd, hu, hPQ, hr⟩

/-! ## Pointwise-iff combinators for sepConj

These are the building blocks the elab-level permutation builder in
`SLTactic.lean` uses to assemble an arbitrary-permutation iff between
two right-folded sepConjs over the same multiset of atoms. The chain
is `Iff.refl` / `Iff.trans` lifted pointwise, plus a frame-on-the-left
combinator for descending into the tail of a sepConj. -/

theorem sepConj_iff_refl (P : Assertion) : ∀ h, P h ↔ P h :=
  fun _ => Iff.rfl

theorem sepConj_iff_trans_pw {P Q R : Assertion}
    (h1 : ∀ h, P h ↔ Q h) (h2 : ∀ h, Q h ↔ R h) :
    ∀ h, P h ↔ R h :=
  fun h => Iff.trans (h1 h) (h2 h)

theorem sepConj_iff_symm_pw {P Q : Assertion} (h : ∀ x, P x ↔ Q x) :
    ∀ x, Q x ↔ P x :=
  fun x => (h x).symm

/-- Reshape the right operand of a sepConj. Pointwise iff over the
    tail lifts to a pointwise iff over `(P ** _)`. Used by the
    permutation builder to descend through a sepConj's right spine. -/
theorem sepConj_iff_congr_right (P : Assertion) {Q Q' : Assertion}
    (hQQ' : ∀ h, Q h ↔ Q' h) :
    ∀ h, (P ** Q) h ↔ (P ** Q') h := by
  intro h
  constructor
  · rintro ⟨h1, h2, hd, hu, hP1, hQ2⟩
    exact ⟨h1, h2, hd, hu, hP1, (hQQ' h2).mp hQ2⟩
  · rintro ⟨h1, h2, hd, hu, hP1, hQ'2⟩
    exact ⟨h1, h2, hd, hu, hP1, (hQQ' h2).mpr hQ'2⟩

/-- Reshape the left operand of a sepConj. Mirror of
    `sepConj_iff_congr_right`. Derived via `sepConj_comm`. -/
theorem sepConj_iff_congr_left (Q : Assertion) {P P' : Assertion}
    (hPP' : ∀ h, P h ↔ P' h) :
    ∀ h, (P ** Q) h ↔ (P' ** Q) h := by
  intro h
  refine Iff.trans (sepConj_comm h) (Iff.trans ?_ (sepConj_comm h))
  exact sepConj_iff_congr_right Q hPP' h

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

theorem pcFree_memU16Is (a v : Nat) : (memU16Is a v).pcFree := by
  intro h heq; rw [heq]; rfl

theorem pcFree_memU32Is (a v : Nat) : (memU32Is a v).pcFree := by
  intro h heq; rw [heq]; rfl

theorem pcFree_memU64Is (a v : Nat) : (memU64Is a v).pcFree := by
  intro h heq; rw [heq]; rfl

theorem pcFree_sepConj {P Q : Assertion} (hP : P.pcFree) (hQ : Q.pcFree) :
    (P ** Q).pcFree := by
  rintro h ⟨h1, h2, _, hu, hP1, hQ2⟩
  rw [← hu, PartialState.union_pc_of_left_none (hP _ hP1)]
  exact hQ _ hQ2

end Svm.SBPF
