/-
  Separation logic over sBPF machine state (after Kennedy et al. 2013 / the
  EvmAsm.Rv64.SepLogic adaptation).

  Registers, memory bytes, and the PC are separable resources; an `Assertion`
  is a predicate on a `PartialState` (partial heap owning a subset). `P ** Q`
  holds when the state splits into two disjoint pieces satisfying `P` and `Q`.
  The bridge to the executable `State` is `Assertion.holdsFor` (some compatible
  partial state satisfies it). Memory is byte-level; multi-byte assertions are
  built from byte points-to via `**`.
-/

import SVM.SBPF.Execute

namespace SVM.SBPF

/-! ## PartialState — partial ownership of registers, memory, PC

To extend `PartialState` with a new resource field:

1. Add the field below.
2. Add a `singletonX` builder + projection lemmas (mirror `singletonPC`;
   default the field to `none` on the other singletons via `@[simp]`).
3. Add one clause to `Disjoint` and `CompatibleWith`.
4. Extend `union` (and its `union_X_of_left_*` / `union_X_eq_none_iff` helpers);
   `union_empty_*`/`union_assoc` pick up the field once the `match` is added.

Destructure sites (`hd.regs`/`hd.mem`/`hd.pc`) stay stable; only
`Disjoint`/`CompatibleWith` construction sites need the new field (found by
`lake build`).
-/

/-- A partial view of an sBPF machine state: `some v` owns the resource at value
    `v`, `none` doesn't own it. `returnData`/`callStack` default to `none` so
    record-syntax singleton builders pick them up automatically. -/
structure PartialState where
  regs : Reg → Option Nat
  mem  : Nat → Option Nat
  pc   : Option Nat
  returnData : Option ByteArray := none
  callStack : Option (List CallFrame) := none
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

/-- Partial state owning exactly the returnData buffer. -/
def singletonReturnData (rd : ByteArray) : PartialState :=
  { regs := fun _ => none
    mem  := fun _ => none
    pc   := none
    returnData := some rd }

/-- Partial state owning exactly the call stack. -/
def singletonCallStack (cs : List CallFrame) : PartialState :=
  { regs := fun _ => none
    mem  := fun _ => none
    pc   := none
    callStack := some cs }

/-- Two partial states are disjoint if they never both own the same resource
    (one clause per `PartialState` field). -/
structure Disjoint (h1 h2 : PartialState) : Prop where
  regs : ∀ r, h1.regs r = none ∨ h2.regs r = none
  mem  : ∀ a, h1.mem  a = none ∨ h2.mem  a = none
  pc   : h1.pc = none ∨ h2.pc = none
  returnData : h1.returnData = none ∨ h2.returnData = none
  callStack : h1.callStack = none ∨ h2.callStack = none

/-- Left-biased union of two partial states. -/
def union (h1 h2 : PartialState) : PartialState where
  regs := fun r => match h1.regs r with | some v => some v | none => h2.regs r
  mem  := fun a => match h1.mem  a with | some v => some v | none => h2.mem  a
  pc   := match h1.pc with | some v => some v | none => h2.pc
  returnData := match h1.returnData with | some v => some v | none => h2.returnData
  callStack := match h1.callStack with | some v => some v | none => h2.callStack

/-- A partial state is compatible with a full machine state if every owned
    resource agrees with it (one clause per `PartialState` field). -/
structure CompatibleWith (h : PartialState) (s : State) : Prop where
  regs : ∀ r v, h.regs r = some v → s.regs.get r = v
  mem  : ∀ a v, h.mem  a = some v → s.mem a = v
  pc   : ∀ v,   h.pc   = some v → s.pc = v
  returnData : ∀ rd, h.returnData = some rd → s.returnData = rd
  callStack : ∀ cs, h.callStack = some cs → s.callStack = cs

/-! ## Disjoint lemmas -/

theorem Disjoint.symm {h1 h2 : PartialState} (hd : h1.Disjoint h2) :
    h2.Disjoint h1 :=
  { regs := fun r => (hd.regs r).symm
    mem  := fun a => (hd.mem a).symm
    pc   := hd.pc.symm
    returnData := hd.returnData.symm
    callStack := hd.callStack.symm }

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

@[simp] theorem singletonReg_returnData {r : Reg} {v : Nat} :
    (singletonReg r v).returnData = none := rfl

@[simp] theorem singletonReg_callStack {r : Reg} {v : Nat} :
    (singletonReg r v).callStack = none := rfl

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

@[simp] theorem singletonMem_returnData {a v : Nat} :
    (singletonMem a v).returnData = none := rfl

@[simp] theorem singletonMem_callStack {a v : Nat} :
    (singletonMem a v).callStack = none := rfl

@[simp] theorem singletonPC_regs {v : Nat} (r : Reg) :
    (singletonPC v).regs r = none := rfl

@[simp] theorem singletonPC_mem {v : Nat} (a : Nat) :
    (singletonPC v).mem a = none := rfl

@[simp] theorem singletonPC_pc_self {v : Nat} :
    (singletonPC v).pc = some v := rfl

@[simp] theorem singletonPC_returnData {v : Nat} :
    (singletonPC v).returnData = none := rfl

@[simp] theorem singletonPC_callStack {v : Nat} :
    (singletonPC v).callStack = none := rfl

@[simp] theorem singletonReturnData_regs {rd : ByteArray} (r : Reg) :
    (singletonReturnData rd).regs r = none := rfl

@[simp] theorem singletonReturnData_mem {rd : ByteArray} (a : Nat) :
    (singletonReturnData rd).mem a = none := rfl

@[simp] theorem singletonReturnData_pc {rd : ByteArray} :
    (singletonReturnData rd).pc = none := rfl

@[simp] theorem singletonReturnData_returnData_self {rd : ByteArray} :
    (singletonReturnData rd).returnData = some rd := rfl

@[simp] theorem singletonReturnData_callStack {rd : ByteArray} :
    (singletonReturnData rd).callStack = none := rfl

@[simp] theorem singletonCallStack_regs {cs : List CallFrame} (r : Reg) :
    (singletonCallStack cs).regs r = none := rfl

@[simp] theorem singletonCallStack_mem {cs : List CallFrame} (a : Nat) :
    (singletonCallStack cs).mem a = none := rfl

@[simp] theorem singletonCallStack_pc {cs : List CallFrame} :
    (singletonCallStack cs).pc = none := rfl

@[simp] theorem singletonCallStack_returnData {cs : List CallFrame} :
    (singletonCallStack cs).returnData = none := rfl

@[simp] theorem singletonCallStack_callStack_self {cs : List CallFrame} :
    (singletonCallStack cs).callStack = some cs := rfl

/-! ### singletonMemU64 — 8 consecutive bytes encoding a u64 value

Owns 8 bytes at `addr` with LE decode `v % 2^64`; the building block for `↦U64`
(ldxdw/stxdw). -/

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

@[simp] theorem singletonMemU64_returnData {addr v : Nat} :
    (singletonMemU64 addr v).returnData = none := rfl

@[simp] theorem singletonMemU64_callStack {addr v : Nat} :
    (singletonMemU64 addr v).callStack = none := rfl

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

Same shape as `singletonMemU64` for 2-byte / 4-byte ownership (`ldxh`/`stxh`,
`ldxw`/`stxw`). -/

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

@[simp] theorem singletonMemU16_returnData {addr v : Nat} :
    (singletonMemU16 addr v).returnData = none := rfl

@[simp] theorem singletonMemU16_callStack {addr v : Nat} :
    (singletonMemU16 addr v).callStack = none := rfl

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

@[simp] theorem singletonMemU32_returnData {addr v : Nat} :
    (singletonMemU32 addr v).returnData = none := rfl

@[simp] theorem singletonMemU32_callStack {addr v : Nat} :
    (singletonMemU32 addr v).callStack = none := rfl

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

/-! ### singletonMem32Bytes — 32 consecutive bytes from a `ByteArray`

Owns 32 bytes at `addr` where byte `i ∈ [0, 32)` = `(bs.get! i).toNat`; the
building block for `↦Bytes32` (PDA / hash syscalls). Carries an opaque
`ByteArray` payload (indexed, not integer-decoded).

CALLER OBLIGATION (L4): owns 32 bytes unconditionally, so faithful only when
`bs.size = 32`. A SHORTER `bs` STRENGTHENS the assertion with phantom zero bytes
(via `get!`'s default); a LONGER `bs`'s tail is ignored. Every current use is a
hash/PDA output whose 32-byte length is guaranteed by the crypto SIZE axioms
(pinned Rust-side, L7). Any NEW use over a variable-length array must establish
`bs.size = 32` first. -/

/-- Partial state owning 32 consecutive bytes = `bs`. A single conditional, not
    32 unrolled `if`s — keeps definition and proof linear. -/
def singletonMem32Bytes (addr : Nat) (bs : ByteArray) : PartialState :=
  { regs := fun _ => none
    mem := fun a =>
      if addr ≤ a ∧ a < addr + 32 then some (bs.get! (a - addr)).toNat
      else none
    pc := none }

@[simp] theorem singletonMem32Bytes_regs {addr : Nat} {bs : ByteArray} (r : Reg) :
    (singletonMem32Bytes addr bs).regs r = none := rfl

@[simp] theorem singletonMem32Bytes_pc {addr : Nat} {bs : ByteArray} :
    (singletonMem32Bytes addr bs).pc = none := rfl

@[simp] theorem singletonMem32Bytes_returnData {addr : Nat} {bs : ByteArray} :
    (singletonMem32Bytes addr bs).returnData = none := rfl

@[simp] theorem singletonMem32Bytes_callStack {addr : Nat} {bs : ByteArray} :
    (singletonMem32Bytes addr bs).callStack = none := rfl

/-- Byte at offset `i ∈ [0, 32)` = `(bs.get! i).toNat` (one parameterized lemma
    replacing 32 unrolled `_mem_i`). -/
theorem singletonMem32Bytes_mem_at (addr : Nat) (bs : ByteArray) (i : Nat)
    (hi : i < 32) :
    (singletonMem32Bytes addr bs).mem (addr + i) = some (bs.get! i).toNat := by
  unfold singletonMem32Bytes
  show (if addr ≤ addr + i ∧ addr + i < addr + 32 then
          some (bs.get! ((addr + i) - addr)).toNat
        else none) = some (bs.get! i).toNat
  rw [if_pos ⟨Nat.le_add_right _ _, by omega⟩,
      show (addr + i) - addr = i from by omega]

/-- Address outside the 32-byte range owns nothing. -/
theorem singletonMem32Bytes_mem_outside (addr : Nat) (bs : ByteArray) (a : Nat)
    (h : a < addr ∨ a ≥ addr + 32) :
    (singletonMem32Bytes addr bs).mem a = none := by
  unfold singletonMem32Bytes
  show (if addr ≤ a ∧ a < addr + 32 then some (bs.get! (a - addr)).toNat else none) = none
  apply if_neg
  rintro ⟨h1, h2⟩
  omega

/-! ### singletonMemBytes — variable-length byte blob from a `ByteArray`

`singletonMem32Bytes` generalized to arbitrary length: owns `bs.size` bytes at
`addr` (byte `i` = `(bs.get! i).toNat`), for variable-length syscall reads (PDA
seeds, hash inputs). `bs.size = 0` owns nothing. -/

/-- Partial state owning `bs.size` consecutive bytes = `bs`; `singletonMem32Bytes`
    parametric in length. -/
def singletonMemBytes (addr : Nat) (bs : ByteArray) : PartialState :=
  { regs := fun _ => none
    mem := fun a =>
      if addr ≤ a ∧ a < addr + bs.size then some (bs.get! (a - addr)).toNat
      else none
    pc := none }

@[simp] theorem singletonMemBytes_regs {addr : Nat} {bs : ByteArray} (r : Reg) :
    (singletonMemBytes addr bs).regs r = none := rfl

@[simp] theorem singletonMemBytes_pc {addr : Nat} {bs : ByteArray} :
    (singletonMemBytes addr bs).pc = none := rfl

@[simp] theorem singletonMemBytes_returnData {addr : Nat} {bs : ByteArray} :
    (singletonMemBytes addr bs).returnData = none := rfl

@[simp] theorem singletonMemBytes_callStack {addr : Nat} {bs : ByteArray} :
    (singletonMemBytes addr bs).callStack = none := rfl

/-- Byte at offset `i ∈ [0, bs.size)` equals `(bs.get! i).toNat`. -/
theorem singletonMemBytes_mem_at (addr : Nat) (bs : ByteArray) (i : Nat)
    (hi : i < bs.size) :
    (singletonMemBytes addr bs).mem (addr + i) = some (bs.get! i).toNat := by
  unfold singletonMemBytes
  show (if addr ≤ addr + i ∧ addr + i < addr + bs.size then
          some (bs.get! ((addr + i) - addr)).toNat
        else none) = some (bs.get! i).toNat
  rw [if_pos ⟨Nat.le_add_right _ _, by omega⟩,
      show (addr + i) - addr = i from by omega]

/-- Address outside the `[addr, addr + bs.size)` range owns nothing. -/
theorem singletonMemBytes_mem_outside (addr : Nat) (bs : ByteArray) (a : Nat)
    (h : a < addr ∨ a ≥ addr + bs.size) :
    (singletonMemBytes addr bs).mem a = none := by
  unfold singletonMemBytes
  show (if addr ≤ a ∧ a < addr + bs.size then
          some (bs.get! (a - addr)).toNat else none) = none
  apply if_neg
  rintro ⟨h1, h2⟩
  omega

/-! ### `_mem_isSome` helpers — used by range-disjointness derivations

Per memory atom, "address in range ⇒ atom owns it" as an `∃ v, mem a = some v`
witness. Range-disjointness picks a sentinel in one atom's range and uses SL
disjointness to conclude the other doesn't own it. -/

theorem singletonMemU64_mem_isSome (addr v : Nat) (a : Nat)
    (h : addr ≤ a ∧ a < addr + 8) :
    ∃ x, (singletonMemU64 addr v).mem a = some x := by
  obtain ⟨h1, h2⟩ := h
  rcases Nat.lt_or_ge a (addr + 1) with h_lt | h_ge
  · refine ⟨v % 256, ?_⟩
    have : a = addr := by omega
    rw [this]; exact singletonMemU64_mem_0 _ _
  rcases Nat.lt_or_ge a (addr + 2) with h_lt | h_ge
  · refine ⟨v / 0x100 % 256, ?_⟩
    have : a = addr + 1 := by omega
    rw [this]; exact singletonMemU64_mem_1 _ _
  rcases Nat.lt_or_ge a (addr + 3) with h_lt | h_ge
  · refine ⟨v / 0x10000 % 256, ?_⟩
    have : a = addr + 2 := by omega
    rw [this]; exact singletonMemU64_mem_2 _ _
  rcases Nat.lt_or_ge a (addr + 4) with h_lt | h_ge
  · refine ⟨v / 0x1000000 % 256, ?_⟩
    have : a = addr + 3 := by omega
    rw [this]; exact singletonMemU64_mem_3 _ _
  rcases Nat.lt_or_ge a (addr + 5) with h_lt | h_ge
  · refine ⟨v / 0x100000000 % 256, ?_⟩
    have : a = addr + 4 := by omega
    rw [this]; exact singletonMemU64_mem_4 _ _
  rcases Nat.lt_or_ge a (addr + 6) with h_lt | h_ge
  · refine ⟨v / 0x10000000000 % 256, ?_⟩
    have : a = addr + 5 := by omega
    rw [this]; exact singletonMemU64_mem_5 _ _
  rcases Nat.lt_or_ge a (addr + 7) with h_lt | h_ge
  · refine ⟨v / 0x1000000000000 % 256, ?_⟩
    have : a = addr + 6 := by omega
    rw [this]; exact singletonMemU64_mem_6 _ _
  · refine ⟨v / 0x100000000000000 % 256, ?_⟩
    have : a = addr + 7 := by omega
    rw [this]; exact singletonMemU64_mem_7 _ _

theorem singletonMemBytes_mem_isSome (addr : Nat) (bs : ByteArray) (a : Nat)
    (h : addr ≤ a ∧ a < addr + bs.size) :
    ∃ x, (singletonMemBytes addr bs).mem a = some x := by
  obtain ⟨h1, h2⟩ := h
  have h_lt : a - addr < bs.size := by omega
  have key := singletonMemBytes_mem_at addr bs (a - addr) h_lt
  rw [show addr + (a - addr) = a from by omega] at key
  exact ⟨_, key⟩

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
@[simp] theorem empty_returnData : empty.returnData = none := rfl
@[simp] theorem empty_callStack : empty.callStack = none := rfl

theorem Disjoint_empty_left {h : PartialState} : empty.Disjoint h :=
  { regs := fun _ => Or.inl rfl
    mem  := fun _ => Or.inl rfl
    pc   := Or.inl rfl
    returnData := Or.inl rfl
    callStack := Or.inl rfl }

theorem Disjoint_empty_right {h : PartialState} : h.Disjoint empty :=
  Disjoint_empty_left.symm

/-! ## Field-projection helpers for `union`.

Extract each field of `union h1 h2` under known field conditions, avoiding a
hand `match` reduction in larger proofs. -/

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

@[simp] theorem union_returnData_of_left_none {h1 h2 : PartialState}
    (h : h1.returnData = none) : (h1.union h2).returnData = h2.returnData := by
  show (match h1.returnData with | some v => some v | none => h2.returnData) =
       h2.returnData
  rw [h]

theorem union_returnData_of_left_some {h1 h2 : PartialState} {v : ByteArray}
    (h : h1.returnData = some v) : (h1.union h2).returnData = some v := by
  show (match h1.returnData with | some v => some v | none => h2.returnData) =
       some v
  rw [h]

/-- If both halves have `returnData = none` so does the union. Side conditions
    discharged by the per-atom `@[simp]` lemmas, so `by simp` closes
    arbitrarily-deep `(unions).returnData = none` goals. -/
@[simp] theorem union_returnData_eq_none_of_both {h1 h2 : PartialState}
    (h1_rd : h1.returnData = none) (h2_rd : h2.returnData = none) :
    (h1.union h2).returnData = none := by
  rw [union_returnData_of_left_none h1_rd]; exact h2_rd

/-- Equational form of `union_returnData_eq_none_iff`; `@[simp]` so simp reduces
    `(unions).returnData` to a chain of singleton lookups. -/
@[simp] theorem union_returnData_eq_match (h1 h2 : PartialState) :
    (h1.union h2).returnData =
      (match h1.returnData with | some v => some v | none => h2.returnData) :=
  rfl

@[simp] theorem union_callStack_of_left_none {h1 h2 : PartialState}
    (h : h1.callStack = none) : (h1.union h2).callStack = h2.callStack := by
  show (match h1.callStack with | some v => some v | none => h2.callStack) =
       h2.callStack
  rw [h]

theorem union_callStack_of_left_some {h1 h2 : PartialState}
    {v : List CallFrame}
    (h : h1.callStack = some v) : (h1.union h2).callStack = some v := by
  show (match h1.callStack with | some v => some v | none => h2.callStack) =
       some v
  rw [h]

@[simp] theorem union_callStack_eq_none_of_both {h1 h2 : PartialState}
    (h1_cs : h1.callStack = none) (h2_cs : h2.callStack = none) :
    (h1.union h2).callStack = none := by
  rw [union_callStack_of_left_none h1_cs]; exact h2_cs

@[simp] theorem union_callStack_eq_match (h1 h2 : PartialState) :
    (h1.union h2).callStack =
      (match h1.callStack with | some v => some v | none => h2.callStack) :=
  rfl

/-! ## Frame-field compat discharge

The Mem* instruction specs each rebuild a post `holdsFor` whose partial state
is `X.union h_R` (new atom chain + old frame) from a pre-compat over
`hp = h_P.union h_R`. Since the atom chains are `returnData`/`callStack`-silent,
those two compat obligations always reduce to the pre's: these two lemmas
discharge them deterministically (previously an identical `first | ...`
backtracking block copied at every site). -/

theorem CompatibleWith.union_returnData_frame
    {hp h_P h_R X : PartialState} {s : State}
    (hcompat : hp.CompatibleWith s) (hu : h_P.union h_R = hp)
    (hX : X.returnData = none) (hP : h_P.returnData = none)
    {rd : ByteArray} (hva : (X.union h_R).returnData = some rd) :
    s.returnData = rd := by
  rw [union_returnData_of_left_none hX] at hva
  exact hcompat.returnData rd
    (by rw [← hu, union_returnData_of_left_none hP]; exact hva)

theorem CompatibleWith.union_callStack_frame
    {hp h_P h_R X : PartialState} {s : State}
    (hcompat : hp.CompatibleWith s) (hu : h_P.union h_R = hp)
    (hX : X.callStack = none) (hP : h_P.callStack = none)
    {cs : List CallFrame} (hva : (X.union h_R).callStack = some cs) :
    s.callStack = cs := by
  rw [union_callStack_of_left_none hX] at hva
  exact hcompat.callStack cs
    (by rw [← hu, union_callStack_of_left_none hP]; exact hva)

/-! ## Union lemmas -/

theorem union_empty_left {h : PartialState} : empty.union h = h := by
  cases h
  rfl

theorem union_comm_of_disjoint {h1 h2 : PartialState} (hd : h1.Disjoint h2) :
    h1.union h2 = h2.union h1 := by
  show PartialState.mk _ _ _ _ _ = PartialState.mk _ _ _ _ _
  simp only [PartialState.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext r
    rcases hd.regs r with h | h
    · rw [h]; cases h2.regs r <;> rfl
    · rw [h]; cases h1.regs r <;> rfl
  · funext a
    rcases hd.mem a with h | h
    · rw [h]; cases h2.mem a <;> rfl
    · rw [h]; cases h1.mem a <;> rfl
  · rcases hd.pc with h | h
    · rw [h]; cases h2.pc <;> rfl
    · rw [h]; cases h1.pc <;> rfl
  · rcases hd.returnData with h | h
    · rw [h]; cases h2.returnData <;> rfl
    · rw [h]; cases h1.returnData <;> rfl
  · rcases hd.callStack with h | h
    · rw [h]; cases h2.callStack <;> rfl
    · rw [h]; cases h1.callStack <;> rfl

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

theorem union_returnData_eq_none_iff {h1 h2 : PartialState} :
    (h1.union h2).returnData = none ↔
      h1.returnData = none ∧ h2.returnData = none := by
  show (match h1.returnData with | some v => some v | none => h2.returnData) =
       none ↔ _
  cases h1.returnData
  · cases h2.returnData <;> simp
  · simp

theorem union_callStack_eq_none_iff {h1 h2 : PartialState} :
    (h1.union h2).callStack = none ↔
      h1.callStack = none ∧ h2.callStack = none := by
  show (match h1.callStack with | some v => some v | none => h2.callStack) =
       none ↔ _
  cases h1.callStack
  · cases h2.callStack <;> simp
  · simp

/-! ## Union associativity -/

theorem union_assoc {h1 h2 h3 : PartialState} :
    h1.union (h2.union h3) = (h1.union h2).union h3 := by
  obtain ⟨r1, m1, p1, d1, c1⟩ := h1
  obtain ⟨r2, m2, p2, d2, c2⟩ := h2
  obtain ⟨r3, m3, p3, d3, c3⟩ := h3
  show PartialState.mk _ _ _ _ _ = PartialState.mk _ _ _ _ _
  simp only [PartialState.mk.injEq, union]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext r; cases r1 r <;> cases r2 r <;> cases r3 r <;> rfl
  · funext a; cases m1 a <;> cases m2 a <;> cases m3 a <;> rfl
  · cases p1 <;> cases p2 <;> cases p3 <;> rfl
  · cases d1 <;> cases d2 <;> cases d3 <;> rfl
  · cases c1 <;> cases c2 <;> cases c3 <;> rfl

/-! ## Disjoint redistribution under union -/

theorem Disjoint_of_union_left {h1 h2 h3 : PartialState}
    (hd : (h1.union h2).Disjoint h3) : h1.Disjoint h3 where
  regs := fun r => by
    rcases hd.regs r with hl | hl
    · left; exact (union_regs_eq_none_iff.mp hl).1
    · right; exact hl
  mem := fun a => by
    rcases hd.mem a with hl | hl
    · left; exact (union_mem_eq_none_iff.mp hl).1
    · right; exact hl
  pc := by
    rcases hd.pc with hl | hl
    · left; exact union_pc_eq_none_iff.mp hl |>.1
    · right; exact hl
  returnData := by
    rcases hd.returnData with hl | hl
    · left; exact union_returnData_eq_none_iff.mp hl |>.1
    · right; exact hl
  callStack := by
    rcases hd.callStack with hl | hl
    · left; exact union_callStack_eq_none_iff.mp hl |>.1
    · right; exact hl

theorem Disjoint_of_union_right {h1 h2 h3 : PartialState}
    (hd : (h1.union h2).Disjoint h3) : h2.Disjoint h3 where
  regs := fun r => by
    rcases hd.regs r with hl | hl
    · left; exact (union_regs_eq_none_iff.mp hl).2
    · right; exact hl
  mem := fun a => by
    rcases hd.mem a with hl | hl
    · left; exact (union_mem_eq_none_iff.mp hl).2
    · right; exact hl
  pc := by
    rcases hd.pc with hl | hl
    · left; exact union_pc_eq_none_iff.mp hl |>.2
    · right; exact hl
  returnData := by
    rcases hd.returnData with hl | hl
    · left; exact union_returnData_eq_none_iff.mp hl |>.2
    · right; exact hl
  callStack := by
    rcases hd.callStack with hl | hl
    · left; exact union_callStack_eq_none_iff.mp hl |>.2
    · right; exact hl

theorem Disjoint_union_of_both {h1 h2 h3 : PartialState}
    (hd1 : h1.Disjoint h3) (hd2 : h2.Disjoint h3) : (h1.union h2).Disjoint h3 where
  regs := fun r => by
    rcases hd1.regs r with hl | hl <;> rcases hd2.regs r with hl' | hl'
    · left; exact union_regs_eq_none_iff.mpr ⟨hl, hl'⟩
    · right; exact hl'
    · right; exact hl
    · right; exact hl
  mem := fun a => by
    rcases hd1.mem a with hl | hl <;> rcases hd2.mem a with hl' | hl'
    · left; exact union_mem_eq_none_iff.mpr ⟨hl, hl'⟩
    · right; exact hl'
    · right; exact hl
    · right; exact hl
  pc := by
    rcases hd1.pc with hl | hl <;> rcases hd2.pc with hl' | hl'
    · left; exact union_pc_eq_none_iff.mpr ⟨hl, hl'⟩
    · right; exact hl'
    · right; exact hl
    · right; exact hl
  returnData := by
    rcases hd1.returnData with hl | hl <;> rcases hd2.returnData with hl' | hl'
    · left; exact union_returnData_eq_none_iff.mpr ⟨hl, hl'⟩
    · right; exact hl'
    · right; exact hl
    · right; exact hl
  callStack := by
    rcases hd1.callStack with hl | hl <;> rcases hd2.callStack with hl' | hl'
    · left; exact union_callStack_eq_none_iff.mpr ⟨hl, hl'⟩
    · right; exact hl'
    · right; exact hl
    · right; exact hl

theorem Disjoint_symm_of_union_left {h1 h2 h3 : PartialState}
    (hd : h1.Disjoint (h2.union h3)) : h1.Disjoint h2 :=
  (Disjoint_of_union_left hd.symm).symm

theorem Disjoint_symm_of_union_right {h1 h2 h3 : PartialState}
    (hd : h1.Disjoint (h2.union h3)) : h1.Disjoint h3 :=
  (Disjoint_of_union_right hd.symm).symm

/-! ## Byte-blob split/join — fine↔coarse field aggregation

Relate a single `singletonMemBytes` blob to the union of two adjacent blobs —
the foundation for reshaping a lift's scattered cells into the coarse
`↦Bytes`/`↦Pubkey` account-field atoms a `tokenAcctBalance` refinement needs. -/

/-- `get!` agrees with the bounds-checked `getElem` in range. -/
private theorem ba_get!_eq (a : ByteArray) (i : Nat) (h : i < a.size) :
    a.get! i = a[i] := by
  rw [ByteArray.getElem_eq_getElem_data]
  show a.data[i]! = a.data[i]
  exact getElem!_pos a.data i h

/-- Two adjacent byte blobs `[addr, addr+|bs1|)` and `[addr+|bs1|, …)`
    own disjoint memory. -/
theorem singletonMemBytes_disjoint_adj (addr : Nat) (bs1 bs2 : ByteArray) :
    (singletonMemBytes addr bs1).Disjoint (singletonMemBytes (addr + bs1.size) bs2) where
  regs := fun _ => Or.inl rfl
  mem := fun a => by
    by_cases h : a < addr + bs1.size
    · right; exact singletonMemBytes_mem_outside (addr + bs1.size) bs2 a (Or.inl h)
    · left;  exact singletonMemBytes_mem_outside addr bs1 a (Or.inr (by omega))
  pc := Or.inl rfl
  returnData := Or.inl rfl
  callStack := Or.inl rfl

/-- The union of two adjacent byte blobs is the blob over the
    concatenated `ByteArray`. The join half of the split/join pair. -/
theorem singletonMemBytes_union_adj (addr : Nat) (bs1 bs2 : ByteArray) :
    (singletonMemBytes addr bs1).union (singletonMemBytes (addr + bs1.size) bs2)
      = singletonMemBytes addr (bs1 ++ bs2) := by
  have hsz : (bs1 ++ bs2).size = bs1.size + bs2.size := ByteArray.size_append
  show PartialState.mk _ _ _ _ _ = PartialState.mk _ _ _ _ _
  simp only [PartialState.mk.injEq]
  refine ⟨rfl, ?_, rfl, rfl, rfl⟩
  · funext a
    show ((singletonMemBytes addr bs1).union
            (singletonMemBytes (addr + bs1.size) bs2)).mem a
        = (singletonMemBytes addr (bs1 ++ bs2)).mem a
    by_cases h1 : addr ≤ a ∧ a < addr + bs1.size
    · obtain ⟨hlo, hhi⟩ := h1
      have hi  : a - addr < bs1.size := by omega
      have hi2 : a - addr < (bs1 ++ bs2).size := by omega
      have hL : (singletonMemBytes addr bs1).mem a = some (bs1.get! (a - addr)).toNat := by
        have h := singletonMemBytes_mem_at addr bs1 (a - addr) hi
        rwa [show addr + (a - addr) = a from by omega] at h
      have hR : (singletonMemBytes addr (bs1 ++ bs2)).mem a
              = some ((bs1 ++ bs2).get! (a - addr)).toNat := by
        have h := singletonMemBytes_mem_at addr (bs1 ++ bs2) (a - addr) hi2
        rwa [show addr + (a - addr) = a from by omega] at h
      rw [union_mem_of_left_some hL, hR]
      congr 2
      rw [ba_get!_eq _ _ hi2, ba_get!_eq _ _ hi, ByteArray.getElem_append_left hi]
    · rw [union_mem_of_left_none
            (singletonMemBytes_mem_outside addr bs1 a (by omega))]
      by_cases h2 : addr + bs1.size ≤ a ∧ a < addr + bs1.size + bs2.size
      · obtain ⟨hlo, hhi⟩ := h2
        have hi  : a - (addr + bs1.size) < bs2.size := by omega
        have hi2 : a - addr < (bs1 ++ bs2).size := by omega
        have hge : bs1.size ≤ a - addr := by omega
        have hL : (singletonMemBytes (addr + bs1.size) bs2).mem a
                = some (bs2.get! (a - (addr + bs1.size))).toNat := by
          have h := singletonMemBytes_mem_at (addr + bs1.size) bs2 (a - (addr + bs1.size)) hi
          rwa [show (addr + bs1.size) + (a - (addr + bs1.size)) = a from by omega] at h
        have hR : (singletonMemBytes addr (bs1 ++ bs2)).mem a
                = some ((bs1 ++ bs2).get! (a - addr)).toNat := by
          have h := singletonMemBytes_mem_at addr (bs1 ++ bs2) (a - addr) hi2
          rwa [show addr + (a - addr) = a from by omega] at h
        rw [hL, hR]
        congr 2
        rw [ba_get!_eq _ _ hi2, ba_get!_eq _ _ hi,
            ByteArray.getElem_append_right hge]
        simp only [Nat.sub_sub]
      · rw [singletonMemBytes_mem_outside (addr + bs1.size) bs2 a (by omega),
            singletonMemBytes_mem_outside addr (bs1 ++ bs2) a (by omega)]

/-- The 8-byte LE encoding of `v`'s low 64 bits (byte `k` = `v / 256^k % 256`,
    matching `singletonMemU64`). -/
def u64LE (v : Nat) : ByteArray :=
  ⟨#[(v % 256).toUInt8, (v / 0x100 % 256).toUInt8, (v / 0x10000 % 256).toUInt8,
      (v / 0x1000000 % 256).toUInt8, (v / 0x100000000 % 256).toUInt8,
      (v / 0x10000000000 % 256).toUInt8, (v / 0x1000000000000 % 256).toUInt8,
      (v / 0x100000000000000 % 256).toUInt8]⟩

@[simp] theorem u64LE_size (v : Nat) : (u64LE v).size = 8 := rfl

/-- A `singletonMemU64` cell is the byte-blob of its 8-byte LE encoding — the
    state-level core of the `↦U64`↔`↦Bytes` bridge. -/
theorem singletonMemU64_eq_bytes (a v : Nat) :
    singletonMemU64 a v = singletonMemBytes a (u64LE v) := by
  show PartialState.mk _ _ _ _ _ = PartialState.mk _ _ _ _ _
  rw [PartialState.mk.injEq]
  refine ⟨rfl, ?_, rfl, rfl, rfl⟩
  funext x
  by_cases hx : a ≤ x ∧ x < a + 8
  · obtain ⟨hlo, hhi⟩ := hx
    obtain ⟨k, hk, rfl⟩ : ∃ k, k < 8 ∧ x = a + k := ⟨x - a, by omega, by omega⟩
    show (singletonMemU64 a v).mem (a + k) = (singletonMemBytes a (u64LE v)).mem (a + k)
    rw [singletonMemBytes_mem_at a (u64LE v) k (by rw [u64LE_size]; exact hk)]
    rcases k with _|_|_|_|_|_|_|_|k
    · rw [Nat.add_zero, singletonMemU64_mem_0]
      congr 1
      exact (UInt8.toNat_ofNat_of_lt' (by simp only [UInt8.size]; omega)).symm
    · rw [singletonMemU64_mem_1]
      congr 1
      exact (UInt8.toNat_ofNat_of_lt' (by simp only [UInt8.size]; omega)).symm
    · rw [singletonMemU64_mem_2]
      congr 1
      exact (UInt8.toNat_ofNat_of_lt' (by simp only [UInt8.size]; omega)).symm
    · rw [singletonMemU64_mem_3]
      congr 1
      exact (UInt8.toNat_ofNat_of_lt' (by simp only [UInt8.size]; omega)).symm
    · rw [singletonMemU64_mem_4]
      congr 1
      exact (UInt8.toNat_ofNat_of_lt' (by simp only [UInt8.size]; omega)).symm
    · rw [singletonMemU64_mem_5]
      congr 1
      exact (UInt8.toNat_ofNat_of_lt' (by simp only [UInt8.size]; omega)).symm
    · rw [singletonMemU64_mem_6]
      congr 1
      exact (UInt8.toNat_ofNat_of_lt' (by simp only [UInt8.size]; omega)).symm
    · rw [singletonMemU64_mem_7]
      congr 1
      exact (UInt8.toNat_ofNat_of_lt' (by simp only [UInt8.size]; omega)).symm
    · exact absurd hk (by omega)
  · show (singletonMemU64 a v).mem x = (singletonMemBytes a (u64LE v)).mem x
    rw [singletonMemU64_mem_outside a v x (by omega),
        singletonMemBytes_mem_outside a (u64LE v) x (by rw [u64LE_size]; omega)]

/-- The 4-byte LE encoding of `v`'s low 32 bits (byte `k` = `v / 256^k % 256`,
    matching `singletonMemU32`). -/
def u32LE (v : Nat) : ByteArray :=
  ⟨#[(v % 256).toUInt8, (v / 0x100 % 256).toUInt8,
      (v / 0x10000 % 256).toUInt8, (v / 0x1000000 % 256).toUInt8]⟩

@[simp] theorem u32LE_size (v : Nat) : (u32LE v).size = 4 := rfl

/-- A `singletonMemU32` cell is the byte-blob of its 4-byte LE encoding — the
    word-width sibling of `singletonMemU64_eq_bytes` (H8 Phase B-2 byte demotion
    of `stw`/`ldxw`). -/
theorem singletonMemU32_eq_bytes (a v : Nat) :
    singletonMemU32 a v = singletonMemBytes a (u32LE v) := by
  show PartialState.mk _ _ _ _ _ = PartialState.mk _ _ _ _ _
  rw [PartialState.mk.injEq]
  refine ⟨rfl, ?_, rfl, rfl, rfl⟩
  funext x
  by_cases hx : a ≤ x ∧ x < a + 4
  · obtain ⟨hlo, hhi⟩ := hx
    obtain ⟨k, hk, rfl⟩ : ∃ k, k < 4 ∧ x = a + k := ⟨x - a, by omega, by omega⟩
    show (singletonMemU32 a v).mem (a + k) = (singletonMemBytes a (u32LE v)).mem (a + k)
    rw [singletonMemBytes_mem_at a (u32LE v) k (by rw [u32LE_size]; exact hk)]
    rcases k with _|_|_|_|k
    · rw [Nat.add_zero, singletonMemU32_mem_0]
      congr 1
      exact (UInt8.toNat_ofNat_of_lt' (by simp only [UInt8.size]; omega)).symm
    · rw [singletonMemU32_mem_1]
      congr 1
      exact (UInt8.toNat_ofNat_of_lt' (by simp only [UInt8.size]; omega)).symm
    · rw [singletonMemU32_mem_2]
      congr 1
      exact (UInt8.toNat_ofNat_of_lt' (by simp only [UInt8.size]; omega)).symm
    · rw [singletonMemU32_mem_3]
      congr 1
      exact (UInt8.toNat_ofNat_of_lt' (by simp only [UInt8.size]; omega)).symm
    · exact absurd hk (by omega)
  · show (singletonMemU32 a v).mem x = (singletonMemBytes a (u32LE v)).mem x
    rw [singletonMemU32_mem_outside a v x (by omega),
        singletonMemBytes_mem_outside a (u32LE v) x (by rw [u32LE_size]; omega)]

/-- One-byte `ByteArray` holding `v`'s low byte. -/
def byteBA (v : Nat) : ByteArray := ⟨#[v.toUInt8]⟩

@[simp] theorem byteBA_size (v : Nat) : (byteBA v).size = 1 := rfl

/-- A single byte cell (`< 256`) is the one-byte blob — the leaf for folding a
    lift's `ldxb`-read cells into a coarse field. -/
theorem singletonMem_eq_bytes (a v : Nat) (hv : v < 256) :
    singletonMem a v = singletonMemBytes a (byteBA v) := by
  show PartialState.mk _ _ _ _ _ = PartialState.mk _ _ _ _ _
  rw [PartialState.mk.injEq]
  refine ⟨rfl, ?_, rfl, rfl, rfl⟩
  funext x
  by_cases hx : x = a
  · subst hx
    show (singletonMem x v).mem x = (singletonMemBytes x (byteBA v)).mem x
    have hb := singletonMemBytes_mem_at x (byteBA v) 0 (by rw [byteBA_size]; omega)
    rw [Nat.add_zero] at hb
    rw [singletonMem_mem_self, hb]
    congr 1
    exact (UInt8.toNat_ofNat_of_lt' (by simp only [UInt8.size]; omega)).symm
  · show (singletonMem a v).mem x = (singletonMemBytes a (byteBA v)).mem x
    rw [singletonMem_mem_other hx,
        singletonMemBytes_mem_outside a (byteBA v) x (by rw [byteBA_size]; omega)]

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

/-- Memory byte at `a` holds `v`. NOTE (L3): `singletonMem` stores `v` RAW (not
    mod 256), so faithful to an 8-bit cell only when `v < 256`. Every `step`
    byte store writes `_ % 256`, so the WF range is all that's ever produced;
    decode-equality specs carry the `v < 256` guard explicitly. (Canonicalizing
    to `v % 256` deferred — ripples through every byte-level spec for a
    not-unsound LOW finding.) -/
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

/-- 32 consecutive bytes at `addr` = `bs` (byte `i` = `(bs.get! i).toNat`), for
    PDA / hash syscalls passing opaque 32-byte blobs (pubkeys, hash outputs). -/
def memBytes32Is (addr : Nat) (bs : ByteArray) : Assertion :=
  fun h => h = PartialState.singletonMem32Bytes addr bs

@[inherit_doc] notation:50 a " ↦Bytes32 " bs => memBytes32Is a bs

/-- `bs.size` consecutive bytes at `addr` = `bs`. Variable-length sibling of
    `memBytes32Is` (PDA seeds, hash inputs). -/
def memBytesIs (addr : Nat) (bs : ByteArray) : Assertion :=
  fun h => h = PartialState.singletonMemBytes addr bs

@[inherit_doc] notation:50 a " ↦Bytes " bs => memBytesIs a bs

/-- The PC holds value `v`, and that's all we own. -/
def pcIs (v : Nat) : Assertion :=
  fun h => h = PartialState.singletonPC v

/-- The returnData buffer holds `rd`, and that's all we own. -/
def returnDataIs (rd : ByteArray) : Assertion :=
  fun h => h = PartialState.singletonReturnData rd

@[inherit_doc] notation:50 "↦ReturnData " rd => returnDataIs rd

/-- The call stack equals `cs`, and that's all we own. -/
def callStackIs (cs : List CallFrame) : Assertion :=
  fun h => h = PartialState.singletonCallStack cs

@[inherit_doc] notation:50 "↦CallStack " cs => callStackIs cs

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

/-- Swap the first two atoms of a 3-fold sepConj, for composing specs whose
    assertion orders differ (`ldxb` gives `dst ** src ** mem`, `stxb` wants
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

Building blocks for `Tactic/SL.lean`'s permutation builder, which assembles an
arbitrary-permutation iff between two right-folded sepConjs over the same atom
multiset: pointwise `Iff.refl`/`Iff.trans` plus a frame-on-the-left combinator. -/

theorem sepConj_iff_refl (P : Assertion) : ∀ h, P h ↔ P h :=
  fun _ => Iff.rfl

theorem sepConj_iff_trans_pw {P Q R : Assertion}
    (h1 : ∀ h, P h ↔ Q h) (h2 : ∀ h, Q h ↔ R h) :
    ∀ h, P h ↔ R h :=
  fun h => Iff.trans (h1 h) (h2 h)

theorem sepConj_iff_symm_pw {P Q : Assertion} (h : ∀ x, P x ↔ Q x) :
    ∀ x, Q x ↔ P x :=
  fun x => (h x).symm

/-- Reshape the right operand of a sepConj (pointwise iff over the tail lifts to
    `(P ** _)`); descends through the right spine. -/
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

/-! ## List-fold sepConj + permutation iff

`foldSepConj` collapses a `List Assertion` into a right-folded sepConj with
trailing `emp`. This shape admits a uniform `cons` case, making the
permutation-invariance theorem `foldSepConj_perm` a clean `List.Perm` induction.

The payoff: `sl_block_iter` builds a permutation iff in **constant** Expr size
(one `foldSepConj_perm`) instead of an O(N²) adjacent-swap chain — linear, not
super-linear, in atom count (plus the O(N) `bridge` to/from the trailing-emp
form). -/

/-- Right-folded sepConj with trailing `emp`. For `[a, b, c]`:
    `a ** (b ** (c ** emp))`. Always defined (empty list = `emp`). -/
def foldSepConj : List Assertion → Assertion
  | [] => emp
  | a :: rest => a ** foldSepConj rest

@[simp] theorem foldSepConj_nil : foldSepConj [] = emp := rfl

@[simp] theorem foldSepConj_cons (a : Assertion) (rest : List Assertion) :
    foldSepConj (a :: rest) = (a ** foldSepConj rest) := rfl

/-- Permutation-invariance: any List-permutation of the atoms preserves
    `foldSepConj`'s truth-set. `List.Perm` induction's `cons`/`swap`/`trans`
    cases map to `congr_right` / `swap_first_two` / `Iff.trans`. -/
theorem foldSepConj_perm {l1 l2 : List Assertion} (h : l1.Perm l2) :
    ∀ s, foldSepConj l1 s ↔ foldSepConj l2 s := by
  induction h with
  | nil => intro s; exact Iff.rfl
  | cons x _ ih =>
    intro s
    show (x ** foldSepConj _) s ↔ (x ** foldSepConj _) s
    refine ⟨?_, ?_⟩
    · rintro ⟨h1, h2, hd, hu, hP, hQ⟩
      exact ⟨h1, h2, hd, hu, hP, (ih h2).mp hQ⟩
    · rintro ⟨h1, h2, hd, hu, hP, hQ⟩
      exact ⟨h1, h2, hd, hu, hP, (ih h2).mpr hQ⟩
  | swap x y rest =>
    intro s
    -- List.Perm.swap : (x :: y :: l).Perm (y :: x :: l) — note x is first on LHS
    -- foldSepConj (y :: x :: rest) = y ** (x ** foldSepConj rest)
    -- foldSepConj (x :: y :: rest) = x ** (y ** foldSepConj rest)
    show (y ** x ** foldSepConj rest) s ↔ (x ** y ** foldSepConj rest) s
    exact sepConj_swap_first_two s
  | trans _ _ ih1 ih2 =>
    intro s; exact (ih1 s).trans (ih2 s)

/-- Swap adjacent elements at position `k`. Structural recursion on the spine —
    no `Inhabited` needed (no out-of-range lookup), and the perm proof follows
    by the same induction. -/
def swapAt {α} : List α → Nat → List α
  | [], _ => []
  | [a], _ => [a]
  | a :: b :: rest, 0 => b :: a :: rest
  | a :: b :: rest, k + 1 => a :: swapAt (b :: rest) k

theorem swapAt_perm {α} : ∀ (l : List α) (k : Nat), l.Perm (swapAt l k)
  | [], _ => List.Perm.refl _
  | [_], _ => List.Perm.refl _
  | a :: b :: rest, 0 => List.Perm.swap b a rest
  | a :: b :: rest, k + 1 => List.Perm.cons a (swapAt_perm (b :: rest) k)

/-- Apply a sequence of adjacent-position swaps to a list, left-to-right. -/
def applySwaps {α} (l : List α) (swaps : List Nat) : List α :=
  swaps.foldl swapAt l

theorem applySwaps_perm {α} (l : List α) (swaps : List Nat) :
    l.Perm (applySwaps l swaps) := by
  induction swaps generalizing l with
  | nil => exact List.Perm.refl l
  | cons k rest ih =>
    show l.Perm (applySwaps (swapAt l k) rest)
    exact (swapAt_perm l k).trans (ih (swapAt l k))

/-- `(P ** emp) h ↔ P h` flipped — the bridge from a no-trailing-emp sepConj to
    the trailing-emp form at the singleton-list base case. -/
theorem sepConj_emp_right_symm {P : Assertion} : ∀ h, P h ↔ (P ** emp) h :=
  fun h => (sepConj_emp_right h).symm

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

/-! ## pcFree — assertion does not own the PC -/

/-- An assertion is *pc-free* when no satisfying partial state owns the PC — the
    frame side-condition in `cuTripleWithin` so a PC bump doesn't invalidate it. -/
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

theorem pcFree_memBytes32Is (a : Nat) (bs : ByteArray) : (memBytes32Is a bs).pcFree := by
  intro h heq; rw [heq]; rfl

theorem pcFree_memBytesIs (a : Nat) (bs : ByteArray) : (memBytesIs a bs).pcFree := by
  intro h heq; rw [heq]; rfl

theorem pcFree_callStackIs (cs : List CallFrame) : (callStackIs cs).pcFree := by
  intro h heq; rw [heq]; rfl

theorem pcFree_returnDataIs (rd : ByteArray) : (returnDataIs rd).pcFree := by
  intro h heq; rw [heq]; rfl

theorem pcFree_sepConj {P Q : Assertion} (hP : P.pcFree) (hQ : Q.pcFree) :
    (P ** Q).pcFree := by
  rintro h ⟨h1, h2, _, hu, hP1, hQ2⟩
  rw [← hu, PartialState.union_pc_of_left_none (hP _ hP1)]
  exact hQ _ hQ2

/-- SL split/join for the byte-blob atom: `↦Bytes` over a concatenation
    separates into two adjacent sub-blobs — the reusable bridge from a lift's
    fine cells to coarse `↦Bytes`/`↦Pubkey` account-field atoms. -/
theorem memBytesIs_append (addr : Nat) (bs1 bs2 : ByteArray) :
    ∀ h, memBytesIs addr (bs1 ++ bs2) h ↔
         (memBytesIs addr bs1 ** memBytesIs (addr + bs1.size) bs2) h := by
  intro h
  constructor
  · intro hh
    exact ⟨PartialState.singletonMemBytes addr bs1,
           PartialState.singletonMemBytes (addr + bs1.size) bs2,
           PartialState.singletonMemBytes_disjoint_adj addr bs1 bs2,
           (PartialState.singletonMemBytes_union_adj addr bs1 bs2).trans hh.symm, rfl, rfl⟩
  · rintro ⟨h1, h2, _, hu, h1eq, h2eq⟩
    show h = PartialState.singletonMemBytes addr (bs1 ++ bs2)
    rw [← hu, h1eq, h2eq, PartialState.singletonMemBytes_union_adj]

/-- SL bridge: a `↦U64` cell equals the `↦Bytes` blob of its 8-byte LE encoding.
    With `memBytesIs_append`, folds dword-load cells into a coarse account
    field. -/
theorem memU64Is_eq_memBytesIs (a v : Nat) :
    ∀ h, memU64Is a v h ↔ memBytesIs a (PartialState.u64LE v) h := by
  intro h
  rw [show memU64Is a v h = (h = PartialState.singletonMemU64 a v) from rfl,
      show memBytesIs a (PartialState.u64LE v) h
         = (h = PartialState.singletonMemBytes a (PartialState.u64LE v)) from rfl,
      PartialState.singletonMemU64_eq_bytes]

/-- SL bridge: a `↦U32` cell equals the `↦Bytes` blob of its 4-byte LE encoding
    (word-width sibling of `memU64Is_eq_memBytesIs`). -/
theorem memU32Is_eq_memBytesIs (a v : Nat) :
    ∀ h, memU32Is a v h ↔ memBytesIs a (PartialState.u32LE v) h := by
  intro h
  rw [show memU32Is a v h = (h = PartialState.singletonMemU32 a v) from rfl,
      show memBytesIs a (PartialState.u32LE v) h
         = (h = PartialState.singletonMemBytes a (PartialState.u32LE v)) from rfl,
      PartialState.singletonMemU32_eq_bytes]

/-- SL bridge: a single byte cell `↦ₘ` (`< 256`) equals the one-byte `↦Bytes`
    blob. With `memBytesIs_append`, folds `ldxb`-read cells into a coarse field. -/
theorem memByteIs_eq_memBytesIs (a v : Nat) (hv : v < 256) :
    ∀ h, memByteIs a v h ↔ memBytesIs a (PartialState.byteBA v) h := by
  intro h
  rw [show memByteIs a v h = (h = PartialState.singletonMem a v) from rfl,
      show memBytesIs a (PartialState.byteBA v) h
         = (h = PartialState.singletonMemBytes a (PartialState.byteBA v)) from rfl,
      PartialState.singletonMem_eq_bytes a v hv]

end SVM.SBPF
