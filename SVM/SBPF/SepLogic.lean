/-
  Separation logic over sBPF machine state.

  Following Kennedy et al. (2013) and the EvmAsm.Rv64.SepLogic adaptation
  in Verified-zkEVM/evm-asm: registers, memory bytes, and the program
  counter are separable resources. An `Assertion` is a predicate on a
  `PartialState` (a partial heap that owns some subset of those resources).
  The separating conjunction `P ** Q` holds when the partial state splits
  into two disjoint pieces, with `P` holding on one and `Q` on the other.

  The bridge to the executable `State` from `SVM.SBPF.Execute` is
  `Assertion.holdsFor`: an assertion holds for a full machine state when
  some partial state compatible with the full state satisfies it.

  Memory is byte-level. Multi-byte (u64) assertions are built from byte
  points-to via `**`.
-/

import SVM.SBPF.Execute

namespace SVM.SBPF

/-! ## PartialState — partial ownership of registers, memory, PC

Extending `PartialState` with a new resource field (e.g., the future
`returnData : Option ByteArray` of deferred lift #2):

1. Add the field to `PartialState` below.
2. Add a `singletonX` builder + projection lemmas (mirror the existing
   `singletonPC` pattern — defaults the new field to `none` on the
   other singletons via `@[simp]` lemmas).
3. Add one clause to `Disjoint` and one to `CompatibleWith` for the
   new field.
4. Extend `union` (and its `union_X_of_left_*` / `union_X_eq_none_iff`
   field helpers). `union_empty_left`/`union_empty_right`/`union_assoc`
   pick up the new field automatically once the `match` is added.

Destructure sites are stable: `hd.regs` / `hd.mem` / `hd.pc` continue
to work after a new field appears at the bottom of either structure.
Only construction sites that build `Disjoint` or `CompatibleWith`
directly need the new field — they're locatable by `lake build`.
-/

/-- A partial view of an sBPF machine state. `some v` means we own the
    resource and assert its value is `v`; `none` means we don't own it.

    `returnData` and `callStack` default to `none` so singleton builders
    that use record-construction syntax pick up the defaults automatically. -/
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

/-- Two partial states are disjoint if they never both own the same resource.

    Field-wise structure: each field of `PartialState` contributes one
    disjointness clause. Adding a new field to `PartialState` adds one
    clause here — call sites that access `hd.regs` / `hd.mem` / `hd.pc`
    keep working unchanged; only construction sites need to provide the
    new field. -/
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

/-- A partial state is compatible with a full machine state if every
    owned resource agrees with the full state.

    Mirrors `Disjoint` — field-wise structure, one clause per
    `PartialState` field. -/
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

The partial state owns 32 bytes starting at `addr`, where byte `i ∈
[0, 32)` equals `(bs.get! i).toNat`. Used as the building block for
the `↦Bytes32` assertion that PDA / hash-family syscall specs need.

Unlike the `U16`/`U32`/`U64` atoms (which carry a Nat decoded LE),
this atom carries an opaque `ByteArray` payload — bytes are indexed,
not integer-decoded. Callers are expected to keep `bs.size = 32`;
larger arrays have their tail ignored, smaller arrays fall through
to `bs.get!`'s default (zero). -/

/-- Partial state owning 32 consecutive memory bytes whose contents are
    `bs`. A single conditional, not 32 unrolled `if`s — keeps both the
    definition and the byte-extraction proof linear in size. -/
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

/-- Byte at offset `i ∈ [0, 32)` equals `(bs.get! i).toNat`. The single
    parameterized lemma replaces 32 unrolled `_mem_i` lemmas. -/
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

Generalization of `singletonMem32Bytes` to arbitrary lengths. The
partial state owns `bs.size` bytes starting at `addr`, where byte
`i ∈ [0, bs.size)` equals `(bs.get! i).toNat`. Used by syscall
specs that read variable-length data (PDA seeds, hash inputs, etc.).

For `bs.size = 0` the atom owns nothing — equivalent to `empty`
on the mem side. -/

/-- Partial state owning `bs.size` consecutive memory bytes whose
    contents are `bs`. Single-conditional `mem` field, same shape
    as `singletonMem32Bytes` but parametric in length. -/
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

For each memory atom, "address in range ⇒ atom owns it" packaged as an
`∃ v, mem a = some v` witness. The range-disjointness pattern picks a
sentinel address in one atom's range and uses these helpers together
with SL disjointness to conclude the other atom doesn't own it. -/

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

theorem singletonMem32Bytes_mem_isSome (addr : Nat) (bs : ByteArray) (a : Nat)
    (h : addr ≤ a ∧ a < addr + 32) :
    ∃ x, (singletonMem32Bytes addr bs).mem a = some x := by
  obtain ⟨h1, h2⟩ := h
  have h_lt : a - addr < 32 := by omega
  have key := singletonMem32Bytes_mem_at addr bs (a - addr) h_lt
  rw [show addr + (a - addr) = a from by omega] at key
  exact ⟨_, key⟩

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

/-- Simp-friendly form: if both halves have `returnData = none`, so does
    the union. The two side conditions are discharged by the per-atom
    `singletonX_returnData = none` `@[simp]` lemmas, so this enables
    `by simp` to close arbitrarily-deep `(unions).returnData = none`
    goals built from non-returnData atoms. -/
@[simp] theorem union_returnData_eq_none_of_both {h1 h2 : PartialState}
    (h1_rd : h1.returnData = none) (h2_rd : h2.returnData = none) :
    (h1.union h2).returnData = none := by
  rw [union_returnData_of_left_none h1_rd]; exact h2_rd

/-- Equational version of the `union_returnData_eq_none_iff` lemma —
    `@[simp]` so that simp can recursively reduce `(unions).returnData`
    to a chain of singleton-returnData lookups. -/
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

/-! ## Union lemmas -/

theorem union_empty_left {h : PartialState} : empty.union h = h := by
  cases h
  rfl

theorem union_empty_right {h : PartialState} : h.union empty = h := by
  obtain ⟨regs, mem, pc, rd, cs⟩ := h
  show PartialState.mk _ _ _ _ _ = _
  simp only [PartialState.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext r; cases regs r <;> rfl
  · funext a; cases mem  a <;> rfl
  · cases pc <;> rfl
  · cases rd <;> rfl
  · cases cs <;> rfl

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

These relate a single `singletonMemBytes` blob to the union of two
adjacent blobs, the foundation for reshaping a lift's scattered
byte/dword cells into the coarse `↦Bytes`/`↦Pubkey` account-field
atoms a `tokenAcctBalance` refinement needs. -/

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

/-- 32 consecutive memory bytes at `addr` whose contents are the
    `ByteArray` `bs`. Byte `i ∈ [0, 32)` holds `(bs.get! i).toNat`.
    Used by PDA / hash syscall specs that pass opaque 32-byte blobs
    (pubkeys, hash outputs) where a single-Nat decode isn't useful. -/
def memBytes32Is (addr : Nat) (bs : ByteArray) : Assertion :=
  fun h => h = PartialState.singletonMem32Bytes addr bs

@[inherit_doc] notation:50 a " ↦Bytes32 " bs => memBytes32Is a bs

/-- `bs.size` consecutive memory bytes at `addr` whose contents are
    the `ByteArray` `bs`. Variable-length sibling of `memBytes32Is`,
    used by syscall specs that read variable-length data (PDA seeds,
    hash inputs). -/
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
`Tactic/SL.lean` uses to assemble an arbitrary-permutation iff between
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

/-! ## List-fold sepConj + permutation iff

`foldSepConj` collapses a `List Assertion` into a right-folded
sepConj with `emp` at the trailing position. This shape (vs the
"no trailing emp" form `rebuildSepConj` produces in tactic land)
admits a uniform `cons` case in proofs, making the
permutation-invariance theorem `foldSepConj_perm` a clean induction
on `List.Perm`.

The point of these lemmas is that `sl_block_iter`'s tactic
machinery can then build a permutation iff in **constant** Expr
size (one application of `foldSepConj_perm`), instead of the
previous O(N²) chain of adjacent-swap applications. This dropped
the bridge step from being super-linear in atom count to linear
(plus a `bridge` lemma below to/from the trailing-emp form,
which is O(N) per side). -/

/-- Right-folded sepConj with trailing `emp`. For `[a, b, c]`:
    `a ** (b ** (c ** emp))`. Always defined (empty list = `emp`). -/
def foldSepConj : List Assertion → Assertion
  | [] => emp
  | a :: rest => a ** foldSepConj rest

@[simp] theorem foldSepConj_nil : foldSepConj [] = emp := rfl

@[simp] theorem foldSepConj_cons (a : Assertion) (rest : List Assertion) :
    foldSepConj (a :: rest) = (a ** foldSepConj rest) := rfl

/-- The permutation-invariance theorem: any List-permutation of the
    atoms preserves the `foldSepConj` assertion's truth-set.
    Induction on `List.Perm` decomposes into `cons`/`swap`/`trans`,
    each handled by an existing structural sepConj lemma
    (`congr_right` / `swap_first_two` / `Iff.trans`). -/
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

/-- Swap adjacent elements at position `k` in a list. Structural recursion
    on the list's spine — needs no `Inhabited` instance (no out-of-range
    lookup), and the perm proof falls out by the same induction. -/
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

/-- Convenience: the perm-iff between two `foldSepConj`s where the
    second is the result of applying a swap sequence to the first.
    This is the "single application" the sl_block_iter tactic needs to
    replace its O(N²) iff chain. -/
theorem foldSepConj_applySwaps_iff (atoms : List Assertion) (swaps : List Nat) :
    ∀ s, foldSepConj atoms s ↔ foldSepConj (applySwaps atoms swaps) s :=
  foldSepConj_perm (applySwaps_perm atoms swaps)

/-- `(P ** emp) h ↔ P h` flipped. The bridge from a "no trailing emp"
    sepConj (`rebuildSepConj`'s output) to a "trailing emp" form
    (`foldSepConj`'s output) at the singleton-list base case. -/
theorem sepConj_emp_right_symm {P : Assertion} : ∀ h, P h ↔ (P ** emp) h :=
  fun h => (sepConj_emp_right h).symm

/-- Symmetry of pointwise iff. Used to flip `bridge2` (foldSepConj →
    rebuildSepConj) from its naturally-stated direction. -/
theorem sepConj_iff_pw_symm {P Q : Assertion} (h : ∀ s, P s ↔ Q s) :
    ∀ s, Q s ↔ P s := fun s => (h s).symm

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

/-- SL-level split/join for the byte-blob atom: a `↦Bytes` over a
    concatenation separates into the two adjacent sub-blobs. The
    reusable bridge from a lift's fine-grained cells to the coarse
    `↦Bytes`/`↦Pubkey` account-field atoms of `tokenAcctBalance`. -/
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

end SVM.SBPF
