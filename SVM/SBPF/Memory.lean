-- Flat byte-addressable memory model for sBPF verification.
--
-- Mapped regions (NOTHING below 0x100000000):
--   0x100000000 : Program region (.text + .rodata + .data.rel.ro)
--   0x200000000 : Stack
--   0x300000000 : Heap
--   0x400000000 : Input buffer (serialized accounts + instruction data)
--
-- "No low region" is load-bearing: `effectiveAddr` clamps a negative address
-- to 0, so the fault there is only sound while address 0 is unmapped (M3).
-- Programs receive the input buffer pointer in r1 at entry.

import SVM.SBPF.ISA
import Std.Data.HashMap

namespace SVM.SBPF.Memory

open SVM.SBPF

/-! ## Memory type

Was `abbrev Mem := Nat → Nat`, where each `writeU*` returned a closure, so a
read walked an N-deep chain (SPL Token: ~50min `diff_mollusk`). Now a thin
overlay: writes go into a `Std.HashMap Nat UInt8`, reads check the overlay then
fall through to `default` on miss. The `Coe (Nat → Nat) Mem` keeps closure-style
constructors (sysvar/Pda/Native bodies, cold paths) type-checking via `default`;
the `CoeFun` keeps the `mem a` syntax compiling at every call site. -/

structure Mem where
  default : Nat → Nat := fun _ => 0
  overlay : Std.HashMap Nat UInt8 := {}

/-- Look up a byte: overlay first, fall through to `default` on miss. -/
@[inline] def Mem.read (m : Mem) (a : Nat) : Nat :=
  match m.overlay[a]? with
  | some b => b.toNat
  | none   => m.default a

/-- Insert one byte into the overlay (mod 256).

    `irreducible` so `whnf` stops here: the struct-update chain has no lambda
    head (unlike the old `Nat → Nat` `writeU*`), so whnf'd recursively into
    HashMap internals, blowing heartbeats in `Region.lean`/`InstructionSpecs`.
    Opaque restores the old behavior — everything goes through simp/rw rules. -/
@[inline, irreducible] def Mem.put (m : Mem) (addr val : Nat) : Mem :=
  { m with overlay := m.overlay.insert addr (val % 256).toUInt8 }

/-- Apply syntax: `mem a` desugars to `Mem.read mem a`. -/
instance : CoeFun Mem (fun _ => Nat → Nat) := ⟨Mem.read⟩

/-- Lift a `Nat → Nat` to a `Mem` with empty overlay and `default := f`.
    Closure-style constructors ride this. -/
instance : Coe (Nat → Nat) Mem := ⟨fun f => { default := f }⟩

instance : Inhabited Mem := ⟨{}⟩

/-! ## `Mem.put` / `Mem.read` interaction lemmas

Semantic API for the (opaque) overlay model: the rest of the code reasons via
these. `@[simp]` so `unfold Memory.writeU8; simp` patterns close. -/

@[simp] theorem Mem.read_put_self (m : Mem) (addr val : Nat) :
    (Mem.put m addr val).read addr = val % 256 := by
  unfold Mem.put Mem.read
  simp

@[simp] theorem Mem.read_put_other (m : Mem) (addr addr' val : Nat) (h : addr' ≠ addr) :
    (Mem.put m addr val).read addr' = m.read addr' := by
  unfold Mem.put Mem.read
  simp [Std.HashMap.getElem?_insert, Ne.symm h]

/-- if-form of `Mem.read (Mem.put ...) ...`: recovers the old `writeU8`
    post-unfold shape so existing `unfold Memory.writeU8; show (if ...)`
    patterns still match. `@[simp]` reproduces the pre-refactor goal shape;
    subsumes `read_put_self`/`read_put_other` (kept for direct `rw`). -/
@[simp] theorem Mem.read_put (m : Mem) (addr val a : Nat) :
    Mem.read (Mem.put m addr val) a =
      if a = addr then val % 256 else Mem.read m a := by
  by_cases h : a = addr
  · subst h; simp [Mem.read_put_self]
  · simp [Mem.read_put_other _ _ _ _ h, h]

/-! ## Region base addresses -/

-- Unused: `.rodata` lives inside the program region, not at 0; nothing is
-- mapped at address 0 (M3). Kept for reference.
def RODATA_START   : Nat := 0x000000000
def BYTECODE_START : Nat := 0x100000000
def STACK_START    : Nat := 0x200000000
def HEAP_START     : Nat := 0x300000000
def INPUT_START    : Nat := 0x400000000

/-- Size of each sBPF region (= the region spacing). Also the threshold below
    which the ELF loader's `R_BPF_64_Relative` patch bumps an address into the
    program region (`MM_PROGRAM_START` in agave). -/
def MM_REGION_SIZE : Nat := 0x100000000

/-! ## Effective address computation -/

/-- Effective address from base register and signed offset.

    NOTE: `Int.toNat` clamps negative results to 0; real sBPF would trap them on
    the region bounds check. Unreachable in practice (verified programs use
    non-negative offsets); sound because address 0 is unmapped (M3). -/
def effectiveAddr (base : Nat) (off : Int) : Nat :=
  Int.toNat ((↑base : Int) + off)

/-! ## Read operations (little-endian) -/

/-- Read 1 byte -/
def readU8 (mem : Mem) (addr : Nat) : Nat :=
  mem addr % 256

/-- Read 2 bytes little-endian -/
def readU16 (mem : Mem) (addr : Nat) : Nat :=
  mem addr % 256 +
  mem (addr + 1) % 256 * 0x100

/-- Read 4 bytes little-endian -/
def readU32 (mem : Mem) (addr : Nat) : Nat :=
  mem addr % 256 +
  mem (addr + 1) % 256 * 0x100 +
  mem (addr + 2) % 256 * 0x10000 +
  mem (addr + 3) % 256 * 0x1000000

/-- Read 8 bytes little-endian -/
def readU64 (mem : Mem) (addr : Nat) : Nat :=
  mem addr % 256 +
  mem (addr + 1) % 256 * 0x100 +
  mem (addr + 2) % 256 * 0x10000 +
  mem (addr + 3) % 256 * 0x1000000 +
  mem (addr + 4) % 256 * 0x100000000 +
  mem (addr + 5) % 256 * 0x10000000000 +
  mem (addr + 6) % 256 * 0x1000000000000 +
  mem (addr + 7) % 256 * 0x100000000000000

/-! ## Write operations (little-endian)

Each write updates the overlay, leaving `default` untouched. These are the only
overlay-fast-path sites; closure-style constructors land in `default` and pay
chain-walk on read, which is fine since they run O(1) times (vs `writeU*` once
per store, millions of times). -/

/-- Write 1 byte. Inserts `val % 256` at `addr`. -/
def writeU8 (mem : Mem) (addr val : Nat) : Mem :=
  Mem.put mem addr val

/-- Write 2 bytes little-endian.

    NOTE: low byte outermost (`addr` last) on purpose, so `simp [Mem.read_put]`
    peels into the same nested-if order as the pre-refactor lambda body and
    existing `unfold Memory.writeU16; show (if ...)` patterns still match. -/
def writeU16 (mem : Mem) (addr val : Nat) : Mem :=
  let m1 := Mem.put mem  (addr + 1)  (val / 0x100 % 0x100)
  Mem.put m1                  addr        (val % 0x100)

/-- Write 4 bytes little-endian. Low byte outermost; see `writeU16`. -/
def writeU32 (mem : Mem) (addr val : Nat) : Mem :=
  let m1 := Mem.put mem  (addr + 3)  (val / 0x1000000 % 0x100)
  let m2 := Mem.put m1   (addr + 2)  (val / 0x10000 % 0x100)
  let m3 := Mem.put m2   (addr + 1)  (val / 0x100 % 0x100)
  Mem.put m3             addr        (val % 0x100)

/-- Write 8 bytes little-endian. Low byte outermost; see `writeU16`. -/
def writeU64 (mem : Mem) (addr val : Nat) : Mem :=
  let m1 := Mem.put mem  (addr + 7)  (val / 0x100000000000000 % 0x100)
  let m2 := Mem.put m1   (addr + 6)  (val / 0x1000000000000 % 0x100)
  let m3 := Mem.put m2   (addr + 5)  (val / 0x10000000000 % 0x100)
  let m4 := Mem.put m3   (addr + 4)  (val / 0x100000000 % 0x100)
  let m5 := Mem.put m4   (addr + 3)  (val / 0x1000000 % 0x100)
  let m6 := Mem.put m5   (addr + 2)  (val / 0x10000 % 0x100)
  let m7 := Mem.put m6   (addr + 1)  (val / 0x100 % 0x100)
  Mem.put m7             addr        (val % 0x100)

/-! ## Generic read/write by width -/

/-- Read N bytes from memory according to width -/
def readByWidth (mem : Mem) (addr : Nat) : SVM.SBPF.Width → Nat
  | .byte  => readU8 mem addr
  | .half  => readU16 mem addr
  | .word  => readU32 mem addr
  | .dword => readU64 mem addr

/-- Write N bytes to memory according to width -/
def writeByWidth (mem : Mem) (addr val : Nat) : SVM.SBPF.Width → Mem
  | .byte  => writeU8 mem addr val
  | .half  => writeU16 mem addr val
  | .word  => writeU32 mem addr val
  | .dword => writeU64 mem addr val

/-! ## Per-byte read lemmas for `writeU{8,16,32,64}`

Per width: `read_at_i` reads back the i-th written byte, `read_other` propagates
a read outside the write footprint. The round-trip/disjoint theorems below are
then mechanical (one per byte). All discharge via `Mem.read_put_{self,other}`
plus a constant-base `omega`. -/

theorem writeU8_read_at (mem : Mem) (addr val : Nat) :
    (writeU8 mem addr val).read addr = val % 256 := by
  unfold writeU8; rw [Mem.read_put_self]

theorem writeU8_read_other (mem : Mem) (addr val a : Nat) (h : a ≠ addr) :
    (writeU8 mem addr val).read a = mem.read a := by
  unfold writeU8; exact Mem.read_put_other mem addr a val h

theorem writeU16_read_at_0 (mem : Mem) (addr val : Nat) :
    (writeU16 mem addr val).read addr = val % 256 := by
  unfold writeU16; rw [Mem.read_put_self]; omega

theorem writeU16_read_at_1 (mem : Mem) (addr val : Nat) :
    (writeU16 mem addr val).read (addr + 1) = val / 256 % 256 := by
  unfold writeU16
  rw [Mem.read_put_other _ _ _ _ (by omega : addr + 1 ≠ addr),
      Mem.read_put_self]
  omega

theorem writeU16_read_other (mem : Mem) (addr val a : Nat)
    (h0 : a ≠ addr) (h1 : a ≠ addr + 1) :
    (writeU16 mem addr val).read a = mem.read a := by
  unfold writeU16
  rw [Mem.read_put_other _ _ _ _ h0,
      Mem.read_put_other _ _ _ _ h1]

theorem writeU32_read_at_0 (mem : Mem) (addr val : Nat) :
    (writeU32 mem addr val).read addr = val % 256 := by
  unfold writeU32; rw [Mem.read_put_self]; omega

theorem writeU32_read_at_1 (mem : Mem) (addr val : Nat) :
    (writeU32 mem addr val).read (addr + 1) = val / 256 % 256 := by
  unfold writeU32
  rw [Mem.read_put_other _ _ _ _ (by omega : addr + 1 ≠ addr),
      Mem.read_put_self]
  omega

theorem writeU32_read_at_2 (mem : Mem) (addr val : Nat) :
    (writeU32 mem addr val).read (addr + 2) = val / 65536 % 256 := by
  unfold writeU32
  rw [Mem.read_put_other _ _ _ _ (by omega : addr + 2 ≠ addr),
      Mem.read_put_other _ _ _ _ (by omega : addr + 2 ≠ addr + 1),
      Mem.read_put_self]
  omega

theorem writeU32_read_at_3 (mem : Mem) (addr val : Nat) :
    (writeU32 mem addr val).read (addr + 3) = val / 16777216 % 256 := by
  unfold writeU32
  rw [Mem.read_put_other _ _ _ _ (by omega : addr + 3 ≠ addr),
      Mem.read_put_other _ _ _ _ (by omega : addr + 3 ≠ addr + 1),
      Mem.read_put_other _ _ _ _ (by omega : addr + 3 ≠ addr + 2),
      Mem.read_put_self]
  omega

theorem writeU32_read_other (mem : Mem) (addr val a : Nat)
    (h0 : a ≠ addr) (h1 : a ≠ addr + 1) (h2 : a ≠ addr + 2) (h3 : a ≠ addr + 3) :
    (writeU32 mem addr val).read a = mem.read a := by
  unfold writeU32
  rw [Mem.read_put_other _ _ _ _ h0,
      Mem.read_put_other _ _ _ _ h1,
      Mem.read_put_other _ _ _ _ h2,
      Mem.read_put_other _ _ _ _ h3]

theorem writeU64_read_at_0 (mem : Mem) (addr val : Nat) :
    (writeU64 mem addr val).read addr = val % 256 := by
  unfold writeU64; rw [Mem.read_put_self]; omega

theorem writeU64_read_at_1 (mem : Mem) (addr val : Nat) :
    (writeU64 mem addr val).read (addr + 1) = val / 256 % 256 := by
  unfold writeU64
  rw [Mem.read_put_other _ _ _ _ (by omega : addr + 1 ≠ addr),
      Mem.read_put_self]
  omega

theorem writeU64_read_at_2 (mem : Mem) (addr val : Nat) :
    (writeU64 mem addr val).read (addr + 2) = val / 65536 % 256 := by
  unfold writeU64
  rw [Mem.read_put_other _ _ _ _ (by omega : addr + 2 ≠ addr),
      Mem.read_put_other _ _ _ _ (by omega : addr + 2 ≠ addr + 1),
      Mem.read_put_self]
  omega

theorem writeU64_read_at_3 (mem : Mem) (addr val : Nat) :
    (writeU64 mem addr val).read (addr + 3) = val / 16777216 % 256 := by
  unfold writeU64
  rw [Mem.read_put_other _ _ _ _ (by omega : addr + 3 ≠ addr),
      Mem.read_put_other _ _ _ _ (by omega : addr + 3 ≠ addr + 1),
      Mem.read_put_other _ _ _ _ (by omega : addr + 3 ≠ addr + 2),
      Mem.read_put_self]
  omega

theorem writeU64_read_at_4 (mem : Mem) (addr val : Nat) :
    (writeU64 mem addr val).read (addr + 4) = val / 4294967296 % 256 := by
  unfold writeU64
  rw [Mem.read_put_other _ _ _ _ (by omega : addr + 4 ≠ addr),
      Mem.read_put_other _ _ _ _ (by omega : addr + 4 ≠ addr + 1),
      Mem.read_put_other _ _ _ _ (by omega : addr + 4 ≠ addr + 2),
      Mem.read_put_other _ _ _ _ (by omega : addr + 4 ≠ addr + 3),
      Mem.read_put_self]
  omega

theorem writeU64_read_at_5 (mem : Mem) (addr val : Nat) :
    (writeU64 mem addr val).read (addr + 5) = val / 1099511627776 % 256 := by
  unfold writeU64
  rw [Mem.read_put_other _ _ _ _ (by omega : addr + 5 ≠ addr),
      Mem.read_put_other _ _ _ _ (by omega : addr + 5 ≠ addr + 1),
      Mem.read_put_other _ _ _ _ (by omega : addr + 5 ≠ addr + 2),
      Mem.read_put_other _ _ _ _ (by omega : addr + 5 ≠ addr + 3),
      Mem.read_put_other _ _ _ _ (by omega : addr + 5 ≠ addr + 4),
      Mem.read_put_self]
  omega

theorem writeU64_read_at_6 (mem : Mem) (addr val : Nat) :
    (writeU64 mem addr val).read (addr + 6) = val / 281474976710656 % 256 := by
  unfold writeU64
  rw [Mem.read_put_other _ _ _ _ (by omega : addr + 6 ≠ addr),
      Mem.read_put_other _ _ _ _ (by omega : addr + 6 ≠ addr + 1),
      Mem.read_put_other _ _ _ _ (by omega : addr + 6 ≠ addr + 2),
      Mem.read_put_other _ _ _ _ (by omega : addr + 6 ≠ addr + 3),
      Mem.read_put_other _ _ _ _ (by omega : addr + 6 ≠ addr + 4),
      Mem.read_put_other _ _ _ _ (by omega : addr + 6 ≠ addr + 5),
      Mem.read_put_self]
  omega

theorem writeU64_read_at_7 (mem : Mem) (addr val : Nat) :
    (writeU64 mem addr val).read (addr + 7) = val / 72057594037927936 % 256 := by
  unfold writeU64
  rw [Mem.read_put_other _ _ _ _ (by omega : addr + 7 ≠ addr),
      Mem.read_put_other _ _ _ _ (by omega : addr + 7 ≠ addr + 1),
      Mem.read_put_other _ _ _ _ (by omega : addr + 7 ≠ addr + 2),
      Mem.read_put_other _ _ _ _ (by omega : addr + 7 ≠ addr + 3),
      Mem.read_put_other _ _ _ _ (by omega : addr + 7 ≠ addr + 4),
      Mem.read_put_other _ _ _ _ (by omega : addr + 7 ≠ addr + 5),
      Mem.read_put_other _ _ _ _ (by omega : addr + 7 ≠ addr + 6),
      Mem.read_put_self]
  omega

theorem writeU64_read_other (mem : Mem) (addr val a : Nat)
    (h0 : a ≠ addr) (h1 : a ≠ addr + 1) (h2 : a ≠ addr + 2) (h3 : a ≠ addr + 3)
    (h4 : a ≠ addr + 4) (h5 : a ≠ addr + 5) (h6 : a ≠ addr + 6) (h7 : a ≠ addr + 7) :
    (writeU64 mem addr val).read a = mem.read a := by
  unfold writeU64
  rw [Mem.read_put_other _ _ _ _ h0,
      Mem.read_put_other _ _ _ _ h1,
      Mem.read_put_other _ _ _ _ h2,
      Mem.read_put_other _ _ _ _ h3,
      Mem.read_put_other _ _ _ _ h4,
      Mem.read_put_other _ _ _ _ h5,
      Mem.read_put_other _ _ _ _ h6,
      Mem.read_put_other _ _ _ _ h7]

/-! ## Memory coherence theorems (previously axioms; see history)

LE encode/decode round-trips in range (same-address group); a write doesn't
disturb reads outside its footprint (disjoint group). Each reduces to the
per-byte lemmas plus a constant-base `omega`. -/

/-! ### Same-address round-trip -/

/-- Reading back a U64 from the address it was just written to yields the original value -/
theorem readU64_writeU64_same (mem : Mem) (addr val : Nat)
    (h : val < 2 ^ 64) :
    readU64 (writeU64 mem addr val) addr = val := by
  unfold readU64
  show (writeU64 mem addr val).read addr % 256 +
       (writeU64 mem addr val).read (addr + 1) % 256 * 0x100 +
       (writeU64 mem addr val).read (addr + 2) % 256 * 0x10000 +
       (writeU64 mem addr val).read (addr + 3) % 256 * 0x1000000 +
       (writeU64 mem addr val).read (addr + 4) % 256 * 0x100000000 +
       (writeU64 mem addr val).read (addr + 5) % 256 * 0x10000000000 +
       (writeU64 mem addr val).read (addr + 6) % 256 * 0x1000000000000 +
       (writeU64 mem addr val).read (addr + 7) % 256 * 0x100000000000000 = val
  rw [writeU64_read_at_0, writeU64_read_at_1, writeU64_read_at_2, writeU64_read_at_3,
      writeU64_read_at_4, writeU64_read_at_5, writeU64_read_at_6, writeU64_read_at_7]
  omega

/-- Reading back a U32 from the address it was just written to yields the original value -/
theorem readU32_writeU32_same (mem : Mem) (addr val : Nat)
    (h : val < 2 ^ 32) :
    readU32 (writeU32 mem addr val) addr = val := by
  unfold readU32
  show (writeU32 mem addr val).read addr % 256 +
       (writeU32 mem addr val).read (addr + 1) % 256 * 0x100 +
       (writeU32 mem addr val).read (addr + 2) % 256 * 0x10000 +
       (writeU32 mem addr val).read (addr + 3) % 256 * 0x1000000 = val
  rw [writeU32_read_at_0, writeU32_read_at_1, writeU32_read_at_2, writeU32_read_at_3]
  omega

/-- Reading back a U8 from the address it was just written to yields the original value -/
theorem readU8_writeU8_same (mem : Mem) (addr val : Nat)
    (h : val < 2 ^ 8) :
    readU8 (writeU8 mem addr val) addr = val := by
  unfold readU8
  show (writeU8 mem addr val).read addr % 256 = val
  rw [writeU8_read_at]
  omega

/-! ### Disjoint-address theorems (single-premise, within same region) -/

/-- Writing a U64 does not affect reads from non-overlapping addresses -/
theorem readU64_writeU64_disjoint (mem : Mem) (rAddr wAddr val : Nat)
    (h : rAddr + 8 ≤ wAddr ∨ wAddr + 8 ≤ rAddr) :
    readU64 (writeU64 mem wAddr val) rAddr = readU64 mem rAddr := by
  unfold readU64
  show (writeU64 mem wAddr val).read rAddr % 256 +
       (writeU64 mem wAddr val).read (rAddr + 1) % 256 * 0x100 +
       (writeU64 mem wAddr val).read (rAddr + 2) % 256 * 0x10000 +
       (writeU64 mem wAddr val).read (rAddr + 3) % 256 * 0x1000000 +
       (writeU64 mem wAddr val).read (rAddr + 4) % 256 * 0x100000000 +
       (writeU64 mem wAddr val).read (rAddr + 5) % 256 * 0x10000000000 +
       (writeU64 mem wAddr val).read (rAddr + 6) % 256 * 0x1000000000000 +
       (writeU64 mem wAddr val).read (rAddr + 7) % 256 * 0x100000000000000 = _
  rw [writeU64_read_other _ _ _ _
        (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega),
      writeU64_read_other _ _ _ _
        (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega),
      writeU64_read_other _ _ _ _
        (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega),
      writeU64_read_other _ _ _ _
        (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega),
      writeU64_read_other _ _ _ _
        (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega),
      writeU64_read_other _ _ _ _
        (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega),
      writeU64_read_other _ _ _ _
        (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega),
      writeU64_read_other _ _ _ _
        (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)]

/-- Writing a U32 does not affect U64 reads from non-overlapping addresses -/
theorem readU64_writeU32_disjoint (mem : Mem) (rAddr wAddr val : Nat)
    (h : rAddr + 8 ≤ wAddr ∨ wAddr + 4 ≤ rAddr) :
    readU64 (writeU32 mem wAddr val) rAddr = readU64 mem rAddr := by
  unfold readU64
  show (writeU32 mem wAddr val).read rAddr % 256 +
       (writeU32 mem wAddr val).read (rAddr + 1) % 256 * 0x100 +
       (writeU32 mem wAddr val).read (rAddr + 2) % 256 * 0x10000 +
       (writeU32 mem wAddr val).read (rAddr + 3) % 256 * 0x1000000 +
       (writeU32 mem wAddr val).read (rAddr + 4) % 256 * 0x100000000 +
       (writeU32 mem wAddr val).read (rAddr + 5) % 256 * 0x10000000000 +
       (writeU32 mem wAddr val).read (rAddr + 6) % 256 * 0x1000000000000 +
       (writeU32 mem wAddr val).read (rAddr + 7) % 256 * 0x100000000000000 = _
  rw [writeU32_read_other _ _ _ _ (by omega) (by omega) (by omega) (by omega),
      writeU32_read_other _ _ _ _ (by omega) (by omega) (by omega) (by omega),
      writeU32_read_other _ _ _ _ (by omega) (by omega) (by omega) (by omega),
      writeU32_read_other _ _ _ _ (by omega) (by omega) (by omega) (by omega),
      writeU32_read_other _ _ _ _ (by omega) (by omega) (by omega) (by omega),
      writeU32_read_other _ _ _ _ (by omega) (by omega) (by omega) (by omega),
      writeU32_read_other _ _ _ _ (by omega) (by omega) (by omega) (by omega),
      writeU32_read_other _ _ _ _ (by omega) (by omega) (by omega) (by omega)]

/-- Writing a U16 does not affect U64 reads from non-overlapping addresses -/
theorem readU64_writeU16_disjoint (mem : Mem) (rAddr wAddr val : Nat)
    (h : rAddr + 8 ≤ wAddr ∨ wAddr + 2 ≤ rAddr) :
    readU64 (writeU16 mem wAddr val) rAddr = readU64 mem rAddr := by
  unfold readU64
  show (writeU16 mem wAddr val).read rAddr % 256 +
       (writeU16 mem wAddr val).read (rAddr + 1) % 256 * 0x100 +
       (writeU16 mem wAddr val).read (rAddr + 2) % 256 * 0x10000 +
       (writeU16 mem wAddr val).read (rAddr + 3) % 256 * 0x1000000 +
       (writeU16 mem wAddr val).read (rAddr + 4) % 256 * 0x100000000 +
       (writeU16 mem wAddr val).read (rAddr + 5) % 256 * 0x10000000000 +
       (writeU16 mem wAddr val).read (rAddr + 6) % 256 * 0x1000000000000 +
       (writeU16 mem wAddr val).read (rAddr + 7) % 256 * 0x100000000000000 = _
  rw [writeU16_read_other _ _ _ _ (by omega) (by omega),
      writeU16_read_other _ _ _ _ (by omega) (by omega),
      writeU16_read_other _ _ _ _ (by omega) (by omega),
      writeU16_read_other _ _ _ _ (by omega) (by omega),
      writeU16_read_other _ _ _ _ (by omega) (by omega),
      writeU16_read_other _ _ _ _ (by omega) (by omega),
      writeU16_read_other _ _ _ _ (by omega) (by omega),
      writeU16_read_other _ _ _ _ (by omega) (by omega)]

/-- Writing a U8 does not affect U64 reads from non-overlapping addresses -/
theorem readU64_writeU8_disjoint (mem : Mem) (rAddr wAddr val : Nat)
    (h : wAddr < rAddr ∨ rAddr + 8 ≤ wAddr) :
    readU64 (writeU8 mem wAddr val) rAddr = readU64 mem rAddr := by
  unfold readU64
  show (writeU8 mem wAddr val).read rAddr % 256 +
       (writeU8 mem wAddr val).read (rAddr + 1) % 256 * 0x100 +
       (writeU8 mem wAddr val).read (rAddr + 2) % 256 * 0x10000 +
       (writeU8 mem wAddr val).read (rAddr + 3) % 256 * 0x1000000 +
       (writeU8 mem wAddr val).read (rAddr + 4) % 256 * 0x100000000 +
       (writeU8 mem wAddr val).read (rAddr + 5) % 256 * 0x10000000000 +
       (writeU8 mem wAddr val).read (rAddr + 6) % 256 * 0x1000000000000 +
       (writeU8 mem wAddr val).read (rAddr + 7) % 256 * 0x100000000000000 = _
  rw [writeU8_read_other _ _ _ _ (by omega),
      writeU8_read_other _ _ _ _ (by omega),
      writeU8_read_other _ _ _ _ (by omega),
      writeU8_read_other _ _ _ _ (by omega),
      writeU8_read_other _ _ _ _ (by omega),
      writeU8_read_other _ _ _ _ (by omega),
      writeU8_read_other _ _ _ _ (by omega),
      writeU8_read_other _ _ _ _ (by omega)]

/-- Writing a U64 does not affect U32 reads from non-overlapping addresses -/
theorem readU32_writeU64_disjoint (mem : Mem) (rAddr wAddr val : Nat)
    (h : rAddr + 4 ≤ wAddr ∨ wAddr + 8 ≤ rAddr) :
    readU32 (writeU64 mem wAddr val) rAddr = readU32 mem rAddr := by
  unfold readU32
  show (writeU64 mem wAddr val).read rAddr % 256 +
       (writeU64 mem wAddr val).read (rAddr + 1) % 256 * 0x100 +
       (writeU64 mem wAddr val).read (rAddr + 2) % 256 * 0x10000 +
       (writeU64 mem wAddr val).read (rAddr + 3) % 256 * 0x1000000 = _
  rw [writeU64_read_other _ _ _ _
        (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega),
      writeU64_read_other _ _ _ _
        (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega),
      writeU64_read_other _ _ _ _
        (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega),
      writeU64_read_other _ _ _ _
        (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)]

/-- Writing a U32 does not affect U32 reads from non-overlapping addresses -/
theorem readU32_writeU32_disjoint (mem : Mem) (rAddr wAddr val : Nat)
    (h : rAddr + 4 ≤ wAddr ∨ wAddr + 4 ≤ rAddr) :
    readU32 (writeU32 mem wAddr val) rAddr = readU32 mem rAddr := by
  unfold readU32
  show (writeU32 mem wAddr val).read rAddr % 256 +
       (writeU32 mem wAddr val).read (rAddr + 1) % 256 * 0x100 +
       (writeU32 mem wAddr val).read (rAddr + 2) % 256 * 0x10000 +
       (writeU32 mem wAddr val).read (rAddr + 3) % 256 * 0x1000000 = _
  rw [writeU32_read_other _ _ _ _ (by omega) (by omega) (by omega) (by omega),
      writeU32_read_other _ _ _ _ (by omega) (by omega) (by omega) (by omega),
      writeU32_read_other _ _ _ _ (by omega) (by omega) (by omega) (by omega),
      writeU32_read_other _ _ _ _ (by omega) (by omega) (by omega) (by omega)]

/-- Writing a U64 does not affect individual byte reads outside the written range -/
theorem readU8_writeU64_outside (mem : Mem) (bAddr wAddr val : Nat)
    (h : bAddr < wAddr ∨ wAddr + 8 ≤ bAddr) :
    readU8 (writeU64 mem wAddr val) bAddr = readU8 mem bAddr := by
  unfold readU8
  show (writeU64 mem wAddr val).read bAddr % 256 = _
  rw [writeU64_read_other _ _ _ _
        (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)]

/-- Writing a U32 does not affect byte reads outside the written range -/
theorem readU8_writeU32_outside (mem : Mem) (bAddr wAddr val : Nat)
    (h : bAddr < wAddr ∨ wAddr + 4 ≤ bAddr) :
    readU8 (writeU32 mem wAddr val) bAddr = readU8 mem bAddr := by
  unfold readU8
  show (writeU32 mem wAddr val).read bAddr % 256 = _
  rw [writeU32_read_other _ _ _ _ (by omega) (by omega) (by omega) (by omega)]

/-- Writing a U16 does not affect byte reads outside the written range -/
theorem readU8_writeU16_outside (mem : Mem) (bAddr wAddr val : Nat)
    (h : bAddr < wAddr ∨ wAddr + 2 ≤ bAddr) :
    readU8 (writeU16 mem wAddr val) bAddr = readU8 mem bAddr := by
  unfold readU8
  show (writeU16 mem wAddr val).read bAddr % 256 = _
  rw [writeU16_read_other _ _ _ _ (by omega) (by omega)]

/-- Writing a U8 does not affect byte reads at different addresses -/
theorem readU8_writeU8_disjoint (mem : Mem) (rAddr wAddr val : Nat)
    (h : rAddr ≠ wAddr) :
    readU8 (writeU8 mem wAddr val) rAddr = readU8 mem rAddr := by
  unfold readU8
  show (writeU8 mem wAddr val).read rAddr % 256 = _
  rw [writeU8_read_other _ _ _ _ h]

/-! ### Region frame axioms (two-premise: read below STACK_START, write above)

Derivable from the disjoint axioms, but stated separately because `omega`
resolves two simple inequalities faster than one compound disjunction; the
`mem_frame` tactic uses them for region-based stripping. -/

/-- Input read survives stack write (U64 × U64) -/
theorem readU64_writeU64_frame (mem : Mem) (rAddr wAddr val : Nat)
    (h_r : rAddr + 8 ≤ STACK_START) (h_w : STACK_START ≤ wAddr) :
    readU64 (writeU64 mem wAddr val) rAddr = readU64 mem rAddr :=
  readU64_writeU64_disjoint mem rAddr wAddr val (Or.inl (by omega))

/-- Input read survives stack write (U64 × U32) -/
theorem readU64_writeU32_frame (mem : Mem) (rAddr wAddr val : Nat)
    (h_r : rAddr + 8 ≤ STACK_START) (h_w : STACK_START ≤ wAddr) :
    readU64 (writeU32 mem wAddr val) rAddr = readU64 mem rAddr :=
  readU64_writeU32_disjoint mem rAddr wAddr val (Or.inl (by omega))

/-- Input read survives stack write (U64 × U16) -/
theorem readU64_writeU16_frame (mem : Mem) (rAddr wAddr val : Nat)
    (h_r : rAddr + 8 ≤ STACK_START) (h_w : STACK_START ≤ wAddr) :
    readU64 (writeU16 mem wAddr val) rAddr = readU64 mem rAddr :=
  readU64_writeU16_disjoint mem rAddr wAddr val (Or.inl (by omega))

/-- Input read survives stack write (U64 × U8) -/
theorem readU64_writeU8_frame (mem : Mem) (rAddr wAddr val : Nat)
    (h_r : rAddr + 8 ≤ STACK_START) (h_w : STACK_START ≤ wAddr) :
    readU64 (writeU8 mem wAddr val) rAddr = readU64 mem rAddr :=
  readU64_writeU8_disjoint mem rAddr wAddr val (Or.inr (by omega))

/-- Input read survives stack write (U32 × U64) -/
theorem readU32_writeU64_frame (mem : Mem) (rAddr wAddr val : Nat)
    (h_r : rAddr + 4 ≤ STACK_START) (h_w : STACK_START ≤ wAddr) :
    readU32 (writeU64 mem wAddr val) rAddr = readU32 mem rAddr :=
  readU32_writeU64_disjoint mem rAddr wAddr val (Or.inl (by omega))

/-- Input read survives stack write (U32 × U32) -/
theorem readU32_writeU32_frame (mem : Mem) (rAddr wAddr val : Nat)
    (h_r : rAddr + 4 ≤ STACK_START) (h_w : STACK_START ≤ wAddr) :
    readU32 (writeU32 mem wAddr val) rAddr = readU32 mem rAddr :=
  readU32_writeU32_disjoint mem rAddr wAddr val (Or.inl (by omega))

/-- Byte read survives stack write (U8 × U64) -/
theorem readU8_writeU64_frame (mem : Mem) (rAddr wAddr val : Nat)
    (h_r : rAddr + 1 ≤ STACK_START) (h_w : STACK_START ≤ wAddr) :
    readU8 (writeU64 mem wAddr val) rAddr = readU8 mem rAddr :=
  readU8_writeU64_outside mem rAddr wAddr val (Or.inl (by omega))

/-- Byte read survives stack write (U8 × U32) -/
theorem readU8_writeU32_frame (mem : Mem) (rAddr wAddr val : Nat)
    (h_r : rAddr + 1 ≤ STACK_START) (h_w : STACK_START ≤ wAddr) :
    readU8 (writeU32 mem wAddr val) rAddr = readU8 mem rAddr :=
  readU8_writeU32_outside mem rAddr wAddr val (Or.inl (by omega))

/-- Byte read survives stack write (U8 × U16) -/
theorem readU8_writeU16_frame (mem : Mem) (rAddr wAddr val : Nat)
    (h_r : rAddr + 1 ≤ STACK_START) (h_w : STACK_START ≤ wAddr) :
    readU8 (writeU16 mem wAddr val) rAddr = readU8 mem rAddr :=
  readU8_writeU16_outside mem rAddr wAddr val (Or.inl (by omega))

/-- Byte read survives stack write (U8 × U8) -/
theorem readU8_writeU8_frame (mem : Mem) (rAddr wAddr val : Nat)
    (h_r : rAddr + 1 ≤ STACK_START) (h_w : STACK_START ≤ wAddr) :
    readU8 (writeU8 mem wAddr val) rAddr = readU8 mem rAddr :=
  readU8_writeU8_disjoint mem rAddr wAddr val (by omega)

/-! ### Region predicate -/

/-- Input region [base, base + bound) lies entirely below STACK_START -/
def belowStack (base bound : Nat) : Prop := base + bound ≤ STACK_START

/-! ## Region table — runtime bounds enforcement

Total `Mem` lets a stray access past mapped regions silently succeed, where
agave raises `AccessViolation`. Close that with a parallel bounds layer: a
`RegionTable` of valid `[start, start+size)` intervals + writability, consulted
by `step` on `.ldx`/`.st`/`.stx`, routing a miss to `ERR_ACCESS_VIOLATION`.
Total `Mem` is preserved, so the coherence theorems above stay sound. -/

structure Region where
  start    : Nat
  size     : Nat
  writable : Bool
  deriving Inhabited, Repr

/-- List of mapped regions; order irrelevant, the check folds over the list. -/
abbrev RegionTable := List Region

/-- Does `[addr, addr + len)` lie entirely within this region? -/
def Region.contains (r : Region) (addr len : Nat) : Bool :=
  decide (r.start ≤ addr ∧ addr + len ≤ r.start + r.size)

/-- Is `[addr, addr + len)` covered by *some* region in the table? -/
def RegionTable.containsRange (rt : RegionTable) (addr len : Nat) : Bool :=
  rt.any (·.contains addr len)

/-- Is `[addr, addr + len)` covered by a *writable* region? -/
def RegionTable.containsWritable (rt : RegionTable) (addr len : Nat) : Bool :=
  rt.any (fun r => r.writable && r.contains addr len)

/-! ## Input buffer layout helpers

The runtime serializes accounts into the input buffer with a fixed per-account
layout; offsets here are relative to each account record's start (absolute
offsets depend on preceding account data sizes, so programs use .equ). -/

/-- Offsets within a single account record (relative to account start). -/
structure AccountLayout where
  header   : Nat  -- 8 bytes: dup marker, is_signer, is_writable, executable, ...
  key      : Nat  -- 32 bytes: account pubkey
  owner    : Nat  -- 32 bytes: owner program pubkey
  lamports : Nat  -- 8 bytes: lamport balance (u64 LE)
  dataLen  : Nat  -- 8 bytes: account data length (u64 LE)
  data     : Nat  -- variable: account data bytes

/-- Standard account layout (offsets from account start, after the num_accounts u64) -/
def standardAccountLayout : AccountLayout where
  header   := 0x00
  key      := 0x08
  owner    := 0x28
  lamports := 0x48
  dataLen  := 0x50
  data     := 0x58

end SVM.SBPF.Memory
