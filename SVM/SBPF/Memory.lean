-- Flat byte-addressable memory model for sBPF verification
--
-- sBPF uses a flat address space partitioned into 5 regions:
--   0x000000000 : Read-only data (.rodata)
--   0x100000000 : Bytecode
--   0x200000000 : Stack
--   0x300000000 : Heap
--   0x400000000 : Input buffer (serialized accounts + instruction data)
--
-- Programs receive a pointer to the input buffer in r1 at entry.

import SVM.SBPF.ISA
import Std.Data.HashMap

namespace SVM.SBPF.Memory

open SVM.SBPF

/-! ## Memory type

`Mem` was originally `abbrev Mem := Nat → Nat`. Each `writeU*` returned
`fun a => if a = addr then val else mem a`, so after N writes a read
walked an N-deep closure chain. For SPL Token (post-execution chain
~thousands deep, input ~5 KB) that was tens of millions of Nat
equality tests per `process_instruction`, making `diff_mollusk` take
~50 minutes (dominated by `encodeRun`'s FFI-return-path
`readBytes` walk).

The fix is a thin overlay: writes go into a `Std.HashMap Nat UInt8`,
reads check the overlay first and fall through to the `default`
function on miss. The `Coe (Nat → Nat) Mem` instance keeps inline
closure-style constructors (sysvar / Pda / Native syscall bodies)
type-checking — they land in `default`, which is fine for cold paths
that get few reads. The `CoeFun Mem (fun _ => Nat → Nat)` instance
keeps the `mem a` application syntax compiling at every existing call
site (readU*, readBytes, etc.). -/

structure Mem where
  default : Nat → Nat := fun _ => 0
  overlay : Std.HashMap Nat UInt8 := {}

/-- Look up a byte: overlay first, fall through to `default` on miss. -/
@[inline] def Mem.read (m : Mem) (a : Nat) : Nat :=
  match m.overlay[a]? with
  | some b => b.toNat
  | none   => m.default a

/-- Insert a single byte into the overlay (mod 256).

    `irreducible` so the kernel's `whnf` stops here during proof-time
    defeq checks. With the old `Mem := Nat → Nat`, `writeU*` produced
    a lambda which was a natural whnf head; the new struct-update
    chain has no such head and whnf'd recursively into HashMap
    internals, blowing heartbeat limits in `Region.lean` /
    `InstructionSpecs.lean`. Keeping `Mem.put` opaque restores the
    old proof behavior — everything still goes through the axioms /
    `simp`/`rw` rules, never relying on transparent unfolding. -/
@[inline, irreducible] def Mem.put (m : Mem) (addr val : Nat) : Mem :=
  { m with overlay := m.overlay.insert addr (val % 256).toUInt8 }

/-- Apply syntax: `mem a` desugars to `Mem.read mem a`. -/
instance : CoeFun Mem (fun _ => Nat → Nat) := ⟨Mem.read⟩

/-- A plain `Nat → Nat` lifts to a `Mem` whose overlay is empty and
    whose `default` is the supplied function. Closure-style
    constructors (`fun a => if cond then v else mem a`) ride this. -/
instance : Coe (Nat → Nat) Mem := ⟨fun f => { default := f }⟩

instance : Inhabited Mem := ⟨{}⟩

/-! ## `Mem.put` / `Mem.read` interaction lemmas

These are the semantic API for the overlay model: the rest of the
code treats `Mem.put` and `Mem.read` as opaque (since `Mem.put` is
`@[irreducible]`) and reasons via these two lemmas. Marked `@[simp]`
so existing `unfold Memory.writeU8; simp` patterns in
`InstructionSpecs.lean` close after the rewrite to `Mem.put`. -/

@[simp] theorem Mem.read_put_self (m : Mem) (addr val : Nat) :
    (Mem.put m addr val).read addr = val % 256 := by
  unfold Mem.put Mem.read
  simp

@[simp] theorem Mem.read_put_other (m : Mem) (addr addr' val : Nat) (h : addr' ≠ addr) :
    (Mem.put m addr val).read addr' = m.read addr' := by
  unfold Mem.put Mem.read
  simp [Std.HashMap.getElem?_insert, Ne.symm h]

/-- if-form of `Mem.read (Mem.put ...) ...`. Recovers the shape that
    the old `writeU8` produced after unfolding (`fun a => if a = addr
    then val % 256 else mem a`), so existing
    `unfold Memory.writeU8; show (if ...) = _` patterns in
    `InstructionSpecs.lean` still match. Marked `@[simp]` so `simp`
    after `unfold Memory.writeU*` reproduces the pre-refactor goal
    shape automatically; subsumes `read_put_self` / `read_put_other`
    in simp contexts (which remain as named lemmas for direct `rw`). -/
@[simp] theorem Mem.read_put (m : Mem) (addr val a : Nat) :
    Mem.read (Mem.put m addr val) a =
      if a = addr then val % 256 else Mem.read m a := by
  by_cases h : a = addr
  · subst h; simp [Mem.read_put_self]
  · simp [Mem.read_put_other _ _ _ _ h, h]

/-! ## Region base addresses -/

def RODATA_START   : Nat := 0x000000000
def BYTECODE_START : Nat := 0x100000000
def STACK_START    : Nat := 0x200000000
def HEAP_START     : Nat := 0x300000000
def INPUT_START    : Nat := 0x400000000

/-- Size of each sBPF memory region. Same value as the spacing between
    `BYTECODE_START`/`STACK_START`/`HEAP_START`/`INPUT_START`. Also the
    threshold below which the ELF loader's `R_BPF_64_Relative` patch
    bumps an address into the program region (`MM_PROGRAM_START` in
    agave / solana-sbpf nomenclature). -/
def MM_REGION_SIZE : Nat := 0x100000000

/-! ## Effective address computation -/

/-- Compute effective address from base register value and signed offset.

    NOTE: Int.toNat clamps negative results to 0. In real sBPF, a negative
    effective address would be caught by the memory region bounds check
    (which we do not model). All verified programs use non-negative offsets,
    so this clamping is unreachable in practice. -/
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

Each write returns a fresh `Mem` whose overlay has been updated with
the new byte(s). The `default` function is preserved untouched, so any
read of an address that wasn't overwritten still falls through to it.

These are the only sites that actually take the overlay-fast-path —
the closure-style constructors elsewhere (`Sysvar`, `Pda`, ...) land
in `default` via `Coe` and pay the chain-walk cost on read. That's
fine because they execute O(1) times per program run, whereas
`writeU*` runs once per store instruction (millions of times). -/

/-- Write 1 byte. Inserts `val % 256` at `addr`. -/
def writeU8 (mem : Mem) (addr val : Nat) : Mem :=
  Mem.put mem addr val

/-- Write 2 bytes little-endian.

    NOTE: the put-chain is intentionally ordered with the *low* byte
    outermost (`addr` last). When `simp [Mem.read_put]` peels off
    layers, it produces the nested-if tree in the same order as the
    pre-refactor `writeU16` lambda body (`if a = addr then ... else if
    a = addr + 1 then ... else mem a`), so existing
    `unfold Memory.writeU16; show (if ...) = _` patterns in
    `InstructionSpecs.lean` still match without rewriting. -/
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

For each write width, `read_at_i` computes the result of reading the
i-th byte of the just-written value, and `read_other` propagates a
read at any address outside the write footprint. The round-trip and
disjoint theorems below are then mechanical: read-after-write is
`read_at_i` (one per byte of the read), and read-disjoint-from-write
is `read_other` (one per byte of the read).

All proofs unfold to one or two `Mem.put` layers and discharge via
`Mem.read_put_self` / `Mem.read_put_other` plus a constant-base
`omega` for the byte-extraction arithmetic. -/

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

Little-endian encode/decode is a round-trip for values within range
(same-address group) and a write doesn't disturb reads outside its
footprint (disjoint group). Each proof reduces to the per-byte
lemmas above plus a constant-base `omega` for the LE arithmetic. -/

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

These are derivable from the disjoint axioms (if rAddr + N ≤ STACK_START
and STACK_START ≤ wAddr then rAddr + N ≤ wAddr). Stated separately because
omega resolves two simple inequalities faster than one compound disjunction,
and the `mem_frame` tactic uses them for efficient region-based stripping. -/

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

`Mem := Nat → Nat` is a total function, so a stray read/write past a
program's mapped regions silently succeeds (returns zero / writes
to nothing). Agave fails such accesses with `AccessViolation`.

We close that gap with a parallel bounds-check layer: a `RegionTable`
listing the valid `[start, start + size)` intervals plus their
writability. The Lean `step` consults the table on `.ldx` / `.st` /
`.stx` and routes a miss to `ERR_ACCESS_VIOLATION`.

Total `Mem` is preserved, so the SepLogic coherence theorems above
stay sound (they were 13 axioms until 2026-05-23; now proved from
`Mem.put` / `Mem.read_put_self` / `Mem.read_put_other` via the
per-byte `writeU*_read_at_i` / `writeU*_read_other` lemmas). -/

structure Region where
  start    : Nat
  size     : Nat
  writable : Bool
  deriving Inhabited, Repr

/-- A region table is just the list of mapped regions. Order is
    irrelevant for correctness; the check folds over the whole list. -/
abbrev RegionTable := List Region

/-- Does the half-open access `[addr, addr + len)` lie entirely
    within this region? -/
def Region.contains (r : Region) (addr len : Nat) : Bool :=
  decide (r.start ≤ addr ∧ addr + len ≤ r.start + r.size)

/-- Is `[addr, addr + len)` covered by *some* region in the table? -/
def RegionTable.containsRange (rt : RegionTable) (addr len : Nat) : Bool :=
  rt.any (·.contains addr len)

/-- Is `[addr, addr + len)` covered by a *writable* region? -/
def RegionTable.containsWritable (rt : RegionTable) (addr len : Nat) : Bool :=
  rt.any (fun r => r.writable && r.contains addr len)

/-! ## Input buffer layout helpers

The Solana runtime serializes accounts into the input buffer with a fixed
layout per account. Offsets are relative to the start of each account record.
The exact absolute offsets depend on preceding account data sizes, so programs
define them as .equ constants. -/

/-- Offsets within a single account record (relative to account start) -/
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
