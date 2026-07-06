import SVM.SBPF.InstructionSpecs.MemDwordLoad

namespace SVM.SBPF

open Memory

/-! ## Memory loads/stores — halfword width (`u16`)

Thin instantiations of the width-generic cell helpers in `MemByte.lean`
with `M := PartialState.singletonMemU16 ..`. The three lemmas below are
the width's byte-decomposition facts (write-read at each in-footprint
byte, write framing outside, and equal footprints across values). -/

/-- `writeU16 _ addr w` reproduces every byte owned by
    `singletonMemU16 addr v` when `w ≡ v (mod 2^16)`. -/
theorem singletonMemU16_write_in (addr v w : Nat)
    (hvw : w % 2 ^ 16 = v % 2 ^ 16) :
    ∀ (m : Memory.Mem) (a val : Nat),
      (PartialState.singletonMemU16 addr v).mem a = some val →
      (Memory.writeU16 m addr w) a = val := by
  intro m a val h
  by_cases h0 : a = addr
  · subst h0
    have hval : val = v % 256 := by
      rw [PartialState.singletonMemU16_mem_0] at h
      exact (Option.some.inj h).symm
    rw [hval, Memory.writeU16_read_at_0]
    omega
  · by_cases h1 : a = addr + 1
    · subst h1
      have hval : val = v / 0x100 % 256 := by
        rw [PartialState.singletonMemU16_mem_1] at h
        exact (Option.some.inj h).symm
      rw [hval, Memory.writeU16_read_at_1]
      omega
    · rw [PartialState.singletonMemU16_mem_outside _ _ a (by omega)] at h
      nomatch h

/-- `writeU16` leaves every byte outside `singletonMemU16`'s footprint
    unchanged. -/
theorem singletonMemU16_write_out (addr v w : Nat) :
    ∀ (m : Memory.Mem) (a : Nat),
      (PartialState.singletonMemU16 addr v).mem a = none →
      (Memory.writeU16 m addr w) a = m a := by
  intro m a h
  by_cases h0 : a = addr
  · subst h0; rw [PartialState.singletonMemU16_mem_0] at h; nomatch h
  · by_cases h1 : a = addr + 1
    · subst h1; rw [PartialState.singletonMemU16_mem_1] at h; nomatch h
    · exact Memory.writeU16_read_other m addr w a h0 h1

/-- `singletonMemU16` atoms at the same address have the same footprint
    regardless of value. -/
theorem singletonMemU16_foot (addr v w : Nat) :
    ∀ a, (PartialState.singletonMemU16 addr v).mem a = none ↔
         (PartialState.singletonMemU16 addr w).mem a = none := by
  intro a
  by_cases h0 : a = addr
  · subst h0
    rw [PartialState.singletonMemU16_mem_0, PartialState.singletonMemU16_mem_0]
    exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  · by_cases h1 : a = addr + 1
    · subst h1
      rw [PartialState.singletonMemU16_mem_1, PartialState.singletonMemU16_mem_1]
      exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
    · rw [PartialState.singletonMemU16_mem_outside _ _ a (by omega),
          PartialState.singletonMemU16_mem_outside _ _ a (by omega)]

/-- `ldx .half dst src off`: load 16-bit value at `[src + off]` into `dst`. -/
theorem ldxh_spec
    (dst src : Reg) (off : Int) (vOldDst baseAddr v : Nat) (pc : Nat)
    (hne : dst ≠ .r10) (hv : v < 2 ^ 16) :
    cuTripleWithinMem 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.ldx .half dst src off))
      ((dst ↦ᵣ vOldDst) ** (src ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr off ↦U16 v))
      ((dst ↦ᵣ v) ** (src ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr off ↦U16 v))
      (fun rt => rt.containsRange (effectiveAddr baseAddr off) 2 = true) :=
  cuTripleWithinMem_load_cell_via_reg_addr dst src vOldDst baseAddr v pc
    (.ldx .half dst src off)
    (PartialState.singletonMemU16 (effectiveAddr baseAddr off) v) _ _
    hne (fun _ => Iff.rfl)
    (PartialState.singletonMemU16_memOnly _ _)
    (fun s _ hsrc hmem hreg => by
      have h_readU16 : Memory.readU16 s.mem (effectiveAddr baseAddr off) = v :=
        readU16_eq_of_bytes_match hv
          (hmem _ _ (PartialState.singletonMemU16_mem_0 _ _))
          (hmem _ _ (PartialState.singletonMemU16_mem_1 _ _))
      simp only [step, hsrc, Width.bytes, if_pos hreg,
                 Memory.readByWidth, h_readU16])

/-- `ldx .half r r off`: same-register variant (owns ONE register atom;
    the two-atom form is unsatisfiable when dst = src). -/
theorem ldxh_same_spec
    (r : Reg) (off : Int) (baseAddr v : Nat) (pc : Nat)
    (hne : r ≠ .r10) (hv : v < 2 ^ 16) :
    cuTripleWithinMem 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.ldx .half r r off))
      ((r ↦ᵣ baseAddr) ** (effectiveAddr baseAddr off ↦U16 v))
      ((r ↦ᵣ v) ** (effectiveAddr baseAddr off ↦U16 v))
      (fun rt => rt.containsRange (effectiveAddr baseAddr off) 2 = true) :=
  cuTripleWithinMem_load_cell_same_reg r baseAddr v pc
    (.ldx .half r r off)
    (PartialState.singletonMemU16 (effectiveAddr baseAddr off) v) _ _
    hne (fun _ => Iff.rfl)
    (PartialState.singletonMemU16_memOnly _ _)
    (fun s hr hmem hreg => by
      have h_readU16 : Memory.readU16 s.mem (effectiveAddr baseAddr off) = v :=
        readU16_eq_of_bytes_match hv
          (hmem _ _ (PartialState.singletonMemU16_mem_0 _ _))
          (hmem _ _ (PartialState.singletonMemU16_mem_1 _ _))
      simp only [step, hr, Width.bytes, if_pos hreg,
                 Memory.readByWidth, h_readU16])

/-- `stx .half baseReg off valReg`: write valReg's low 16 bits at `[baseReg + off]`. -/
theorem stxh_spec
    (baseReg valReg : Reg) (off : Int)
    (baseAddr vSrc oldV : Nat) (pc : Nat) :
    cuTripleWithinMem 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.stx .half baseReg off valReg))
      ((baseReg ↦ᵣ baseAddr) ** (valReg ↦ᵣ vSrc) **
        (effectiveAddr baseAddr off ↦U16 oldV))
      ((baseReg ↦ᵣ baseAddr) ** (valReg ↦ᵣ vSrc) **
        (effectiveAddr baseAddr off ↦U16 vSrc))
      (fun rt => rt.containsWritable (effectiveAddr baseAddr off) 2 = true) :=
  cuTripleWithinMem_store_cell_via_reg_addr baseReg valReg baseAddr vSrc pc
    (.stx .half baseReg off valReg)
    (PartialState.singletonMemU16 (effectiveAddr baseAddr off) oldV)
    (PartialState.singletonMemU16 (effectiveAddr baseAddr off) vSrc)
    _ _
    (fun m => Memory.writeU16 m (effectiveAddr baseAddr off) (vSrc % 2 ^ 16)) _
    (fun _ => Iff.rfl) (fun _ => Iff.rfl)
    (PartialState.singletonMemU16_memOnly _ _)
    (PartialState.singletonMemU16_memOnly _ _)
    (singletonMemU16_foot _ _ _)
    (singletonMemU16_write_in _ _ _ (by omega))
    (singletonMemU16_write_out _ _ _)
    (fun s hbase hval hreg => by
      simp only [step, hbase, Width.bytes, if_pos hreg,
                 Memory.writeByWidth, hval])

/-- `st .half baseReg off imm`: store `toU64 imm % 2^(2*8)` (16-bit truncation,
    matching `writeByWidth`) at `[baseReg + off]`. From the immediate-store
    cell helper. -/
theorem sth_spec
    (baseReg : Reg) (off : Int) (imm : Int)
    (baseAddr oldHalfVal : Nat) (pc : Nat) :
    cuTripleWithinMem 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.st .half baseReg off imm))
      ((baseReg ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr off ↦U16 oldHalfVal))
      ((baseReg ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr off ↦U16 (toU64 imm % 2 ^ (2 * 8))))
      (fun rt => rt.containsWritable (effectiveAddr baseAddr off) 2 = true) :=
  cuTripleWithinMem_store_imm_cell_via_reg_addr baseReg baseAddr pc
    (.st .half baseReg off imm)
    (PartialState.singletonMemU16 (effectiveAddr baseAddr off) oldHalfVal)
    (PartialState.singletonMemU16 (effectiveAddr baseAddr off)
      (toU64 imm % 2 ^ (2 * 8)))
    _ _
    (fun m => Memory.writeU16 m (effectiveAddr baseAddr off)
      (toU64 imm % 2 ^ (2 * 8))) _
    (fun _ => Iff.rfl) (fun _ => Iff.rfl)
    (PartialState.singletonMemU16_memOnly _ _)
    (PartialState.singletonMemU16_memOnly _ _)
    (singletonMemU16_foot _ _ _)
    (singletonMemU16_write_in _ _ _ rfl)
    (singletonMemU16_write_out _ _ _)
    (fun s hbase hreg => by
      simp only [step, hbase, Width.bytes, if_pos hreg, Memory.writeByWidth])


end SVM.SBPF
