import SVM.SBPF.InstructionSpecs.MemHalfword
import SVM.SBPF.SegAggregation

namespace SVM.SBPF

open Memory

/-! ## Memory loads/stores — word width (`u32`)

Thin instantiations of the width-generic cell helpers in `MemByte.lean`
with `M := PartialState.singletonMemU32 ..`; the three lemmas below are
the width's byte-decomposition facts. -/

/-- `writeU32 _ addr w` reproduces every byte owned by
    `singletonMemU32 addr v` when `w ≡ v (mod 2^32)`. -/
theorem singletonMemU32_write_in (addr v w : Nat)
    (hvw : w % 2 ^ 32 = v % 2 ^ 32) :
    ∀ (m : Memory.Mem) (a val : Nat),
      (PartialState.singletonMemU32 addr v).mem a = some val →
      (Memory.writeU32 m addr w) a = val := by
  intro m a val h
  by_cases h0 : a = addr
  · subst h0
    have hval : val = v % 256 := by
      rw [PartialState.singletonMemU32_mem_0] at h
      exact (Option.some.inj h).symm
    rw [hval, Memory.writeU32_read_at_0]
    omega
  · by_cases h1 : a = addr + 1
    · subst h1
      have hval : val = v / 0x100 % 256 := by
        rw [PartialState.singletonMemU32_mem_1] at h
        exact (Option.some.inj h).symm
      rw [hval, Memory.writeU32_read_at_1]
      omega
    · by_cases h2 : a = addr + 2
      · subst h2
        have hval : val = v / 0x10000 % 256 := by
          rw [PartialState.singletonMemU32_mem_2] at h
          exact (Option.some.inj h).symm
        rw [hval, Memory.writeU32_read_at_2]
        omega
      · by_cases h3 : a = addr + 3
        · subst h3
          have hval : val = v / 0x1000000 % 256 := by
            rw [PartialState.singletonMemU32_mem_3] at h
            exact (Option.some.inj h).symm
          rw [hval, Memory.writeU32_read_at_3]
          omega
        · rw [PartialState.singletonMemU32_mem_outside _ _ a (by omega)] at h
          nomatch h

/-- `writeU32` leaves every byte outside `singletonMemU32`'s footprint
    unchanged. -/
theorem singletonMemU32_write_out (addr v w : Nat) :
    ∀ (m : Memory.Mem) (a : Nat),
      (PartialState.singletonMemU32 addr v).mem a = none →
      (Memory.writeU32 m addr w) a = m a := by
  intro m a h
  by_cases h0 : a = addr
  · subst h0; rw [PartialState.singletonMemU32_mem_0] at h; nomatch h
  · by_cases h1 : a = addr + 1
    · subst h1; rw [PartialState.singletonMemU32_mem_1] at h; nomatch h
    · by_cases h2 : a = addr + 2
      · subst h2; rw [PartialState.singletonMemU32_mem_2] at h; nomatch h
      · by_cases h3 : a = addr + 3
        · subst h3; rw [PartialState.singletonMemU32_mem_3] at h; nomatch h
        · exact Memory.writeU32_read_other m addr w a h0 h1 h2 h3

/-- `singletonMemU32` atoms at the same address have the same footprint
    regardless of value. -/
theorem singletonMemU32_foot (addr v w : Nat) :
    ∀ a, (PartialState.singletonMemU32 addr v).mem a = none ↔
         (PartialState.singletonMemU32 addr w).mem a = none := by
  intro a
  by_cases h0 : a = addr
  · subst h0
    rw [PartialState.singletonMemU32_mem_0, PartialState.singletonMemU32_mem_0]
    exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  · by_cases h1 : a = addr + 1
    · subst h1
      rw [PartialState.singletonMemU32_mem_1, PartialState.singletonMemU32_mem_1]
      exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
    · by_cases h2 : a = addr + 2
      · subst h2
        rw [PartialState.singletonMemU32_mem_2, PartialState.singletonMemU32_mem_2]
        exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
      · by_cases h3 : a = addr + 3
        · subst h3
          rw [PartialState.singletonMemU32_mem_3, PartialState.singletonMemU32_mem_3]
          exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
        · rw [PartialState.singletonMemU32_mem_outside _ _ a (by omega),
              PartialState.singletonMemU32_mem_outside _ _ a (by omega)]

/-- `ldx .word dst src off`: load 32-bit value at `[src + off]` into `dst`. -/
theorem ldxw_spec
    (dst src : Reg) (off : Int) (vOldDst baseAddr v : Nat) (pc : Nat)
    (hne : dst ≠ .r10) (hv : v < 2 ^ 32) :
    cuTripleWithinMem 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.ldx .word dst src off))
      ((dst ↦ᵣ vOldDst) ** (src ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr off ↦U32 v))
      ((dst ↦ᵣ v) ** (src ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr off ↦U32 v))
      (fun rt => rt.containsRange (effectiveAddr baseAddr off) 4 = true) :=
  cuTripleWithinMem_load_cell_via_reg_addr dst src vOldDst baseAddr v pc
    (.ldx .word dst src off)
    (PartialState.singletonMemU32 (effectiveAddr baseAddr off) v) _ _
    hne (fun _ => Iff.rfl)
    (PartialState.singletonMemU32_memOnly _ _)
    (fun s _ hsrc hmem hreg => by
      have h_readU32 : Memory.readU32 s.mem (effectiveAddr baseAddr off) = v :=
        readU32_eq_of_bytes_match hv
          (hmem _ _ (PartialState.singletonMemU32_mem_0 _ _))
          (hmem _ _ (PartialState.singletonMemU32_mem_1 _ _))
          (hmem _ _ (PartialState.singletonMemU32_mem_2 _ _))
          (hmem _ _ (PartialState.singletonMemU32_mem_3 _ _))
      simp only [step, hsrc, Width.bytes, if_pos hreg,
                 Memory.readByWidth, h_readU32])

/-- `ldx .word r r off`: same-register variant (owns ONE register atom;
    the two-atom form is unsatisfiable when dst = src). -/
theorem ldxw_same_spec
    (r : Reg) (off : Int) (baseAddr v : Nat) (pc : Nat)
    (hne : r ≠ .r10) (hv : v < 2 ^ 32) :
    cuTripleWithinMem 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.ldx .word r r off))
      ((r ↦ᵣ baseAddr) ** (effectiveAddr baseAddr off ↦U32 v))
      ((r ↦ᵣ v) ** (effectiveAddr baseAddr off ↦U32 v))
      (fun rt => rt.containsRange (effectiveAddr baseAddr off) 4 = true) :=
  cuTripleWithinMem_load_cell_same_reg r baseAddr v pc
    (.ldx .word r r off)
    (PartialState.singletonMemU32 (effectiveAddr baseAddr off) v) _ _
    hne (fun _ => Iff.rfl)
    (PartialState.singletonMemU32_memOnly _ _)
    (fun s hr hmem hreg => by
      have h_readU32 : Memory.readU32 s.mem (effectiveAddr baseAddr off) = v :=
        readU32_eq_of_bytes_match hv
          (hmem _ _ (PartialState.singletonMemU32_mem_0 _ _))
          (hmem _ _ (PartialState.singletonMemU32_mem_1 _ _))
          (hmem _ _ (PartialState.singletonMemU32_mem_2 _ _))
          (hmem _ _ (PartialState.singletonMemU32_mem_3 _ _))
      simp only [step, hr, Width.bytes, if_pos hreg,
                 Memory.readByWidth, h_readU32])

/-- `stx .word baseReg off valReg`: write valReg's low 32 bits at `[baseReg + off]`. -/
theorem stxw_spec
    (baseReg valReg : Reg) (off : Int)
    (baseAddr vSrc oldV : Nat) (pc : Nat) :
    cuTripleWithinMem 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.stx .word baseReg off valReg))
      ((baseReg ↦ᵣ baseAddr) ** (valReg ↦ᵣ vSrc) **
        (effectiveAddr baseAddr off ↦U32 oldV))
      ((baseReg ↦ᵣ baseAddr) ** (valReg ↦ᵣ vSrc) **
        (effectiveAddr baseAddr off ↦U32 vSrc))
      (fun rt => rt.containsWritable (effectiveAddr baseAddr off) 4 = true) :=
  cuTripleWithinMem_store_cell_via_reg_addr baseReg valReg baseAddr vSrc pc
    (.stx .word baseReg off valReg)
    (PartialState.singletonMemU32 (effectiveAddr baseAddr off) oldV)
    (PartialState.singletonMemU32 (effectiveAddr baseAddr off) vSrc)
    _ _
    (fun m => Memory.writeU32 m (effectiveAddr baseAddr off) (vSrc % 2 ^ 32)) _
    (fun _ => Iff.rfl) (fun _ => Iff.rfl)
    (PartialState.singletonMemU32_memOnly _ _)
    (PartialState.singletonMemU32_memOnly _ _)
    (singletonMemU32_foot _ _ _)
    (singletonMemU32_write_in _ _ _ (by omega))
    (singletonMemU32_write_out _ _ _)
    (fun s hbase hval hreg => by
      simp only [step, hbase, Width.bytes, if_pos hreg,
                 Memory.writeByWidth, hval])

/-- `st .word baseReg off imm`: store `toU64 imm % 2^(4*8)` at
    `[baseReg + off]` (matching `writeByWidth`). From the immediate-store
    cell helper. -/
theorem stw_spec
    (baseReg : Reg) (off : Int) (imm : Int)
    (baseAddr oldWordVal : Nat) (pc : Nat) :
    cuTripleWithinMem 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.st .word baseReg off imm))
      ((baseReg ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr off ↦U32 oldWordVal))
      ((baseReg ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr off ↦U32 (toU64 imm % 2 ^ (4 * 8))))
      (fun rt => rt.containsWritable (effectiveAddr baseAddr off) 4 = true) :=
  cuTripleWithinMem_store_imm_cell_via_reg_addr baseReg baseAddr pc
    (.st .word baseReg off imm)
    (PartialState.singletonMemU32 (effectiveAddr baseAddr off) oldWordVal)
    (PartialState.singletonMemU32 (effectiveAddr baseAddr off)
      (toU64 imm % 2 ^ (4 * 8)))
    _ _
    (fun m => Memory.writeU32 m (effectiveAddr baseAddr off)
      (toU64 imm % 2 ^ (4 * 8))) _
    (fun _ => Iff.rfl) (fun _ => Iff.rfl)
    (PartialState.singletonMemU32_memOnly _ _)
    (PartialState.singletonMemU32_memOnly _ _)
    (singletonMemU32_foot _ _ _)
    (singletonMemU32_write_in _ _ _ rfl)
    (singletonMemU32_write_out _ _ _)
    (fun s hbase hreg => by
      simp only [step, hbase, Width.bytes, if_pos hreg, Memory.writeByWidth])

/-! ## Word store over BYTE-granular memory (qedlift hot regions)

The compiler's tail-zeroing idiom (`stw [r10-4] 0; stw [r10-7] 0`) overlaps
two word stores; qedlift demotes the union span to per-byte atoms (H8 Phase
B-2, `docs/QEDLIFT_ALIASING_DESIGN.md`). `stw_spec` reshaped through
`byte_atoms_eq_memU32Is`: post bytes `c0..c3` are emitter-supplied params
with `decide`-discharged defining hyps. -/

set_option maxHeartbeats 400000 in
/-- `st .word baseReg off imm` over four byte atoms `[addr, addr+4)`. -/
theorem stw_bytes_spec
    (baseReg : Reg) (off : Int) (imm : Int)
    (baseAddr b0 b1 b2 b3 c0 c1 c2 c3 : Nat)
    (a0 a1 a2 a3 : Nat) (pc : Nat)
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256)
    (hc0 : c0 = toU64 imm % 2 ^ (4 * 8) % 256)
    (hc1 : c1 = toU64 imm % 2 ^ (4 * 8) / 0x100 % 256)
    (hc2 : c2 = toU64 imm % 2 ^ (4 * 8) / 0x10000 % 256)
    (hc3 : c3 = toU64 imm % 2 ^ (4 * 8) / 0x1000000 % 256)
    -- Slot addresses as params (see `ldxdw_bytes_spec`).
    (ha0 : a0 = effectiveAddr baseAddr off)
    (ha1 : a1 = effectiveAddr baseAddr off + 1)
    (ha2 : a2 = effectiveAddr baseAddr off + 2)
    (ha3 : a3 = effectiveAddr baseAddr off + 3) :
    cuTripleWithinMem 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.st .word baseReg off imm))
      ((baseReg ↦ᵣ baseAddr) **
        ((a0 ↦ₘ b0) ** (a1 ↦ₘ b1) ** (a2 ↦ₘ b2) ** (a3 ↦ₘ b3)))
      ((baseReg ↦ᵣ baseAddr) **
        ((a0 ↦ₘ c0) ** (a1 ↦ₘ c1) ** (a2 ↦ₘ c2) ** (a3 ↦ₘ c3)))
      (fun rt => rt.containsWritable (effectiveAddr baseAddr off) 4 = true) := by
  subst ha0 ha1 ha2 ha3
  have hcb0 : c0 < 256 := by omega
  have hcb1 : c1 < 256 := by omega
  have hcb2 : c2 < 256 := by omega
  have hcb3 : c3 < 256 := by omega
  have hv : toU64 imm % 2 ^ (4 * 8)
      = c0 + 256 * (c1 + 256 * (c2 + 256 * c3)) := by
    subst hc0 hc1 hc2 hc3
    omega
  have hbridge_pre := byte_atoms_eq_memU32Is (effectiveAddr baseAddr off)
      b0 b1 b2 b3 hb0 hb1 hb2 hb3
  have hbridge_post := byte_atoms_eq_memU32Is (effectiveAddr baseAddr off)
      c0 c1 c2 c3 hcb0 hcb1 hcb2 hcb3
  refine cuTripleWithinMem_weaken ?_ ?_ (fun _ x => x)
    (stw_spec baseReg off imm baseAddr
      (b0 + 256 * (b1 + 256 * (b2 + 256 * b3))) pc)
  · intro h hh
    exact (sepConj_iff_congr_right _ (fun h' => hbridge_pre h') h).mp hh
  · intro h hh
    rw [hv] at hh
    exact (sepConj_iff_congr_right _
      (fun h' => (hbridge_post h').symm) h).mp hh

end SVM.SBPF
