import SVM.SBPF.InstructionSpecs.MemWord

namespace SVM.SBPF

open Memory

/-! ## Memory stores — dword width

`stxdw` writes valReg's 8 little-endian bytes at `[baseReg + off]`,
replacing a `memU64Is` claim. Thin instantiations of the width-generic
cell helpers in `MemByte.lean` with `M := PartialState.singletonMemU64 ..`;
the three lemmas below are the width's byte-decomposition facts. No
`vSrc < 2^64` hypothesis: `writeU64` masks `% 256` per slot and
`256 | 2^64`, so `(vSrc % 2^64)/256^i % 256 = vSrc/256^i % 256`
(omega discharges). -/

/-- `writeU64 _ addr w` reproduces every byte owned by
    `singletonMemU64 addr v` when `w ≡ v (mod 2^64)`. -/
theorem singletonMemU64_write_in (addr v w : Nat)
    (hvw : w % 2 ^ 64 = v % 2 ^ 64) :
    ∀ (m : Memory.Mem) (a val : Nat),
      (PartialState.singletonMemU64 addr v).mem a = some val →
      (Memory.writeU64 m addr w) a = val := by
  intro m a val h
  by_cases h0 : a = addr
  · subst h0
    have hval : val = v % 256 := by
      rw [PartialState.singletonMemU64_mem_0] at h
      exact (Option.some.inj h).symm
    rw [hval, Memory.writeU64_read_at_0]
    omega
  · by_cases h1 : a = addr + 1
    · subst h1
      have hval : val = v / 0x100 % 256 := by
        rw [PartialState.singletonMemU64_mem_1] at h
        exact (Option.some.inj h).symm
      rw [hval, Memory.writeU64_read_at_1]
      omega
    · by_cases h2 : a = addr + 2
      · subst h2
        have hval : val = v / 0x10000 % 256 := by
          rw [PartialState.singletonMemU64_mem_2] at h
          exact (Option.some.inj h).symm
        rw [hval, Memory.writeU64_read_at_2]
        omega
      · by_cases h3 : a = addr + 3
        · subst h3
          have hval : val = v / 0x1000000 % 256 := by
            rw [PartialState.singletonMemU64_mem_3] at h
            exact (Option.some.inj h).symm
          rw [hval, Memory.writeU64_read_at_3]
          omega
        · by_cases h4 : a = addr + 4
          · subst h4
            have hval : val = v / 0x100000000 % 256 := by
              rw [PartialState.singletonMemU64_mem_4] at h
              exact (Option.some.inj h).symm
            rw [hval, Memory.writeU64_read_at_4]
            omega
          · by_cases h5 : a = addr + 5
            · subst h5
              have hval : val = v / 0x10000000000 % 256 := by
                rw [PartialState.singletonMemU64_mem_5] at h
                exact (Option.some.inj h).symm
              rw [hval, Memory.writeU64_read_at_5]
              omega
            · by_cases h6 : a = addr + 6
              · subst h6
                have hval : val = v / 0x1000000000000 % 256 := by
                  rw [PartialState.singletonMemU64_mem_6] at h
                  exact (Option.some.inj h).symm
                rw [hval, Memory.writeU64_read_at_6]
                omega
              · by_cases h7 : a = addr + 7
                · subst h7
                  have hval : val = v / 0x100000000000000 % 256 := by
                    rw [PartialState.singletonMemU64_mem_7] at h
                    exact (Option.some.inj h).symm
                  rw [hval, Memory.writeU64_read_at_7]
                  omega
                · rw [PartialState.singletonMemU64_mem_outside _ _ a (by omega)] at h
                  nomatch h

/-- `writeU64` leaves every byte outside `singletonMemU64`'s footprint
    unchanged. -/
theorem singletonMemU64_write_out (addr v w : Nat) :
    ∀ (m : Memory.Mem) (a : Nat),
      (PartialState.singletonMemU64 addr v).mem a = none →
      (Memory.writeU64 m addr w) a = m a := by
  intro m a h
  by_cases h0 : a = addr
  · subst h0; rw [PartialState.singletonMemU64_mem_0] at h; nomatch h
  · by_cases h1 : a = addr + 1
    · subst h1; rw [PartialState.singletonMemU64_mem_1] at h; nomatch h
    · by_cases h2 : a = addr + 2
      · subst h2; rw [PartialState.singletonMemU64_mem_2] at h; nomatch h
      · by_cases h3 : a = addr + 3
        · subst h3; rw [PartialState.singletonMemU64_mem_3] at h; nomatch h
        · by_cases h4 : a = addr + 4
          · subst h4; rw [PartialState.singletonMemU64_mem_4] at h; nomatch h
          · by_cases h5 : a = addr + 5
            · subst h5; rw [PartialState.singletonMemU64_mem_5] at h; nomatch h
            · by_cases h6 : a = addr + 6
              · subst h6; rw [PartialState.singletonMemU64_mem_6] at h; nomatch h
              · by_cases h7 : a = addr + 7
                · subst h7; rw [PartialState.singletonMemU64_mem_7] at h; nomatch h
                · exact Memory.writeU64_read_other m addr w a h0 h1 h2 h3 h4 h5 h6 h7

/-- `singletonMemU64` atoms at the same address have the same footprint
    regardless of value. -/
theorem singletonMemU64_foot (addr v w : Nat) :
    ∀ a, (PartialState.singletonMemU64 addr v).mem a = none ↔
         (PartialState.singletonMemU64 addr w).mem a = none := by
  intro a
  by_cases h0 : a = addr
  · subst h0
    rw [PartialState.singletonMemU64_mem_0, PartialState.singletonMemU64_mem_0]
    exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  · by_cases h1 : a = addr + 1
    · subst h1
      rw [PartialState.singletonMemU64_mem_1, PartialState.singletonMemU64_mem_1]
      exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
    · by_cases h2 : a = addr + 2
      · subst h2
        rw [PartialState.singletonMemU64_mem_2, PartialState.singletonMemU64_mem_2]
        exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
      · by_cases h3 : a = addr + 3
        · subst h3
          rw [PartialState.singletonMemU64_mem_3, PartialState.singletonMemU64_mem_3]
          exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
        · by_cases h4 : a = addr + 4
          · subst h4
            rw [PartialState.singletonMemU64_mem_4, PartialState.singletonMemU64_mem_4]
            exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
          · by_cases h5 : a = addr + 5
            · subst h5
              rw [PartialState.singletonMemU64_mem_5, PartialState.singletonMemU64_mem_5]
              exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
            · by_cases h6 : a = addr + 6
              · subst h6
                rw [PartialState.singletonMemU64_mem_6, PartialState.singletonMemU64_mem_6]
                exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
              · by_cases h7 : a = addr + 7
                · subst h7
                  rw [PartialState.singletonMemU64_mem_7, PartialState.singletonMemU64_mem_7]
                  exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
                · rw [PartialState.singletonMemU64_mem_outside _ _ a (by omega),
                      PartialState.singletonMemU64_mem_outside _ _ a (by omega)]

/-- `stx .dword baseReg off valReg`: write valReg's 64 bits little-endian
    at `[baseReg + off]`. -/
theorem stxdw_spec
    (baseReg valReg : Reg) (off : Int)
    (baseAddr vSrc oldV : Nat) (pc : Nat) :
    cuTripleWithinMem 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.stx .dword baseReg off valReg))
      ((baseReg ↦ᵣ baseAddr) ** (valReg ↦ᵣ vSrc) **
        (effectiveAddr baseAddr off ↦U64 oldV))
      ((baseReg ↦ᵣ baseAddr) ** (valReg ↦ᵣ vSrc) **
        (effectiveAddr baseAddr off ↦U64 vSrc))
      (fun rt => rt.containsWritable (effectiveAddr baseAddr off) 8 = true) :=
  cuTripleWithinMem_store_cell_via_reg_addr baseReg valReg baseAddr vSrc pc
    (.stx .dword baseReg off valReg)
    (PartialState.singletonMemU64 (effectiveAddr baseAddr off) oldV)
    (PartialState.singletonMemU64 (effectiveAddr baseAddr off) vSrc)
    _ _
    (fun m => Memory.writeU64 m (effectiveAddr baseAddr off) (vSrc % 2 ^ 64)) _
    (fun _ => Iff.rfl) (fun _ => Iff.rfl)
    (PartialState.singletonMemU64_memOnly _ _)
    (PartialState.singletonMemU64_memOnly _ _)
    (singletonMemU64_foot _ _ _)
    (singletonMemU64_write_in _ _ _ (by omega))
    (singletonMemU64_write_out _ _ _)
    (fun s hbase hval hreg => by
      simp only [step, hbase, Width.bytes, if_pos hreg,
                 Memory.writeByWidth, hval])

/-- `st .dword baseReg off imm`: store `toU64 imm % 2^(8*8)` at
    `[baseReg + off]`. From the immediate-store cell helper. -/
theorem stdw_spec
    (baseReg : Reg) (off : Int) (imm : Int)
    (baseAddr oldDwordVal : Nat) (pc : Nat) :
    cuTripleWithinMem 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.st .dword baseReg off imm))
      ((baseReg ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr off ↦U64 oldDwordVal))
      ((baseReg ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr off ↦U64 (toU64 imm % 2 ^ (8 * 8))))
      (fun rt => rt.containsWritable (effectiveAddr baseAddr off) 8 = true) :=
  cuTripleWithinMem_store_imm_cell_via_reg_addr baseReg baseAddr pc
    (.st .dword baseReg off imm)
    (PartialState.singletonMemU64 (effectiveAddr baseAddr off) oldDwordVal)
    (PartialState.singletonMemU64 (effectiveAddr baseAddr off)
      (toU64 imm % 2 ^ (8 * 8)))
    _ _
    (fun m => Memory.writeU64 m (effectiveAddr baseAddr off)
      (toU64 imm % 2 ^ (8 * 8))) _
    (fun _ => Iff.rfl) (fun _ => Iff.rfl)
    (PartialState.singletonMemU64_memOnly _ _)
    (PartialState.singletonMemU64_memOnly _ _)
    (singletonMemU64_foot _ _ _)
    (singletonMemU64_write_in _ _ _ rfl)
    (singletonMemU64_write_out _ _ _)
    (fun s hbase hreg => by
      simp only [step, hbase, Width.bytes, if_pos hreg, Memory.writeByWidth])

end SVM.SBPF
