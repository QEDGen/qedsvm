import SVM.SBPF.InstructionSpecs.MemByte
import SVM.SBPF.SegAggregation

namespace SVM.SBPF

open Memory

/-! ## Memory loads — dword width

`ldxdw` reads 8 LE bytes into a register; owns dst+src regs and a `memU64Is`
claim over the 8 bytes. Thin instantiations of the width-generic cell
helpers in `MemByte.lean` with `M := PartialState.singletonMemU64 ..`;
step discharged via `readU64_eq_of_bytes_match`. -/

/-- `ldx .dword dst src off`: load 64-bit value at `[src + off]` into `dst`. -/
theorem ldxdw_spec
    (dst src : Reg) (off : Int) (vOldDst baseAddr v : Nat) (pc : Nat)
    (hne : dst ≠ .r10) (hv : v < 2 ^ 64) :
    cuTripleWithinMem 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.ldx .dword dst src off))
      ((dst ↦ᵣ vOldDst) ** (src ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr off ↦U64 v))
      ((dst ↦ᵣ v) ** (src ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr off ↦U64 v))
      (fun rt => rt.containsRange (effectiveAddr baseAddr off) 8 = true) :=
  cuTripleWithinMem_load_cell_via_reg_addr dst src vOldDst baseAddr v pc
    (.ldx .dword dst src off)
    (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v) _ _
    hne (fun _ => Iff.rfl)
    (PartialState.singletonMemU64_memOnly _ _)
    (fun s _ hsrc hmem hreg => by
      have h_readU64 : Memory.readU64 s.mem (effectiveAddr baseAddr off) = v :=
        readU64_eq_of_bytes_match hv
          (hmem _ _ (PartialState.singletonMemU64_mem_0 _ _))
          (hmem _ _ (PartialState.singletonMemU64_mem_1 _ _))
          (hmem _ _ (PartialState.singletonMemU64_mem_2 _ _))
          (hmem _ _ (PartialState.singletonMemU64_mem_3 _ _))
          (hmem _ _ (PartialState.singletonMemU64_mem_4 _ _))
          (hmem _ _ (PartialState.singletonMemU64_mem_5 _ _))
          (hmem _ _ (PartialState.singletonMemU64_mem_6 _ _))
          (hmem _ _ (PartialState.singletonMemU64_mem_7 _ _))
      simp only [step, hsrc, Width.bytes, if_pos hreg,
                 Memory.readByWidth, h_readU64])

/-- `ldx .dword r r off`: same-register variant. Well-defined when dst = src
    because `step` reads `r` as base address before writing the loaded value;
    precondition owns one register atom + the 8-byte claim, post overwrites `r`. -/
theorem ldxdw_same_spec
    (r : Reg) (off : Int) (baseAddr v : Nat) (pc : Nat)
    (hne : r ≠ .r10) (hv : v < 2 ^ 64) :
    cuTripleWithinMem 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.ldx .dword r r off))
      ((r ↦ᵣ baseAddr) ** (effectiveAddr baseAddr off ↦U64 v))
      ((r ↦ᵣ v) ** (effectiveAddr baseAddr off ↦U64 v))
      (fun rt => rt.containsRange (effectiveAddr baseAddr off) 8 = true) :=
  cuTripleWithinMem_load_cell_same_reg r baseAddr v pc
    (.ldx .dword r r off)
    (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v) _ _
    hne (fun _ => Iff.rfl)
    (PartialState.singletonMemU64_memOnly _ _)
    (fun s hr hmem hreg => by
      have h_readU64 : Memory.readU64 s.mem (effectiveAddr baseAddr off) = v :=
        readU64_eq_of_bytes_match hv
          (hmem _ _ (PartialState.singletonMemU64_mem_0 _ _))
          (hmem _ _ (PartialState.singletonMemU64_mem_1 _ _))
          (hmem _ _ (PartialState.singletonMemU64_mem_2 _ _))
          (hmem _ _ (PartialState.singletonMemU64_mem_3 _ _))
          (hmem _ _ (PartialState.singletonMemU64_mem_4 _ _))
          (hmem _ _ (PartialState.singletonMemU64_mem_5 _ _))
          (hmem _ _ (PartialState.singletonMemU64_mem_6 _ _))
          (hmem _ _ (PartialState.singletonMemU64_mem_7 _ _))
      simp only [step, hr, Width.bytes, if_pos hreg,
                 Memory.readByWidth, h_readU64])

/-! ## Dword load over BYTE-granular memory (qedlift hot regions)

For MIXED-width access (e.g. pinocchio reads `input[0]` as byte and `input[0..8)`
as dword), qedlift keeps byte granularity so the sepConj stays satisfiable (H8
Phase B). This is `ldxdw_spec` reshaped through `byte_atoms_eq_memU64Is`; loaded
value is the LE Horner combination. -/

set_option maxHeartbeats 800000 in
/-- `ldx .dword dst src off` over eight byte atoms `[addr, addr+8)`.
    The loaded value is `b0 + 256·(b1 + 256·(… + 256·b7))`. -/
theorem ldxdw_bytes_spec
    (dst src : Reg) (off : Int)
    (vOldDst baseAddr b0 b1 b2 b3 b4 b5 b6 b7 : Nat)
    (a0 a1 a2 a3 a4 a5 a6 a7 : Nat) (pc : Nat)
    (hne : dst ≠ .r10)
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256)
    (hb4 : b4 < 256) (hb5 : b5 < 256) (hb6 : b6 < 256) (hb7 : b7 < 256)
    -- Slot addresses as parameters: byte cells may live under FOREIGN renderings;
    -- defining eqns are `rfl` for native slots, decide-discharged `h_alias_*` for foreign.
    (ha0 : a0 = effectiveAddr baseAddr off)
    (ha1 : a1 = effectiveAddr baseAddr off + 1)
    (ha2 : a2 = effectiveAddr baseAddr off + 2)
    (ha3 : a3 = effectiveAddr baseAddr off + 3)
    (ha4 : a4 = effectiveAddr baseAddr off + 4)
    (ha5 : a5 = effectiveAddr baseAddr off + 5)
    (ha6 : a6 = effectiveAddr baseAddr off + 6)
    (ha7 : a7 = effectiveAddr baseAddr off + 7) :
    cuTripleWithinMem 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.ldx .dword dst src off))
      ((dst ↦ᵣ vOldDst) ** (src ↦ᵣ baseAddr) **
        ((a0 ↦ₘ b0) ** (a1 ↦ₘ b1) ** (a2 ↦ₘ b2) ** (a3 ↦ₘ b3) **
         (a4 ↦ₘ b4) ** (a5 ↦ₘ b5) ** (a6 ↦ₘ b6) ** (a7 ↦ₘ b7)))
      ((dst ↦ᵣ b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 *
          (b4 + 256 * (b5 + 256 * (b6 + 256 * b7))))))) **
        (src ↦ᵣ baseAddr) **
        ((a0 ↦ₘ b0) ** (a1 ↦ₘ b1) ** (a2 ↦ₘ b2) ** (a3 ↦ₘ b3) **
         (a4 ↦ₘ b4) ** (a5 ↦ₘ b5) ** (a6 ↦ₘ b6) ** (a7 ↦ₘ b7)))
      (fun rt => rt.containsRange (effectiveAddr baseAddr off) 8 = true) := by
  subst ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7
  have hcombo : (b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 *
      (b4 + 256 * (b5 + 256 * (b6 + 256 * b7))))))) < 2 ^ 64 := by omega
  have hbridge := byte_atoms_eq_memU64Is (effectiveAddr baseAddr off)
      b0 b1 b2 b3 b4 b5 b6 b7 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
  refine cuTripleWithinMem_weaken ?_ ?_ (fun _ x => x)
    (ldxdw_spec dst src off vOldDst baseAddr _ pc hne hcombo)
  · intro h hh
    exact (sepConj_iff_congr_right _ (fun h' =>
      sepConj_iff_congr_right _ (fun h'' => hbridge h'') h') h).mp hh
  · intro h hh
    exact (sepConj_iff_congr_right _ (fun h' =>
      sepConj_iff_congr_right _ (fun h'' => (hbridge h'').symm) h') h).mp hh

end SVM.SBPF
