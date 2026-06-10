import SVM.SBPF.InstructionSpecs.Jump

namespace SVM.SBPF

open Memory

/-! ## Memory-byte reasoning helpers shared across widths

`readU64_eq_of_bytes_match` connects 8 byte-level facts to a single
`readU64` value via the `readU64_writeU64_same` lemma (a proven
theorem, not an axiom) — we show `mem` agrees with `writeU64 mem addr v`
at every address, then apply it. Used by `ldxdw_spec` to discharge step
semantics. -/

theorem readU16_eq_of_bytes_match {mem : Memory.Mem} {addr v : Nat}
    (hv : v < 2 ^ 16)
    (h0 : mem addr = v % 256)
    (h1 : mem (addr + 1) = v / 0x100 % 256) :
    Memory.readU16 mem addr = v := by
  unfold Memory.readU16
  rw [h0, h1]
  omega

theorem readU32_eq_of_bytes_match {mem : Memory.Mem} {addr v : Nat}
    (hv : v < 2 ^ 32)
    (h0 : mem addr = v % 256)
    (h1 : mem (addr + 1) = v / 0x100 % 256)
    (h2 : mem (addr + 2) = v / 0x10000 % 256)
    (h3 : mem (addr + 3) = v / 0x1000000 % 256) :
    Memory.readU32 mem addr = v := by
  unfold Memory.readU32
  rw [h0, h1, h2, h3]
  omega

theorem readU64_eq_of_bytes_match {mem : Memory.Mem} {addr v : Nat}
    (hv : v < 2 ^ 64)
    (h0 : mem addr = v % 256)
    (h1 : mem (addr + 1) = v / 0x100 % 256)
    (h2 : mem (addr + 2) = v / 0x10000 % 256)
    (h3 : mem (addr + 3) = v / 0x1000000 % 256)
    (h4 : mem (addr + 4) = v / 0x100000000 % 256)
    (h5 : mem (addr + 5) = v / 0x10000000000 % 256)
    (h6 : mem (addr + 6) = v / 0x1000000000000 % 256)
    (h7 : mem (addr + 7) = v / 0x100000000000000 % 256) :
    Memory.readU64 mem addr = v := by
  unfold Memory.readU64
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  omega

/-! ## Memory loads — byte-width helper + `ldx .byte`

The SL memory-op pattern is "owns a destination register, a base
register, and one memory byte; the instruction reads them and writes
a derived value to the destination." Capturing this once collapses
each per-instruction byte-load spec to a 3-line invocation that
supplies only the `step` reduction.

`cuTripleWithinMem_load_byte_via_reg_addr` is the generic pattern:
- precondition owns `(dst ↦ᵣ vOldDst) ** (src ↦ᵣ baseAddr) ** (addr ↦ₘ byteVal)`,
- postcondition is the same shape with `dst` updated to `vNew`,
- region requirement asserts the 1-byte read range is contained,
- `h_step` is the per-instruction step reduction (caller-supplied).

The proof here pays the 4-level partial-state destructure cost once;
specs built atop it (like `ldxb_spec`) are mechanical. -/

/-- Generic byte-load triple via a register-indexed address. -/
theorem cuTripleWithinMem_load_byte_via_reg_addr
    (dst src : Reg) (off : Int)
    (vOldDst baseAddr byteVal vNew : Nat) (pc : Nat) (insn : Insn)
    (hne : dst ≠ .r10)
    (h_step : ∀ s : State,
        s.regs.get dst = vOldDst →
        s.regs.get src = baseAddr →
        s.mem (effectiveAddr baseAddr off) = byteVal →
        s.regions.containsRange (effectiveAddr baseAddr off) 1 = true →
        step insn s = { s with regs := s.regs.set dst vNew, pc := s.pc + 1 }) :
    cuTripleWithinMem 1 0 pc (pc + 1)
      (CodeReq.singleton pc insn)
      ((dst ↦ᵣ vOldDst) ** (src ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr off ↦ₘ byteVal))
      ((dst ↦ᵣ vNew) ** (src ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr off ↦ₘ byteVal))
      (fun rt => rt.containsRange (effectiveAddr baseAddr off) 1 = true) := by
  intro R hRfree fetch hcr s hPR hpc hex h_region
  obtain ⟨hp, hcompat, h_P, h_R, hd_PR, hu_PR, h_P_sat, h_R_sat⟩ := hPR
  obtain ⟨h_dst, h_SM, hd_dst_SM, hu_dst_SM, h_dst_pred, h_SM_sat⟩ := h_P_sat
  obtain ⟨h_src, h_mem, hd_src_mem, hu_src_mem, h_src_pred, h_mem_pred⟩ := h_SM_sat
  rw [h_src_pred] at hu_src_mem hd_src_mem
  rw [h_mem_pred] at hu_src_mem hd_src_mem
  rw [h_dst_pred] at hu_dst_SM hd_dst_SM
  clear h_src_pred h_mem_pred h_dst_pred h_src h_mem h_dst
  have hcr_regs := hcompat.regs
  have hcm_mem := hcompat.mem
  have hne_dst_src : dst ≠ src := by
    have hd_dst_SM_regs := hd_dst_SM.regs
    intro habs
    rcases hd_dst_SM_regs dst with hl | hr
    · rw [PartialState.singletonReg_regs_self] at hl; nomatch hl
    · rw [← hu_src_mem] at hr
      have : ((PartialState.singletonReg src baseAddr).union
              (PartialState.singletonMem (effectiveAddr baseAddr off) byteVal)).regs dst
              = some baseAddr := by
        rw [habs]
        exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
      rw [this] at hr; nomatch hr
  have h_SM_regs_src : h_SM.regs src = some baseAddr := by
    rw [← hu_src_mem]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_SM_mem_addr : h_SM.mem (effectiveAddr baseAddr off) = some byteVal := by
    rw [← hu_src_mem]
    rw [PartialState.union_mem_of_left_none
        (PartialState.singletonReg_mem (effectiveAddr baseAddr off))]
    exact PartialState.singletonMem_mem_self
  have h_P_regs_dst : h_P.regs dst = some vOldDst := by
    rw [← hu_dst_SM]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_regs_src : h_P.regs src = some baseAddr := by
    rw [← hu_dst_SM]
    rw [PartialState.union_regs_of_left_none
        (PartialState.singletonReg_regs_other hne_dst_src.symm)]
    exact h_SM_regs_src
  have h_P_mem_addr : h_P.mem (effectiveAddr baseAddr off) = some byteVal := by
    rw [← hu_dst_SM]
    rw [PartialState.union_mem_of_left_none
        (PartialState.singletonReg_mem (effectiveAddr baseAddr off))]
    exact h_SM_mem_addr
  have hp_regs_dst : hp.regs dst = some vOldDst := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_dst
  have hp_regs_src : hp.regs src = some baseAddr := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_src
  have hp_mem_addr : hp.mem (effectiveAddr baseAddr off) = some byteVal := by
    rw [← hu_PR]; exact PartialState.union_mem_of_left_some h_P_mem_addr
  have hs_regs_dst : s.regs.get dst = vOldDst := hcr_regs dst vOldDst hp_regs_dst
  have hs_regs_src : s.regs.get src = baseAddr := hcr_regs src baseAddr hp_regs_src
  have hs_mem_addr : s.mem (effectiveAddr baseAddr off) = byteVal :=
    hcm_mem _ byteVal hp_mem_addr
  have hfetch : fetch s.pc = some insn := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hexec : executeFn fetch s 1 =
      { s with regs := s.regs.set dst vNew, pc := s.pc + 1 } := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch,
        executeFn_zero,
        h_step s hs_regs_dst hs_regs_src hs_mem_addr h_region]
  have hd_PR_regs := hd_PR.regs
  have hd_PR_mem := hd_PR.mem
  have h_R_no_dst : h_R.regs dst = none := by
    rcases hd_PR_regs dst with hl | hr
    · rw [h_P_regs_dst] at hl; nomatch hl
    · exact hr
  have h_R_no_src : h_R.regs src = none := by
    rcases hd_PR_regs src with hl | hr
    · rw [h_P_regs_src] at hl; nomatch hl
    · exact hr
  have h_R_no_mem_addr : h_R.mem (effectiveAddr baseAddr off) = none := by
    rcases hd_PR_mem (effectiveAddr baseAddr off) with hl | hr
    · rw [h_P_mem_addr] at hl; nomatch hl
    · exact hr
  have h_R_no_pc : h_R.pc = none := hRfree _ h_R_sat
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_, ?_⟩
  · rw [hexec]; show s.pc + 1 = pc + 1; rw [hpc]
  · rw [hexec]; exact hex
  · rw [hexec]; show s.cuConsumed ≤ s.cuConsumed + 0; omega
  · rw [hexec]
    refine ⟨_, ?_,
            (PartialState.singletonReg dst vNew).union
              ((PartialState.singletonReg src baseAddr).union
                (PartialState.singletonMem (effectiveAddr baseAddr off) byteVal)),
            h_R, ?_, rfl,
            ⟨PartialState.singletonReg dst vNew,
             (PartialState.singletonReg src baseAddr).union
              (PartialState.singletonMem (effectiveAddr baseAddr off) byteVal),
             ?_, rfl, rfl,
             ⟨PartialState.singletonReg src baseAddr,
              PartialState.singletonMem (effectiveAddr baseAddr off) byteVal,
              hd_src_mem, rfl, rfl, rfl⟩⟩,
            h_R_sat⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro r vr hvr
        show (s.regs.set dst vNew).get r = vr
        by_cases hrdst : r = dst
        · rw [hrdst] at hvr
          have h_inner :
              ((PartialState.singletonReg dst vNew).union
                ((PartialState.singletonReg src baseAddr).union
                  (PartialState.singletonMem (effectiveAddr baseAddr off) byteVal))).regs dst
              = some vNew :=
            PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
          rw [PartialState.union_regs_of_left_some h_inner] at hvr
          have : vr = vNew := (Option.some.inj hvr).symm
          rw [hrdst, this]; exact RegFile.get_set_self _ _ _ hne
        · rw [RegFile.get_set_diff _ _ _ _ hrdst]
          by_cases hrsrc : r = src
          · rw [hrsrc] at hvr
            have h_inner :
                ((PartialState.singletonReg dst vNew).union
                  ((PartialState.singletonReg src baseAddr).union
                    (PartialState.singletonMem (effectiveAddr baseAddr off) byteVal))).regs src
                = some baseAddr := by
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hne_dst_src.symm)]
              exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
            rw [PartialState.union_regs_of_left_some h_inner] at hvr
            have : vr = baseAddr := (Option.some.inj hvr).symm
            rw [hrsrc, this]
            exact hcr_regs src baseAddr hp_regs_src
          · have h_outer_h1_none :
                ((PartialState.singletonReg dst vNew).union
                  ((PartialState.singletonReg src baseAddr).union
                    (PartialState.singletonMem (effectiveAddr baseAddr off) byteVal))).regs r
                = none := by
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrdst)]
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrsrc)]
              exact PartialState.singletonMem_regs r
            rw [PartialState.union_regs_of_left_none h_outer_h1_none] at hvr
            apply hcr_regs r vr
            have h_P_none : h_P.regs r = none := by
              rw [← hu_dst_SM]
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrdst)]
              rw [← hu_src_mem]
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrsrc)]
              exact PartialState.singletonMem_regs r
            rw [← hu_PR]
            rw [PartialState.union_regs_of_left_none h_P_none]
            exact hvr
      · intro a vm hvm
        show s.mem a = vm
        by_cases ha : a = effectiveAddr baseAddr off
        · rw [ha] at hvm ⊢
          have h_inner :
              ((PartialState.singletonReg dst vNew).union
                ((PartialState.singletonReg src baseAddr).union
                  (PartialState.singletonMem (effectiveAddr baseAddr off) byteVal))).mem
                  (effectiveAddr baseAddr off)
              = some byteVal := by
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            exact PartialState.singletonMem_mem_self
          rw [PartialState.union_mem_of_left_some h_inner] at hvm
          have : vm = byteVal := (Option.some.inj hvm).symm
          rw [this]; exact hs_mem_addr
        · have h_outer_h1_none :
              ((PartialState.singletonReg dst vNew).union
                ((PartialState.singletonReg src baseAddr).union
                  (PartialState.singletonMem (effectiveAddr baseAddr off) byteVal))).mem a
              = none := by
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            exact PartialState.singletonMem_mem_other ha
          rw [PartialState.union_mem_of_left_none h_outer_h1_none] at hvm
          apply hcm_mem a vm
          have h_P_none : h_P.mem a = none := by
            rw [← hu_dst_SM]
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            rw [← hu_src_mem]
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            exact PartialState.singletonMem_mem_other ha
          rw [← hu_PR]
          rw [PartialState.union_mem_of_left_none h_P_none]
          exact hvm
      · intro vp hvp
        have h_outer_h1_pc :
            ((PartialState.singletonReg dst vNew).union
              ((PartialState.singletonReg src baseAddr).union
                (PartialState.singletonMem (effectiveAddr baseAddr off) byteVal))).pc
            = none := by
          rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
          rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
          exact PartialState.singletonMem_pc
        rw [PartialState.union_pc_of_left_none h_outer_h1_pc] at hvp
        rw [h_R_no_pc] at hvp
        nomatch hvp
      · intro rd hva
        first
        | exact hcompat.returnData rd hva
        | (rw [PartialState.union_returnData_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.returnData rd
             (by rw [
                    ← hu_PR,
                    ← hu_dst_SM,
                    ← hu_src_mem,
                    PartialState.union_returnData_of_left_none (by first | rfl | simp)]
                 exact hva))
        | (rw [PartialState.union_returnData_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.returnData rd
             (by rw [
                    ← hu_PR,
                    ← hu_dst_SM,
                    ← hu_src_mem,
                    PartialState.union_returnData_of_left_none (by first | rfl | simp)]
                 exact hva))
        | (rw [PartialState.union_returnData_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.returnData rd (by rw [← hu_PR]; exact hva))
      · intro cs hva
        first
        | exact hcompat.callStack cs hva
        | (rw [PartialState.union_callStack_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.callStack cs
             (by rw [
                    ← hu_PR,
                    ← hu_dst_SM,
                    ← hu_src_mem,
                    PartialState.union_callStack_of_left_none (by first | rfl | simp)]
                 exact hva))
        | (rw [PartialState.union_callStack_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.callStack cs
             (by rw [
                    ← hu_PR,
                    ← hu_dst_SM,
                    ← hu_src_mem,
                    PartialState.union_callStack_of_left_none (by first | rfl | simp)]
                 exact hva))
        | (rw [PartialState.union_callStack_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.callStack cs (by rw [← hu_PR]; exact hva))
    · refine ⟨?_, ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
      · intro r
        by_cases hrdst : r = dst
        · rw [hrdst]; right; exact h_R_no_dst
        · by_cases hrsrc : r = src
          · rw [hrsrc]; right; exact h_R_no_src
          · left
            rw [PartialState.union_regs_of_left_none
                (PartialState.singletonReg_regs_other hrdst)]
            rw [PartialState.union_regs_of_left_none
                (PartialState.singletonReg_regs_other hrsrc)]
            exact PartialState.singletonMem_regs r
      · intro a
        by_cases ha : a = effectiveAddr baseAddr off
        · rw [ha]; right; exact h_R_no_mem_addr
        · left
          rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
          rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
          exact PartialState.singletonMem_mem_other ha
      · left
        rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
        rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
        exact PartialState.singletonMem_pc
    · refine ⟨fun r => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
      · by_cases hrdst : r = dst
        · right
          rw [hrdst,
              PartialState.union_regs_of_left_none
                (PartialState.singletonReg_regs_other hne_dst_src)]
          exact PartialState.singletonMem_regs dst
        · left; exact PartialState.singletonReg_regs_other hrdst
      · left; exact PartialState.singletonReg_mem a
      · left; exact PartialState.singletonReg_pc

/-- `ldx .byte dst src off`: load byte at `[src + off]` into `dst`,
    masked to 8 bits. Derived from
    `cuTripleWithinMem_load_byte_via_reg_addr` with `vNew := byteVal % 256`. -/
theorem ldxb_spec
    (dst src : Reg) (off : Int) (vOldDst baseAddr byteVal : Nat) (pc : Nat)
    (hne : dst ≠ .r10) :
    cuTripleWithinMem 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.ldx .byte dst src off))
      ((dst ↦ᵣ vOldDst) ** (src ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr off ↦ₘ byteVal))
      ((dst ↦ᵣ (byteVal % 256)) ** (src ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr off ↦ₘ byteVal))
      (fun rt => rt.containsRange (effectiveAddr baseAddr off) 1 = true) :=
  cuTripleWithinMem_load_byte_via_reg_addr dst src off vOldDst baseAddr byteVal
    (byteVal % 256) pc (.ldx .byte dst src off) hne
    (fun _ _ hsrc hmem hreg => by
      simp only [step, hsrc, Width.bytes, if_pos hreg,
                 Memory.readByWidth, Memory.readU8, hmem])

/-- `ldx .byte r r off`: same-register variant — load a byte at `[r + off]`
    into `r`. `step` reads `r` as the base address before writing the loaded
    byte, so dst = src is well-defined. Owns one register atom (`r ↦ᵣ baseAddr`)
    plus the byte cell; the post overwrites `r` with `byteVal % 256`. The
    generic `ldxb_spec` can't cover this — it splits dst and src into two
    register atoms, which collapse to a duplicate (unsatisfiable) `r` atom
    when dst = src (e.g. the `ldxb r2, [r2]` pointer-deref at p_token's
    initializeMint entry). -/
theorem ldxb_same_spec
    (r : Reg) (off : Int) (baseAddr byteVal : Nat) (pc : Nat)
    (hne : r ≠ .r10) :
    cuTripleWithinMem 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.ldx .byte r r off))
      ((r ↦ᵣ baseAddr) ** (effectiveAddr baseAddr off ↦ₘ byteVal))
      ((r ↦ᵣ (byteVal % 256)) ** (effectiveAddr baseAddr off ↦ₘ byteVal))
      (fun rt => rt.containsRange (effectiveAddr baseAddr off) 1 = true) := by
  intro R hRfree fetch hcr s hPR hpc hex h_region
  obtain ⟨hp, hcompat, h_P, h_R, hd_PR, hu_PR, h_P_sat, h_R_sat⟩ := hPR
  obtain ⟨h_reg, h_mem, hd_reg_mem, hu_reg_mem, h_reg_pred, h_mem_pred⟩ := h_P_sat
  rw [h_reg_pred] at hu_reg_mem hd_reg_mem
  rw [h_mem_pred] at hu_reg_mem hd_reg_mem
  clear h_reg_pred h_mem_pred h_reg h_mem
  have hcr_regs := hcompat.regs
  have hcm_mem := hcompat.mem
  have h_P_regs_r : h_P.regs r = some baseAddr := by
    rw [← hu_reg_mem]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_mem_0 : h_P.mem (effectiveAddr baseAddr off) = some byteVal := by
    rw [← hu_reg_mem,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact PartialState.singletonMem_mem_self
  have hp_regs_r : hp.regs r = some baseAddr := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r
  have hp_mem_0 : hp.mem (effectiveAddr baseAddr off) = some byteVal := by
    rw [← hu_PR]; exact PartialState.union_mem_of_left_some h_P_mem_0
  have hs_regs_r : s.regs.get r = baseAddr := hcr_regs r baseAddr hp_regs_r
  have hs_mem_0 : s.mem (effectiveAddr baseAddr off) = byteVal := hcm_mem _ _ hp_mem_0
  have hfetch : fetch s.pc = some (.ldx .byte r r off) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hexec : executeFn fetch s 1 =
      { s with regs := s.regs.set r (byteVal % 256), pc := s.pc + 1 } := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch,
        executeFn_zero]
    simp only [step, hs_regs_r, Width.bytes, if_pos h_region,
               Memory.readByWidth, Memory.readU8, hs_mem_0]
  have hd_PR_regs := hd_PR.regs
  have hd_PR_mem := hd_PR.mem
  have h_R_no_r : h_R.regs r = none := by
    rcases hd_PR_regs r with hl | hr
    · rw [h_P_regs_r] at hl; nomatch hl
    · exact hr
  have h_R_no_mem_0 : h_R.mem (effectiveAddr baseAddr off) = none := by
    rcases hd_PR_mem (effectiveAddr baseAddr off) with hl | hr
    · rw [h_P_mem_0] at hl; nomatch hl
    · exact hr
  have h_R_no_pc : h_R.pc = none := hRfree _ h_R_sat
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_, ?_⟩
  · rw [hexec]; show s.pc + 1 = pc + 1; rw [hpc]
  · rw [hexec]; exact hex
  · rw [hexec]; show s.cuConsumed ≤ s.cuConsumed + 0; omega
  · rw [hexec]
    refine ⟨_, ?_,
            (PartialState.singletonReg r (byteVal % 256)).union
              (PartialState.singletonMem (effectiveAddr baseAddr off) byteVal),
            h_R, ?_, rfl,
            ⟨PartialState.singletonReg r (byteVal % 256),
             PartialState.singletonMem (effectiveAddr baseAddr off) byteVal,
             ?_, rfl, rfl, rfl⟩,
            h_R_sat⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro rr vr hvr
        show (s.regs.set r (byteVal % 256)).get rr = vr
        by_cases hrr : rr = r
        · rw [hrr] at hvr
          have h_inner :
              ((PartialState.singletonReg r (byteVal % 256)).union
                (PartialState.singletonMem (effectiveAddr baseAddr off) byteVal)).regs r
              = some (byteVal % 256) :=
            PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
          rw [PartialState.union_regs_of_left_some h_inner] at hvr
          have : vr = byteVal % 256 := (Option.some.inj hvr).symm
          rw [hrr, this]
          exact RegFile.get_set_self _ _ _ hne
        · rw [RegFile.get_set_diff _ _ _ _ hrr]
          have h_outer_none :
              ((PartialState.singletonReg r (byteVal % 256)).union
                (PartialState.singletonMem (effectiveAddr baseAddr off) byteVal)).regs rr
              = none := by
            rw [PartialState.union_regs_of_left_none
                (PartialState.singletonReg_regs_other hrr)]
            exact PartialState.singletonMem_regs rr
          rw [PartialState.union_regs_of_left_none h_outer_none] at hvr
          apply hcr_regs rr vr
          have h_P_none : h_P.regs rr = none := by
            rw [← hu_reg_mem]
            rw [PartialState.union_regs_of_left_none
                (PartialState.singletonReg_regs_other hrr)]
            exact PartialState.singletonMem_regs rr
          rw [← hu_PR]
          rw [PartialState.union_regs_of_left_none h_P_none]
          exact hvr
      · intro a vm hvm
        show s.mem a = vm
        by_cases ha0 : a = effectiveAddr baseAddr off
        · rw [ha0] at hvm ⊢
          have h_inner :
              ((PartialState.singletonReg r (byteVal % 256)).union
                (PartialState.singletonMem (effectiveAddr baseAddr off) byteVal)).mem
                  (effectiveAddr baseAddr off) = some byteVal := by
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            exact PartialState.singletonMem_mem_self
          rw [PartialState.union_mem_of_left_some h_inner] at hvm
          have : vm = byteVal := (Option.some.inj hvm).symm
          rw [this]; exact hs_mem_0
        · have h_outer_none :
              ((PartialState.singletonReg r (byteVal % 256)).union
                (PartialState.singletonMem (effectiveAddr baseAddr off) byteVal)).mem a
              = none := by
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            exact PartialState.singletonMem_mem_other ha0
          rw [PartialState.union_mem_of_left_none h_outer_none] at hvm
          apply hcm_mem a vm
          have h_P_none : h_P.mem a = none := by
            rw [← hu_reg_mem]
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            exact PartialState.singletonMem_mem_other ha0
          rw [← hu_PR]
          rw [PartialState.union_mem_of_left_none h_P_none]
          exact hvm
      · intro vp hvp
        have h_outer_pc :
            ((PartialState.singletonReg r (byteVal % 256)).union
              (PartialState.singletonMem (effectiveAddr baseAddr off) byteVal)).pc = none := by
          rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
          exact PartialState.singletonMem_pc
        rw [PartialState.union_pc_of_left_none h_outer_pc] at hvp
        rw [h_R_no_pc] at hvp
        nomatch hvp
      · intro rd hva
        first
        | exact hcompat.returnData rd hva
        | (rw [PartialState.union_returnData_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.returnData rd
             (by rw [← hu_PR, ← hu_reg_mem,
                    PartialState.union_returnData_of_left_none (by first | rfl | simp)]
                 exact hva))
        | (rw [PartialState.union_returnData_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.returnData rd (by rw [← hu_PR]; exact hva))
      · intro cs hva
        first
        | exact hcompat.callStack cs hva
        | (rw [PartialState.union_callStack_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.callStack cs
             (by rw [← hu_PR, ← hu_reg_mem,
                    PartialState.union_callStack_of_left_none (by first | rfl | simp)]
                 exact hva))
        | (rw [PartialState.union_callStack_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.callStack cs (by rw [← hu_PR]; exact hva))
    · refine ⟨?_, ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
      · intro rr
        by_cases hrr : rr = r
        · rw [hrr]; right; exact h_R_no_r
        · left
          rw [PartialState.union_regs_of_left_none
              (PartialState.singletonReg_regs_other hrr)]
          exact PartialState.singletonMem_regs rr
      · intro a
        by_cases ha0 : a = effectiveAddr baseAddr off
        · rw [ha0]; right; exact h_R_no_mem_0
        · left
          rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
          exact PartialState.singletonMem_mem_other ha0
      · left
        rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
        exact PartialState.singletonMem_pc
    · refine ⟨fun rr => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
      · right; exact PartialState.singletonMem_regs rr
      · left; exact PartialState.singletonReg_mem a
      · left; exact PartialState.singletonReg_pc

/-! ## Memory stores — byte-width helper + `stx .byte`

The byte-store SL pattern: instruction reads two registers (base
address + value), updates one memory byte to a value derived from
those registers. Symmetric to the load helper but with the partial
state's memory cell changing value between pre and post (the byte
masked to 8 bits is what `writeU8` actually stores). -/

/-- Generic byte-store triple via a register-indexed address.
    `newByteVal` is the actual byte stored, so callers pass it
    pre-masked (`< 256`) — `h_lt` discharges `writeU8`'s internal mod. -/
theorem cuTripleWithinMem_store_byte_via_reg_addr
    (baseReg valReg : Reg) (off : Int)
    (baseAddr vSrc oldByteVal newByteVal : Nat)
    (pc : Nat) (insn : Insn)
    (h_lt : newByteVal < 256)
    (h_step : ∀ s : State,
        s.regs.get baseReg = baseAddr →
        s.regs.get valReg = vSrc →
        s.regions.containsWritable (effectiveAddr baseAddr off) 1 = true →
        step insn s =
          { s with mem := Memory.writeU8 s.mem (effectiveAddr baseAddr off) newByteVal,
                   pc := s.pc + 1 }) :
    cuTripleWithinMem 1 0 pc (pc + 1)
      (CodeReq.singleton pc insn)
      ((baseReg ↦ᵣ baseAddr) ** (valReg ↦ᵣ vSrc) **
        (effectiveAddr baseAddr off ↦ₘ oldByteVal))
      ((baseReg ↦ᵣ baseAddr) ** (valReg ↦ᵣ vSrc) **
        (effectiveAddr baseAddr off ↦ₘ newByteVal))
      (fun rt => rt.containsWritable (effectiveAddr baseAddr off) 1 = true) := by
  intro R hRfree fetch hcr s hPR hpc hex h_region
  obtain ⟨hp, hcompat, h_P, h_R, hd_PR, hu_PR, h_P_sat, h_R_sat⟩ := hPR
  obtain ⟨h_base, h_VM, hd_base_VM, hu_base_VM, h_base_pred, h_VM_sat⟩ := h_P_sat
  obtain ⟨h_val, h_mem, hd_val_mem, hu_val_mem, h_val_pred, h_mem_pred⟩ := h_VM_sat
  rw [h_val_pred] at hu_val_mem hd_val_mem
  rw [h_mem_pred] at hu_val_mem hd_val_mem
  rw [h_base_pred] at hu_base_VM hd_base_VM
  clear h_val_pred h_mem_pred h_base_pred h_val h_mem h_base
  have hcr_regs := hcompat.regs
  have hcm_mem := hcompat.mem
  have hne_base_val : baseReg ≠ valReg := by
    have hd_base_VM_regs := hd_base_VM.regs
    intro habs
    rcases hd_base_VM_regs baseReg with hl | hr
    · rw [PartialState.singletonReg_regs_self] at hl; nomatch hl
    · rw [← hu_val_mem] at hr
      have : ((PartialState.singletonReg valReg vSrc).union
              (PartialState.singletonMem (effectiveAddr baseAddr off) oldByteVal)).regs baseReg
              = some vSrc := by
        rw [habs]
        exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
      rw [this] at hr; nomatch hr
  have h_VM_regs_val : h_VM.regs valReg = some vSrc := by
    rw [← hu_val_mem]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_VM_mem_addr : h_VM.mem (effectiveAddr baseAddr off) = some oldByteVal := by
    rw [← hu_val_mem]
    rw [PartialState.union_mem_of_left_none
        (PartialState.singletonReg_mem (effectiveAddr baseAddr off))]
    exact PartialState.singletonMem_mem_self
  have h_P_regs_base : h_P.regs baseReg = some baseAddr := by
    rw [← hu_base_VM]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_regs_val : h_P.regs valReg = some vSrc := by
    rw [← hu_base_VM]
    rw [PartialState.union_regs_of_left_none
        (PartialState.singletonReg_regs_other hne_base_val.symm)]
    exact h_VM_regs_val
  have h_P_mem_addr : h_P.mem (effectiveAddr baseAddr off) = some oldByteVal := by
    rw [← hu_base_VM]
    rw [PartialState.union_mem_of_left_none
        (PartialState.singletonReg_mem (effectiveAddr baseAddr off))]
    exact h_VM_mem_addr
  have hp_regs_base : hp.regs baseReg = some baseAddr := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_base
  have hp_regs_val : hp.regs valReg = some vSrc := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_val
  have hp_mem_addr : hp.mem (effectiveAddr baseAddr off) = some oldByteVal := by
    rw [← hu_PR]; exact PartialState.union_mem_of_left_some h_P_mem_addr
  have hs_regs_base : s.regs.get baseReg = baseAddr :=
    hcr_regs baseReg baseAddr hp_regs_base
  have hs_regs_val : s.regs.get valReg = vSrc := hcr_regs valReg vSrc hp_regs_val
  have hfetch : fetch s.pc = some insn := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hexec : executeFn fetch s 1 =
      { s with mem := Memory.writeU8 s.mem (effectiveAddr baseAddr off) newByteVal,
               pc := s.pc + 1 } := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch,
        executeFn_zero,
        h_step s hs_regs_base hs_regs_val h_region]
  have hd_PR_regs := hd_PR.regs
  have hd_PR_mem := hd_PR.mem
  have h_R_no_base : h_R.regs baseReg = none := by
    rcases hd_PR_regs baseReg with hl | hr
    · rw [h_P_regs_base] at hl; nomatch hl
    · exact hr
  have h_R_no_val : h_R.regs valReg = none := by
    rcases hd_PR_regs valReg with hl | hr
    · rw [h_P_regs_val] at hl; nomatch hl
    · exact hr
  have h_R_no_mem_addr : h_R.mem (effectiveAddr baseAddr off) = none := by
    rcases hd_PR_mem (effectiveAddr baseAddr off) with hl | hr
    · rw [h_P_mem_addr] at hl; nomatch hl
    · exact hr
  have h_R_no_pc : h_R.pc = none := hRfree _ h_R_sat
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_, ?_⟩
  · rw [hexec]; show s.pc + 1 = pc + 1; rw [hpc]
  · rw [hexec]; exact hex
  · rw [hexec]; show s.cuConsumed ≤ s.cuConsumed + 0; omega
  · rw [hexec]
    refine ⟨_, ?_,
            (PartialState.singletonReg baseReg baseAddr).union
              ((PartialState.singletonReg valReg vSrc).union
                (PartialState.singletonMem (effectiveAddr baseAddr off) (newByteVal))),
            h_R, ?_, rfl,
            ⟨PartialState.singletonReg baseReg baseAddr,
             (PartialState.singletonReg valReg vSrc).union
              (PartialState.singletonMem (effectiveAddr baseAddr off) (newByteVal)),
             ?_, rfl, rfl,
             ⟨PartialState.singletonReg valReg vSrc,
              PartialState.singletonMem (effectiveAddr baseAddr off) (newByteVal),
              ?_, rfl, rfl, rfl⟩⟩,
            h_R_sat⟩
    -- (a) Compat of the new witness with the post state (post = { s with mem := ..., pc := s.pc + 1 }).
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro r vr hvr
        -- regs are unchanged in the post state
        show s.regs.get r = vr
        by_cases hrbase : r = baseReg
        · rw [hrbase] at hvr
          have h_inner :
              ((PartialState.singletonReg baseReg baseAddr).union
                ((PartialState.singletonReg valReg vSrc).union
                  (PartialState.singletonMem (effectiveAddr baseAddr off)
                    (newByteVal)))).regs baseReg = some baseAddr :=
            PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
          rw [PartialState.union_regs_of_left_some h_inner] at hvr
          have : vr = baseAddr := (Option.some.inj hvr).symm
          rw [hrbase, this]; exact hs_regs_base
        · by_cases hrval : r = valReg
          · rw [hrval] at hvr
            have h_inner :
                ((PartialState.singletonReg baseReg baseAddr).union
                  ((PartialState.singletonReg valReg vSrc).union
                    (PartialState.singletonMem (effectiveAddr baseAddr off)
                      (newByteVal)))).regs valReg = some vSrc := by
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hne_base_val.symm)]
              exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
            rw [PartialState.union_regs_of_left_some h_inner] at hvr
            have : vr = vSrc := (Option.some.inj hvr).symm
            rw [hrval, this]; exact hs_regs_val
          · have h_outer_h1_none :
                ((PartialState.singletonReg baseReg baseAddr).union
                  ((PartialState.singletonReg valReg vSrc).union
                    (PartialState.singletonMem (effectiveAddr baseAddr off)
                      (newByteVal)))).regs r = none := by
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrbase)]
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrval)]
              exact PartialState.singletonMem_regs r
            rw [PartialState.union_regs_of_left_none h_outer_h1_none] at hvr
            apply hcr_regs r vr
            have h_P_none : h_P.regs r = none := by
              rw [← hu_base_VM]
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrbase)]
              rw [← hu_val_mem]
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrval)]
              exact PartialState.singletonMem_regs r
            rw [← hu_PR]
            rw [PartialState.union_regs_of_left_none h_P_none]
            exact hvr
      · intro a vm hvm
        show (Memory.writeU8 s.mem (effectiveAddr baseAddr off) newByteVal) a = vm
        by_cases ha : a = effectiveAddr baseAddr off
        · rw [ha] at hvm ⊢
          have h_inner :
              ((PartialState.singletonReg baseReg baseAddr).union
                ((PartialState.singletonReg valReg vSrc).union
                  (PartialState.singletonMem (effectiveAddr baseAddr off)
                    (newByteVal)))).mem (effectiveAddr baseAddr off)
              = some (newByteVal) := by
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            exact PartialState.singletonMem_mem_self
          rw [PartialState.union_mem_of_left_some h_inner] at hvm
          have : vm = newByteVal := (Option.some.inj hvm).symm
          rw [this]
          -- writeU8 stores `newByteVal % 256` at addr; with h_lt, equals newByteVal.
          unfold Memory.writeU8; simp
          exact h_lt
        · have h_outer_h1_none :
              ((PartialState.singletonReg baseReg baseAddr).union
                ((PartialState.singletonReg valReg vSrc).union
                  (PartialState.singletonMem (effectiveAddr baseAddr off)
                    (newByteVal)))).mem a = none := by
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            exact PartialState.singletonMem_mem_other ha
          rw [PartialState.union_mem_of_left_none h_outer_h1_none] at hvm
          -- mem at a ≠ addr is unchanged by writeU8
          unfold Memory.writeU8
          simp [ha]
          -- new state mem at a = s.mem a; from pre compat
          apply hcm_mem a vm
          have h_P_none : h_P.mem a = none := by
            rw [← hu_base_VM]
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            rw [← hu_val_mem]
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            exact PartialState.singletonMem_mem_other ha
          rw [← hu_PR]
          rw [PartialState.union_mem_of_left_none h_P_none]
          exact hvm
      · intro vp hvp
        have h_outer_h1_pc :
            ((PartialState.singletonReg baseReg baseAddr).union
              ((PartialState.singletonReg valReg vSrc).union
                (PartialState.singletonMem (effectiveAddr baseAddr off)
                  (newByteVal)))).pc = none := by
          rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
          rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
          exact PartialState.singletonMem_pc
        rw [PartialState.union_pc_of_left_none h_outer_h1_pc] at hvp
        rw [h_R_no_pc] at hvp
        nomatch hvp
      · intro rd hva
        first
        | exact hcompat.returnData rd hva
        | (rw [PartialState.union_returnData_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.returnData rd
             (by rw [
                    ← hu_PR,
                    ← hu_base_VM,
                    ← hu_val_mem,
                    PartialState.union_returnData_of_left_none (by first | rfl | simp)]
                 exact hva))
        | (rw [PartialState.union_returnData_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.returnData rd
             (by rw [
                    ← hu_PR,
                    ← hu_base_VM,
                    ← hu_val_mem,
                    PartialState.union_returnData_of_left_none (by first | rfl | simp)]
                 exact hva))
        | (rw [PartialState.union_returnData_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.returnData rd (by rw [← hu_PR]; exact hva))
      · intro cs hva
        first
        | exact hcompat.callStack cs hva
        | (rw [PartialState.union_callStack_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.callStack cs
             (by rw [
                    ← hu_PR,
                    ← hu_base_VM,
                    ← hu_val_mem,
                    PartialState.union_callStack_of_left_none (by first | rfl | simp)]
                 exact hva))
        | (rw [PartialState.union_callStack_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.callStack cs
             (by rw [
                    ← hu_PR,
                    ← hu_base_VM,
                    ← hu_val_mem,
                    PartialState.union_callStack_of_left_none (by first | rfl | simp)]
                 exact hva))
        | (rw [PartialState.union_callStack_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.callStack cs (by rw [← hu_PR]; exact hva))
    -- (b) Outer disjointness: new witness ⊥ h_R.
    · refine ⟨?_, ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
      · intro r
        by_cases hrbase : r = baseReg
        · rw [hrbase]; right; exact h_R_no_base
        · by_cases hrval : r = valReg
          · rw [hrval]; right; exact h_R_no_val
          · left
            rw [PartialState.union_regs_of_left_none
                (PartialState.singletonReg_regs_other hrbase)]
            rw [PartialState.union_regs_of_left_none
                (PartialState.singletonReg_regs_other hrval)]
            exact PartialState.singletonMem_regs r
      · intro a
        by_cases ha : a = effectiveAddr baseAddr off
        · rw [ha]; right; exact h_R_no_mem_addr
        · left
          rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
          rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
          exact PartialState.singletonMem_mem_other ha
      · left
        rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
        rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
        exact PartialState.singletonMem_pc
    -- (c) Inner disjointness: singletonReg baseReg ⊥ (singletonReg valReg ⊎ singletonMem addr).
    · refine ⟨fun r => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
      · by_cases hrbase : r = baseReg
        · right
          rw [hrbase,
              PartialState.union_regs_of_left_none
                (PartialState.singletonReg_regs_other hne_base_val)]
          exact PartialState.singletonMem_regs baseReg
        · left; exact PartialState.singletonReg_regs_other hrbase
      · left; exact PartialState.singletonReg_mem a
      · left; exact PartialState.singletonReg_pc
    -- (d) Innermost disjointness: singletonReg valReg ⊥ singletonMem addr.
    -- singletonMem has no regs, singletonReg has no mem, neither owns pc.
    · refine ⟨fun r => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
      · right; exact PartialState.singletonMem_regs r
      · left; exact PartialState.singletonReg_mem a
      · left; exact PartialState.singletonReg_pc

/-- `stx .byte baseReg off valReg`: store byte `(valReg & 0xff)` at
    `[baseReg + off]`. Derived from the store helper with
    `newByteVal := vSrc % 256`. -/
theorem stxb_spec
    (baseReg valReg : Reg) (off : Int)
    (baseAddr vSrc oldByteVal : Nat) (pc : Nat) :
    cuTripleWithinMem 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.stx .byte baseReg off valReg))
      ((baseReg ↦ᵣ baseAddr) ** (valReg ↦ᵣ vSrc) **
        (effectiveAddr baseAddr off ↦ₘ oldByteVal))
      ((baseReg ↦ᵣ baseAddr) ** (valReg ↦ᵣ vSrc) **
        (effectiveAddr baseAddr off ↦ₘ (vSrc % 256)))
      (fun rt => rt.containsWritable (effectiveAddr baseAddr off) 1 = true) :=
  cuTripleWithinMem_store_byte_via_reg_addr baseReg valReg off
    baseAddr vSrc oldByteVal (vSrc % 256) pc (.stx .byte baseReg off valReg)
    (Nat.mod_lt _ (by decide : (0 : Nat) < 256))
    (fun _ hbase hval hreg => by
      simp only [step, hbase, Width.bytes, if_pos hreg,
                 Memory.writeByWidth, hval])

/-! ## Memory stores from immediates — byte-width helper + `st .byte`

Two-resource pattern: owns one base register and one memory byte.
Simpler than `stxb`'s helper because there's no value register —
the value is the instruction's immediate field. -/

/-- Generic byte-store triple from an immediate value. Mirror of
    `cuTripleWithinMem_store_byte_via_reg_addr` minus the value
    register. -/
theorem cuTripleWithinMem_store_imm_byte_via_reg_addr
    (baseReg : Reg) (off : Int)
    (baseAddr oldByteVal newByteVal : Nat) (pc : Nat) (insn : Insn)
    (h_lt : newByteVal < 256)
    (h_step : ∀ s : State,
        s.regs.get baseReg = baseAddr →
        s.regions.containsWritable (effectiveAddr baseAddr off) 1 = true →
        step insn s =
          { s with mem := Memory.writeU8 s.mem (effectiveAddr baseAddr off) newByteVal,
                   pc := s.pc + 1 }) :
    cuTripleWithinMem 1 0 pc (pc + 1)
      (CodeReq.singleton pc insn)
      ((baseReg ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr off ↦ₘ oldByteVal))
      ((baseReg ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr off ↦ₘ newByteVal))
      (fun rt => rt.containsWritable (effectiveAddr baseAddr off) 1 = true) := by
  intro R hRfree fetch hcr s hPR hpc hex h_region
  -- 2-level destructure: hp = h_P ⊎ h_R, h_P = h_base ⊎ h_mem.
  obtain ⟨hp, hcompat, h_P, h_R, hd_PR, hu_PR, h_P_sat, h_R_sat⟩ := hPR
  obtain ⟨h_base, h_mem, hd_base_mem, hu_base_mem, h_base_pred, h_mem_pred⟩ := h_P_sat
  rw [h_base_pred] at hu_base_mem hd_base_mem
  rw [h_mem_pred] at hu_base_mem hd_base_mem
  clear h_base_pred h_mem_pred h_base h_mem
  have hcr_regs := hcompat.regs
  have hcm_mem := hcompat.mem
  have h_P_regs_base : h_P.regs baseReg = some baseAddr := by
    rw [← hu_base_mem]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_mem_addr : h_P.mem (effectiveAddr baseAddr off) = some oldByteVal := by
    rw [← hu_base_mem]
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact PartialState.singletonMem_mem_self
  have hp_regs_base : hp.regs baseReg = some baseAddr := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_base
  have hp_mem_addr : hp.mem (effectiveAddr baseAddr off) = some oldByteVal := by
    rw [← hu_PR]; exact PartialState.union_mem_of_left_some h_P_mem_addr
  have hs_regs_base : s.regs.get baseReg = baseAddr :=
    hcr_regs baseReg baseAddr hp_regs_base
  have hfetch : fetch s.pc = some insn := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hexec : executeFn fetch s 1 =
      { s with mem := Memory.writeU8 s.mem (effectiveAddr baseAddr off) newByteVal,
               pc := s.pc + 1 } := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch,
        executeFn_zero,
        h_step s hs_regs_base h_region]
  have hd_PR_regs := hd_PR.regs
  have hd_PR_mem := hd_PR.mem
  have h_R_no_base : h_R.regs baseReg = none := by
    rcases hd_PR_regs baseReg with hl | hr
    · rw [h_P_regs_base] at hl; nomatch hl
    · exact hr
  have h_R_no_mem_addr : h_R.mem (effectiveAddr baseAddr off) = none := by
    rcases hd_PR_mem (effectiveAddr baseAddr off) with hl | hr
    · rw [h_P_mem_addr] at hl; nomatch hl
    · exact hr
  have h_R_no_pc : h_R.pc = none := hRfree _ h_R_sat
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_, ?_⟩
  · rw [hexec]; show s.pc + 1 = pc + 1; rw [hpc]
  · rw [hexec]; exact hex
  · rw [hexec]; show s.cuConsumed ≤ s.cuConsumed + 0; omega
  · rw [hexec]
    refine ⟨_, ?_,
            (PartialState.singletonReg baseReg baseAddr).union
              (PartialState.singletonMem (effectiveAddr baseAddr off) newByteVal),
            h_R, ?_, rfl,
            ⟨PartialState.singletonReg baseReg baseAddr,
             PartialState.singletonMem (effectiveAddr baseAddr off) newByteVal,
             ?_, rfl, rfl, rfl⟩,
            h_R_sat⟩
    -- (a) Compat of the new witness with the post state.
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro r vr hvr
        show s.regs.get r = vr
        by_cases hrbase : r = baseReg
        · rw [hrbase] at hvr
          have h_inner :
              ((PartialState.singletonReg baseReg baseAddr).union
                (PartialState.singletonMem (effectiveAddr baseAddr off) newByteVal)).regs
                  baseReg = some baseAddr :=
            PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
          rw [PartialState.union_regs_of_left_some h_inner] at hvr
          have : vr = baseAddr := (Option.some.inj hvr).symm
          rw [hrbase, this]; exact hs_regs_base
        · -- r ≠ baseReg: outer-h1 doesn't own r → falls through to h_R.
          have h_outer_h1_none :
              ((PartialState.singletonReg baseReg baseAddr).union
                (PartialState.singletonMem (effectiveAddr baseAddr off) newByteVal)).regs r
              = none := by
            rw [PartialState.union_regs_of_left_none
                (PartialState.singletonReg_regs_other hrbase)]
            exact PartialState.singletonMem_regs r
          rw [PartialState.union_regs_of_left_none h_outer_h1_none] at hvr
          apply hcr_regs r vr
          have h_P_none : h_P.regs r = none := by
            rw [← hu_base_mem]
            rw [PartialState.union_regs_of_left_none
                (PartialState.singletonReg_regs_other hrbase)]
            exact PartialState.singletonMem_regs r
          rw [← hu_PR]
          rw [PartialState.union_regs_of_left_none h_P_none]
          exact hvr
      · intro a vm hvm
        show (Memory.writeU8 s.mem (effectiveAddr baseAddr off) newByteVal) a = vm
        by_cases ha : a = effectiveAddr baseAddr off
        · rw [ha] at hvm ⊢
          have h_inner :
              ((PartialState.singletonReg baseReg baseAddr).union
                (PartialState.singletonMem (effectiveAddr baseAddr off) newByteVal)).mem
                  (effectiveAddr baseAddr off) = some newByteVal := by
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            exact PartialState.singletonMem_mem_self
          rw [PartialState.union_mem_of_left_some h_inner] at hvm
          have : vm = newByteVal := (Option.some.inj hvm).symm
          rw [this]
          unfold Memory.writeU8; simp
          exact h_lt
        · have h_outer_h1_none :
              ((PartialState.singletonReg baseReg baseAddr).union
                (PartialState.singletonMem (effectiveAddr baseAddr off) newByteVal)).mem a
              = none := by
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            exact PartialState.singletonMem_mem_other ha
          rw [PartialState.union_mem_of_left_none h_outer_h1_none] at hvm
          unfold Memory.writeU8
          simp only [Memory.Mem.read_put]
          rw [if_neg ha]
          apply hcm_mem a vm
          have h_P_none : h_P.mem a = none := by
            rw [← hu_base_mem]
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            exact PartialState.singletonMem_mem_other ha
          rw [← hu_PR]
          rw [PartialState.union_mem_of_left_none h_P_none]
          exact hvm
      · intro vp hvp
        have h_outer_h1_pc :
            ((PartialState.singletonReg baseReg baseAddr).union
              (PartialState.singletonMem (effectiveAddr baseAddr off) newByteVal)).pc = none := by
          rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
          exact PartialState.singletonMem_pc
        rw [PartialState.union_pc_of_left_none h_outer_h1_pc] at hvp
        rw [h_R_no_pc] at hvp
        nomatch hvp
      · intro rd hva
        first
        | exact hcompat.returnData rd hva
        | (rw [PartialState.union_returnData_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.returnData rd
             (by rw [
                    ← hu_PR,
                    ← hu_base_mem,
                    PartialState.union_returnData_of_left_none (by first | rfl | simp)]
                 exact hva))
        | (rw [PartialState.union_returnData_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.returnData rd
             (by rw [
                    ← hu_PR,
                    ← hu_base_mem,
                    PartialState.union_returnData_of_left_none (by first | rfl | simp)]
                 exact hva))
        | (rw [PartialState.union_returnData_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.returnData rd (by rw [← hu_PR]; exact hva))
      · intro cs hva
        first
        | exact hcompat.callStack cs hva
        | (rw [PartialState.union_callStack_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.callStack cs
             (by rw [
                    ← hu_PR,
                    ← hu_base_mem,
                    PartialState.union_callStack_of_left_none (by first | rfl | simp)]
                 exact hva))
        | (rw [PartialState.union_callStack_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.callStack cs
             (by rw [
                    ← hu_PR,
                    ← hu_base_mem,
                    PartialState.union_callStack_of_left_none (by first | rfl | simp)]
                 exact hva))
        | (rw [PartialState.union_callStack_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.callStack cs (by rw [← hu_PR]; exact hva))
    -- (b) Outer disjointness: new witness ⊥ h_R.
    · refine ⟨?_, ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
      · intro r
        by_cases hrbase : r = baseReg
        · rw [hrbase]; right; exact h_R_no_base
        · left
          rw [PartialState.union_regs_of_left_none
              (PartialState.singletonReg_regs_other hrbase)]
          exact PartialState.singletonMem_regs r
      · intro a
        by_cases ha : a = effectiveAddr baseAddr off
        · rw [ha]; right; exact h_R_no_mem_addr
        · left
          rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
          exact PartialState.singletonMem_mem_other ha
      · left
        rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
        exact PartialState.singletonMem_pc
    -- (c) Inner disjointness: singletonReg ⊥ singletonMem.
    · refine ⟨fun r => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
      · right; exact PartialState.singletonMem_regs r
      · left; exact PartialState.singletonReg_mem a
      · left; exact PartialState.singletonReg_pc

/-- `st .byte baseReg off imm`: store byte `(imm & 0xff)` at
    `[baseReg + off]`. Derived from the immediate-store helper. -/
theorem stb_spec
    (baseReg : Reg) (off : Int) (imm : Int)
    (baseAddr oldByteVal : Nat) (pc : Nat) :
    cuTripleWithinMem 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.st .byte baseReg off imm))
      ((baseReg ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr off ↦ₘ oldByteVal))
      ((baseReg ↦ᵣ baseAddr) **
        (effectiveAddr baseAddr off ↦ₘ (toU64 imm % 256)))
      (fun rt => rt.containsWritable (effectiveAddr baseAddr off) 1 = true) :=
  cuTripleWithinMem_store_imm_byte_via_reg_addr baseReg off
    baseAddr oldByteVal (toU64 imm % 256) pc (.st .byte baseReg off imm)
    (Nat.mod_lt _ (by decide : (0 : Nat) < 256))
    (fun _ hbase hreg => by
      simp only [step, hbase, Width.bytes, if_pos hreg, Memory.writeByWidth])


end SVM.SBPF
