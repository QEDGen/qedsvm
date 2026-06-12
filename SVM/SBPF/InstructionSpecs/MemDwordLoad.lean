import SVM.SBPF.InstructionSpecs.MemByte
import SVM.SBPF.SegAggregation

namespace SVM.SBPF

open Memory

/-! ## Memory loads — dword width

`ldxdw` reads 8 consecutive bytes (little-endian) into a register.
The precondition owns the destination register, the source register
(base address), and a `memU64Is` claim over the 8 bytes. The post
writes the assembled u64 to `dst` and leaves memory + src unchanged.

Region requirement: `containsRange addr 8`.

The proof's heavy lifting (4-level destructure for the 3 atoms + R,
plus 8 byte-projection lemmas through the union chain) is structurally
identical to `ldxb_spec`'s helper, just scaled to 8 bytes. The
key new piece is `readU64_eq_of_bytes_match` for step discharge. -/

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
      (fun rt => rt.containsRange (effectiveAddr baseAddr off) 8 = true) := by
  intro R hRfree fetch hcr s hPR hpc hex hbud h_region
  -- Destructure the four-level partial-state split.
  obtain ⟨hp, hcompat, h_P, h_R, hd_PR, hu_PR, h_P_sat, h_R_sat⟩ := hPR
  obtain ⟨h_dst, h_SM, hd_dst_SM, hu_dst_SM, h_dst_pred, h_SM_sat⟩ := h_P_sat
  obtain ⟨h_src, h_mem, hd_src_mem, hu_src_mem, h_src_pred, h_mem_pred⟩ := h_SM_sat
  rw [h_src_pred] at hu_src_mem hd_src_mem
  rw [h_mem_pred] at hu_src_mem hd_src_mem
  rw [h_dst_pred] at hu_dst_SM hd_dst_SM
  clear h_src_pred h_mem_pred h_dst_pred h_src h_mem h_dst
  have hcr_regs := hcompat.regs
  have hcm_mem := hcompat.mem
  -- dst ≠ src from inner disjointness (matches ldxb's pattern).
  have hne_dst_src : dst ≠ src := by
    have hd_dst_SM_regs := hd_dst_SM.regs
    intro habs
    rcases hd_dst_SM_regs dst with hl | hr
    · rw [PartialState.singletonReg_regs_self] at hl; nomatch hl
    · rw [← hu_src_mem] at hr
      have : ((PartialState.singletonReg src baseAddr).union
              (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v)).regs dst
              = some baseAddr := by
        rw [habs]
        exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
      rw [this] at hr; nomatch hr
  -- ===== Climb-up to extract reg + 8 mem byte values =====
  have h_SM_regs_src : h_SM.regs src = some baseAddr := by
    rw [← hu_src_mem]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  -- 8 byte extractions at h_SM level (similar shape, varying offsets).
  have h_SM_mem_0 :
      h_SM.mem (effectiveAddr baseAddr off) = some (v % 256) := by
    rw [← hu_src_mem,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact PartialState.singletonMemU64_mem_0 _ _
  have h_SM_mem_1 :
      h_SM.mem (effectiveAddr baseAddr off + 1) = some (v / 0x100 % 256) := by
    rw [← hu_src_mem,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact PartialState.singletonMemU64_mem_1 _ _
  have h_SM_mem_2 :
      h_SM.mem (effectiveAddr baseAddr off + 2) = some (v / 0x10000 % 256) := by
    rw [← hu_src_mem,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact PartialState.singletonMemU64_mem_2 _ _
  have h_SM_mem_3 :
      h_SM.mem (effectiveAddr baseAddr off + 3) = some (v / 0x1000000 % 256) := by
    rw [← hu_src_mem,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact PartialState.singletonMemU64_mem_3 _ _
  have h_SM_mem_4 :
      h_SM.mem (effectiveAddr baseAddr off + 4) = some (v / 0x100000000 % 256) := by
    rw [← hu_src_mem,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact PartialState.singletonMemU64_mem_4 _ _
  have h_SM_mem_5 :
      h_SM.mem (effectiveAddr baseAddr off + 5) = some (v / 0x10000000000 % 256) := by
    rw [← hu_src_mem,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact PartialState.singletonMemU64_mem_5 _ _
  have h_SM_mem_6 :
      h_SM.mem (effectiveAddr baseAddr off + 6) = some (v / 0x1000000000000 % 256) := by
    rw [← hu_src_mem,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact PartialState.singletonMemU64_mem_6 _ _
  have h_SM_mem_7 :
      h_SM.mem (effectiveAddr baseAddr off + 7) = some (v / 0x100000000000000 % 256) := by
    rw [← hu_src_mem,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact PartialState.singletonMemU64_mem_7 _ _
  -- Climb to h_P (dst-singleton has no mem and src ≠ dst so regs lookup fall-through is straightforward).
  have h_P_regs_dst : h_P.regs dst = some vOldDst := by
    rw [← hu_dst_SM]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_regs_src : h_P.regs src = some baseAddr := by
    rw [← hu_dst_SM,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other hne_dst_src.symm)]
    exact h_SM_regs_src
  -- 8 byte extractions at h_P level (peel singletonReg dst _ which has no mem).
  have h_P_mem (i : Nat) (hi : i < 8) (val : Nat)
      (h_SM_at : h_SM.mem (effectiveAddr baseAddr off + i) = some val) :
      h_P.mem (effectiveAddr baseAddr off + i) = some val := by
    rw [← hu_dst_SM,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact h_SM_at
  have h_P_mem_0 :
      h_P.mem (effectiveAddr baseAddr off) = some (v % 256) := by
    have := h_P_mem 0 (by omega) _ h_SM_mem_0
    simpa using this
  have h_P_mem_1 :=
    h_P_mem 1 (by omega) _ h_SM_mem_1
  have h_P_mem_2 :=
    h_P_mem 2 (by omega) _ h_SM_mem_2
  have h_P_mem_3 :=
    h_P_mem 3 (by omega) _ h_SM_mem_3
  have h_P_mem_4 :=
    h_P_mem 4 (by omega) _ h_SM_mem_4
  have h_P_mem_5 :=
    h_P_mem 5 (by omega) _ h_SM_mem_5
  have h_P_mem_6 :=
    h_P_mem 6 (by omega) _ h_SM_mem_6
  have h_P_mem_7 :=
    h_P_mem 7 (by omega) _ h_SM_mem_7
  -- Climb to hp.
  have hp_regs_dst : hp.regs dst = some vOldDst := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_dst
  have hp_regs_src : hp.regs src = some baseAddr := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_src
  have hp_mem (i_addr : Nat) (val : Nat)
      (h_P_at : h_P.mem i_addr = some val) :
      hp.mem i_addr = some val := by
    rw [← hu_PR]; exact PartialState.union_mem_of_left_some h_P_at
  have hs_regs_src : s.regs.get src = baseAddr := hcr_regs src baseAddr hp_regs_src
  -- Extract s.mem values.
  have hs_mem_0 : s.mem (effectiveAddr baseAddr off) = v % 256 :=
    hcm_mem _ _ (hp_mem _ _ h_P_mem_0)
  have hs_mem_1 : s.mem (effectiveAddr baseAddr off + 1) = v / 0x100 % 256 :=
    hcm_mem _ _ (hp_mem _ _ h_P_mem_1)
  have hs_mem_2 : s.mem (effectiveAddr baseAddr off + 2) = v / 0x10000 % 256 :=
    hcm_mem _ _ (hp_mem _ _ h_P_mem_2)
  have hs_mem_3 : s.mem (effectiveAddr baseAddr off + 3) = v / 0x1000000 % 256 :=
    hcm_mem _ _ (hp_mem _ _ h_P_mem_3)
  have hs_mem_4 : s.mem (effectiveAddr baseAddr off + 4) = v / 0x100000000 % 256 :=
    hcm_mem _ _ (hp_mem _ _ h_P_mem_4)
  have hs_mem_5 : s.mem (effectiveAddr baseAddr off + 5) = v / 0x10000000000 % 256 :=
    hcm_mem _ _ (hp_mem _ _ h_P_mem_5)
  have hs_mem_6 : s.mem (effectiveAddr baseAddr off + 6) = v / 0x1000000000000 % 256 :=
    hcm_mem _ _ (hp_mem _ _ h_P_mem_6)
  have hs_mem_7 : s.mem (effectiveAddr baseAddr off + 7) = v / 0x100000000000000 % 256 :=
    hcm_mem _ _ (hp_mem _ _ h_P_mem_7)
  -- ===== Step: readU64 yields v via the assembly helper =====
  have h_readU64 : Memory.readU64 s.mem (effectiveAddr baseAddr off) = v :=
    readU64_eq_of_bytes_match hv hs_mem_0 hs_mem_1 hs_mem_2 hs_mem_3
      hs_mem_4 hs_mem_5 hs_mem_6 hs_mem_7
  have hfetch : fetch s.pc = some (.ldx .dword dst src off) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hexec : executeFn fetch s 1 =
      chargeCu { s with regs := s.regs.set dst v, pc := s.pc + 1 } := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch,
        executeFn_zero]
    simp only [step, hs_regs_src, Width.bytes, if_pos h_region,
               Memory.readByWidth, h_readU64]
  -- ===== h_R cannot own dst, src, or any of the 8 mem bytes =====
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
  have h_R_no_mem (a val : Nat) (h_P_at : h_P.mem a = some val) :
      h_R.mem a = none := by
    rcases hd_PR_mem a with hl | hr
    · rw [h_P_at] at hl; nomatch hl
    · exact hr
  have h_R_no_pc : h_R.pc = none := hRfree _ h_R_sat
  -- ===== Build the post =====
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_, ?_⟩
  · rw [hexec]; show s.pc + 1 = pc + 1; rw [hpc]
  · rw [hexec]; exact hex
  · rw [hexec]; show s.cuConsumed + 1 ≤ s.cuConsumed + 1 + 0; omega
  · rw [hexec]
    refine ⟨_, ?_,
            (PartialState.singletonReg dst v).union
              ((PartialState.singletonReg src baseAddr).union
                (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v)),
            h_R, ?_, rfl,
            ⟨PartialState.singletonReg dst v,
             (PartialState.singletonReg src baseAddr).union
              (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v),
             ?_, rfl, rfl,
             ⟨PartialState.singletonReg src baseAddr,
              PartialState.singletonMemU64 (effectiveAddr baseAddr off) v,
              hd_src_mem, rfl, rfl, rfl⟩⟩,
            h_R_sat⟩
    -- (a) Compat: regs, mem (9-case), pc.
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      -- regs:
      · intro r vr hvr
        show (s.regs.set dst v).get r = vr
        by_cases hrdst : r = dst
        · rw [hrdst] at hvr
          have h_inner :
              ((PartialState.singletonReg dst v).union
                ((PartialState.singletonReg src baseAddr).union
                  (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v))).regs dst
              = some v :=
            PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
          rw [PartialState.union_regs_of_left_some h_inner] at hvr
          have : vr = v := (Option.some.inj hvr).symm
          rw [hrdst, this]
          exact RegFile.get_set_self _ _ _ hne
        · rw [RegFile.get_set_diff _ _ _ _ hrdst]
          by_cases hrsrc : r = src
          · rw [hrsrc] at hvr
            have h_inner :
                ((PartialState.singletonReg dst v).union
                  ((PartialState.singletonReg src baseAddr).union
                    (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v))).regs src
                = some baseAddr := by
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hne_dst_src.symm)]
              exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
            rw [PartialState.union_regs_of_left_some h_inner] at hvr
            have : vr = baseAddr := (Option.some.inj hvr).symm
            rw [hrsrc, this]
            exact hcr_regs src baseAddr hp_regs_src
          · have h_outer_h1_none :
                ((PartialState.singletonReg dst v).union
                  ((PartialState.singletonReg src baseAddr).union
                    (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v))).regs r
                = none := by
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrdst)]
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrsrc)]
              exact PartialState.singletonMemU64_regs r
            rw [PartialState.union_regs_of_left_none h_outer_h1_none] at hvr
            apply hcr_regs r vr
            have h_P_none : h_P.regs r = none := by
              rw [← hu_dst_SM]
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrdst)]
              rw [← hu_src_mem]
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrsrc)]
              exact PartialState.singletonMemU64_regs r
            rw [← hu_PR]
            rw [PartialState.union_regs_of_left_none h_P_none]
            exact hvr
      -- mem: in-range (8 cases) or outside (1 case).
      · intro a vm hvm
        show s.mem a = vm
        -- Helper for in-range case at offset `i`: peel through union to singletonMemU64, equate vm.
        -- Outside case: outer-h1 owns nothing at a, fall through to h_R via hp.
        by_cases ha0 : a = effectiveAddr baseAddr off
        · rw [ha0] at hvm ⊢
          have h_inner :
              ((PartialState.singletonReg dst v).union
                ((PartialState.singletonReg src baseAddr).union
                  (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v))).mem
                  (effectiveAddr baseAddr off) = some (v % 256) := by
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            exact PartialState.singletonMemU64_mem_0 _ _
          rw [PartialState.union_mem_of_left_some h_inner] at hvm
          have : vm = v % 256 := (Option.some.inj hvm).symm
          rw [this]; exact hs_mem_0
        · by_cases ha1 : a = effectiveAddr baseAddr off + 1
          · rw [ha1] at hvm ⊢
            have h_inner :
                ((PartialState.singletonReg dst v).union
                  ((PartialState.singletonReg src baseAddr).union
                    (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v))).mem
                    (effectiveAddr baseAddr off + 1) = some (v / 0x100 % 256) := by
              rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
              rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
              exact PartialState.singletonMemU64_mem_1 _ _
            rw [PartialState.union_mem_of_left_some h_inner] at hvm
            have : vm = v / 0x100 % 256 := (Option.some.inj hvm).symm
            rw [this]; exact hs_mem_1
          · by_cases ha2 : a = effectiveAddr baseAddr off + 2
            · rw [ha2] at hvm ⊢
              have h_inner :
                  ((PartialState.singletonReg dst v).union
                    ((PartialState.singletonReg src baseAddr).union
                      (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v))).mem
                      (effectiveAddr baseAddr off + 2) = some (v / 0x10000 % 256) := by
                rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                exact PartialState.singletonMemU64_mem_2 _ _
              rw [PartialState.union_mem_of_left_some h_inner] at hvm
              have : vm = v / 0x10000 % 256 := (Option.some.inj hvm).symm
              rw [this]; exact hs_mem_2
            · by_cases ha3 : a = effectiveAddr baseAddr off + 3
              · rw [ha3] at hvm ⊢
                have h_inner :
                    ((PartialState.singletonReg dst v).union
                      ((PartialState.singletonReg src baseAddr).union
                        (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v))).mem
                        (effectiveAddr baseAddr off + 3) = some (v / 0x1000000 % 256) := by
                  rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                  rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                  exact PartialState.singletonMemU64_mem_3 _ _
                rw [PartialState.union_mem_of_left_some h_inner] at hvm
                have : vm = v / 0x1000000 % 256 := (Option.some.inj hvm).symm
                rw [this]; exact hs_mem_3
              · by_cases ha4 : a = effectiveAddr baseAddr off + 4
                · rw [ha4] at hvm ⊢
                  have h_inner :
                      ((PartialState.singletonReg dst v).union
                        ((PartialState.singletonReg src baseAddr).union
                          (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v))).mem
                          (effectiveAddr baseAddr off + 4) = some (v / 0x100000000 % 256) := by
                    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                    exact PartialState.singletonMemU64_mem_4 _ _
                  rw [PartialState.union_mem_of_left_some h_inner] at hvm
                  have : vm = v / 0x100000000 % 256 := (Option.some.inj hvm).symm
                  rw [this]; exact hs_mem_4
                · by_cases ha5 : a = effectiveAddr baseAddr off + 5
                  · rw [ha5] at hvm ⊢
                    have h_inner :
                        ((PartialState.singletonReg dst v).union
                          ((PartialState.singletonReg src baseAddr).union
                            (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v))).mem
                            (effectiveAddr baseAddr off + 5) = some (v / 0x10000000000 % 256) := by
                      rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                      rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                      exact PartialState.singletonMemU64_mem_5 _ _
                    rw [PartialState.union_mem_of_left_some h_inner] at hvm
                    have : vm = v / 0x10000000000 % 256 := (Option.some.inj hvm).symm
                    rw [this]; exact hs_mem_5
                  · by_cases ha6 : a = effectiveAddr baseAddr off + 6
                    · rw [ha6] at hvm ⊢
                      have h_inner :
                          ((PartialState.singletonReg dst v).union
                            ((PartialState.singletonReg src baseAddr).union
                              (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v))).mem
                              (effectiveAddr baseAddr off + 6) = some (v / 0x1000000000000 % 256) := by
                        rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                        rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                        exact PartialState.singletonMemU64_mem_6 _ _
                      rw [PartialState.union_mem_of_left_some h_inner] at hvm
                      have : vm = v / 0x1000000000000 % 256 := (Option.some.inj hvm).symm
                      rw [this]; exact hs_mem_6
                    · by_cases ha7 : a = effectiveAddr baseAddr off + 7
                      · rw [ha7] at hvm ⊢
                        have h_inner :
                            ((PartialState.singletonReg dst v).union
                              ((PartialState.singletonReg src baseAddr).union
                                (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v))).mem
                                (effectiveAddr baseAddr off + 7) = some (v / 0x100000000000000 % 256) := by
                          rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                          rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                          exact PartialState.singletonMemU64_mem_7 _ _
                        rw [PartialState.union_mem_of_left_some h_inner] at hvm
                        have : vm = v / 0x100000000000000 % 256 := (Option.some.inj hvm).symm
                        rw [this]; exact hs_mem_7
                      · -- outside [addr, addr+8)
                        have h_outer_none :
                            ((PartialState.singletonReg dst v).union
                              ((PartialState.singletonReg src baseAddr).union
                                (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v))).mem a
                            = none := by
                          rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                          rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                          exact PartialState.singletonMemU64_mem_outside _ _ a (by omega)
                        rw [PartialState.union_mem_of_left_none h_outer_none] at hvm
                        apply hcm_mem a vm
                        have h_P_none : h_P.mem a = none := by
                          rw [← hu_dst_SM]
                          rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                          rw [← hu_src_mem]
                          rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                          exact PartialState.singletonMemU64_mem_outside _ _ a (by omega)
                        rw [← hu_PR]
                        rw [PartialState.union_mem_of_left_none h_P_none]
                        exact hvm
      -- pc:
      · intro vp hvp
        have h_outer_pc :
            ((PartialState.singletonReg dst v).union
              ((PartialState.singletonReg src baseAddr).union
                (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v))).pc = none := by
          rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
          rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
          exact PartialState.singletonMemU64_pc
        rw [PartialState.union_pc_of_left_none h_outer_pc] at hvp
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
    -- (b) Outer disjointness: new witness ⊥ h_R.
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
            exact PartialState.singletonMemU64_regs r
      · intro a
        by_cases ha0 : a = effectiveAddr baseAddr off
        · rw [ha0]; right; exact h_R_no_mem _ _ h_P_mem_0
        · by_cases ha1 : a = effectiveAddr baseAddr off + 1
          · rw [ha1]; right; exact h_R_no_mem _ _ h_P_mem_1
          · by_cases ha2 : a = effectiveAddr baseAddr off + 2
            · rw [ha2]; right; exact h_R_no_mem _ _ h_P_mem_2
            · by_cases ha3 : a = effectiveAddr baseAddr off + 3
              · rw [ha3]; right; exact h_R_no_mem _ _ h_P_mem_3
              · by_cases ha4 : a = effectiveAddr baseAddr off + 4
                · rw [ha4]; right; exact h_R_no_mem _ _ h_P_mem_4
                · by_cases ha5 : a = effectiveAddr baseAddr off + 5
                  · rw [ha5]; right; exact h_R_no_mem _ _ h_P_mem_5
                  · by_cases ha6 : a = effectiveAddr baseAddr off + 6
                    · rw [ha6]; right; exact h_R_no_mem _ _ h_P_mem_6
                    · by_cases ha7 : a = effectiveAddr baseAddr off + 7
                      · rw [ha7]; right; exact h_R_no_mem _ _ h_P_mem_7
                      · left
                        rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                        rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                        exact PartialState.singletonMemU64_mem_outside _ _ a (by omega)
      · left
        rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
        rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
        exact PartialState.singletonMemU64_pc
    -- (c) Inner disjointness: singletonReg dst v ⊥ (singletonReg src baseAddr ⊎ singletonMemU64 ...).
    · refine ⟨fun r => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
      · by_cases hrdst : r = dst
        · right
          rw [hrdst,
              PartialState.union_regs_of_left_none
                (PartialState.singletonReg_regs_other hne_dst_src)]
          exact PartialState.singletonMemU64_regs dst
        · left; exact PartialState.singletonReg_regs_other hrdst
      · left; exact PartialState.singletonReg_mem a
      · left; exact PartialState.singletonReg_pc

/-- `ldx .dword r r off`: same-register variant — load 64-bit value at `[r + off]`
    into `r`. Because `step` first reads `r.value` as the base address and only
    then writes the loaded value, the operation is well-defined when dst = src.
    Precondition owns only one register atom (`r ↦ᵣ baseAddr`) plus the 8-byte
    memory claim; the post overwrites `r` with the loaded value. -/
theorem ldxdw_same_spec
    (r : Reg) (off : Int) (baseAddr v : Nat) (pc : Nat)
    (hne : r ≠ .r10) (hv : v < 2 ^ 64) :
    cuTripleWithinMem 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.ldx .dword r r off))
      ((r ↦ᵣ baseAddr) ** (effectiveAddr baseAddr off ↦U64 v))
      ((r ↦ᵣ v) ** (effectiveAddr baseAddr off ↦U64 v))
      (fun rt => rt.containsRange (effectiveAddr baseAddr off) 8 = true) := by
  intro R hRfree fetch hcr s hPR hpc hex hbud h_region
  -- Destructure the three-level partial-state split (2 atoms instead of 3).
  obtain ⟨hp, hcompat, h_P, h_R, hd_PR, hu_PR, h_P_sat, h_R_sat⟩ := hPR
  obtain ⟨h_reg, h_mem, hd_reg_mem, hu_reg_mem, h_reg_pred, h_mem_pred⟩ := h_P_sat
  rw [h_reg_pred] at hu_reg_mem hd_reg_mem
  rw [h_mem_pred] at hu_reg_mem hd_reg_mem
  clear h_reg_pred h_mem_pred h_reg h_mem
  have hcr_regs := hcompat.regs
  have hcm_mem := hcompat.mem
  -- ===== Extract reg + 8 mem byte values at h_P level =====
  have h_P_regs_r : h_P.regs r = some baseAddr := by
    rw [← hu_reg_mem]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  -- 8 byte extractions at h_P level (peel singletonReg, then read singletonMemU64).
  have h_P_mem_0 :
      h_P.mem (effectiveAddr baseAddr off) = some (v % 256) := by
    rw [← hu_reg_mem,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact PartialState.singletonMemU64_mem_0 _ _
  have h_P_mem_1 :
      h_P.mem (effectiveAddr baseAddr off + 1) = some (v / 0x100 % 256) := by
    rw [← hu_reg_mem,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact PartialState.singletonMemU64_mem_1 _ _
  have h_P_mem_2 :
      h_P.mem (effectiveAddr baseAddr off + 2) = some (v / 0x10000 % 256) := by
    rw [← hu_reg_mem,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact PartialState.singletonMemU64_mem_2 _ _
  have h_P_mem_3 :
      h_P.mem (effectiveAddr baseAddr off + 3) = some (v / 0x1000000 % 256) := by
    rw [← hu_reg_mem,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact PartialState.singletonMemU64_mem_3 _ _
  have h_P_mem_4 :
      h_P.mem (effectiveAddr baseAddr off + 4) = some (v / 0x100000000 % 256) := by
    rw [← hu_reg_mem,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact PartialState.singletonMemU64_mem_4 _ _
  have h_P_mem_5 :
      h_P.mem (effectiveAddr baseAddr off + 5) = some (v / 0x10000000000 % 256) := by
    rw [← hu_reg_mem,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact PartialState.singletonMemU64_mem_5 _ _
  have h_P_mem_6 :
      h_P.mem (effectiveAddr baseAddr off + 6) = some (v / 0x1000000000000 % 256) := by
    rw [← hu_reg_mem,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact PartialState.singletonMemU64_mem_6 _ _
  have h_P_mem_7 :
      h_P.mem (effectiveAddr baseAddr off + 7) = some (v / 0x100000000000000 % 256) := by
    rw [← hu_reg_mem,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact PartialState.singletonMemU64_mem_7 _ _
  -- Climb to hp.
  have hp_regs_r : hp.regs r = some baseAddr := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r
  have hp_mem (i_addr : Nat) (val : Nat)
      (h_P_at : h_P.mem i_addr = some val) :
      hp.mem i_addr = some val := by
    rw [← hu_PR]; exact PartialState.union_mem_of_left_some h_P_at
  have hs_regs_r : s.regs.get r = baseAddr := hcr_regs r baseAddr hp_regs_r
  -- Extract s.mem values.
  have hs_mem_0 : s.mem (effectiveAddr baseAddr off) = v % 256 :=
    hcm_mem _ _ (hp_mem _ _ h_P_mem_0)
  have hs_mem_1 : s.mem (effectiveAddr baseAddr off + 1) = v / 0x100 % 256 :=
    hcm_mem _ _ (hp_mem _ _ h_P_mem_1)
  have hs_mem_2 : s.mem (effectiveAddr baseAddr off + 2) = v / 0x10000 % 256 :=
    hcm_mem _ _ (hp_mem _ _ h_P_mem_2)
  have hs_mem_3 : s.mem (effectiveAddr baseAddr off + 3) = v / 0x1000000 % 256 :=
    hcm_mem _ _ (hp_mem _ _ h_P_mem_3)
  have hs_mem_4 : s.mem (effectiveAddr baseAddr off + 4) = v / 0x100000000 % 256 :=
    hcm_mem _ _ (hp_mem _ _ h_P_mem_4)
  have hs_mem_5 : s.mem (effectiveAddr baseAddr off + 5) = v / 0x10000000000 % 256 :=
    hcm_mem _ _ (hp_mem _ _ h_P_mem_5)
  have hs_mem_6 : s.mem (effectiveAddr baseAddr off + 6) = v / 0x1000000000000 % 256 :=
    hcm_mem _ _ (hp_mem _ _ h_P_mem_6)
  have hs_mem_7 : s.mem (effectiveAddr baseAddr off + 7) = v / 0x100000000000000 % 256 :=
    hcm_mem _ _ (hp_mem _ _ h_P_mem_7)
  -- ===== Step: readU64 yields v via the assembly helper =====
  have h_readU64 : Memory.readU64 s.mem (effectiveAddr baseAddr off) = v :=
    readU64_eq_of_bytes_match hv hs_mem_0 hs_mem_1 hs_mem_2 hs_mem_3
      hs_mem_4 hs_mem_5 hs_mem_6 hs_mem_7
  have hfetch : fetch s.pc = some (.ldx .dword r r off) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hexec : executeFn fetch s 1 =
      chargeCu { s with regs := s.regs.set r v, pc := s.pc + 1 } := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch,
        executeFn_zero]
    simp only [step, hs_regs_r, Width.bytes, if_pos h_region,
               Memory.readByWidth, h_readU64]
  -- ===== h_R cannot own r or any of the 8 mem bytes =====
  have hd_PR_regs := hd_PR.regs
  have hd_PR_mem := hd_PR.mem
  have h_R_no_r : h_R.regs r = none := by
    rcases hd_PR_regs r with hl | hr
    · rw [h_P_regs_r] at hl; nomatch hl
    · exact hr
  have h_R_no_mem (a val : Nat) (h_P_at : h_P.mem a = some val) :
      h_R.mem a = none := by
    rcases hd_PR_mem a with hl | hr
    · rw [h_P_at] at hl; nomatch hl
    · exact hr
  have h_R_no_pc : h_R.pc = none := hRfree _ h_R_sat
  -- ===== Build the post =====
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_, ?_⟩
  · rw [hexec]; show s.pc + 1 = pc + 1; rw [hpc]
  · rw [hexec]; exact hex
  · rw [hexec]; show s.cuConsumed + 1 ≤ s.cuConsumed + 1 + 0; omega
  · rw [hexec]
    refine ⟨_, ?_,
            (PartialState.singletonReg r v).union
              (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v),
            h_R, ?_, rfl,
            ⟨PartialState.singletonReg r v,
             PartialState.singletonMemU64 (effectiveAddr baseAddr off) v,
             ?_, rfl, rfl, rfl⟩,
            h_R_sat⟩
    -- (a) Compat: regs, mem (9-case), pc, returnData, callStack.
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      -- regs:
      · intro rr vr hvr
        show (s.regs.set r v).get rr = vr
        by_cases hrr : rr = r
        · rw [hrr] at hvr
          have h_inner :
              ((PartialState.singletonReg r v).union
                (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v)).regs r
              = some v :=
            PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
          rw [PartialState.union_regs_of_left_some h_inner] at hvr
          have : vr = v := (Option.some.inj hvr).symm
          rw [hrr, this]
          exact RegFile.get_set_self _ _ _ hne
        · rw [RegFile.get_set_diff _ _ _ _ hrr]
          have h_outer_h1_none :
              ((PartialState.singletonReg r v).union
                (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v)).regs rr
              = none := by
            rw [PartialState.union_regs_of_left_none
                (PartialState.singletonReg_regs_other hrr)]
            exact PartialState.singletonMemU64_regs rr
          rw [PartialState.union_regs_of_left_none h_outer_h1_none] at hvr
          apply hcr_regs rr vr
          have h_P_none : h_P.regs rr = none := by
            rw [← hu_reg_mem]
            rw [PartialState.union_regs_of_left_none
                (PartialState.singletonReg_regs_other hrr)]
            exact PartialState.singletonMemU64_regs rr
          rw [← hu_PR]
          rw [PartialState.union_regs_of_left_none h_P_none]
          exact hvr
      -- mem: in-range (8 cases) or outside (1 case).
      · intro a vm hvm
        show s.mem a = vm
        by_cases ha0 : a = effectiveAddr baseAddr off
        · rw [ha0] at hvm ⊢
          have h_inner :
              ((PartialState.singletonReg r v).union
                (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v)).mem
                  (effectiveAddr baseAddr off) = some (v % 256) := by
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            exact PartialState.singletonMemU64_mem_0 _ _
          rw [PartialState.union_mem_of_left_some h_inner] at hvm
          have : vm = v % 256 := (Option.some.inj hvm).symm
          rw [this]; exact hs_mem_0
        · by_cases ha1 : a = effectiveAddr baseAddr off + 1
          · rw [ha1] at hvm ⊢
            have h_inner :
                ((PartialState.singletonReg r v).union
                  (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v)).mem
                    (effectiveAddr baseAddr off + 1) = some (v / 0x100 % 256) := by
              rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
              exact PartialState.singletonMemU64_mem_1 _ _
            rw [PartialState.union_mem_of_left_some h_inner] at hvm
            have : vm = v / 0x100 % 256 := (Option.some.inj hvm).symm
            rw [this]; exact hs_mem_1
          · by_cases ha2 : a = effectiveAddr baseAddr off + 2
            · rw [ha2] at hvm ⊢
              have h_inner :
                  ((PartialState.singletonReg r v).union
                    (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v)).mem
                      (effectiveAddr baseAddr off + 2) = some (v / 0x10000 % 256) := by
                rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                exact PartialState.singletonMemU64_mem_2 _ _
              rw [PartialState.union_mem_of_left_some h_inner] at hvm
              have : vm = v / 0x10000 % 256 := (Option.some.inj hvm).symm
              rw [this]; exact hs_mem_2
            · by_cases ha3 : a = effectiveAddr baseAddr off + 3
              · rw [ha3] at hvm ⊢
                have h_inner :
                    ((PartialState.singletonReg r v).union
                      (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v)).mem
                        (effectiveAddr baseAddr off + 3) = some (v / 0x1000000 % 256) := by
                  rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                  exact PartialState.singletonMemU64_mem_3 _ _
                rw [PartialState.union_mem_of_left_some h_inner] at hvm
                have : vm = v / 0x1000000 % 256 := (Option.some.inj hvm).symm
                rw [this]; exact hs_mem_3
              · by_cases ha4 : a = effectiveAddr baseAddr off + 4
                · rw [ha4] at hvm ⊢
                  have h_inner :
                      ((PartialState.singletonReg r v).union
                        (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v)).mem
                          (effectiveAddr baseAddr off + 4) = some (v / 0x100000000 % 256) := by
                    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                    exact PartialState.singletonMemU64_mem_4 _ _
                  rw [PartialState.union_mem_of_left_some h_inner] at hvm
                  have : vm = v / 0x100000000 % 256 := (Option.some.inj hvm).symm
                  rw [this]; exact hs_mem_4
                · by_cases ha5 : a = effectiveAddr baseAddr off + 5
                  · rw [ha5] at hvm ⊢
                    have h_inner :
                        ((PartialState.singletonReg r v).union
                          (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v)).mem
                            (effectiveAddr baseAddr off + 5) = some (v / 0x10000000000 % 256) := by
                      rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                      exact PartialState.singletonMemU64_mem_5 _ _
                    rw [PartialState.union_mem_of_left_some h_inner] at hvm
                    have : vm = v / 0x10000000000 % 256 := (Option.some.inj hvm).symm
                    rw [this]; exact hs_mem_5
                  · by_cases ha6 : a = effectiveAddr baseAddr off + 6
                    · rw [ha6] at hvm ⊢
                      have h_inner :
                          ((PartialState.singletonReg r v).union
                            (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v)).mem
                              (effectiveAddr baseAddr off + 6) = some (v / 0x1000000000000 % 256) := by
                        rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                        exact PartialState.singletonMemU64_mem_6 _ _
                      rw [PartialState.union_mem_of_left_some h_inner] at hvm
                      have : vm = v / 0x1000000000000 % 256 := (Option.some.inj hvm).symm
                      rw [this]; exact hs_mem_6
                    · by_cases ha7 : a = effectiveAddr baseAddr off + 7
                      · rw [ha7] at hvm ⊢
                        have h_inner :
                            ((PartialState.singletonReg r v).union
                              (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v)).mem
                                (effectiveAddr baseAddr off + 7) = some (v / 0x100000000000000 % 256) := by
                          rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                          exact PartialState.singletonMemU64_mem_7 _ _
                        rw [PartialState.union_mem_of_left_some h_inner] at hvm
                        have : vm = v / 0x100000000000000 % 256 := (Option.some.inj hvm).symm
                        rw [this]; exact hs_mem_7
                      · -- outside [addr, addr+8)
                        have h_outer_none :
                            ((PartialState.singletonReg r v).union
                              (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v)).mem a
                            = none := by
                          rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                          exact PartialState.singletonMemU64_mem_outside _ _ a (by omega)
                        rw [PartialState.union_mem_of_left_none h_outer_none] at hvm
                        apply hcm_mem a vm
                        have h_P_none : h_P.mem a = none := by
                          rw [← hu_reg_mem]
                          rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                          exact PartialState.singletonMemU64_mem_outside _ _ a (by omega)
                        rw [← hu_PR]
                        rw [PartialState.union_mem_of_left_none h_P_none]
                        exact hvm
      -- pc:
      · intro vp hvp
        have h_outer_pc :
            ((PartialState.singletonReg r v).union
              (PartialState.singletonMemU64 (effectiveAddr baseAddr off) v)).pc = none := by
          rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
          exact PartialState.singletonMemU64_pc
        rw [PartialState.union_pc_of_left_none h_outer_pc] at hvp
        rw [h_R_no_pc] at hvp
        nomatch hvp
      · intro rd hva
        first
        | exact hcompat.returnData rd hva
        | (rw [PartialState.union_returnData_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.returnData rd
             (by rw [
                    ← hu_PR,
                    ← hu_reg_mem,
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
                    ← hu_reg_mem,
                    PartialState.union_callStack_of_left_none (by first | rfl | simp)]
                 exact hva))
        | (rw [PartialState.union_callStack_of_left_none (by first | rfl | simp)] at hva
           exact hcompat.callStack cs (by rw [← hu_PR]; exact hva))
    -- (b) Outer disjointness: new witness ⊥ h_R.
    · refine ⟨?_, ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
      · intro rr
        by_cases hrr : rr = r
        · rw [hrr]; right; exact h_R_no_r
        · left
          rw [PartialState.union_regs_of_left_none
              (PartialState.singletonReg_regs_other hrr)]
          exact PartialState.singletonMemU64_regs rr
      · intro a
        by_cases ha0 : a = effectiveAddr baseAddr off
        · rw [ha0]; right; exact h_R_no_mem _ _ h_P_mem_0
        · by_cases ha1 : a = effectiveAddr baseAddr off + 1
          · rw [ha1]; right; exact h_R_no_mem _ _ h_P_mem_1
          · by_cases ha2 : a = effectiveAddr baseAddr off + 2
            · rw [ha2]; right; exact h_R_no_mem _ _ h_P_mem_2
            · by_cases ha3 : a = effectiveAddr baseAddr off + 3
              · rw [ha3]; right; exact h_R_no_mem _ _ h_P_mem_3
              · by_cases ha4 : a = effectiveAddr baseAddr off + 4
                · rw [ha4]; right; exact h_R_no_mem _ _ h_P_mem_4
                · by_cases ha5 : a = effectiveAddr baseAddr off + 5
                  · rw [ha5]; right; exact h_R_no_mem _ _ h_P_mem_5
                  · by_cases ha6 : a = effectiveAddr baseAddr off + 6
                    · rw [ha6]; right; exact h_R_no_mem _ _ h_P_mem_6
                    · by_cases ha7 : a = effectiveAddr baseAddr off + 7
                      · rw [ha7]; right; exact h_R_no_mem _ _ h_P_mem_7
                      · left
                        rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                        exact PartialState.singletonMemU64_mem_outside _ _ a (by omega)
      · left
        rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
        exact PartialState.singletonMemU64_pc
    -- (c) Inner disjointness: singletonReg r v ⊥ singletonMemU64 ...
    --     Same shape as hd_reg_mem (which witnesses disjointness for the precondition's
    --     singletonReg r baseAddr ⊎ singletonMemU64 ...). Reg side: singletonMemU64 has no
    --     regs, so always Or.inl. Mem side: singletonReg has no mem, so always Or.inl.
    · refine ⟨fun rr => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
      · right; exact PartialState.singletonMemU64_regs rr
      · left; exact PartialState.singletonReg_mem a
      · left; exact PartialState.singletonReg_pc

/-! ## Dword load over BYTE-granular memory (qedlift hot regions)

When a region is accessed at MIXED widths (e.g. pinocchio's entrypoint
reads `input[0]` as a byte and `input[0..8)` as a dword), qedlift keeps
it at byte granularity — one `↦ₘ` atom per byte — so the sepConj stays
satisfiable (soundness audit H8 Phase B,
`docs/QEDLIFT_ALIASING_DESIGN.md`). The dword load's spec is
`ldxdw_spec` reshaped through `byte_atoms_eq_memU64Is`: the pre/post
own the 8 byte atoms, and the loaded value is their little-endian
Horner combination. -/

set_option maxHeartbeats 800000 in
/-- `ldx .dword dst src off` over eight byte atoms `[addr, addr+8)`.
    The loaded value is `b0 + 256·(b1 + 256·(… + 256·b7))`. -/
theorem ldxdw_bytes_spec
    (dst src : Reg) (off : Int)
    (vOldDst baseAddr b0 b1 b2 b3 b4 b5 b6 b7 : Nat) (pc : Nat)
    (hne : dst ≠ .r10)
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256)
    (hb4 : b4 < 256) (hb5 : b5 < 256) (hb6 : b6 < 256) (hb7 : b7 < 256) :
    cuTripleWithinMem 1 0 pc (pc + 1)
      (CodeReq.singleton pc (.ldx .dword dst src off))
      ((dst ↦ᵣ vOldDst) ** (src ↦ᵣ baseAddr) **
        ((effectiveAddr baseAddr off ↦ₘ b0) **
         (effectiveAddr baseAddr off + 1 ↦ₘ b1) **
         (effectiveAddr baseAddr off + 2 ↦ₘ b2) **
         (effectiveAddr baseAddr off + 3 ↦ₘ b3) **
         (effectiveAddr baseAddr off + 4 ↦ₘ b4) **
         (effectiveAddr baseAddr off + 5 ↦ₘ b5) **
         (effectiveAddr baseAddr off + 6 ↦ₘ b6) **
         (effectiveAddr baseAddr off + 7 ↦ₘ b7)))
      ((dst ↦ᵣ b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 *
          (b4 + 256 * (b5 + 256 * (b6 + 256 * b7))))))) **
        (src ↦ᵣ baseAddr) **
        ((effectiveAddr baseAddr off ↦ₘ b0) **
         (effectiveAddr baseAddr off + 1 ↦ₘ b1) **
         (effectiveAddr baseAddr off + 2 ↦ₘ b2) **
         (effectiveAddr baseAddr off + 3 ↦ₘ b3) **
         (effectiveAddr baseAddr off + 4 ↦ₘ b4) **
         (effectiveAddr baseAddr off + 5 ↦ₘ b5) **
         (effectiveAddr baseAddr off + 6 ↦ₘ b6) **
         (effectiveAddr baseAddr off + 7 ↦ₘ b7)))
      (fun rt => rt.containsRange (effectiveAddr baseAddr off) 8 = true) := by
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
