import SVM.SBPF.InstructionSpecs.MemWord

namespace SVM.SBPF

open Memory

/-! ## Memory stores — dword width

`stxdw` writes 8 consecutive bytes (little-endian decomposition of
the value register `valReg`) to memory at `[baseReg + off]`. The
precondition owns the two registers and an existing `memU64Is` claim
with some `oldV`; the post replaces that with `memU64Is addr vSrc`.

Region requirement: `containsWritable addr 8`.

Note: no `vSrc < 2^64` hypothesis is needed because `writeU64` masks
to `% 256` at each byte slot, and `256 | 2^64`, so `(vSrc % 2^64) / 256^i % 256
= vSrc / 256^i % 256` for `i ∈ 0..7` (omega discharges). -/

/-- `stx .dword baseReg off valReg`: write valReg's 64 bits little-endian
    at `[baseReg + off]`. -/
theorem stxdw_spec
    (baseReg valReg : Reg) (off : Int)
    (baseAddr vSrc oldV : Nat) (pc : Nat) :
    cuTripleWithinMem 1 pc (pc + 1)
      (CodeReq.singleton pc (.stx .dword baseReg off valReg))
      ((baseReg ↦ᵣ baseAddr) ** (valReg ↦ᵣ vSrc) **
        (effectiveAddr baseAddr off ↦U64 oldV))
      ((baseReg ↦ᵣ baseAddr) ** (valReg ↦ᵣ vSrc) **
        (effectiveAddr baseAddr off ↦U64 vSrc))
      (fun rt => rt.containsWritable (effectiveAddr baseAddr off) 8 = true) := by
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
              (PartialState.singletonMemU64 (effectiveAddr baseAddr off) oldV)).regs baseReg
              = some vSrc := by
        rw [habs]
        exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
      rw [this] at hr; nomatch hr
  have h_VM_regs_val : h_VM.regs valReg = some vSrc := by
    rw [← hu_val_mem]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  -- 8 byte projection facts at h_VM, h_P, hp levels (mirror of ldxdw).
  have h_VM_mem_i (i_addr : Nat) (val : Nat)
      (h_atom : (PartialState.singletonMemU64 (effectiveAddr baseAddr off) oldV).mem i_addr
                = some val) :
      h_VM.mem i_addr = some val := by
    rw [← hu_val_mem,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact h_atom
  have h_P_mem_i (i_addr : Nat) (val : Nat)
      (h_atom : h_VM.mem i_addr = some val) :
      h_P.mem i_addr = some val := by
    rw [← hu_base_VM,
        PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    exact h_atom
  have hp_mem_i (i_addr : Nat) (val : Nat) (h_atom : h_P.mem i_addr = some val) :
      hp.mem i_addr = some val := by
    rw [← hu_PR]; exact PartialState.union_mem_of_left_some h_atom
  -- Climb to extract baseAddr and vSrc through hp.
  have h_P_regs_base : h_P.regs baseReg = some baseAddr := by
    rw [← hu_base_VM]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_regs_val : h_P.regs valReg = some vSrc := by
    rw [← hu_base_VM]
    rw [PartialState.union_regs_of_left_none
        (PartialState.singletonReg_regs_other hne_base_val.symm)]
    exact h_VM_regs_val
  have hp_regs_base : hp.regs baseReg = some baseAddr := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_base
  have hp_regs_val : hp.regs valReg = some vSrc := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_val
  have hs_regs_base : s.regs.get baseReg = baseAddr :=
    hcr_regs baseReg baseAddr hp_regs_base
  have hs_regs_val : s.regs.get valReg = vSrc := hcr_regs valReg vSrc hp_regs_val
  have hfetch : fetch s.pc = some (.stx .dword baseReg off valReg) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  -- The step writes (vSrc % 2^64) via writeU64.
  have hexec : executeFn fetch s 1 =
      { s with mem := Memory.writeU64 s.mem (effectiveAddr baseAddr off) (vSrc % 2 ^ 64),
               pc := s.pc + 1 } := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex hfetch,
        executeFn_zero]
    simp only [step, hs_regs_base, Width.bytes, if_pos h_region,
               Memory.writeByWidth, hs_regs_val]
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
  have h_R_no_mem_at (a val : Nat) (h_P_at : h_P.mem a = some val) :
      h_R.mem a = none := by
    rcases hd_PR_mem a with hl | hr
    · rw [h_P_at] at hl; nomatch hl
    · exact hr
  have h_R_no_pc : h_R.pc = none := hRfree _ h_R_sat
  refine ⟨1, Nat.le_refl 1, ?_, ?_, ?_⟩
  · rw [hexec]; show s.pc + 1 = pc + 1; rw [hpc]
  · rw [hexec]; exact hex
  · rw [hexec]
    refine ⟨_, ?_,
            (PartialState.singletonReg baseReg baseAddr).union
              ((PartialState.singletonReg valReg vSrc).union
                (PartialState.singletonMemU64 (effectiveAddr baseAddr off) vSrc)),
            h_R, ?_, rfl,
            ⟨PartialState.singletonReg baseReg baseAddr,
             (PartialState.singletonReg valReg vSrc).union
              (PartialState.singletonMemU64 (effectiveAddr baseAddr off) vSrc),
             ?_, rfl, rfl,
             ⟨PartialState.singletonReg valReg vSrc,
              PartialState.singletonMemU64 (effectiveAddr baseAddr off) vSrc,
              ?_, rfl, rfl, rfl⟩⟩,
            h_R_sat⟩
    -- (a) Compat.
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      -- regs: unchanged by stxdw (only mem changes).
      · intro r vr hvr
        show s.regs.get r = vr
        by_cases hrbase : r = baseReg
        · rw [hrbase] at hvr
          have h_inner :
              ((PartialState.singletonReg baseReg baseAddr).union
                ((PartialState.singletonReg valReg vSrc).union
                  (PartialState.singletonMemU64 (effectiveAddr baseAddr off) vSrc))).regs baseReg
              = some baseAddr :=
            PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
          rw [PartialState.union_regs_of_left_some h_inner] at hvr
          have : vr = baseAddr := (Option.some.inj hvr).symm
          rw [hrbase, this]; exact hs_regs_base
        · by_cases hrval : r = valReg
          · rw [hrval] at hvr
            have h_inner :
                ((PartialState.singletonReg baseReg baseAddr).union
                  ((PartialState.singletonReg valReg vSrc).union
                    (PartialState.singletonMemU64 (effectiveAddr baseAddr off) vSrc))).regs valReg
                = some vSrc := by
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hne_base_val.symm)]
              exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
            rw [PartialState.union_regs_of_left_some h_inner] at hvr
            have : vr = vSrc := (Option.some.inj hvr).symm
            rw [hrval, this]; exact hs_regs_val
          · have h_outer_h1_none :
                ((PartialState.singletonReg baseReg baseAddr).union
                  ((PartialState.singletonReg valReg vSrc).union
                    (PartialState.singletonMemU64 (effectiveAddr baseAddr off) vSrc))).regs r
                = none := by
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrbase)]
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrval)]
              exact PartialState.singletonMemU64_regs r
            rw [PartialState.union_regs_of_left_none h_outer_h1_none] at hvr
            apply hcr_regs r vr
            have h_P_none : h_P.regs r = none := by
              rw [← hu_base_VM]
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrbase)]
              rw [← hu_val_mem]
              rw [PartialState.union_regs_of_left_none
                  (PartialState.singletonReg_regs_other hrval)]
              exact PartialState.singletonMemU64_regs r
            rw [← hu_PR]
            rw [PartialState.union_regs_of_left_none h_P_none]
            exact hvr
      -- mem: new state mem = writeU64 ... (vSrc % 2^64).
      -- At addr+i (i ∈ 0..7): writeU64 writes byte_i of (vSrc % 2^64) = byte_i of vSrc.
      -- Outside [addr, addr+8): unchanged.
      · intro a vm hvm
        show (Memory.writeU64 s.mem (effectiveAddr baseAddr off) (vSrc % 2 ^ 64)) a = vm
        -- Helper for each in-range case at offset i:
        by_cases ha0 : a = effectiveAddr baseAddr off
        · rw [ha0] at hvm ⊢
          have h_inner :
              ((PartialState.singletonReg baseReg baseAddr).union
                ((PartialState.singletonReg valReg vSrc).union
                  (PartialState.singletonMemU64 (effectiveAddr baseAddr off) vSrc))).mem
                  (effectiveAddr baseAddr off) = some (vSrc % 256) := by
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
            exact PartialState.singletonMemU64_mem_0 _ _
          rw [PartialState.union_mem_of_left_some h_inner] at hvm
          have : vm = vSrc % 256 := (Option.some.inj hvm).symm
          rw [this]
          unfold Memory.writeU64
          simp
        · by_cases ha1 : a = effectiveAddr baseAddr off + 1
          · rw [ha1] at hvm ⊢
            have h_inner :
                ((PartialState.singletonReg baseReg baseAddr).union
                  ((PartialState.singletonReg valReg vSrc).union
                    (PartialState.singletonMemU64 (effectiveAddr baseAddr off) vSrc))).mem
                    (effectiveAddr baseAddr off + 1) = some (vSrc / 0x100 % 256) := by
              rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
              rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
              exact PartialState.singletonMemU64_mem_1 _ _
            rw [PartialState.union_mem_of_left_some h_inner] at hvm
            have : vm = vSrc / 0x100 % 256 := (Option.some.inj hvm).symm
            rw [this]
            unfold Memory.writeU64
            simp [show effectiveAddr baseAddr off + 1 ≠ effectiveAddr baseAddr off from by omega]
            omega
          · by_cases ha2 : a = effectiveAddr baseAddr off + 2
            · rw [ha2] at hvm ⊢
              have h_inner :
                  ((PartialState.singletonReg baseReg baseAddr).union
                    ((PartialState.singletonReg valReg vSrc).union
                      (PartialState.singletonMemU64 (effectiveAddr baseAddr off) vSrc))).mem
                      (effectiveAddr baseAddr off + 2) = some (vSrc / 0x10000 % 256) := by
                rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                exact PartialState.singletonMemU64_mem_2 _ _
              rw [PartialState.union_mem_of_left_some h_inner] at hvm
              have : vm = vSrc / 0x10000 % 256 := (Option.some.inj hvm).symm
              rw [this]
              unfold Memory.writeU64
              simp [show effectiveAddr baseAddr off + 2 ≠ effectiveAddr baseAddr off from by omega,
                    show effectiveAddr baseAddr off + 2 ≠ effectiveAddr baseAddr off + 1 from by omega]
              omega
            · by_cases ha3 : a = effectiveAddr baseAddr off + 3
              · rw [ha3] at hvm ⊢
                have h_inner :
                    ((PartialState.singletonReg baseReg baseAddr).union
                      ((PartialState.singletonReg valReg vSrc).union
                        (PartialState.singletonMemU64 (effectiveAddr baseAddr off) vSrc))).mem
                        (effectiveAddr baseAddr off + 3) = some (vSrc / 0x1000000 % 256) := by
                  rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                  rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                  exact PartialState.singletonMemU64_mem_3 _ _
                rw [PartialState.union_mem_of_left_some h_inner] at hvm
                have : vm = vSrc / 0x1000000 % 256 := (Option.some.inj hvm).symm
                rw [this]
                unfold Memory.writeU64
                simp [show effectiveAddr baseAddr off + 3 ≠ effectiveAddr baseAddr off from by omega,
                      show effectiveAddr baseAddr off + 3 ≠ effectiveAddr baseAddr off + 1 from by omega,
                      show effectiveAddr baseAddr off + 3 ≠ effectiveAddr baseAddr off + 2 from by omega]
                omega
              · by_cases ha4 : a = effectiveAddr baseAddr off + 4
                · rw [ha4] at hvm ⊢
                  have h_inner :
                      ((PartialState.singletonReg baseReg baseAddr).union
                        ((PartialState.singletonReg valReg vSrc).union
                          (PartialState.singletonMemU64 (effectiveAddr baseAddr off) vSrc))).mem
                          (effectiveAddr baseAddr off + 4) = some (vSrc / 0x100000000 % 256) := by
                    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                    exact PartialState.singletonMemU64_mem_4 _ _
                  rw [PartialState.union_mem_of_left_some h_inner] at hvm
                  have : vm = vSrc / 0x100000000 % 256 := (Option.some.inj hvm).symm
                  rw [this]
                  unfold Memory.writeU64
                  simp [show effectiveAddr baseAddr off + 4 ≠ effectiveAddr baseAddr off from by omega,
                        show effectiveAddr baseAddr off + 4 ≠ effectiveAddr baseAddr off + 1 from by omega,
                        show effectiveAddr baseAddr off + 4 ≠ effectiveAddr baseAddr off + 2 from by omega,
                        show effectiveAddr baseAddr off + 4 ≠ effectiveAddr baseAddr off + 3 from by omega]
                  omega
                · by_cases ha5 : a = effectiveAddr baseAddr off + 5
                  · rw [ha5] at hvm ⊢
                    have h_inner :
                        ((PartialState.singletonReg baseReg baseAddr).union
                          ((PartialState.singletonReg valReg vSrc).union
                            (PartialState.singletonMemU64 (effectiveAddr baseAddr off) vSrc))).mem
                            (effectiveAddr baseAddr off + 5) = some (vSrc / 0x10000000000 % 256) := by
                      rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                      rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                      exact PartialState.singletonMemU64_mem_5 _ _
                    rw [PartialState.union_mem_of_left_some h_inner] at hvm
                    have : vm = vSrc / 0x10000000000 % 256 := (Option.some.inj hvm).symm
                    rw [this]
                    unfold Memory.writeU64
                    simp [show effectiveAddr baseAddr off + 5 ≠ effectiveAddr baseAddr off from by omega,
                          show effectiveAddr baseAddr off + 5 ≠ effectiveAddr baseAddr off + 1 from by omega,
                          show effectiveAddr baseAddr off + 5 ≠ effectiveAddr baseAddr off + 2 from by omega,
                          show effectiveAddr baseAddr off + 5 ≠ effectiveAddr baseAddr off + 3 from by omega,
                          show effectiveAddr baseAddr off + 5 ≠ effectiveAddr baseAddr off + 4 from by omega]
                    omega
                  · by_cases ha6 : a = effectiveAddr baseAddr off + 6
                    · rw [ha6] at hvm ⊢
                      have h_inner :
                          ((PartialState.singletonReg baseReg baseAddr).union
                            ((PartialState.singletonReg valReg vSrc).union
                              (PartialState.singletonMemU64 (effectiveAddr baseAddr off) vSrc))).mem
                              (effectiveAddr baseAddr off + 6) = some (vSrc / 0x1000000000000 % 256) := by
                        rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                        rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                        exact PartialState.singletonMemU64_mem_6 _ _
                      rw [PartialState.union_mem_of_left_some h_inner] at hvm
                      have : vm = vSrc / 0x1000000000000 % 256 := (Option.some.inj hvm).symm
                      rw [this]
                      unfold Memory.writeU64
                      simp [show effectiveAddr baseAddr off + 6 ≠ effectiveAddr baseAddr off from by omega,
                            show effectiveAddr baseAddr off + 6 ≠ effectiveAddr baseAddr off + 1 from by omega,
                            show effectiveAddr baseAddr off + 6 ≠ effectiveAddr baseAddr off + 2 from by omega,
                            show effectiveAddr baseAddr off + 6 ≠ effectiveAddr baseAddr off + 3 from by omega,
                            show effectiveAddr baseAddr off + 6 ≠ effectiveAddr baseAddr off + 4 from by omega,
                            show effectiveAddr baseAddr off + 6 ≠ effectiveAddr baseAddr off + 5 from by omega]
                      omega
                    · by_cases ha7 : a = effectiveAddr baseAddr off + 7
                      · rw [ha7] at hvm ⊢
                        have h_inner :
                            ((PartialState.singletonReg baseReg baseAddr).union
                              ((PartialState.singletonReg valReg vSrc).union
                                (PartialState.singletonMemU64 (effectiveAddr baseAddr off) vSrc))).mem
                                (effectiveAddr baseAddr off + 7) = some (vSrc / 0x100000000000000 % 256) := by
                          rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                          rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                          exact PartialState.singletonMemU64_mem_7 _ _
                        rw [PartialState.union_mem_of_left_some h_inner] at hvm
                        have : vm = vSrc / 0x100000000000000 % 256 := (Option.some.inj hvm).symm
                        rw [this]
                        unfold Memory.writeU64
                        simp [show effectiveAddr baseAddr off + 7 ≠ effectiveAddr baseAddr off from by omega,
                              show effectiveAddr baseAddr off + 7 ≠ effectiveAddr baseAddr off + 1 from by omega,
                              show effectiveAddr baseAddr off + 7 ≠ effectiveAddr baseAddr off + 2 from by omega,
                              show effectiveAddr baseAddr off + 7 ≠ effectiveAddr baseAddr off + 3 from by omega,
                              show effectiveAddr baseAddr off + 7 ≠ effectiveAddr baseAddr off + 4 from by omega,
                              show effectiveAddr baseAddr off + 7 ≠ effectiveAddr baseAddr off + 5 from by omega,
                              show effectiveAddr baseAddr off + 7 ≠ effectiveAddr baseAddr off + 6 from by omega]
                        omega
                      · -- a is outside [addr, addr+8).
                        have h_outer_none :
                            ((PartialState.singletonReg baseReg baseAddr).union
                              ((PartialState.singletonReg valReg vSrc).union
                                (PartialState.singletonMemU64 (effectiveAddr baseAddr off) vSrc))).mem a
                            = none := by
                          rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                          rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                          exact PartialState.singletonMemU64_mem_outside _ _ a (by omega)
                        rw [PartialState.union_mem_of_left_none h_outer_none] at hvm
                        unfold Memory.writeU64
                        simp only [Memory.Mem.read_put]
                        rw [if_neg ha0, if_neg ha1, if_neg ha2, if_neg ha3,
                            if_neg ha4, if_neg ha5, if_neg ha6, if_neg ha7]
                        apply hcm_mem a vm
                        have h_P_none : h_P.mem a = none := by
                          rw [← hu_base_VM]
                          rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                          rw [← hu_val_mem]
                          rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                          exact PartialState.singletonMemU64_mem_outside _ _ a (by omega)
                        rw [← hu_PR]
                        rw [PartialState.union_mem_of_left_none h_P_none]
                        exact hvm
      -- pc:
      · intro vp hvp
        have h_outer_pc :
            ((PartialState.singletonReg baseReg baseAddr).union
              ((PartialState.singletonReg valReg vSrc).union
                (PartialState.singletonMemU64 (effectiveAddr baseAddr off) vSrc))).pc = none := by
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
    -- (b) Outer disjointness.
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
            exact PartialState.singletonMemU64_regs r
      · intro a
        by_cases ha0 : a = effectiveAddr baseAddr off
        · rw [ha0]; right
          exact h_R_no_mem_at _ _ (h_P_mem_i _ _ (h_VM_mem_i _ _ (PartialState.singletonMemU64_mem_0 _ _)))
        · by_cases ha1 : a = effectiveAddr baseAddr off + 1
          · rw [ha1]; right
            exact h_R_no_mem_at _ _ (h_P_mem_i _ _ (h_VM_mem_i _ _ (PartialState.singletonMemU64_mem_1 _ _)))
          · by_cases ha2 : a = effectiveAddr baseAddr off + 2
            · rw [ha2]; right
              exact h_R_no_mem_at _ _ (h_P_mem_i _ _ (h_VM_mem_i _ _ (PartialState.singletonMemU64_mem_2 _ _)))
            · by_cases ha3 : a = effectiveAddr baseAddr off + 3
              · rw [ha3]; right
                exact h_R_no_mem_at _ _ (h_P_mem_i _ _ (h_VM_mem_i _ _ (PartialState.singletonMemU64_mem_3 _ _)))
              · by_cases ha4 : a = effectiveAddr baseAddr off + 4
                · rw [ha4]; right
                  exact h_R_no_mem_at _ _ (h_P_mem_i _ _ (h_VM_mem_i _ _ (PartialState.singletonMemU64_mem_4 _ _)))
                · by_cases ha5 : a = effectiveAddr baseAddr off + 5
                  · rw [ha5]; right
                    exact h_R_no_mem_at _ _ (h_P_mem_i _ _ (h_VM_mem_i _ _ (PartialState.singletonMemU64_mem_5 _ _)))
                  · by_cases ha6 : a = effectiveAddr baseAddr off + 6
                    · rw [ha6]; right
                      exact h_R_no_mem_at _ _ (h_P_mem_i _ _ (h_VM_mem_i _ _ (PartialState.singletonMemU64_mem_6 _ _)))
                    · by_cases ha7 : a = effectiveAddr baseAddr off + 7
                      · rw [ha7]; right
                        exact h_R_no_mem_at _ _ (h_P_mem_i _ _ (h_VM_mem_i _ _ (PartialState.singletonMemU64_mem_7 _ _)))
                      · left
                        rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                        rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
                        exact PartialState.singletonMemU64_mem_outside _ _ a (by omega)
      · left
        rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
        rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
        exact PartialState.singletonMemU64_pc
    -- (c) Inner disjointness: singletonReg baseReg ⊥ (singletonReg valReg ⊎ singletonMemU64).
    · refine ⟨fun r => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
      · by_cases hrbase : r = baseReg
        · right
          rw [hrbase,
              PartialState.union_regs_of_left_none
                (PartialState.singletonReg_regs_other hne_base_val)]
          exact PartialState.singletonMemU64_regs baseReg
        · left; exact PartialState.singletonReg_regs_other hrbase
      · left; exact PartialState.singletonReg_mem a
      · left; exact PartialState.singletonReg_pc
    -- (d) Innermost disjointness: singletonReg valReg ⊥ singletonMemU64.
    · refine ⟨fun r => ?_, fun a => ?_, ?_, by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp), by first | exact Or.inl rfl | exact Or.inr rfl | (left; simp) | (right; simp)⟩
      · right; exact PartialState.singletonMemU64_regs r
      · left; exact PartialState.singletonReg_mem a
      · left; exact PartialState.singletonReg_pc


end SVM.SBPF
