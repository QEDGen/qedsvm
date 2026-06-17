import SVM.SBPF.InstructionSpecs.Syscalls.Sysvar
import SVM.SBPF.InstructionSpecs.MemByte

namespace SVM.SBPF

open Memory

/-! ## Syscall: `sol_sha256` (single-slice success triple)

`sol_sha256(r1 = *SliceDesc vals, r2 = n_vals, r3 = *mut [u8;32] out)`: gather the
slice bytes, hash once, write the 32-byte digest to `*r3`, set `r0 := 0`.

This is the `n = 1` instance: the precondition owns ONE 16-byte descriptor
(`vals ↦U64 ptr`, `vals+8 ↦U64 len`) plus the input slice (`ptr ↦Bytes inputBytes`)
and the output cell (`out ↦Bytes32 oldOut`). The post flips `r0 → 0` and the output
to `Sha256.hash inputBytes`; the descriptor + input are framed (read-only).

The H6 region envelope collapses via `State.hashWrite_success`: output writable,
descriptor array readable, the single input slice in region. The three block
disjointness side conditions (`hDescIn`/`hDescOut`/`hInOut`) keep the four owned
mem regions separated, so the digest write doesn't disturb the framed reads and
the post heap is well-formed. Direct proof in the `call_sol_get_sysvar_spec` /
`call_sol_memcmp_spec` style (union-climb the atoms, rebuild the post heap). -/

set_option maxHeartbeats 1600000 in
theorem call_sol_sha256_spec
    (r0Old vals ptr len out : Nat)
    (inputBytes oldOut : ByteArray) (pc : Nat) (nCu : Nat)
    (hInSize : inputBytes.size = len)
    (hPtr : ptr < 2 ^ 64)
    (hLen : len < 2 ^ 64)
    -- Block disjointness: descriptor `[vals,vals+16)`, input `[ptr,ptr+len)`,
    -- output `[out,out+32)` are pairwise separated.
    (hDescIn  : vals + 16 ≤ ptr ∨ ptr + len ≤ vals)
    (hDescOut : vals + 16 ≤ out ∨ out + 32 ≤ vals)
    (hInOut   : ptr + len ≤ out ∨ out + 32 ≤ ptr)
    (hCu : ∀ s : State,
        (step (.call .sol_sha256) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithinMem 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_sha256))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ vals) ** (.r2 ↦ᵣ 1) ** (.r3 ↦ᵣ out) **
        (vals ↦U64 ptr) ** (vals + 8 ↦U64 len) **
        (ptr ↦Bytes inputBytes) ** (out ↦Bytes32 oldOut))
      ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ vals) ** (.r2 ↦ᵣ 1) ** (.r3 ↦ᵣ out) **
        (vals ↦U64 ptr) ** (vals + 8 ↦U64 len) **
        (ptr ↦Bytes inputBytes) ** (out ↦Bytes32 (Sha256.hash inputBytes)))
      (fun rt => (rt.containsWritable out 32 = true ∧
                  rt.containsRange vals 16 = true) ∧
                 rt.containsRange ptr len = true) := by
  intro R hRfree fetch hcr s hPR hpc hex hbud h_region
  obtain ⟨hp, hcompat, h_P, h_R, hd_PR, hu_PR, h_P_sat, h_R_sat⟩ := hPR
  obtain ⟨h_r0, h_T1, hd_r0_T1, hu_r0_T1, h_r0_pred, h_T1_sat⟩ := h_P_sat
  obtain ⟨h_r1, h_T2, hd_r1_T2, hu_r1_T2, h_r1_pred, h_T2_sat⟩ := h_T1_sat
  obtain ⟨h_r2, h_T3, hd_r2_T3, hu_r2_T3, h_r2_pred, h_T3_sat⟩ := h_T2_sat
  obtain ⟨h_r3, h_T4, hd_r3_T4, hu_r3_T4, h_r3_pred, h_T4_sat⟩ := h_T3_sat
  obtain ⟨h_d1, h_T5, hd_d1_T5, hu_d1_T5, h_d1_pred, h_T5_sat⟩ := h_T4_sat
  obtain ⟨h_d2, h_T6, hd_d2_T6, hu_d2_T6, h_d2_pred, h_T6_sat⟩ := h_T5_sat
  obtain ⟨h_in, h_out, hd_in_out, hu_in_out, h_in_pred, h_out_pred⟩ := h_T6_sat
  rw [h_r0_pred] at hu_r0_T1 hd_r0_T1
  rw [h_r1_pred] at hu_r1_T2 hd_r1_T2
  rw [h_r2_pred] at hu_r2_T3 hd_r2_T3
  rw [h_r3_pred] at hu_r3_T4 hd_r3_T4
  rw [h_d1_pred] at hu_d1_T5 hd_d1_T5
  rw [h_d2_pred] at hu_d2_T6 hd_d2_T6
  rw [h_in_pred] at hu_in_out hd_in_out
  rw [h_out_pred] at hu_in_out hd_in_out
  clear h_r0_pred h_r1_pred h_r2_pred h_r3_pred h_d1_pred h_d2_pred h_in_pred h_out_pred
        h_r0 h_r1 h_r2 h_r3 h_d1 h_d2 h_in h_out
  have hcr_regs := hcompat.regs
  have hcm_mem := hcompat.mem
  -- region requirements specialised to this state's registers
  have hWr : s.regions.containsWritable out 32 = true := h_region.1.1
  have hRangeVals : s.regions.containsRange vals 16 = true := h_region.1.2
  have hRangePtr : s.regions.containsRange ptr len = true := h_region.2
  -- climb the four registers to h_P (r3 at h_T3, r2 at h_T2, r1 at h_T1, r0 at h_P)
  have h_T3_regs_r3 : h_T3.regs .r3 = some out := by
    rw [← hu_r3_T4]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_T2_regs_r2 : h_T2.regs .r2 = some 1 := by
    rw [← hu_r2_T3]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_T2_regs_r3 : h_T2.regs .r3 = some out := by
    rw [← hu_r2_T3,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r3 ≠ Reg.r2))]
    exact h_T3_regs_r3
  have h_T1_regs_r1 : h_T1.regs .r1 = some vals := by
    rw [← hu_r1_T2]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_T1_regs_r2 : h_T1.regs .r2 = some 1 := by
    rw [← hu_r1_T2,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r2 ≠ Reg.r1))]
    exact h_T2_regs_r2
  have h_T1_regs_r3 : h_T1.regs .r3 = some out := by
    rw [← hu_r1_T2,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r3 ≠ Reg.r1))]
    exact h_T2_regs_r3
  have h_P_regs_r0 : h_P.regs .r0 = some r0Old := by
    rw [← hu_r0_T1]
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_regs_r1 : h_P.regs .r1 = some vals := by
    rw [← hu_r0_T1,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r1 ≠ Reg.r0))]
    exact h_T1_regs_r1
  have h_P_regs_r2 : h_P.regs .r2 = some 1 := by
    rw [← hu_r0_T1,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r2 ≠ Reg.r0))]
    exact h_T1_regs_r2
  have h_P_regs_r3 : h_P.regs .r3 = some out := by
    rw [← hu_r0_T1,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r3 ≠ Reg.r0))]
    exact h_T1_regs_r3
  have hp_regs_r0 : hp.regs .r0 = some r0Old := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r0
  have hp_regs_r1 : hp.regs .r1 = some vals := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r1
  have hp_regs_r2 : hp.regs .r2 = some 1 := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r2
  have hp_regs_r3 : hp.regs .r3 = some out := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r3
  have hs_regs_r0 : s.regs.get .r0 = r0Old := hcr_regs .r0 r0Old hp_regs_r0
  have hs_r1_field : s.regs.r1 = vals := hcr_regs .r1 vals hp_regs_r1
  have hs_r2_field : s.regs.r2 = 1 := hcr_regs .r2 1 hp_regs_r2
  have hs_r3_field : s.regs.r3 = out := hcr_regs .r3 out hp_regs_r3
  -- generic climb: h_P.mem a from h_T4.mem a (past the four registers)
  have climb4 (a : Nat) : h_P.mem a = h_T4.mem a := by
    rw [← hu_r0_T1, PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a),
        ← hu_r1_T2, PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a),
        ← hu_r2_T3, PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a),
        ← hu_r3_T4, PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
  -- a `some` mem fact at h_P pushes through to s.mem
  have h_P_to_s : ∀ a v, h_P.mem a = some v → s.mem a = v := by
    intro a v hav
    apply hcm_mem a v
    rw [← hu_PR]
    exact PartialState.union_mem_of_left_some hav
  -- descriptor cell 1 bytes
  have d1_in_P : ∀ a v, (PartialState.singletonMemU64 vals ptr).mem a = some v →
      h_P.mem a = some v := by
    intro a v hav
    rw [climb4, ← hu_d1_T5]
    exact PartialState.union_mem_of_left_some hav
  have hReadVals : Memory.readU64 s.mem vals = ptr := by
    apply readU64_eq_of_bytes_match hPtr
    · exact h_P_to_s _ _ (d1_in_P _ _ (PartialState.singletonMemU64_mem_0 vals ptr))
    · exact h_P_to_s _ _ (d1_in_P _ _ (PartialState.singletonMemU64_mem_1 vals ptr))
    · exact h_P_to_s _ _ (d1_in_P _ _ (PartialState.singletonMemU64_mem_2 vals ptr))
    · exact h_P_to_s _ _ (d1_in_P _ _ (PartialState.singletonMemU64_mem_3 vals ptr))
    · exact h_P_to_s _ _ (d1_in_P _ _ (PartialState.singletonMemU64_mem_4 vals ptr))
    · exact h_P_to_s _ _ (d1_in_P _ _ (PartialState.singletonMemU64_mem_5 vals ptr))
    · exact h_P_to_s _ _ (d1_in_P _ _ (PartialState.singletonMemU64_mem_6 vals ptr))
    · exact h_P_to_s _ _ (d1_in_P _ _ (PartialState.singletonMemU64_mem_7 vals ptr))
  -- descriptor cell 2 bytes (at vals+8, past d1)
  have d2_in_P : ∀ a v, (PartialState.singletonMemU64 (vals + 8) len).mem a = some v →
      (vals + 8 ≤ a ∧ a < vals + 8 + 8) → h_P.mem a = some v := by
    intro a v hav ha
    rw [climb4, ← hu_d1_T5,
        PartialState.union_mem_of_left_none
          (PartialState.singletonMemU64_mem_outside vals ptr a (by omega)),
        ← hu_d2_T6]
    exact PartialState.union_mem_of_left_some hav
  have hReadVals8 : Memory.readU64 s.mem (vals + 8) = len := by
    apply readU64_eq_of_bytes_match hLen
    · exact h_P_to_s _ _ (d2_in_P _ _ (PartialState.singletonMemU64_mem_0 (vals+8) len) (by omega))
    · exact h_P_to_s _ _ (d2_in_P _ _ (PartialState.singletonMemU64_mem_1 (vals+8) len) (by omega))
    · exact h_P_to_s _ _ (d2_in_P _ _ (PartialState.singletonMemU64_mem_2 (vals+8) len) (by omega))
    · exact h_P_to_s _ _ (d2_in_P _ _ (PartialState.singletonMemU64_mem_3 (vals+8) len) (by omega))
    · exact h_P_to_s _ _ (d2_in_P _ _ (PartialState.singletonMemU64_mem_4 (vals+8) len) (by omega))
    · exact h_P_to_s _ _ (d2_in_P _ _ (PartialState.singletonMemU64_mem_5 (vals+8) len) (by omega))
    · exact h_P_to_s _ _ (d2_in_P _ _ (PartialState.singletonMemU64_mem_6 (vals+8) len) (by omega))
    · exact h_P_to_s _ _ (d2_in_P _ _ (PartialState.singletonMemU64_mem_7 (vals+8) len) (by omega))
  -- input slice bytes (at ptr, past both descriptor cells)
  have in_in_P : ∀ i, i < inputBytes.size →
      h_P.mem (ptr + i) = some (inputBytes.get! i).toNat := by
    intro i hi
    rw [climb4, ← hu_d1_T5,
        PartialState.union_mem_of_left_none
          (PartialState.singletonMemU64_mem_outside vals ptr (ptr + i) (by omega)),
        ← hu_d2_T6,
        PartialState.union_mem_of_left_none
          (PartialState.singletonMemU64_mem_outside (vals + 8) len (ptr + i) (by omega)),
        ← hu_in_out]
    exact PartialState.union_mem_of_left_some
      (PartialState.singletonMemBytes_mem_at ptr inputBytes i hi)
  have hReadIn : readBytes s.mem ptr len = inputBytes := by
    apply readBytes_eq_of_match s.mem ptr len inputBytes hInSize
    intro i hi
    have hi' : i < inputBytes.size := by rw [hInSize]; exact hi
    rw [h_P_to_s (ptr + i) _ (in_in_P i hi')]
    exact Nat.mod_eq_of_lt (inputBytes.get! i).toNat_lt
  -- readSlices reduces (n = 1) to readBytes of the single slice = inputBytes
  have hSlicesEq : readSlices s.mem vals 1 = inputBytes := by
    unfold readSlices
    simp only [List.range_one, List.foldl_cons, List.foldl_nil, Nat.zero_mul,
               Nat.add_zero]
    rw [hReadVals, hReadVals8, hReadIn]
    exact ByteArray.empty_append
  -- the step effect collapses to a single write via hashWrite_success
  have hExecEq : Sha256.exec s =
      { s with regs := s.regs.set .r0 0,
               mem := writeBytes s.mem out 32 (Sha256.hash inputBytes) } := by
    show s.hashWrite s.regs.r3 32 s.regs.r1 s.regs.r2
          (Sha256.hash (readSlices s.mem s.regs.r1 s.regs.r2)) = _
    rw [hs_r1_field, hs_r2_field, hs_r3_field, hSlicesEq]
    exact s.hashWrite_success out 32 vals 1 (Sha256.hash inputBytes)
      (Or.inr hWr)
      (Or.inr (by rw [Nat.one_mul]; exact hRangeVals))
      (fun i hi => by
        have hi0 : i = 0 := by simpa [List.mem_range, Nat.lt_one_iff] using hi
        subst hi0
        right
        simp only [Nat.zero_mul, Nat.add_zero]
        rw [hReadVals, hReadVals8]
        exact hRangePtr)
  -- exec facts
  have hfetch : fetch s.pc = some (.call .sol_sha256) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hstep_eq : executeFn fetch s 1 = chargeCu (step (.call .sol_sha256) s) := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch, executeFn_zero]
  have hexec_regs : (executeFn fetch s 1).regs = s.regs.set .r0 0 := by
    rw [hstep_eq]; show (Sha256.exec s).regs = s.regs.set .r0 0; rw [hExecEq]
  have hexec_pc : (executeFn fetch s 1).pc = s.pc + 1 := by rw [hstep_eq]; rfl
  have hexec_exit : (executeFn fetch s 1).exitCode = none := by
    rw [hstep_eq]; show (Sha256.exec s).exitCode = none; rw [hExecEq]; exact hex
  have hexec_rd : (executeFn fetch s 1).returnData = s.returnData := by
    rw [hstep_eq]; show (Sha256.exec s).returnData = s.returnData; rw [hExecEq]
  have hexec_cs : (executeFn fetch s 1).callStack = s.callStack := by
    rw [hstep_eq]; show (Sha256.exec s).callStack = s.callStack; rw [hExecEq]
  have hexec_mem_out (i : Nat) (hi : i < 32) :
      (executeFn fetch s 1).mem (out + i) = ((Sha256.hash inputBytes).get! i).toNat := by
    rw [hstep_eq]; show (Sha256.exec s).mem (out + i) = _; rw [hExecEq]
    exact writeBytes_read_inside s.mem out 32 i (Sha256.hash inputBytes) hi
  have hexec_mem_outside (a : Nat) (h : a < out ∨ a ≥ out + 32) :
      (executeFn fetch s 1).mem a = s.mem a := by
    rw [hstep_eq]; show (Sha256.exec s).mem a = s.mem a; rw [hExecEq]
    exact writeBytes_read_outside s.mem out 32 a (Sha256.hash inputBytes) h
  -- s-side register / memory recovery shared by the compat proof
  have hs_regs_r1 : s.regs.get .r1 = vals := hs_r1_field
  have hs_regs_r2 : s.regs.get .r2 = 1 := hs_r2_field
  have hs_regs_r3 : s.regs.get .r3 = out := hs_r3_field
  have hs_d1 : ∀ a v, (PartialState.singletonMemU64 vals ptr).mem a = some v →
      s.mem a = v := fun a v h => h_P_to_s a v (d1_in_P a v h)
  have hs_d2 : ∀ a v, (PartialState.singletonMemU64 (vals + 8) len).mem a = some v →
      (vals + 8 ≤ a ∧ a < vals + 8 + 8) → s.mem a = v :=
    fun a v h ha => h_P_to_s a v (d2_in_P a v h ha)
  have hs_in : ∀ i, i < inputBytes.size →
      s.mem (ptr + i) = (inputBytes.get! i).toNat :=
    fun i hi => h_P_to_s (ptr + i) _ (in_in_P i hi)
  -- ===== build the post heap =====
  let h_r0_new : PartialState := PartialState.singletonReg .r0 0
  let h_r1_new : PartialState := PartialState.singletonReg .r1 vals
  let h_r2_new : PartialState := PartialState.singletonReg .r2 1
  let h_r3_new : PartialState := PartialState.singletonReg .r3 out
  let h_d1_new : PartialState := PartialState.singletonMemU64 vals ptr
  let h_d2_new : PartialState := PartialState.singletonMemU64 (vals + 8) len
  let h_in_new : PartialState := PartialState.singletonMemBytes ptr inputBytes
  let h_out_new : PartialState := PartialState.singletonMem32Bytes out (Sha256.hash inputBytes)
  let h_T6_new : PartialState := h_in_new.union h_out_new
  let h_T5_new : PartialState := h_d2_new.union h_T6_new
  let h_T4_new : PartialState := h_d1_new.union h_T5_new
  let h_T3_new : PartialState := h_r3_new.union h_T4_new
  let h_T2_new : PartialState := h_r2_new.union h_T3_new
  let h_T1_new : PartialState := h_r1_new.union h_T2_new
  let h_P_new : PartialState := h_r0_new.union h_T1_new
  -- innermost mem disjointness: input ⫫ output
  have hd_in_out_new : h_in_new.Disjoint h_out_new :=
    { regs := fun r => Or.inl (PartialState.singletonMemBytes_regs r)
      mem := fun a => by
        by_cases ha : ptr ≤ a ∧ a < ptr + inputBytes.size
        · right
          obtain ⟨h_lo, h_hi⟩ := ha
          exact PartialState.singletonMem32Bytes_mem_outside out _ a (by omega)
        · left
          apply PartialState.singletonMemBytes_mem_outside
          rcases Nat.lt_or_ge a ptr with h' | h'
          · left; exact h'
          · rcases Nat.lt_or_ge a (ptr + inputBytes.size) with h'' | h''
            · exact absurd ⟨h', h''⟩ ha
            · right; exact h''
      pc := Or.inl PartialState.singletonMemBytes_pc
      returnData := Or.inl PartialState.singletonMemBytes_returnData
      callStack := Or.inl PartialState.singletonMemBytes_callStack }
  -- d2 ⫫ (input ∪ output)
  have hd_d2_T6_new : h_d2_new.Disjoint h_T6_new :=
    { regs := fun r => Or.inl (PartialState.singletonMemU64_regs r)
      mem := fun a => by
        by_cases ha : vals + 8 ≤ a ∧ a < vals + 8 + 8
        · right
          obtain ⟨h_lo, h_hi⟩ := ha
          show (h_in_new.union h_out_new).mem a = none
          rw [PartialState.union_mem_of_left_none
                (PartialState.singletonMemBytes_mem_outside ptr inputBytes a (by omega))]
          exact PartialState.singletonMem32Bytes_mem_outside out _ a (by omega)
        · left
          exact PartialState.singletonMemU64_mem_outside (vals + 8) len a (by omega)
      pc := Or.inl PartialState.singletonMemU64_pc
      returnData := Or.inl PartialState.singletonMemU64_returnData
      callStack := Or.inl PartialState.singletonMemU64_callStack }
  -- d1 ⫫ (d2 ∪ input ∪ output)
  have hd_d1_T5_new : h_d1_new.Disjoint h_T5_new :=
    { regs := fun r => Or.inl (PartialState.singletonMemU64_regs r)
      mem := fun a => by
        by_cases ha : vals ≤ a ∧ a < vals + 8
        · right
          obtain ⟨h_lo, h_hi⟩ := ha
          show (h_d2_new.union h_T6_new).mem a = none
          rw [PartialState.union_mem_of_left_none
                (PartialState.singletonMemU64_mem_outside (vals + 8) len a (by omega))]
          show (h_in_new.union h_out_new).mem a = none
          rw [PartialState.union_mem_of_left_none
                (PartialState.singletonMemBytes_mem_outside ptr inputBytes a (by omega))]
          exact PartialState.singletonMem32Bytes_mem_outside out _ a (by omega)
        · left
          exact PartialState.singletonMemU64_mem_outside vals ptr a (by omega)
      pc := Or.inl PartialState.singletonMemU64_pc
      returnData := Or.inl PartialState.singletonMemU64_returnData
      callStack := Or.inl PartialState.singletonMemU64_callStack }
  -- r3 ⫫ (all mem atoms)
  have hT4new_regs_none (r : Reg) : h_T4_new.regs r = none := by
    show (h_d1_new.union h_T5_new).regs r = none
    rw [PartialState.union_regs_of_left_none (PartialState.singletonMemU64_regs r)]
    show (h_d2_new.union h_T6_new).regs r = none
    rw [PartialState.union_regs_of_left_none (PartialState.singletonMemU64_regs r)]
    show (h_in_new.union h_out_new).regs r = none
    rw [PartialState.union_regs_of_left_none (PartialState.singletonMemBytes_regs r)]
    exact PartialState.singletonMem32Bytes_regs r
  have hd_r3_T4_new : h_r3_new.Disjoint h_T4_new := by
    refine
      { regs := fun r => ?_
        mem := fun a => Or.inl (PartialState.singletonReg_mem a)
        pc := Or.inl PartialState.singletonReg_pc
        returnData := Or.inl PartialState.singletonReg_returnData
        callStack := Or.inl PartialState.singletonReg_callStack }
    by_cases hr : r = .r3
    · right; rw [hr]; exact hT4new_regs_none .r3
    · left; exact PartialState.singletonReg_regs_other hr
  have hT3new_regs_other (r : Reg) (hr : r ≠ .r3) : h_T3_new.regs r = none := by
    show (h_r3_new.union h_T4_new).regs r = none
    rw [PartialState.union_regs_of_left_none (PartialState.singletonReg_regs_other hr)]
    exact hT4new_regs_none r
  have hd_r2_T3_new : h_r2_new.Disjoint h_T3_new := by
    refine
      { regs := fun r => ?_
        mem := fun a => Or.inl (PartialState.singletonReg_mem a)
        pc := Or.inl PartialState.singletonReg_pc
        returnData := Or.inl PartialState.singletonReg_returnData
        callStack := Or.inl PartialState.singletonReg_callStack }
    by_cases hr : r = .r2
    · right; rw [hr]; exact hT3new_regs_other .r2 (by decide)
    · left; exact PartialState.singletonReg_regs_other hr
  have hT2new_regs_other (r : Reg) (h2 : r ≠ .r2) (h3 : r ≠ .r3) :
      h_T2_new.regs r = none := by
    show (h_r2_new.union h_T3_new).regs r = none
    rw [PartialState.union_regs_of_left_none (PartialState.singletonReg_regs_other h2)]
    exact hT3new_regs_other r h3
  have hd_r1_T2_new : h_r1_new.Disjoint h_T2_new := by
    refine
      { regs := fun r => ?_
        mem := fun a => Or.inl (PartialState.singletonReg_mem a)
        pc := Or.inl PartialState.singletonReg_pc
        returnData := Or.inl PartialState.singletonReg_returnData
        callStack := Or.inl PartialState.singletonReg_callStack }
    by_cases hr : r = .r1
    · right; rw [hr]; exact hT2new_regs_other .r1 (by decide) (by decide)
    · left; exact PartialState.singletonReg_regs_other hr
  have hT1new_regs_other (r : Reg) (h1 : r ≠ .r1) (h2 : r ≠ .r2) (h3 : r ≠ .r3) :
      h_T1_new.regs r = none := by
    show (h_r1_new.union h_T2_new).regs r = none
    rw [PartialState.union_regs_of_left_none (PartialState.singletonReg_regs_other h1)]
    exact hT2new_regs_other r h2 h3
  have hd_r0_T1_new : h_r0_new.Disjoint h_T1_new := by
    refine
      { regs := fun r => ?_
        mem := fun a => Or.inl (PartialState.singletonReg_mem a)
        pc := Or.inl PartialState.singletonReg_pc
        returnData := Or.inl PartialState.singletonReg_returnData
        callStack := Or.inl PartialState.singletonReg_callStack }
    by_cases hr : r = .r0
    · right; rw [hr]; exact hT1new_regs_other .r0 (by decide) (by decide) (by decide)
    · left; exact PartialState.singletonReg_regs_other hr
  -- ===== per-field projections of h_P_new =====
  have h_P_new_regs_r0 : h_P_new.regs .r0 = some 0 := by
    show (h_r0_new.union h_T1_new).regs .r0 = some 0
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_new_regs_r1 : h_P_new.regs .r1 = some vals := by
    show (h_r0_new.union h_T1_new).regs .r1 = some vals
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r1 ≠ Reg.r0))]
    show (h_r1_new.union h_T2_new).regs .r1 = some vals
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_new_regs_r2 : h_P_new.regs .r2 = some 1 := by
    show (h_r0_new.union h_T1_new).regs .r2 = some 1
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r2 ≠ Reg.r0))]
    show (h_r1_new.union h_T2_new).regs .r2 = some 1
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r2 ≠ Reg.r1))]
    show (h_r2_new.union h_T3_new).regs .r2 = some 1
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_new_regs_r3 : h_P_new.regs .r3 = some out := by
    show (h_r0_new.union h_T1_new).regs .r3 = some out
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r3 ≠ Reg.r0))]
    show (h_r1_new.union h_T2_new).regs .r3 = some out
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r3 ≠ Reg.r1))]
    show (h_r2_new.union h_T3_new).regs .r3 = some out
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r3 ≠ Reg.r2))]
    show (h_r3_new.union h_T4_new).regs .r3 = some out
    exact PartialState.union_regs_of_left_some PartialState.singletonReg_regs_self
  have h_P_new_regs_other (r : Reg)
      (h0 : r ≠ .r0) (h1 : r ≠ .r1) (h2 : r ≠ .r2) (h3 : r ≠ .r3) :
      h_P_new.regs r = none := by
    show (h_r0_new.union h_T1_new).regs r = none
    rw [PartialState.union_regs_of_left_none (PartialState.singletonReg_regs_other h0)]
    exact hT1new_regs_other r h1 h2 h3
  -- mem projections
  have h_P_new_mem_d1 (a : Nat) (ha : vals ≤ a ∧ a < vals + 8) :
      h_P_new.mem a = (PartialState.singletonMemU64 vals ptr).mem a := by
    obtain ⟨x, hx⟩ := PartialState.singletonMemU64_mem_isSome vals ptr a ha
    rw [hx]
    show (h_r0_new.union h_T1_new).mem a = some x
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
    show (h_r1_new.union h_T2_new).mem a = some x
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
    show (h_r2_new.union h_T3_new).mem a = some x
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
    show (h_r3_new.union h_T4_new).mem a = some x
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
    show (h_d1_new.union h_T5_new).mem a = some x
    exact PartialState.union_mem_of_left_some hx
  have h_P_new_mem_d2 (a : Nat) (ha : vals + 8 ≤ a ∧ a < vals + 8 + 8) :
      h_P_new.mem a = (PartialState.singletonMemU64 (vals + 8) len).mem a := by
    obtain ⟨x, hx⟩ := PartialState.singletonMemU64_mem_isSome (vals + 8) len a ha
    rw [hx]
    show (h_r0_new.union h_T1_new).mem a = some x
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
    show (h_r1_new.union h_T2_new).mem a = some x
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
    show (h_r2_new.union h_T3_new).mem a = some x
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
    show (h_r3_new.union h_T4_new).mem a = some x
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
    show (h_d1_new.union h_T5_new).mem a = some x
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonMemU64_mem_outside vals ptr a (by omega))]
    show (h_d2_new.union h_T6_new).mem a = some x
    exact PartialState.union_mem_of_left_some hx
  have h_P_new_mem_in (i : Nat) (hi : i < inputBytes.size) :
      h_P_new.mem (ptr + i) = some (inputBytes.get! i).toNat := by
    show (h_r0_new.union h_T1_new).mem (ptr + i) = _
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    show (h_r1_new.union h_T2_new).mem (ptr + i) = _
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    show (h_r2_new.union h_T3_new).mem (ptr + i) = _
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    show (h_r3_new.union h_T4_new).mem (ptr + i) = _
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    show (h_d1_new.union h_T5_new).mem (ptr + i) = _
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonMemU64_mem_outside vals ptr (ptr + i) (by omega))]
    show (h_d2_new.union h_T6_new).mem (ptr + i) = _
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonMemU64_mem_outside (vals + 8) len (ptr + i) (by omega))]
    show (h_in_new.union h_out_new).mem (ptr + i) = _
    exact PartialState.union_mem_of_left_some
      (PartialState.singletonMemBytes_mem_at ptr inputBytes i hi)
  have h_P_new_mem_out (i : Nat) (hi : i < 32) :
      h_P_new.mem (out + i) = some ((Sha256.hash inputBytes).get! i).toNat := by
    show (h_r0_new.union h_T1_new).mem (out + i) = _
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    show (h_r1_new.union h_T2_new).mem (out + i) = _
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    show (h_r2_new.union h_T3_new).mem (out + i) = _
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    show (h_r3_new.union h_T4_new).mem (out + i) = _
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem _)]
    show (h_d1_new.union h_T5_new).mem (out + i) = _
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonMemU64_mem_outside vals ptr (out + i) (by omega))]
    show (h_d2_new.union h_T6_new).mem (out + i) = _
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonMemU64_mem_outside (vals + 8) len (out + i) (by omega))]
    show (h_in_new.union h_out_new).mem (out + i) = _
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonMemBytes_mem_outside ptr inputBytes (out + i) (by omega))]
    exact PartialState.singletonMem32Bytes_mem_at out _ i hi
  have h_P_new_mem_outside (a : Nat)
      (hd1 : a < vals ∨ a ≥ vals + 8) (hd2 : a < vals + 8 ∨ a ≥ vals + 8 + 8)
      (hin : a < ptr ∨ a ≥ ptr + inputBytes.size) (hou : a < out ∨ a ≥ out + 32) :
      h_P_new.mem a = none := by
    show (h_r0_new.union h_T1_new).mem a = none
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
    show (h_r1_new.union h_T2_new).mem a = none
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
    show (h_r2_new.union h_T3_new).mem a = none
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
    show (h_r3_new.union h_T4_new).mem a = none
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
    show (h_d1_new.union h_T5_new).mem a = none
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonMemU64_mem_outside vals ptr a hd1)]
    show (h_d2_new.union h_T6_new).mem a = none
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonMemU64_mem_outside (vals + 8) len a hd2)]
    show (h_in_new.union h_out_new).mem a = none
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonMemBytes_mem_outside ptr inputBytes a hin)]
    exact PartialState.singletonMem32Bytes_mem_outside out _ a hou
  have h_P_new_pc : h_P_new.pc = none := by
    show (h_r0_new.union h_T1_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    show (h_r1_new.union h_T2_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    show (h_r2_new.union h_T3_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    show (h_r3_new.union h_T4_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    show (h_d1_new.union h_T5_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonMemU64_pc]
    show (h_d2_new.union h_T6_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonMemU64_pc]
    show (h_in_new.union h_out_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonMemBytes_pc]
    exact PartialState.singletonMem32Bytes_pc
  have h_P_new_rd : h_P_new.returnData = none := by
    show (h_r0_new.union h_T1_new).returnData = none
    rw [PartialState.union_returnData_of_left_none PartialState.singletonReg_returnData]
    show (h_r1_new.union h_T2_new).returnData = none
    rw [PartialState.union_returnData_of_left_none PartialState.singletonReg_returnData]
    show (h_r2_new.union h_T3_new).returnData = none
    rw [PartialState.union_returnData_of_left_none PartialState.singletonReg_returnData]
    show (h_r3_new.union h_T4_new).returnData = none
    rw [PartialState.union_returnData_of_left_none PartialState.singletonReg_returnData]
    show (h_d1_new.union h_T5_new).returnData = none
    rw [PartialState.union_returnData_of_left_none PartialState.singletonMemU64_returnData]
    show (h_d2_new.union h_T6_new).returnData = none
    rw [PartialState.union_returnData_of_left_none PartialState.singletonMemU64_returnData]
    show (h_in_new.union h_out_new).returnData = none
    rw [PartialState.union_returnData_of_left_none PartialState.singletonMemBytes_returnData]
    exact PartialState.singletonMem32Bytes_returnData
  have h_P_new_cs : h_P_new.callStack = none := by
    show (h_r0_new.union h_T1_new).callStack = none
    rw [PartialState.union_callStack_of_left_none PartialState.singletonReg_callStack]
    show (h_r1_new.union h_T2_new).callStack = none
    rw [PartialState.union_callStack_of_left_none PartialState.singletonReg_callStack]
    show (h_r2_new.union h_T3_new).callStack = none
    rw [PartialState.union_callStack_of_left_none PartialState.singletonReg_callStack]
    show (h_r3_new.union h_T4_new).callStack = none
    rw [PartialState.union_callStack_of_left_none PartialState.singletonReg_callStack]
    show (h_d1_new.union h_T5_new).callStack = none
    rw [PartialState.union_callStack_of_left_none PartialState.singletonMemU64_callStack]
    show (h_d2_new.union h_T6_new).callStack = none
    rw [PartialState.union_callStack_of_left_none PartialState.singletonMemU64_callStack]
    show (h_in_new.union h_out_new).callStack = none
    rw [PartialState.union_callStack_of_left_none PartialState.singletonMemBytes_callStack]
    exact PartialState.singletonMem32Bytes_callStack
  -- ===== h_R absence facts (frame owns none of P's footprint) =====
  have hd_PR_regs := hd_PR.regs
  have hd_PR_mem := hd_PR.mem
  have hR_no_r0 : h_R.regs .r0 = none := by
    rcases hd_PR_regs .r0 with h | h
    · rw [h_P_regs_r0] at h; nomatch h
    · exact h
  have hR_no_r1 : h_R.regs .r1 = none := by
    rcases hd_PR_regs .r1 with h | h
    · rw [h_P_regs_r1] at h; nomatch h
    · exact h
  have hR_no_r2 : h_R.regs .r2 = none := by
    rcases hd_PR_regs .r2 with h | h
    · rw [h_P_regs_r2] at h; nomatch h
    · exact h
  have hR_no_r3 : h_R.regs .r3 = none := by
    rcases hd_PR_regs .r3 with h | h
    · rw [h_P_regs_r3] at h; nomatch h
    · exact h
  have hR_no_pc : h_R.pc = none := hRfree _ h_R_sat
  have hR_no_mem_d1 (a : Nat) (ha : vals ≤ a ∧ a < vals + 8) : h_R.mem a = none := by
    obtain ⟨x, hx⟩ := PartialState.singletonMemU64_mem_isSome vals ptr a ha
    rcases hd_PR_mem a with h | h
    · rw [d1_in_P a x hx] at h; nomatch h
    · exact h
  have hR_no_mem_d2 (a : Nat) (ha : vals + 8 ≤ a ∧ a < vals + 8 + 8) :
      h_R.mem a = none := by
    obtain ⟨x, hx⟩ := PartialState.singletonMemU64_mem_isSome (vals + 8) len a ha
    rcases hd_PR_mem a with h | h
    · rw [d2_in_P a x hx ha] at h; nomatch h
    · exact h
  have hR_no_mem_in (i : Nat) (hi : i < inputBytes.size) : h_R.mem (ptr + i) = none := by
    rcases hd_PR_mem (ptr + i) with h | h
    · rw [in_in_P i hi] at h; nomatch h
    · exact h
  -- the pre-state output cell (held `oldOut`) is owned by h_P, so absent in h_R
  have out_in_P (i : Nat) (hi : i < 32) :
      h_P.mem (out + i) = some (oldOut.get! i).toNat := by
    rw [climb4, ← hu_d1_T5,
        PartialState.union_mem_of_left_none
          (PartialState.singletonMemU64_mem_outside vals ptr (out + i) (by omega)),
        ← hu_d2_T6,
        PartialState.union_mem_of_left_none
          (PartialState.singletonMemU64_mem_outside (vals + 8) len (out + i) (by omega)),
        ← hu_in_out,
        PartialState.union_mem_of_left_none
          (PartialState.singletonMemBytes_mem_outside ptr inputBytes (out + i) (by omega))]
    exact PartialState.singletonMem32Bytes_mem_at out oldOut i hi
  have hR_no_mem_out (i : Nat) (hi : i < 32) : h_R.mem (out + i) = none := by
    rcases hd_PR_mem (out + i) with h | h
    · rw [out_in_P i hi] at h; nomatch h
    · exact h
  -- ===== outer disjointness h_P_new ⫫ h_R =====
  have hd_PnewR : h_P_new.Disjoint h_R :=
    { regs := fun r => by
        by_cases h0 : r = .r0
        · right; rw [h0]; exact hR_no_r0
        by_cases h1 : r = .r1
        · right; rw [h1]; exact hR_no_r1
        by_cases h2 : r = .r2
        · right; rw [h2]; exact hR_no_r2
        by_cases h3 : r = .r3
        · right; rw [h3]; exact hR_no_r3
        · left; exact h_P_new_regs_other r h0 h1 h2 h3
      mem := fun a => by
        by_cases hou : out ≤ a ∧ a < out + 32
        · right
          obtain ⟨h_lo, h_hi⟩ := hou
          rw [show a = out + (a - out) from by omega]
          exact hR_no_mem_out (a - out) (by omega)
        by_cases hd1 : vals ≤ a ∧ a < vals + 8
        · right; exact hR_no_mem_d1 a hd1
        by_cases hd2 : vals + 8 ≤ a ∧ a < vals + 8 + 8
        · right; exact hR_no_mem_d2 a hd2
        by_cases hin : ptr ≤ a ∧ a < ptr + inputBytes.size
        · right
          obtain ⟨h_lo, h_hi⟩ := hin
          rw [show a = ptr + (a - ptr) from by omega]
          exact hR_no_mem_in (a - ptr) (by omega)
        · left
          apply h_P_new_mem_outside
          · rcases Nat.lt_or_ge a vals with h | h
            · left; exact h
            · rcases Nat.lt_or_ge a (vals + 8) with h' | h'
              · exact absurd ⟨h, h'⟩ hd1
              · right; exact h'
          · rcases Nat.lt_or_ge a (vals + 8) with h | h
            · left; exact h
            · rcases Nat.lt_or_ge a (vals + 8 + 8) with h' | h'
              · exact absurd ⟨h, h'⟩ hd2
              · right; exact h'
          · rcases Nat.lt_or_ge a ptr with h | h
            · left; exact h
            · rcases Nat.lt_or_ge a (ptr + inputBytes.size) with h' | h'
              · exact absurd ⟨h, h'⟩ hin
              · right; exact h'
          · rcases Nat.lt_or_ge a out with h | h
            · left; exact h
            · rcases Nat.lt_or_ge a (out + 32) with h' | h'
              · exact absurd ⟨h, h'⟩ hou
              · right; exact h'
      pc := Or.inl h_P_new_pc
      returnData := Or.inl h_P_new_rd
      callStack := Or.inl h_P_new_cs }
  -- ===== assemble the triple =====
  refine ⟨1, Nat.le_refl 1, ?_, hexec_exit, ?_, ?_⟩
  · rw [hexec_pc, hpc]
  · rw [hstep_eq]
    show (step (.call .sol_sha256) s).cuConsumed + 1 ≤ s.cuConsumed + 1 + nCu
    have := hCu s; omega
  · refine ⟨h_P_new.union h_R, ?_, h_P_new, h_R, hd_PnewR, rfl,
            ⟨h_r0_new, h_T1_new, hd_r0_T1_new, rfl, rfl,
             h_r1_new, h_T2_new, hd_r1_T2_new, rfl, rfl,
             h_r2_new, h_T3_new, hd_r2_T3_new, rfl, rfl,
             h_r3_new, h_T4_new, hd_r3_T4_new, rfl, rfl,
             h_d1_new, h_T5_new, hd_d1_T5_new, rfl, rfl,
             h_d2_new, h_T6_new, hd_d2_T6_new, rfl, rfl,
             h_in_new, h_out_new, hd_in_out_new, rfl, rfl, rfl⟩,
            h_R_sat⟩
    refine
      { regs := ?_, mem := ?_, pc := ?_, returnData := ?_, callStack := ?_ }
    · -- regs compat
      intro r v hvr
      by_cases h0 : r = .r0
      · rw [h0] at hvr
        rw [PartialState.union_regs_of_left_some h_P_new_regs_r0] at hvr
        rw [h0, hexec_regs, ← (Option.some.inj hvr)]
        exact RegFile.get_set_self _ _ _ (by decide : (.r0 : Reg) ≠ .r10)
      by_cases h1 : r = .r1
      · rw [h1] at hvr
        rw [PartialState.union_regs_of_left_some h_P_new_regs_r1] at hvr
        rw [h1, hexec_regs, ← (Option.some.inj hvr),
            RegFile.get_set_diff _ _ _ _ (by decide : (.r1 : Reg) ≠ .r0)]
        exact hs_regs_r1
      by_cases h2 : r = .r2
      · rw [h2] at hvr
        rw [PartialState.union_regs_of_left_some h_P_new_regs_r2] at hvr
        rw [h2, hexec_regs, ← (Option.some.inj hvr),
            RegFile.get_set_diff _ _ _ _ (by decide : (.r2 : Reg) ≠ .r0)]
        exact hs_regs_r2
      by_cases h3 : r = .r3
      · rw [h3] at hvr
        rw [PartialState.union_regs_of_left_some h_P_new_regs_r3] at hvr
        rw [h3, hexec_regs, ← (Option.some.inj hvr),
            RegFile.get_set_diff _ _ _ _ (by decide : (.r3 : Reg) ≠ .r0)]
        exact hs_regs_r3
      · rw [PartialState.union_regs_of_left_none
              (h_P_new_regs_other r h0 h1 h2 h3)] at hvr
        rw [hexec_regs, RegFile.get_set_diff _ _ _ _ h0]
        have h_P_none : h_P.regs r = none := by
          rcases hd_PR_regs r with hl | hr
          · exact hl
          · rw [hr] at hvr; nomatch hvr
        apply hcr_regs r v
        rw [← hu_PR, PartialState.union_regs_of_left_none h_P_none]
        exact hvr
    · -- mem compat
      intro a v hva
      by_cases hou : out ≤ a ∧ a < out + 32
      · obtain ⟨h_lo, h_hi⟩ := hou
        have h_eq : a = out + (a - out) := by omega
        have h_lt : a - out < 32 := by omega
        rw [h_eq] at hva ⊢
        rw [PartialState.union_mem_of_left_some (h_P_new_mem_out _ h_lt)] at hva
        rw [hexec_mem_out _ h_lt, ← (Option.some.inj hva)]
      by_cases hd1 : vals ≤ a ∧ a < vals + 8
      · obtain ⟨h_lo, h_hi⟩ := hd1
        obtain ⟨x, hx⟩ := PartialState.singletonMemU64_mem_isSome vals ptr a ⟨h_lo, h_hi⟩
        have hPx : h_P_new.mem a = some x := (h_P_new_mem_d1 a ⟨h_lo, h_hi⟩).trans hx
        rw [PartialState.union_mem_of_left_some hPx] at hva
        rw [hexec_mem_outside a (by omega), hs_d1 a x hx]
        exact Option.some.inj hva
      by_cases hd2 : vals + 8 ≤ a ∧ a < vals + 8 + 8
      · obtain ⟨h_lo, h_hi⟩ := hd2
        obtain ⟨x, hx⟩ := PartialState.singletonMemU64_mem_isSome (vals + 8) len a ⟨h_lo, h_hi⟩
        have hPx : h_P_new.mem a = some x := (h_P_new_mem_d2 a ⟨h_lo, h_hi⟩).trans hx
        rw [PartialState.union_mem_of_left_some hPx] at hva
        rw [hexec_mem_outside a (by omega), hs_d2 a x hx ⟨h_lo, h_hi⟩]
        exact Option.some.inj hva
      by_cases hin : ptr ≤ a ∧ a < ptr + inputBytes.size
      · obtain ⟨h_lo, h_hi⟩ := hin
        have h_eq : a = ptr + (a - ptr) := by omega
        have h_lt : a - ptr < inputBytes.size := by omega
        rw [h_eq] at hva ⊢
        rw [PartialState.union_mem_of_left_some (h_P_new_mem_in _ h_lt)] at hva
        rw [hexec_mem_outside (ptr + (a - ptr)) (by omega), hs_in _ h_lt,
            ← (Option.some.inj hva)]
      · -- outside all owned regions: value comes from the frame
        have h_out_addr : a < out ∨ a ≥ out + 32 := by
          rcases Nat.lt_or_ge a out with h | h
          · left; exact h
          · rcases Nat.lt_or_ge a (out + 32) with h' | h'
            · exact absurd ⟨h, h'⟩ hou
            · right; exact h'
        rw [PartialState.union_mem_of_left_none
              (h_P_new_mem_outside a
                (by rcases Nat.lt_or_ge a vals with h | h
                    · exact Or.inl h
                    · rcases Nat.lt_or_ge a (vals + 8) with h' | h'
                      · exact absurd ⟨h, h'⟩ hd1
                      · exact Or.inr h')
                (by rcases Nat.lt_or_ge a (vals + 8) with h | h
                    · exact Or.inl h
                    · rcases Nat.lt_or_ge a (vals + 8 + 8) with h' | h'
                      · exact absurd ⟨h, h'⟩ hd2
                      · exact Or.inr h')
                (by rcases Nat.lt_or_ge a ptr with h | h
                    · exact Or.inl h
                    · rcases Nat.lt_or_ge a (ptr + inputBytes.size) with h' | h'
                      · exact absurd ⟨h, h'⟩ hin
                      · exact Or.inr h')
                h_out_addr)] at hva
        rw [hexec_mem_outside a h_out_addr]
        have h_P_none : h_P.mem a = none := by
          rcases hd_PR_mem a with hl | hr
          · exact hl
          · rw [hr] at hva; nomatch hva
        apply hcm_mem a v
        rw [← hu_PR, PartialState.union_mem_of_left_none h_P_none]
        exact hva
    · -- pc compat
      intro v hvp
      rw [PartialState.union_pc_of_left_none h_P_new_pc] at hvp
      rw [hR_no_pc] at hvp
      nomatch hvp
    · -- returnData compat
      intro rd hva
      rw [PartialState.union_returnData_of_left_none h_P_new_rd] at hva
      have h_P_rd_pre : h_P.returnData = none := by
        rw [← hu_r0_T1, ← hu_r1_T2, ← hu_r2_T3, ← hu_r3_T4, ← hu_d1_T5,
            ← hu_d2_T6, ← hu_in_out]
        rfl
      have hp_rd : hp.returnData = some rd := by
        rw [← hu_PR, PartialState.union_returnData_of_left_none h_P_rd_pre]
        exact hva
      rw [hexec_rd]
      exact hcompat.returnData rd hp_rd
    · -- callStack compat
      intro cs hva
      rw [PartialState.union_callStack_of_left_none h_P_new_cs] at hva
      have h_P_cs_pre : h_P.callStack = none := by
        rw [← hu_r0_T1, ← hu_r1_T2, ← hu_r2_T3, ← hu_r3_T4, ← hu_d1_T5,
            ← hu_d2_T6, ← hu_in_out]
        rfl
      have hp_cs : hp.callStack = some cs := by
        rw [← hu_PR, PartialState.union_callStack_of_left_none h_P_cs_pre]
        exact hva
      rw [hexec_cs]
      exact hcompat.callStack cs hp_cs
