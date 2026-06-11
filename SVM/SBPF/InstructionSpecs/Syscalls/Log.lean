import SVM.SBPF.InstructionSpecs.Syscalls.Helper

namespace SVM.SBPF

open Memory

/-! ## Syscall: `sol_log_`

`sol_log_(ptr, len)`: log a byte slice from `[r1..r1+r2)`, set `r0 := 0`.
Memory is read but not written; r1 and r2 are unchanged. `State.log` is
silent in `PartialState` by design. -/

theorem call_sol_log_spec (r0Old : Nat) (pc : Nat) (nCu : Nat)
    (h_step_cu : ∀ s : State,
        (step (.call .sol_log_) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_log_))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ 0) :=
  cuTripleWithin_syscall_writes_r0_only .sol_log_ 0 pc nCu
    (fun s => by simp [step, execSyscall, Logging.execLog])
    (fun s => by simp [step, execSyscall, Logging.execLog])
    (fun s => by simp [step, execSyscall, Logging.execLog])
    (fun s hex => by simp [step, execSyscall, Logging.execLog]; exact hex)
    (fun s => by simp [step, execSyscall, Logging.execLog])
    (fun s => by simp [step, execSyscall, Logging.execLog])
    (fun s => h_step_cu s)
    r0Old

/-! ## Syscall: `sol_log_pubkey`

`sol_log_pubkey(ptr)`: log 32 bytes from `[r1..r1+32)`, set `r0 := 0`.
Same single-atom shape as `sol_log_`. -/

theorem call_sol_log_pubkey_spec (r0Old : Nat) (pc : Nat) (nCu : Nat)
    (h_step_cu : ∀ s : State,
        (step (.call .sol_log_pubkey) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_log_pubkey))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ 0) :=
  cuTripleWithin_syscall_writes_r0_only .sol_log_pubkey 0 pc nCu
    (fun s => by simp [step, execSyscall, Logging.execLogPubkey])
    (fun s => by simp [step, execSyscall, Logging.execLogPubkey])
    (fun s => by simp [step, execSyscall, Logging.execLogPubkey])
    (fun s hex => by simp [step, execSyscall, Logging.execLogPubkey]; exact hex)
    (fun s => by simp [step, execSyscall, Logging.execLogPubkey])
    (fun s => by simp [step, execSyscall, Logging.execLogPubkey])
    (fun s => h_step_cu s)
    r0Old

/-! ## Syscall: `sol_get_stack_height`

Returns the current CPI depth in `r0`. Our model fixes this to `1`
(top-level) regardless of `State.callStack` — see `Misc.execGetStackHeight`. -/

theorem call_sol_get_stack_height_spec (r0Old : Nat) (pc : Nat) (nCu : Nat)
    (h_step_cu : ∀ s : State,
        (step (.call .sol_get_stack_height) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_get_stack_height))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ 1) :=
  cuTripleWithin_syscall_writes_r0_only .sol_get_stack_height 1 pc nCu
    (fun s => by simp [step, execSyscall, Misc.execGetStackHeight])
    (fun s => by simp [step, execSyscall, Misc.execGetStackHeight])
    (fun s => by simp [step, execSyscall, Misc.execGetStackHeight])
    (fun s hex => by simp [step, execSyscall, Misc.execGetStackHeight]; exact hex)
    (fun s => by simp [step, execSyscall, Misc.execGetStackHeight])
    (fun s => by simp [step, execSyscall, Misc.execGetStackHeight])
    (fun s => h_step_cu s)
    r0Old

/-! ## Syscall: `sol_log_64_`

`sol_log_64_(r1..r5)`: emit hex-formatted register dump. r0 := 0.
Memory unchanged. -/

theorem call_sol_log_64_spec (r0Old : Nat) (pc : Nat) (nCu : Nat)
    (h_step_cu : ∀ s : State,
        (step (.call .sol_log_64_) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_log_64_))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ 0) :=
  cuTripleWithin_syscall_writes_r0_only .sol_log_64_ 0 pc nCu
    (fun s => by simp [step, execSyscall, Logging.execLog64])
    (fun s => by simp [step, execSyscall, Logging.execLog64])
    (fun s => by simp [step, execSyscall, Logging.execLog64])
    (fun s hex => by simp [step, execSyscall, Logging.execLog64]; exact hex)
    (fun s => by simp [step, execSyscall, Logging.execLog64])
    (fun s => by simp [step, execSyscall, Logging.execLog64])
    (fun s => h_step_cu s)
    r0Old

/-! ## Syscall: `sol_log_compute_units_`

Emit "Program consumption: <remaining> units remaining". r0 := 0. -/

theorem call_sol_log_compute_units_spec (r0Old : Nat) (pc : Nat) (nCu : Nat)
    (h_step_cu : ∀ s : State,
        (step (.call .sol_log_compute_units_) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_log_compute_units_))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ 0) :=
  cuTripleWithin_syscall_writes_r0_only .sol_log_compute_units_ 0 pc nCu
    (fun s => by simp [step, execSyscall, Logging.execLogComputeUnits])
    (fun s => by simp [step, execSyscall, Logging.execLogComputeUnits])
    (fun s => by simp [step, execSyscall, Logging.execLogComputeUnits])
    (fun s hex => by simp [step, execSyscall, Logging.execLogComputeUnits]; exact hex)
    (fun s => by simp [step, execSyscall, Logging.execLogComputeUnits])
    (fun s => by simp [step, execSyscall, Logging.execLogComputeUnits])
    (fun s => h_step_cu s)
    r0Old

/-! ## Syscall: `sol_log_data`

`sol_log_data(fields_ptr, count)`: read `count` SliceDesc descriptors
from r1, base64-encode each slice they point to, emit joined message.
Memory is read (descriptors + each slice) but not written. r0 := 0. -/

theorem call_sol_log_data_spec (r0Old : Nat) (pc : Nat) (nCu : Nat)
    (h_step_cu : ∀ s : State,
        (step (.call .sol_log_data) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_log_data))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ 0) :=
  cuTripleWithin_syscall_writes_r0_only .sol_log_data 0 pc nCu
    (fun s => by simp [step, execSyscall, Logging.execLogData])
    (fun s => by simp [step, execSyscall, Logging.execLogData])
    (fun s => by simp [step, execSyscall, Logging.execLogData])
    (fun s hex => by simp [step, execSyscall, Logging.execLogData]; exact hex)
    (fun s => by simp [step, execSyscall, Logging.execLogData])
    (fun s => by simp [step, execSyscall, Logging.execLogData])
    (fun s => h_step_cu s)
    r0Old

/-! ## Syscall: `sol_get_epoch_stake`

Returns 0 in `r0` (stake not modeled). Memory unchanged. -/

theorem call_sol_get_epoch_stake_spec (r0Old : Nat) (pc : Nat) (nCu : Nat)
    (h_step_cu : ∀ s : State,
        (step (.call .sol_get_epoch_stake) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_get_epoch_stake))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ 0) :=
  cuTripleWithin_syscall_writes_r0_only .sol_get_epoch_stake 0 pc nCu
    (fun s => by simp [step, execSyscall, Sysvar.execEpochStake])
    (fun s => by simp [step, execSyscall, Sysvar.execEpochStake])
    (fun s => by simp [step, execSyscall, Sysvar.execEpochStake])
    (fun s hex => by simp [step, execSyscall, Sysvar.execEpochStake]; exact hex)
    (fun s => by simp [step, execSyscall, Sysvar.execEpochStake])
    (fun s => by simp [step, execSyscall, Sysvar.execEpochStake])
    (fun s => h_step_cu s)
    r0Old

/-! ## Syscall: `sol_get_processed_sibling_instruction`

Sibling-instruction tracking is not modeled; the syscall returns 0
in `r0` and otherwise leaves state unchanged. -/

theorem call_sol_get_processed_sibling_instruction_spec
    (r0Old : Nat) (pc : Nat) (nCu : Nat)
    (h_step_cu : ∀ s : State,
        (step (.call .sol_get_processed_sibling_instruction) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_get_processed_sibling_instruction))
      (.r0 ↦ᵣ r0Old)
      (.r0 ↦ᵣ 0) :=
  cuTripleWithin_syscall_writes_r0_only
    .sol_get_processed_sibling_instruction 0 pc nCu
    (fun s => by simp [step, execSyscall, Misc.execProcessedSibling])
    (fun s => by simp [step, execSyscall, Misc.execProcessedSibling])
    (fun s => by simp [step, execSyscall, Misc.execProcessedSibling])
    (fun s hex => by simp [step, execSyscall, Misc.execProcessedSibling]; exact hex)
    (fun s => by simp [step, execSyscall, Misc.execProcessedSibling])
    (fun s => by simp [step, execSyscall, Misc.execProcessedSibling])
    (fun s => h_step_cu s)
    r0Old

/-! ## Syscall: `sol_get_sysvar` (SIMD-0127 generic accessor)

`sol_get_sysvar(sysvar_id_addr = r1, var_addr = r2, offset = r3,
length = r4)`: looks the 32-byte id at `*r1` up in the (baked) sysvar
cache and copies `buf[offset..offset+length)` to `*r2`, returning 0.
This is the SUCCESS path — the spec owns the id bytes (read-only,
framed) and the output buffer; the post-state has `r0 = 0` and the
output buffer holding `slice` (the requested sysvar window, supplied
together with `hSlice` pinning it to `buf`).

H7: the pre-fix spec claimed `r0 := 0` with memory UNCHANGED — false
on chain (the real syscall fills the buffer). The hypotheses
discharge, in agave's check order: the `var_addr < MM_INPUT_START`
parameter restriction (`hOutAddr`), the u64 offset/length overflow
aborts (`hOffLen`/`hOutLen`), the cache hit (`hBuf` — use the
`SysvarData.sysvarBuffer_*` evaluation lemmas), and the in-range
window (`hInRange`). The `h_disj` hypothesis keeps the id read
disjoint from the output write (implicit in the sepConj but accepted
explicitly, as in `call_sol_get_return_data_spec`). -/

theorem call_sol_get_sysvar_spec
    (r0Old idA outA offV lenV : Nat)
    (idBytes buf slice bsOut : ByteArray) (pc : Nat) (nCu : Nat)
    (hIdSize : idBytes.size = 32)
    (hBuf : SysvarData.sysvarBuffer idBytes = some buf)
    (hInRange : offV + lenV ≤ buf.size)
    (hOutAddr : outA < Memory.INPUT_START)
    (hOffLen : offV + lenV < U64_MODULUS)
    (hOutLen : outA + lenV < U64_MODULUS)
    (hOutSize : bsOut.size = lenV)
    (hSliceSize : slice.size = lenV)
    (hSlice : ∀ i, i < lenV → slice.get! i = buf.get! (offV + i))
    (h_disj : idA + 32 ≤ outA ∨ outA + lenV ≤ idA)
    (hCu : ∀ s : State,
        (step (.call .sol_get_sysvar) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleWithin 1 nCu pc (pc + 1)
      (CodeReq.singleton pc (.call .sol_get_sysvar))
      ((.r0 ↦ᵣ r0Old) ** (.r1 ↦ᵣ idA) ** (.r2 ↦ᵣ outA) **
        (.r3 ↦ᵣ offV) ** (.r4 ↦ᵣ lenV) **
        (idA ↦Bytes32 idBytes) ** (outA ↦Bytes bsOut))
      ((.r0 ↦ᵣ 0) ** (.r1 ↦ᵣ idA) ** (.r2 ↦ᵣ outA) **
        (.r3 ↦ᵣ offV) ** (.r4 ↦ᵣ lenV) **
        (idA ↦Bytes32 idBytes) ** (outA ↦Bytes slice)) := by
  intro R hRfree fetch hcr s hPR hpc hex hbud
  -- ==== Phase 1: destructure the 7-atom precondition. ====
  obtain ⟨hp, hcompat, h_P, h_R, hd_PR, hu_PR, h_P_sat, h_R_sat⟩ := hPR
  obtain ⟨h_r0, h_T1, hd_r0_T1, hu_r0_T1, h_r0_pred, h_T1_sat⟩ := h_P_sat
  obtain ⟨h_r1, h_T2, hd_r1_T2, hu_r1_T2, h_r1_pred, h_T2_sat⟩ := h_T1_sat
  obtain ⟨h_r2, h_T3, hd_r2_T3, hu_r2_T3, h_r2_pred, h_T3_sat⟩ := h_T2_sat
  obtain ⟨h_r3, h_T4, hd_r3_T4, hu_r3_T4, h_r3_pred, h_T4_sat⟩ := h_T3_sat
  obtain ⟨h_r4, h_T5, hd_r4_T5, hu_r4_T5, h_r4_pred, h_T5_sat⟩ := h_T4_sat
  obtain ⟨h_id, h_out, hd_id_out, hu_id_out, h_id_pred, h_out_pred⟩ := h_T5_sat
  rw [h_r0_pred] at hu_r0_T1 hd_r0_T1
  rw [h_r1_pred] at hu_r1_T2 hd_r1_T2
  rw [h_r2_pred] at hu_r2_T3 hd_r2_T3
  rw [h_r3_pred] at hu_r3_T4 hd_r3_T4
  rw [h_r4_pred] at hu_r4_T5 hd_r4_T5
  rw [h_id_pred] at hu_id_out hd_id_out
  rw [h_out_pred] at hu_id_out hd_id_out
  clear h_r0_pred h_r1_pred h_r2_pred h_r3_pred h_r4_pred h_id_pred h_out_pred
  clear h_r0 h_r1 h_r2 h_r3 h_r4 h_id h_out
  have hcr_regs := hcompat.regs
  have hcm_mem := hcompat.mem
  -- ==== Phase 2: range-disjointness corollaries from h_disj. ====
  have h_id_out_disj (i : Nat) (hi : i < 32) :
      idA + i < outA ∨ idA + i ≥ outA + lenV := by
    rcases h_disj with h | h
    · left; omega
    · right; omega
  have h_out_id_disj (i : Nat) (hi : i < lenV) :
      outA + i < idA ∨ outA + i ≥ idA + 32 := by
    rcases h_disj with h | h
    · right; omega
    · left; omega
  -- ==== Phase 3: lift atom projections through hp. ====
  have h_P_regs_r0 : h_P.regs .r0 = some r0Old := by
    rw [← hu_r0_T1]
    exact PartialState.union_regs_of_left_some
      PartialState.singletonReg_regs_self
  have h_T1_regs_r1 : h_T1.regs .r1 = some idA := by
    rw [← hu_r1_T2]
    exact PartialState.union_regs_of_left_some
      PartialState.singletonReg_regs_self
  have h_T2_regs_r2 : h_T2.regs .r2 = some outA := by
    rw [← hu_r2_T3]
    exact PartialState.union_regs_of_left_some
      PartialState.singletonReg_regs_self
  have h_T3_regs_r3 : h_T3.regs .r3 = some offV := by
    rw [← hu_r3_T4]
    exact PartialState.union_regs_of_left_some
      PartialState.singletonReg_regs_self
  have h_T4_regs_r4 : h_T4.regs .r4 = some lenV := by
    rw [← hu_r4_T5]
    exact PartialState.union_regs_of_left_some
      PartialState.singletonReg_regs_self
  have h_P_regs_r1 : h_P.regs .r1 = some idA := by
    rw [← hu_r0_T1,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r1 ≠ Reg.r0))]
    exact h_T1_regs_r1
  have h_P_regs_r2 : h_P.regs .r2 = some outA := by
    rw [← hu_r0_T1,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r2 ≠ Reg.r0)),
        ← hu_r1_T2,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r2 ≠ Reg.r1))]
    exact h_T2_regs_r2
  have h_P_regs_r3 : h_P.regs .r3 = some offV := by
    rw [← hu_r0_T1,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r3 ≠ Reg.r0)),
        ← hu_r1_T2,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r3 ≠ Reg.r1)),
        ← hu_r2_T3,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r3 ≠ Reg.r2))]
    exact h_T3_regs_r3
  have h_P_regs_r4 : h_P.regs .r4 = some lenV := by
    rw [← hu_r0_T1,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r4 ≠ Reg.r0)),
        ← hu_r1_T2,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r4 ≠ Reg.r1)),
        ← hu_r2_T3,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r4 ≠ Reg.r2)),
        ← hu_r3_T4,
        PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r4 ≠ Reg.r3))]
    exact h_T4_regs_r4
  have hp_regs_r0 : hp.regs .r0 = some r0Old := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r0
  have hp_regs_r1 : hp.regs .r1 = some idA := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r1
  have hp_regs_r2 : hp.regs .r2 = some outA := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r2
  have hp_regs_r3 : hp.regs .r3 = some offV := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r3
  have hp_regs_r4 : hp.regs .r4 = some lenV := by
    rw [← hu_PR]; exact PartialState.union_regs_of_left_some h_P_regs_r4
  have hs_regs_r0 : s.regs.get .r0 = r0Old := hcr_regs .r0 r0Old hp_regs_r0
  have hs_regs_r1 : s.regs.get .r1 = idA := hcr_regs .r1 idA hp_regs_r1
  have hs_regs_r2 : s.regs.get .r2 = outA := hcr_regs .r2 outA hp_regs_r2
  have hs_regs_r3 : s.regs.get .r3 = offV := hcr_regs .r3 offV hp_regs_r3
  have hs_regs_r4 : s.regs.get .r4 = lenV := hcr_regs .r4 lenV hp_regs_r4
  have hs_r1_field : s.regs.r1 = idA := hs_regs_r1
  have hs_r2_field : s.regs.r2 = outA := hs_regs_r2
  have hs_r3_field : s.regs.r3 = offV := hs_regs_r3
  have hs_r4_field : s.regs.r4 = lenV := hs_regs_r4
  -- The id bytes at idA (through the Bytes32 atom).
  have h_P_mem_id (i : Nat) (hi : i < 32) :
      h_P.mem (idA + i) = some (idBytes.get! i).toNat := by
    rw [← hu_r0_T1,
        PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (idA + i)),
        ← hu_r1_T2,
        PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (idA + i)),
        ← hu_r2_T3,
        PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (idA + i)),
        ← hu_r3_T4,
        PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (idA + i)),
        ← hu_r4_T5,
        PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (idA + i)),
        ← hu_id_out]
    exact PartialState.union_mem_of_left_some
      (PartialState.singletonMem32Bytes_mem_at idA idBytes i hi)
  -- The output buffer bytes at outA.
  have h_P_mem_out (i : Nat) (hi : i < bsOut.size) :
      h_P.mem (outA + i) = some (bsOut.get! i).toNat := by
    have h_out_id_no : outA + i < idA ∨ outA + i ≥ idA + 32 := by
      have h_lt : i < lenV := by rw [← hOutSize]; exact hi
      exact h_out_id_disj i h_lt
    rw [← hu_r0_T1,
        PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (outA + i)),
        ← hu_r1_T2,
        PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (outA + i)),
        ← hu_r2_T3,
        PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (outA + i)),
        ← hu_r3_T4,
        PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (outA + i)),
        ← hu_r4_T5,
        PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (outA + i)),
        ← hu_id_out,
        PartialState.union_mem_of_left_none
          (PartialState.singletonMem32Bytes_mem_outside idA idBytes (outA + i) h_out_id_no)]
    exact PartialState.singletonMemBytes_mem_at outA bsOut i hi
  have hp_mem_id (i : Nat) (hi : i < 32) :
      hp.mem (idA + i) = some (idBytes.get! i).toNat := by
    rw [← hu_PR]; exact PartialState.union_mem_of_left_some (h_P_mem_id i hi)
  have hs_mem_id (i : Nat) (hi : i < 32) :
      s.mem (idA + i) = (idBytes.get! i).toNat :=
    hcm_mem (idA + i) _ (hp_mem_id i hi)
  -- ==== Phase 4: readBytes at idA recovers idBytes; executeFn shape. ====
  have h_readBytes : readBytes s.mem idA 32 = idBytes := by
    apply readBytes_eq_of_match s.mem idA 32 idBytes hIdSize
    intro i hi
    rw [hs_mem_id i hi]
    exact Nat.mod_eq_of_lt (idBytes.get! i).toNat_lt
  -- Branch dischargers, phrased on the raw register fields so they fire
  -- BEFORE the hs_*_field rewrites (agave's check order: parameter
  -- restriction, u64 overflows, cache hit, window in range).
  have h_if1 : ¬ (s.regs.r2 ≥ Memory.INPUT_START) := by
    rw [hs_r2_field]; exact Nat.not_le.mpr hOutAddr
  have h_if2 : ¬ (s.regs.r3 + s.regs.r4 ≥ U64_MODULUS
                  ∨ s.regs.r2 + s.regs.r4 ≥ U64_MODULUS) := by
    rw [hs_r2_field, hs_r3_field, hs_r4_field]
    rintro (h | h)
    · exact absurd h (Nat.not_le.mpr hOffLen)
    · exact absurd h (Nat.not_le.mpr hOutLen)
  have h_discr : SysvarData.sysvarBuffer (readBytes s.mem s.regs.r1 32)
      = some buf := by
    rw [hs_r1_field, h_readBytes]; exact hBuf
  have h_if3 : ¬ (s.regs.r3 + s.regs.r4 > buf.size) := by
    rw [hs_r3_field, hs_r4_field]; exact Nat.not_lt.mpr hInRange
  have hfetch : fetch s.pc = some (.call .sol_get_sysvar) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hstep_eq : executeFn fetch s 1 =
      chargeCu (step (.call .sol_get_sysvar) s) := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch, executeFn_zero]
  have hexec_regs : (executeFn fetch s 1).regs = s.regs.set .r0 0 := by
    rw [hstep_eq]; show ((Misc.execGetSysvar s).regs) = s.regs.set .r0 0
    simp only [Misc.execGetSysvar, if_neg h_if1, if_neg h_if2, h_discr,
               if_neg h_if3]
  have hexec_pc : (executeFn fetch s 1).pc = s.pc + 1 := by
    rw [hstep_eq]; rfl
  have hexec_exit : (executeFn fetch s 1).exitCode = none := by
    rw [hstep_eq]; show (Misc.execGetSysvar s).exitCode = none
    simp only [Misc.execGetSysvar, if_neg h_if1, if_neg h_if2, h_discr,
               if_neg h_if3]
    exact hex
  have hexec_rd : (executeFn fetch s 1).returnData = s.returnData := by
    rw [hstep_eq]; show (Misc.execGetSysvar s).returnData = s.returnData
    simp only [Misc.execGetSysvar, if_neg h_if1, if_neg h_if2, h_discr,
               if_neg h_if3]
  have hexec_cs : (executeFn fetch s 1).callStack = s.callStack := by
    rw [hstep_eq]; show (Misc.execGetSysvar s).callStack = s.callStack
    simp only [Misc.execGetSysvar, if_neg h_if1, if_neg h_if2, h_discr,
               if_neg h_if3]
  have hexec_mem_at_out (i : Nat) (hi : i < lenV) :
      (executeFn fetch s 1).mem (outA + i) = (buf.get! (offV + i)).toNat := by
    rw [hstep_eq]
    show ((Misc.execGetSysvar s).mem) (outA + i) = (buf.get! (offV + i)).toNat
    simp only [Misc.execGetSysvar, if_neg h_if1, if_neg h_if2, h_discr,
               if_neg h_if3]
    rw [Mem_read_default, hs_r2_field, hs_r3_field, hs_r4_field]
    rw [if_pos ⟨Nat.le_add_right _ _, by omega⟩,
        show outA + i - outA = i from by omega]
  have hexec_mem_outside (a : Nat)
      (h_out_addr : a < outA ∨ a ≥ outA + lenV) :
      (executeFn fetch s 1).mem a = s.mem a := by
    rw [hstep_eq]
    show ((Misc.execGetSysvar s).mem) a = s.mem a
    simp only [Misc.execGetSysvar, if_neg h_if1, if_neg h_if2, h_discr,
               if_neg h_if3]
    rw [Mem_read_default, hs_r2_field, hs_r3_field, hs_r4_field]
    rw [if_neg]
    rintro ⟨h1, h2⟩
    rcases h_out_addr with h | h <;> omega
  -- ==== Phase 5: facts about hR. ====
  have hd_PR_regs := hd_PR.regs
  have hd_PR_mem := hd_PR.mem
  have h_R_no_r0 : h_R.regs .r0 = none := by
    rcases hd_PR_regs .r0 with hl | hr
    · rw [h_P_regs_r0] at hl; nomatch hl
    · exact hr
  have h_R_no_r1 : h_R.regs .r1 = none := by
    rcases hd_PR_regs .r1 with hl | hr
    · rw [h_P_regs_r1] at hl; nomatch hl
    · exact hr
  have h_R_no_r2 : h_R.regs .r2 = none := by
    rcases hd_PR_regs .r2 with hl | hr
    · rw [h_P_regs_r2] at hl; nomatch hl
    · exact hr
  have h_R_no_r3 : h_R.regs .r3 = none := by
    rcases hd_PR_regs .r3 with hl | hr
    · rw [h_P_regs_r3] at hl; nomatch hl
    · exact hr
  have h_R_no_r4 : h_R.regs .r4 = none := by
    rcases hd_PR_regs .r4 with hl | hr
    · rw [h_P_regs_r4] at hl; nomatch hl
    · exact hr
  have h_R_no_pc : h_R.pc = none := hRfree _ h_R_sat
  have h_R_no_mem_out (i : Nat) (hi : i < bsOut.size) :
      h_R.mem (outA + i) = none := by
    rcases hd_PR_mem (outA + i) with hl | hr
    · rw [h_P_mem_out i hi] at hl; nomatch hl
    · exact hr
  have h_R_no_mem_id (i : Nat) (hi : i < 32) :
      h_R.mem (idA + i) = none := by
    rcases hd_PR_mem (idA + i) with hl | hr
    · rw [h_P_mem_id i hi] at hl; nomatch hl
    · exact hr
  -- P owns no returnData / callStack (all atoms are regs/mem).
  have h_P_rd_pre : h_P.returnData = none := by
    rw [← hu_r0_T1, ← hu_r1_T2, ← hu_r2_T3, ← hu_r3_T4, ← hu_r4_T5,
        ← hu_id_out]
    rfl
  have h_P_cs_pre : h_P.callStack = none := by
    rw [← hu_r0_T1, ← hu_r1_T2, ← hu_r2_T3, ← hu_r3_T4, ← hu_r4_T5,
        ← hu_id_out]
    rfl
  -- ==== Phase 6: build the post heap. ====
  let h_r0_new : PartialState := PartialState.singletonReg .r0 0
  let h_r1_new : PartialState := PartialState.singletonReg .r1 idA
  let h_r2_new : PartialState := PartialState.singletonReg .r2 outA
  let h_r3_new : PartialState := PartialState.singletonReg .r3 offV
  let h_r4_new : PartialState := PartialState.singletonReg .r4 lenV
  let h_id_new : PartialState := PartialState.singletonMem32Bytes idA idBytes
  let h_out_new : PartialState := PartialState.singletonMemBytes outA slice
  let h_T5_new : PartialState := h_id_new.union h_out_new
  let h_T4_new : PartialState := h_r4_new.union h_T5_new
  let h_T3_new : PartialState := h_r3_new.union h_T4_new
  let h_T2_new : PartialState := h_r2_new.union h_T3_new
  let h_T1_new : PartialState := h_r1_new.union h_T2_new
  let h_P_new : PartialState := h_r0_new.union h_T1_new
  have hd_id_out_new : h_id_new.Disjoint h_out_new :=
    { regs := fun r => Or.inl (PartialState.singletonMem32Bytes_regs r)
      mem  := fun a => by
        by_cases ha : idA ≤ a ∧ a < idA + 32
        · right
          obtain ⟨h_lo, h_hi⟩ := ha
          apply PartialState.singletonMemBytes_mem_outside
          have h_lt : a - idA < 32 := by omega
          rcases h_id_out_disj (a - idA) h_lt with h | h
          · left; rw [hSliceSize] at *; omega
          · right; rw [hSliceSize]; omega
        · left
          apply PartialState.singletonMem32Bytes_mem_outside
          rcases Nat.lt_or_ge a idA with h' | h'
          · left; exact h'
          · rcases Nat.lt_or_ge a (idA + 32) with h'' | h''
            · exact absurd ⟨h', h''⟩ ha
            · right; exact h''
      pc   := Or.inl PartialState.singletonMem32Bytes_pc
      returnData := Or.inl PartialState.singletonMem32Bytes_returnData
      callStack := Or.inl PartialState.singletonMem32Bytes_callStack }
  have hd_r4_T5_new : h_r4_new.Disjoint h_T5_new := by
    refine
      { regs := fun r => ?_
        mem  := fun a => Or.inl (PartialState.singletonReg_mem a)
        pc   := Or.inl PartialState.singletonReg_pc
        returnData := Or.inl PartialState.singletonReg_returnData
        callStack := Or.inl PartialState.singletonReg_callStack }
    by_cases hr : r = .r4
    · right; rw [hr]
      show (h_id_new.union h_out_new).regs .r4 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonMem32Bytes_regs .r4)]
      exact PartialState.singletonMemBytes_regs .r4
    · left; exact PartialState.singletonReg_regs_other hr
  have hd_r3_T4_new : h_r3_new.Disjoint h_T4_new := by
    refine
      { regs := fun r => ?_
        mem  := fun a => Or.inl (PartialState.singletonReg_mem a)
        pc   := Or.inl PartialState.singletonReg_pc
        returnData := Or.inl PartialState.singletonReg_returnData
        callStack := Or.inl PartialState.singletonReg_callStack }
    by_cases hr : r = .r3
    · right; rw [hr]
      show (h_r4_new.union h_T5_new).regs .r3 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r3 ≠ Reg.r4))]
      show (h_id_new.union h_out_new).regs .r3 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonMem32Bytes_regs .r3)]
      exact PartialState.singletonMemBytes_regs .r3
    · left; exact PartialState.singletonReg_regs_other hr
  have hd_r2_T3_new : h_r2_new.Disjoint h_T3_new := by
    refine
      { regs := fun r => ?_
        mem  := fun a => Or.inl (PartialState.singletonReg_mem a)
        pc   := Or.inl PartialState.singletonReg_pc
        returnData := Or.inl PartialState.singletonReg_returnData
        callStack := Or.inl PartialState.singletonReg_callStack }
    by_cases hr : r = .r2
    · right; rw [hr]
      show (h_r3_new.union h_T4_new).regs .r2 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r2 ≠ Reg.r3))]
      show (h_r4_new.union h_T5_new).regs .r2 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r2 ≠ Reg.r4))]
      show (h_id_new.union h_out_new).regs .r2 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonMem32Bytes_regs .r2)]
      exact PartialState.singletonMemBytes_regs .r2
    · left; exact PartialState.singletonReg_regs_other hr
  have hd_r1_T2_new : h_r1_new.Disjoint h_T2_new := by
    refine
      { regs := fun r => ?_
        mem  := fun a => Or.inl (PartialState.singletonReg_mem a)
        pc   := Or.inl PartialState.singletonReg_pc
        returnData := Or.inl PartialState.singletonReg_returnData
        callStack := Or.inl PartialState.singletonReg_callStack }
    by_cases hr : r = .r1
    · right; rw [hr]
      show (h_r2_new.union h_T3_new).regs .r1 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r1 ≠ Reg.r2))]
      show (h_r3_new.union h_T4_new).regs .r1 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r1 ≠ Reg.r3))]
      show (h_r4_new.union h_T5_new).regs .r1 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r1 ≠ Reg.r4))]
      show (h_id_new.union h_out_new).regs .r1 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonMem32Bytes_regs .r1)]
      exact PartialState.singletonMemBytes_regs .r1
    · left; exact PartialState.singletonReg_regs_other hr
  have hd_r0_T1_new : h_r0_new.Disjoint h_T1_new := by
    refine
      { regs := fun r => ?_
        mem  := fun a => Or.inl (PartialState.singletonReg_mem a)
        pc   := Or.inl PartialState.singletonReg_pc
        returnData := Or.inl PartialState.singletonReg_returnData
        callStack := Or.inl PartialState.singletonReg_callStack }
    by_cases hr : r = .r0
    · right; rw [hr]
      show (h_r1_new.union h_T2_new).regs .r0 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r0 ≠ Reg.r1))]
      show (h_r2_new.union h_T3_new).regs .r0 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r0 ≠ Reg.r2))]
      show (h_r3_new.union h_T4_new).regs .r0 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r0 ≠ Reg.r3))]
      show (h_r4_new.union h_T5_new).regs .r0 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonReg_regs_other (by decide : Reg.r0 ≠ Reg.r4))]
      show (h_id_new.union h_out_new).regs .r0 = none
      rw [PartialState.union_regs_of_left_none
            (PartialState.singletonMem32Bytes_regs .r0)]
      exact PartialState.singletonMemBytes_regs .r0
    · left; exact PartialState.singletonReg_regs_other hr
  -- Per-field projections of h_P_new.
  have h_P_new_regs_r0 : h_P_new.regs .r0 = some 0 := by
    show (h_r0_new.union h_T1_new).regs .r0 = some 0
    exact PartialState.union_regs_of_left_some
      PartialState.singletonReg_regs_self
  have h_P_new_regs_r1 : h_P_new.regs .r1 = some idA := by
    show (h_r0_new.union h_T1_new).regs .r1 = some idA
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r1 ≠ Reg.r0))]
    show (h_r1_new.union h_T2_new).regs .r1 = some idA
    exact PartialState.union_regs_of_left_some
      PartialState.singletonReg_regs_self
  have h_P_new_regs_r2 : h_P_new.regs .r2 = some outA := by
    show (h_r0_new.union h_T1_new).regs .r2 = some outA
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r2 ≠ Reg.r0))]
    show (h_r1_new.union h_T2_new).regs .r2 = some outA
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r2 ≠ Reg.r1))]
    show (h_r2_new.union h_T3_new).regs .r2 = some outA
    exact PartialState.union_regs_of_left_some
      PartialState.singletonReg_regs_self
  have h_P_new_regs_r3 : h_P_new.regs .r3 = some offV := by
    show (h_r0_new.union h_T1_new).regs .r3 = some offV
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r3 ≠ Reg.r0))]
    show (h_r1_new.union h_T2_new).regs .r3 = some offV
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r3 ≠ Reg.r1))]
    show (h_r2_new.union h_T3_new).regs .r3 = some offV
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r3 ≠ Reg.r2))]
    show (h_r3_new.union h_T4_new).regs .r3 = some offV
    exact PartialState.union_regs_of_left_some
      PartialState.singletonReg_regs_self
  have h_P_new_regs_r4 : h_P_new.regs .r4 = some lenV := by
    show (h_r0_new.union h_T1_new).regs .r4 = some lenV
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r4 ≠ Reg.r0))]
    show (h_r1_new.union h_T2_new).regs .r4 = some lenV
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r4 ≠ Reg.r1))]
    show (h_r2_new.union h_T3_new).regs .r4 = some lenV
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r4 ≠ Reg.r2))]
    show (h_r3_new.union h_T4_new).regs .r4 = some lenV
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other (by decide : Reg.r4 ≠ Reg.r3))]
    show (h_r4_new.union h_T5_new).regs .r4 = some lenV
    exact PartialState.union_regs_of_left_some
      PartialState.singletonReg_regs_self
  have h_P_new_regs_other (r : Reg)
      (h0 : r ≠ .r0) (h1 : r ≠ .r1) (h2 : r ≠ .r2) (h3 : r ≠ .r3)
      (h4 : r ≠ .r4) :
      h_P_new.regs r = none := by
    show (h_r0_new.union h_T1_new).regs r = none
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other h0)]
    show (h_r1_new.union h_T2_new).regs r = none
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other h1)]
    show (h_r2_new.union h_T3_new).regs r = none
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other h2)]
    show (h_r3_new.union h_T4_new).regs r = none
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other h3)]
    show (h_r4_new.union h_T5_new).regs r = none
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonReg_regs_other h4)]
    show (h_id_new.union h_out_new).regs r = none
    rw [PartialState.union_regs_of_left_none
          (PartialState.singletonMem32Bytes_regs r)]
    exact PartialState.singletonMemBytes_regs r
  have h_P_new_mem_at_id (i : Nat) (hi : i < 32) :
      h_P_new.mem (idA + i) = some (idBytes.get! i).toNat := by
    show (h_r0_new.union h_T1_new).mem (idA + i) = some (idBytes.get! i).toNat
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (idA + i))]
    show (h_r1_new.union h_T2_new).mem (idA + i) = some (idBytes.get! i).toNat
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (idA + i))]
    show (h_r2_new.union h_T3_new).mem (idA + i) = some (idBytes.get! i).toNat
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (idA + i))]
    show (h_r3_new.union h_T4_new).mem (idA + i) = some (idBytes.get! i).toNat
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (idA + i))]
    show (h_r4_new.union h_T5_new).mem (idA + i) = some (idBytes.get! i).toNat
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (idA + i))]
    show (h_id_new.union h_out_new).mem (idA + i) = some (idBytes.get! i).toNat
    exact PartialState.union_mem_of_left_some
      (PartialState.singletonMem32Bytes_mem_at idA idBytes i hi)
  have h_P_new_mem_at_out (i : Nat) (hi : i < lenV) :
      h_P_new.mem (outA + i) = some (slice.get! i).toNat := by
    have h_out_id_no : outA + i < idA ∨ outA + i ≥ idA + 32 :=
      h_out_id_disj i hi
    have h_lt_slice : i < slice.size := by rw [hSliceSize]; exact hi
    show (h_r0_new.union h_T1_new).mem (outA + i) = some (slice.get! i).toNat
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (outA + i))]
    show (h_r1_new.union h_T2_new).mem (outA + i) = some (slice.get! i).toNat
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (outA + i))]
    show (h_r2_new.union h_T3_new).mem (outA + i) = some (slice.get! i).toNat
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (outA + i))]
    show (h_r3_new.union h_T4_new).mem (outA + i) = some (slice.get! i).toNat
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (outA + i))]
    show (h_r4_new.union h_T5_new).mem (outA + i) = some (slice.get! i).toNat
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonReg_mem (outA + i))]
    show (h_id_new.union h_out_new).mem (outA + i) = some (slice.get! i).toNat
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonMem32Bytes_mem_outside idA idBytes (outA + i) h_out_id_no)]
    exact PartialState.singletonMemBytes_mem_at outA slice i h_lt_slice
  have h_P_new_mem_outside (a : Nat)
      (h_out_addr : a < outA ∨ a ≥ outA + lenV)
      (h_id_addr : a < idA ∨ a ≥ idA + 32) :
      h_P_new.mem a = none := by
    have h_out_slice : a < outA ∨ a ≥ outA + slice.size := by
      rw [hSliceSize]; exact h_out_addr
    show (h_r0_new.union h_T1_new).mem a = none
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
    show (h_r1_new.union h_T2_new).mem a = none
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
    show (h_r2_new.union h_T3_new).mem a = none
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
    show (h_r3_new.union h_T4_new).mem a = none
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
    show (h_r4_new.union h_T5_new).mem a = none
    rw [PartialState.union_mem_of_left_none (PartialState.singletonReg_mem a)]
    show (h_id_new.union h_out_new).mem a = none
    rw [PartialState.union_mem_of_left_none
          (PartialState.singletonMem32Bytes_mem_outside idA idBytes a h_id_addr)]
    exact PartialState.singletonMemBytes_mem_outside outA slice a h_out_slice
  have h_P_new_pc : h_P_new.pc = none := by
    show (h_r0_new.union h_T1_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    show (h_r1_new.union h_T2_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    show (h_r2_new.union h_T3_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    show (h_r3_new.union h_T4_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    show (h_r4_new.union h_T5_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonReg_pc]
    show (h_id_new.union h_out_new).pc = none
    rw [PartialState.union_pc_of_left_none PartialState.singletonMem32Bytes_pc]
    exact PartialState.singletonMemBytes_pc
  have h_P_new_rd_none : h_P_new.returnData = none := by
    show ((PartialState.singletonReg .r0 0).union
            ((PartialState.singletonReg .r1 idA).union
              ((PartialState.singletonReg .r2 outA).union
                ((PartialState.singletonReg .r3 offV).union
                  ((PartialState.singletonReg .r4 lenV).union
                    ((PartialState.singletonMem32Bytes idA idBytes).union
                      (PartialState.singletonMemBytes outA slice))))))).returnData
        = none
    rfl
  have h_P_new_cs_none : h_P_new.callStack = none := by
    show ((PartialState.singletonReg .r0 0).union
            ((PartialState.singletonReg .r1 idA).union
              ((PartialState.singletonReg .r2 outA).union
                ((PartialState.singletonReg .r3 offV).union
                  ((PartialState.singletonReg .r4 lenV).union
                    ((PartialState.singletonMem32Bytes idA idBytes).union
                      (PartialState.singletonMemBytes outA slice))))))).callStack
        = none
    rfl
  -- ==== Phase 7: outer disjointness h_P_new ⫫ h_R. ====
  have hd_PnewR : h_P_new.Disjoint h_R :=
    { regs := fun r => by
        by_cases h0 : r = .r0
        · right; rw [h0]; exact h_R_no_r0
        by_cases h1 : r = .r1
        · right; rw [h1]; exact h_R_no_r1
        by_cases h2 : r = .r2
        · right; rw [h2]; exact h_R_no_r2
        by_cases h3 : r = .r3
        · right; rw [h3]; exact h_R_no_r3
        by_cases h4 : r = .r4
        · right; rw [h4]; exact h_R_no_r4
        · left; exact h_P_new_regs_other r h0 h1 h2 h3 h4
      mem := fun a => by
        by_cases ha : outA ≤ a ∧ a < outA + lenV
        · right
          obtain ⟨h_lo, h_hi⟩ := ha
          have h_eq : a = outA + (a - outA) := by omega
          have h_lt : a - outA < lenV := by omega
          have h_lt_bsOut : a - outA < bsOut.size := by
            rw [hOutSize]; exact h_lt
          rw [h_eq]; exact h_R_no_mem_out _ h_lt_bsOut
        · by_cases hb : idA ≤ a ∧ a < idA + 32
          · right
            obtain ⟨h_lo, h_hi⟩ := hb
            have h_eq : a = idA + (a - idA) := by omega
            have h_lt : a - idA < 32 := by omega
            rw [h_eq]; exact h_R_no_mem_id _ h_lt
          · left
            apply h_P_new_mem_outside
            · rcases Nat.lt_or_ge a outA with h | h
              · left; exact h
              · rcases Nat.lt_or_ge a (outA + lenV) with h' | h'
                · exact absurd ⟨h, h'⟩ ha
                · right; exact h'
            · rcases Nat.lt_or_ge a idA with h | h
              · left; exact h
              · rcases Nat.lt_or_ge a (idA + 32) with h' | h'
                · exact absurd ⟨h, h'⟩ hb
                · right; exact h'
      pc := Or.inl h_P_new_pc
      returnData := Or.inl h_P_new_rd_none
      callStack := Or.inl h_P_new_cs_none }
  -- ==== Phase 8: assemble the witness. ====
  refine ⟨1, Nat.le_refl 1, ?_, hexec_exit, ?_, ?_⟩
  · rw [hexec_pc, hpc]
  · rw [hstep_eq]
    show (step (.call .sol_get_sysvar) s).cuConsumed + 1
        ≤ s.cuConsumed + 1 + nCu
    have := hCu s; omega
  · refine ⟨h_P_new.union h_R, ?_, h_P_new, h_R, hd_PnewR, rfl,
            ⟨h_r0_new, h_T1_new, hd_r0_T1_new, rfl, rfl,
             h_r1_new, h_T2_new, hd_r1_T2_new, rfl, rfl,
             h_r2_new, h_T3_new, hd_r2_T3_new, rfl, rfl,
             h_r3_new, h_T4_new, hd_r3_T4_new, rfl, rfl,
             h_r4_new, h_T5_new, hd_r4_T5_new, rfl, rfl,
             h_id_new, h_out_new, hd_id_out_new, rfl, rfl, rfl⟩,
            h_R_sat⟩
    refine
      { regs := ?_, mem := ?_, pc := ?_, returnData := ?_, callStack := ?_ }
    · intro r v hvr
      by_cases h0 : r = .r0
      · rw [h0] at hvr
        rw [PartialState.union_regs_of_left_some h_P_new_regs_r0] at hvr
        have hv0 : v = 0 := (Option.some.inj hvr).symm
        rw [h0, hexec_regs, hv0]
        exact RegFile.get_set_self _ _ _ (by decide : (.r0 : Reg) ≠ .r10)
      by_cases h1 : r = .r1
      · rw [h1] at hvr
        rw [PartialState.union_regs_of_left_some h_P_new_regs_r1] at hvr
        have hv1 : v = idA := (Option.some.inj hvr).symm
        rw [h1, hexec_regs, hv1,
            RegFile.get_set_diff _ _ _ _ (by decide : (.r1 : Reg) ≠ .r0)]
        exact hs_regs_r1
      by_cases h2 : r = .r2
      · rw [h2] at hvr
        rw [PartialState.union_regs_of_left_some h_P_new_regs_r2] at hvr
        have hv2 : v = outA := (Option.some.inj hvr).symm
        rw [h2, hexec_regs, hv2,
            RegFile.get_set_diff _ _ _ _ (by decide : (.r2 : Reg) ≠ .r0)]
        exact hs_regs_r2
      by_cases h3 : r = .r3
      · rw [h3] at hvr
        rw [PartialState.union_regs_of_left_some h_P_new_regs_r3] at hvr
        have hv3 : v = offV := (Option.some.inj hvr).symm
        rw [h3, hexec_regs, hv3,
            RegFile.get_set_diff _ _ _ _ (by decide : (.r3 : Reg) ≠ .r0)]
        exact hs_regs_r3
      by_cases h4 : r = .r4
      · rw [h4] at hvr
        rw [PartialState.union_regs_of_left_some h_P_new_regs_r4] at hvr
        have hv4 : v = lenV := (Option.some.inj hvr).symm
        rw [h4, hexec_regs, hv4,
            RegFile.get_set_diff _ _ _ _ (by decide : (.r4 : Reg) ≠ .r0)]
        exact hs_regs_r4
      · rw [PartialState.union_regs_of_left_none
              (h_P_new_regs_other r h0 h1 h2 h3 h4)] at hvr
        rw [hexec_regs, RegFile.get_set_diff _ _ _ _ h0]
        have h_P_none : h_P.regs r = none := by
          rcases hd_PR_regs r with hl | hr
          · exact hl
          · rw [hr] at hvr; nomatch hvr
        apply hcr_regs r v
        rw [← hu_PR, PartialState.union_regs_of_left_none h_P_none]
        exact hvr
    · intro a v hva
      by_cases ha : outA ≤ a ∧ a < outA + lenV
      · obtain ⟨h_lo, h_hi⟩ := ha
        have h_eq : a = outA + (a - outA) := by omega
        have h_lt : a - outA < lenV := by omega
        rw [h_eq] at hva ⊢
        rw [PartialState.union_mem_of_left_some
              (h_P_new_mem_at_out _ h_lt)] at hva
        have hveq : v = (slice.get! (a - outA)).toNat :=
          (Option.some.inj hva).symm
        rw [hexec_mem_at_out _ h_lt, hveq, hSlice _ h_lt]
      · by_cases hb : idA ≤ a ∧ a < idA + 32
        · obtain ⟨h_lo, h_hi⟩ := hb
          have h_eq : a = idA + (a - idA) := by omega
          have h_lt : a - idA < 32 := by omega
          rw [h_eq] at hva ⊢
          rw [PartialState.union_mem_of_left_some
                (h_P_new_mem_at_id _ h_lt)] at hva
          have hveq : v = (idBytes.get! (a - idA)).toNat :=
            (Option.some.inj hva).symm
          have h_id_out_no : idA + (a - idA) < outA
              ∨ idA + (a - idA) ≥ outA + lenV := h_id_out_disj _ h_lt
          rw [hexec_mem_outside _ h_id_out_no, hveq]
          exact hs_mem_id _ h_lt
        · have h_out_addr : a < outA ∨ a ≥ outA + lenV := by
            rcases Nat.lt_or_ge a outA with h | h
            · left; exact h
            · rcases Nat.lt_or_ge a (outA + lenV) with h' | h'
              · exact absurd ⟨h, h'⟩ ha
              · right; exact h'
          have h_id_addr : a < idA ∨ a ≥ idA + 32 := by
            rcases Nat.lt_or_ge a idA with h | h
            · left; exact h
            · rcases Nat.lt_or_ge a (idA + 32) with h' | h'
              · exact absurd ⟨h, h'⟩ hb
              · right; exact h'
          rw [PartialState.union_mem_of_left_none
                (h_P_new_mem_outside a h_out_addr h_id_addr)] at hva
          rw [hexec_mem_outside a h_out_addr]
          have h_P_none : h_P.mem a = none := by
            rcases hd_PR_mem a with hl | hr
            · exact hl
            · rw [hr] at hva; nomatch hva
          apply hcm_mem a v
          rw [← hu_PR, PartialState.union_mem_of_left_none h_P_none]
          exact hva
    · intro v hvp
      rw [PartialState.union_pc_of_left_none h_P_new_pc] at hvp
      rw [h_R_no_pc] at hvp
      nomatch hvp
    · intro rd hva
      rw [PartialState.union_returnData_of_left_none h_P_new_rd_none] at hva
      have hp_rd : hp.returnData = some rd := by
        rw [← hu_PR, PartialState.union_returnData_of_left_none h_P_rd_pre]
        exact hva
      rw [hexec_rd]
      exact hcompat.returnData rd hp_rd
    · intro cs hva
      rw [PartialState.union_callStack_of_left_none h_P_new_cs_none] at hva
      have hp_cs : hp.callStack = some cs := by
        rw [← hu_PR, PartialState.union_callStack_of_left_none h_P_cs_pre]
        exact hva
      rw [hexec_cs]
      exact hcompat.callStack cs hp_cs

/-! ## Syscall: `.unknown` (unrecognized hash)

For any unrecognized / unregistered syscall hash agave rejects the
program; we fail closed with the same effect (`exitCode :=
ERR_UNSUPPORTED_INSTRUCTION`) rather than fabricate success. A lift that
reaches an unknown syscall therefore proves an ABORT. See
docs/SOUNDNESS_AUDIT_* (H7). -/

theorem call_sol_unknown_aborts_spec (hash : Nat) (pc : Nat) (nCu : Nat)
    (hCu : ∀ s : State,
        (step (.call (.unknown hash)) s).cuConsumed ≤ s.cuConsumed + nCu) :
    cuTripleAbortsWithin 1 nCu pc
      (CodeReq.singleton pc (.call (.unknown hash)))
      emp ERR_UNSUPPORTED_INSTRUCTION := by
  intro R hRfree fetch hcr s hPR hpc hex hbud
  obtain ⟨hp, hcompat, h1, hR, hd, hu, hP1, hRsat⟩ := hPR
  rw [hP1, PartialState.union_empty_left] at hu
  rw [hP1] at hd
  clear hP1 h1
  have hfetch : fetch s.pc = some (.call (.unknown hash)) := by
    rw [hpc]; exact hcr pc _ CodeReq.singleton_self
  have hstep_eq : executeFn fetch s 1 = chargeCu (step (.call (.unknown hash)) s) := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch, executeFn_zero]
  have hexec : executeFn fetch s 1 = chargeCu
      { (Misc.execUnknown s) with pc := s.pc + 1
                                  cuConsumed := (Misc.execUnknown s).cuConsumed
                                    + syscallCu (.unknown hash) s } := by
    rw [show (1 : Nat) = 0 + 1 from rfl,
        executeFn_step fetch s 0 _ hex (by omega) hfetch, executeFn_zero]
    simp only [step, execSyscall]
  refine ⟨1, Nat.le_refl 1, ?_, ?_⟩
  · rw [hexec]
    show (Misc.execUnknown s).exitCode = some ERR_UNSUPPORTED_INSTRUCTION
    rfl
  · rw [hstep_eq]
    show (step (.call (.unknown hash)) s).cuConsumed + 1 ≤ s.cuConsumed + 1 + nCu
    have := hCu s; omega


end SVM.SBPF
