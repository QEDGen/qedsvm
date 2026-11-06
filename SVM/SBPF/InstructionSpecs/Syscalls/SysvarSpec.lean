import SVM.SBPF.InstructionSpecs.Preamble

/-! # Functional sysvar specs (#105)

The state after each sysvar syscall body, for any environment `s.regions.sysvars`.
The separation-logic triples in `SysvarGeneral.lean` are proved from these. Each
syscall's CU is charged before its body, so a fault keeps it (`syscallCu`). -/

namespace SVM.SBPF

open Memory

/-! ## Typed getters -/

/-- A typed getter writes its bytes when the output is below the input region,
    writable and aligned. -/
theorem Sysvar.execTyped_ok (align size : Nat) (bytes : ByteArray) (s : State)
    (hin : s.regs.r1 < Memory.INPUT_START)
    (hw : s.regions.containsWritable s.regs.r1 size = true)
    (halign : s.regs.r1 % align = 0) :
    Sysvar.execTyped align size bytes s =
      { s with regs := s.regs.set .r0 0,
               mem := fun a =>
                 if a ≥ s.regs.r1 ∧ a - s.regs.r1 < size then (bytes.get! (a - s.regs.r1)).toNat
                 else s.mem a } := by
  simp only [Sysvar.execTyped, State.guardWrite]
  rw [if_neg (Nat.not_le.mpr hin), if_pos (Or.inr hw), if_neg (by omega)]

/-- An output in the input region faults, even a writable one. -/
theorem Sysvar.execTyped_faults_input (align size : Nat) (bytes : ByteArray) (s : State)
    (hin : Memory.INPUT_START ≤ s.regs.r1) :
    (Sysvar.execTyped align size bytes s).vmError = some .accessViolation ∧
    (Sysvar.execTyped align size bytes s).exitCode = some ERR_ACCESS_VIOLATION := by
  simp only [Sysvar.execTyped, State.accessFault]
  rw [if_pos hin]
  exact ⟨rfl, rfl⟩

/-- A writable output that isn't aligned for the sysvar's type faults. -/
theorem Sysvar.execTyped_faults_unaligned (align size : Nat) (bytes : ByteArray) (s : State)
    (hin : s.regs.r1 < Memory.INPUT_START)
    (hw : s.regions.containsWritable s.regs.r1 size = true)
    (halign : s.regs.r1 % align ≠ 0) :
    (Sysvar.execTyped align size bytes s).vmError = some .unalignedPointer ∧
    (Sysvar.execTyped align size bytes s).exitCode = some ERR_UNALIGNED_POINTER := by
  simp only [Sysvar.execTyped, State.guardWrite]
  rw [if_neg (Nat.not_le.mpr hin), if_pos (Or.inr hw), if_pos halign]
  exact ⟨rfl, rfl⟩

/-! ## `sol_get_epoch_stake` -/

theorem Sysvar.execEpochStake_null (s : State) (h : s.regs.r1 = 0) :
    Sysvar.execEpochStake s =
      { s with regs := s.regs.set .r0 (s.regions.sysvars.totalStake % U64_MODULUS) } := by
  simp only [Sysvar.execEpochStake]; rw [if_pos h]

theorem Sysvar.execEpochStake_vote (s : State) (h : s.regs.r1 ≠ 0)
    (hr : s.regions.containsRange s.regs.r1 32 = true) :
    Sysvar.execEpochStake s =
      let stake := s.regions.sysvars.stakeOf (readBytes s.mem s.regs.r1 32) % U64_MODULUS
      { s with regs := s.regs.set .r0 stake } := by
  simp only [Sysvar.execEpochStake, State.guardRead]
  rw [if_neg h, if_pos (Or.inr hr)]

theorem Sysvar.execEpochStake_faults (s : State) (h : s.regs.r1 ≠ 0)
    (hr : s.regions.containsRange s.regs.r1 32 = false) :
    (Sysvar.execEpochStake s).vmError = some .accessViolation ∧
    (Sysvar.execEpochStake s).exitCode = some ERR_ACCESS_VIOLATION := by
  simp only [Sysvar.execEpochStake, State.guardRead, State.accessFault]
  rw [if_neg h, if_neg (by
    rintro (h' | h')
    · exact absurd h' (by decide)
    · rw [hr] at h'; exact absurd h' (by decide))]
  exact ⟨rfl, rfl⟩

/-! ## `sol_get_sysvar`: past the fault checks -/

/-- What `sol_get_sysvar` requires of its arguments before it looks at the id. -/
structure Misc.GetSysvarArgsOk (s : State) : Prop where
  outBelowInput : s.regs.r2 < Memory.INPUT_START
  outWritable : s.regs.r4 = 0 ∨ s.regions.containsWritable s.regs.r2 s.regs.r4 = true
  idReadable : s.regions.containsRange s.regs.r1 32 = true
  noOverflow : s.regs.r3 + s.regs.r4 < U64_MODULUS ∧ s.regs.r2 + s.regs.r4 < U64_MODULUS

private theorem getSysvar_past_checks (s : State) (h : Misc.GetSysvarArgsOk s) :
    Misc.execGetSysvar s =
      match s.regions.sysvars.bincode (readBytes s.mem s.regs.r1 32) with
      | none => { s with regs := s.regs.set .r0 2 }
      | some buf =>
        if s.regs.r3 + s.regs.r4 > buf.size then { s with regs := s.regs.set .r0 1 }
        else
          { s with regs := s.regs.set .r0 0,
                   mem := fun a =>
                     if a ≥ s.regs.r2 ∧ a - s.regs.r2 < s.regs.r4 then
                       (buf.get! (s.regs.r3 + (a - s.regs.r2))).toNat
                     else s.mem a } := by
  simp only [Misc.execGetSysvar, State.guardWrite, State.guardRead]
  rw [if_neg (Nat.not_le.mpr h.outBelowInput), if_pos h.outWritable,
    if_pos (Or.inr h.idReadable), if_neg (by have := h.noOverflow; omega)]
  rfl

/-- An id outside the environment's sysvars is `SYSVAR_NOT_FOUND`, in-band. -/
theorem Misc.execGetSysvar_notFound (s : State) (h : Misc.GetSysvarArgsOk s)
    (hid : s.regions.sysvars.bincode (readBytes s.mem s.regs.r1 32) = none) :
    Misc.execGetSysvar s = { s with regs := s.regs.set .r0 2 } := by
  rw [getSysvar_past_checks s h, hid]

/-- A window past the sysvar's end is `OFFSET_LENGTH_EXCEEDS_SYSVAR`, in-band. -/
theorem Misc.execGetSysvar_outOfRange (s : State) (h : Misc.GetSysvarArgsOk s) (buf : ByteArray)
    (hid : s.regions.sysvars.bincode (readBytes s.mem s.regs.r1 32) = some buf)
    (hover : s.regs.r3 + s.regs.r4 > buf.size) :
    Misc.execGetSysvar s = { s with regs := s.regs.set .r0 1 } := by
  rw [getSysvar_past_checks s h, hid]
  simp only [if_pos hover]

/-- An output in the input region faults. -/
theorem Misc.execGetSysvar_faults_input (s : State) (hin : Memory.INPUT_START ≤ s.regs.r2) :
    (Misc.execGetSysvar s).vmError = some .accessViolation ∧
    (Misc.execGetSysvar s).exitCode = some ERR_ACCESS_VIOLATION := by
  simp only [Misc.execGetSysvar]
  rw [if_pos hin]
  exact ⟨rfl, rfl⟩

end SVM.SBPF
