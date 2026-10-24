-- Miscellaneous syscalls: alloc_free, remaining_compute_units (H7),
-- get_stack_height, processed_sibling_instruction, get_sysvar (SIMD-0127), unknown.

import SVM.SBPF.Machine
import SVM.Syscalls.SysvarData

namespace SVM.SBPF
namespace Misc

/-- Default CU charge for these (`sysvar_base_cost / syscall_base_cost = 100`). -/
def cu : Nat := 100

/-- Pure `(r0, heapNext)` step for `sol_alloc_free_`, decoupled so `execAllocFree`
    is a single record-update (keeps `execSyscall_preserves_*` trivially closable). -/
@[simp] def allocFreeStep (heapNext size freeFlag : Nat) : Nat × Nat :=
  let HEAP_START : Nat := 0x300000000
  let HEAP_SIZE  : Nat := 0x8000  -- 32 KiB
  if freeFlag ≠ 0 then
    -- Free is a no-op: agave's bump allocator only resets on the next invocation.
    (0, heapNext)
  else
    let aligned := if size % 8 = 0 then size else size + (8 - size % 8)
    let nextAfter := heapNext + aligned
    if nextAfter > HEAP_START + HEAP_SIZE then (0, heapNext)
    else (heapNext, nextAfter)

/-- `sol_alloc_free_`: bump allocator over the BPF program-local heap.
    ABI: r1 = size, r2 = free flag (0 = alloc, 1 = free); r0 = ptr or 0 on OOM.
    Aligns `size` up to 8, returns the current `heapNext`, bumps by the aligned
    size. Free is a no-op (agave resets the allocator per invocation, not within). -/
@[simp] def execAllocFree (s : State) : State :=
  let (newR0, newHeapNext) := allocFreeStep s.heapNext s.regs.r1 s.regs.r2
  { s with regs := s.regs.set .r0 newR0, heapNext := newHeapNext }

/-- `sol_remaining_compute_units`: real remaining budget in r0 (H7). agave consumes
    `syscall_base_cost` (100) first then returns `get_remaining()`, whose meter
    already includes this call insn; so remaining = `cuBudget − (cuConsumed + 1 +
    100)`, saturating at 0. Pre-H5 this was fail-open (r0 unchanged, false on chain). -/
@[simp] def execRemainingComputeUnits (s : State) : State :=
  { s with regs := s.regs.set .r0 (s.cuBudget - (s.cuConsumed + 1 + cu)) }

/-- `sol_get_stack_height`: top-level invocation depth = 1. -/
@[simp] def execGetStackHeight (s : State) : State :=
  { s with regs := s.regs.set .r0 1 }

/-- `sol_get_processed_sibling_instruction`: we don't track siblings, return 0. -/
@[simp] def execProcessedSibling (s : State) : State :=
  { s with regs := s.regs.set .r0 0 }

/-- `sol_get_sysvar(id_addr=r1, var_addr=r2, offset=r3, length=r4)` — SIMD-0127
    generic accessor, faithful to agave's `SyscallGetSysvar` in ITS check order:

    1. `var_addr ≥ MM_INPUT_START` → `ERR_ACCESS_VIOLATION`
       (`syscall_parameter_address_restrictions`, active under `all_enabled()`).
    2. H6: `[var_addr, +length)` must be writable (`translate_mut!`), then the
       32-byte id readable (`translate_type::<Pubkey>`), else `.accessViolation`.
    3. `offset+length` / `var_addr+length` overflowing u64 → `ERR_INVALID_LENGTH`.
    4. id not in cache → r0 := 2 (`SYSVAR_NOT_FOUND`, in-band; no abort).
    5. `offset+length > buf.size` → r0 := 1 (`OFFSET_LENGTH_EXCEEDS_SYSVAR`).
    6. else copy `buf[offset..offset+length)` to `*var_addr`, r0 := 0.

    Buffers are the Rust-pinned mollusk defaults in `SysvarData.lean`.
    H7: pre-fix this returned r0 := 0 WITHOUT writing the buffer (false on chain). -/
@[simp] def execGetSysvar (s : State) : State :=
  let idA  := s.regs.r1
  let outA := s.regs.r2
  let off  := s.regs.r3
  let len  := s.regs.r4
  if outA ≥ Memory.INPUT_START then
    { s with exitCode := some ERR_ACCESS_VIOLATION, vmError := some .accessViolation }
  else s.guardWrite outA len fun s =>
  s.guardRead idA 32 fun s =>
  if off + len ≥ U64_MODULUS ∨ outA + len ≥ U64_MODULUS then
    { s with exitCode := some ERR_INVALID_LENGTH, vmError := some .invalidLength }
  else
    match SysvarData.sysvarBuffer (readBytes s.mem idA 32) with
    | none => { s with regs := s.regs.set .r0 2 }
    | some buf =>
      if off + len > buf.size then
        { s with regs := s.regs.set .r0 1 }
      else
        let mem' : Memory.Mem := fun a =>
          if a ≥ outA ∧ a - outA < len then
            (buf.get! (off + (a - outA))).toNat
          else s.mem a
        { s with regs := s.regs.set .r0 0, mem := mem' }

/-- H6 fault direction, output slice: a non-empty `[r2, r2+r4)` outside a writable
    region traps (agave `translate_mut!` on `var_addr`). Pinned cross-engine by
    `oob_get_sysvar.so`. -/
theorem execGetSysvar_faults_oob_out (s : State)
    (hin : s.regs.r2 < Memory.INPUT_START) (hne : s.regs.r4 ≠ 0)
    (hoob : s.regions.containsWritable s.regs.r2 s.regs.r4 = false) :
    (execGetSysvar s).vmError = some .accessViolation ∧
    (execGetSysvar s).exitCode = some ERR_ACCESS_VIOLATION := by
  simp only [execGetSysvar, State.guardWrite, State.accessFault]
  rw [if_neg (Nat.not_le.mpr hin), if_neg (by
    rintro (h | h)
    · exact hne h
    · rw [hoob] at h; exact absurd h (by decide))]
  exact ⟨rfl, rfl⟩

/-- H6 fault direction, sysvar id: with the output slice writable, a 32-byte id
    at `r1` outside every region traps (agave `translate_type::<Pubkey>`). -/
theorem execGetSysvar_faults_oob_id (s : State)
    (hin : s.regs.r2 < Memory.INPUT_START)
    (hout : s.regs.r4 = 0 ∨ s.regions.containsWritable s.regs.r2 s.regs.r4 = true)
    (hoob : s.regions.containsRange s.regs.r1 32 = false) :
    (execGetSysvar s).vmError = some .accessViolation ∧
    (execGetSysvar s).exitCode = some ERR_ACCESS_VIOLATION := by
  simp only [execGetSysvar, State.guardWrite, State.guardRead, State.accessFault]
  rw [if_neg (Nat.not_le.mpr hin), if_pos hout, if_neg (by
    rintro (h | h)
    · exact absurd h (by decide)
    · rw [hoob] at h; exact absurd h (by decide))]
  exact ⟨rfl, rfl⟩

/-- Unknown / unregistered syscall hash. Agave rejects (`UnknownSyscall`); we fail
    closed rather than fabricate `r0 := 0` (which would let a proof continue past a
    call the real VM never runs). See docs/SOUNDNESS_AUDIT_* (H7). -/
@[simp] def execUnknown (s : State) : State :=
  { s with exitCode := some ERR_UNSUPPORTED_INSTRUCTION, vmError := some .unsupportedInstruction }

end Misc
end SVM.SBPF
