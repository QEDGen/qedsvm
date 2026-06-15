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
    2. mem translation of `[var_addr, +length)` + 32-byte id — NOT modeled (H6).
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
  else if off + len ≥ U64_MODULUS ∨ outA + len ≥ U64_MODULUS then
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

/-- Unknown / unregistered syscall hash. Agave rejects (`UnknownSyscall`); we fail
    closed rather than fabricate `r0 := 0` (which would let a proof continue past a
    call the real VM never runs). See docs/SOUNDNESS_AUDIT_* (H7). -/
@[simp] def execUnknown (s : State) : State :=
  { s with exitCode := some ERR_UNSUPPORTED_INSTRUCTION, vmError := some .unsupportedInstruction }

end Misc
end SVM.SBPF
