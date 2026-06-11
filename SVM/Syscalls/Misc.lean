-- Miscellaneous syscalls that don't fit elsewhere:
--   `sol_alloc_free_`           (deprecated; modern programs ship their own allocator)
--   `sol_remaining_compute_units` (writes the real remaining budget to r0 — H7)
--   `sol_get_stack_height`      (top-level = depth 1 — we don't model CPI)
--   `sol_get_processed_sibling_instruction` (we don't track sibling instrs)
--   `sol_get_sysvar`            (generic sysvar lookup — base cost only)
--   `.unknown _`                (any imm hash that doesn't match a known syscall)

import SVM.SBPF.Machine

namespace SVM.SBPF
namespace Misc

/-- Default CU charge for these (`sysvar_base_cost / syscall_base_cost = 100`). -/
def cu : Nat := 100

/-- Pure compute step for `sol_alloc_free_`: returns the new
    `(r0, heapNext)` pair without producing a State. Decoupled so
    `execAllocFree` can use a single top-level record-update —
    keeping `execSyscall_preserves_r10` / `_preserves_regions`
    closable by the standard "record-update doesn't touch unmentioned
    fields" rule. -/
@[simp] def allocFreeStep (heapNext size freeFlag : Nat) : Nat × Nat :=
  let HEAP_START : Nat := 0x300000000
  let HEAP_SIZE  : Nat := 0x8000  -- 32 KiB
  if freeFlag ≠ 0 then
    -- Free is a no-op; agave's bump allocator only resets on the next
    -- invocation. We leave r0 unchanged (caller can ignore it) and
    -- preserve heapNext.
    (0, heapNext)
  else
    let aligned := if size % 8 = 0 then size else size + (8 - size % 8)
    let nextAfter := heapNext + aligned
    if nextAfter > HEAP_START + HEAP_SIZE then (0, heapNext)
    else (heapNext, nextAfter)

/-- `sol_alloc_free_`: bump allocator over the BPF program-local heap.
    ABI: r1 = size, r2 = free flag (0 = alloc, 1 = free). Returns the
    allocated pointer (or 0 on OOM) in r0.

    Tier-2 #6 — agave's heap is `[MM_HEAP_START, MM_HEAP_START +
    heap_size)` (default 32 KiB). Each `sol_alloc_free_(size, 0)`
    aligns `size` up to 8 bytes, returns the current `heapNext`, and
    bumps it by the aligned size. Free is a no-op — agave resets the
    bump allocator on each invocation, not within one. The CPI
    handler resets `heapNext` to `MM_HEAP_START` on each sub-state. -/
@[simp] def execAllocFree (s : State) : State :=
  let (newR0, newHeapNext) := allocFreeStep s.heapNext s.regs.r1 s.regs.r2
  { s with regs := s.regs.set .r0 newR0, heapNext := newHeapNext }

/-- `sol_remaining_compute_units`: returns the REAL remaining compute
    budget in r0 (H7, unlocked by H5 total metering). agave consumes
    `syscall_base_cost` (100) first, then returns `get_remaining()`;
    the rbpf meter at that point already includes the call instruction
    itself. In our model `s.cuConsumed` at body time covers everything
    BEFORE this instruction, so remaining =
    `cuBudget − (cuConsumed + 1 [this insn's baseline] + 100 [base])`,
    saturating at 0 (Nat subtraction). Pre-H5 this was a fail-open
    no-op (r0 left unchanged — a lift could prove "r0 preserved"
    across the syscall, which is false on chain). -/
@[simp] def execRemainingComputeUnits (s : State) : State :=
  { s with regs := s.regs.set .r0 (s.cuBudget - (s.cuConsumed + 1 + cu)) }

/-- `sol_get_stack_height`: top-level invocation depth = 1. -/
@[simp] def execGetStackHeight (s : State) : State :=
  { s with regs := s.regs.set .r0 1 }

/-- `sol_get_processed_sibling_instruction`: we don't track siblings.
    Return 0. -/
@[simp] def execProcessedSibling (s : State) : State :=
  { s with regs := s.regs.set .r0 0 }

/-- `sol_get_sysvar` (generic lookup): return 0 (success, no data
    surfaced — the per-sysvar getters are the modeled path). -/
@[simp] def execGetSysvar (s : State) : State :=
  { s with regs := s.regs.set .r0 0 }

/-- Unknown / unregistered syscall hash. Agave rejects the program
    (`UnknownSyscall`); we fail closed with the same effect rather than
    fabricate success (`r0 := 0`), which would let a proof continue past
    a call the real VM never executes. See docs/SOUNDNESS_AUDIT_* (H7). -/
@[simp] def execUnknown (s : State) : State :=
  { s with exitCode := some ERR_UNSUPPORTED_INSTRUCTION }

end Misc
end SVM.SBPF
