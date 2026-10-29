-- Memory-operation syscalls: `sol_memcpy`, `sol_memmove`, `sol_memset`,
-- `sol_memcmp`. CU charge is shared: `mem_op_consume = max(10, n / 250)`.

import SVM.SBPF.Machine

namespace SVM.SBPF
namespace MemOps

/-- `mem_op_consume(n) = max(10, n / 250)`; `n` = r3 for all four mem-ops. -/
@[simp] def cu (s : State) : Nat := Nat.max 10 (s.regs.r3 / 250)

/-- agave `is_nonoverlapping(src, n, dst, n)`: the distance between the two
    starts is at least `n`. Nat subtraction saturates as agave's does. -/
def nonoverlapping (src dst n : Nat) : Bool :=
  if src > dst then src - dst ≥ n else dst - src ≥ n

/-- `n` bytes from `src` placed at `dst`, every byte read from the original
    `m`, so an overlapping move is exact (memmove semantics). -/
def moveMem (m : Memory.Mem) (dst src n : Nat) : Memory.Mem :=
  fun a => if a ≥ dst ∧ a - dst < n then m (src + (a - dst)) % 256 else m a

/-- `sol_memmove(dst, src, n)`: copy `n` bytes src→dst, set r0 = 0; the
    ranges may overlap. H6: agave translates `dst` (Store) then `src` (Load);
    either out of region faults. The guards here run in the other order, which
    is unobservable: both fault to the same `accessFault` state. Zero-length
    slices are not translated. -/
@[simp] def execMove (s : State) : State :=
  let dst := s.regs.r1
  let src := s.regs.r2
  let n   := s.regs.r3
  s.guardRead src n fun s =>
  s.guardWrite dst n fun s =>
    { s with regs := s.regs.set .r0 0, mem := moveMem s.mem dst src n }

/-- `sol_memcpy(dst, src, n)`: `execMove` behind agave's overlap check, which
    runs after the CU charge and before either pointer is translated, so an
    overlapping memcpy faults `copyOverlapping` even out of region (#103). -/
@[simp] def execCopy (s : State) : State :=
  if nonoverlapping s.regs.r2 s.regs.r1 s.regs.r3 then execMove s
  else { s with exitCode := some ERR_COPY_OVERLAPPING, vmError := some .copyOverlapping }

/-- `sol_memset(dst, val, n)`: write the low byte of r2 into `n` bytes at
    `dst`. H6: `dst` slice (Store) must be writable; a `u8` slice has no
    alignment to check. -/
@[simp] def execSet (s : State) : State :=
  let dst := s.regs.r1
  let val := s.regs.r2 % 256
  let n   := s.regs.r3
  s.guardWrite dst n fun s =>
    let mem' : Memory.Mem := fun a =>
      if a ≥ dst ∧ a - dst < n then val
      else s.mem a
    { s with regs := s.regs.set .r0 0, mem := mem' }

/-- `sol_memcmp(p1, p2, n, out)`: write the i32 difference of the first
    differing byte pair (`a - b`, in `[-255,255]`) as two's-complement u32 to
    `*r4`. Agave writes the exact difference, not just the sign. See
    docs/SOUNDNESS_AUDIT_* (H7). H6: both inputs (Load) in region, and the
    fixed 4-byte `*r4` result (Store) writable — checked even for `n = 0`.
    The result is an `i32` translated with `check_aligned` (every loader but
    the deprecated v1), so a writable but unaligned `*r4` faults
    `unalignedPointer` after the region checks (#103). agave checks the host
    pointer; host buffers are allocated aligned and regions start at aligned
    virtual addresses, so this model checks the virtual address instead
    (differential-tested on the heap). -/
@[simp] def execCmp (s : State) : State :=
  let p1   := s.regs.r1
  let p2   := s.regs.r2
  let n    := s.regs.r3
  let outA := s.regs.r4
  s.guardRead p1 n fun s =>
  s.guardRead p2 n fun s =>
  s.guardWrite outA 4 fun s =>
  if outA % 4 ≠ 0 then
    { s with exitCode := some ERR_UNALIGNED_POINTER, vmError := some .unalignedPointer }
  else
    let cmp : Int := (List.range n).foldl (fun acc i =>
      if acc ≠ 0 then acc
      else
        let va := s.mem (p1 + i) % 256
        let vb := s.mem (p2 + i) % 256
        (va : Int) - (vb : Int)) 0
    let cmpU32 : Nat :=
      if cmp ≥ 0 then cmp.toNat else U32_MODULUS - (-cmp).toNat
    let mem' := Memory.writeU32 s.mem outA cmpU32
    { s with regs := s.regs.set .r0 0, mem := mem' }

end MemOps
end SVM.SBPF
