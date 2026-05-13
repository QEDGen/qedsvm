-- Memory-operation syscalls: `sol_memcpy`, `sol_memmove`, `sol_memset`,
-- `sol_memcmp`. CU charge is shared: `mem_op_consume = max(10, n / 250)`.

import Svm.SBPF.Machine

namespace Svm.SBPF
namespace MemOps

/-- `mem_op_consume(n) = max(10, n / 250)`. `n` is r3 for all four
    mem-op syscalls. -/
@[simp] def cu (s : State) : Nat := Nat.max 10 (s.regs.r3 / 250)

/-- `sol_memcpy(dst, src, n)` / `sol_memmove(dst, src, n)`. Both share
    semantics in our model (no overlap-handling distinction): copy `n`
    bytes from `src` to `dst`. Sets r0 = 0. -/
@[simp] def execCopy (s : State) : State :=
  let dst := s.regs.r1
  let src := s.regs.r2
  let n   := s.regs.r3
  let mem' : Memory.Mem := fun a =>
    if a ≥ dst ∧ a - dst < n then s.mem (src + (a - dst)) % 256
    else s.mem a
  { s with regs := s.regs.set .r0 0, mem := mem' }

/-- `sol_memset(dst, val, n)`: write the low byte of r2 into `n` bytes
    starting at `dst`. -/
@[simp] def execSet (s : State) : State :=
  let dst := s.regs.r1
  let val := s.regs.r2 % 256
  let n   := s.regs.r3
  let mem' : Memory.Mem := fun a =>
    if a ≥ dst ∧ a - dst < n then val
    else s.mem a
  { s with regs := s.regs.set .r0 0, mem := mem' }

/-- `sol_memcmp(p1, p2, n, out)`: write -1/0/+1 (as i32, two's
    complement) to `*r4`. -/
@[simp] def execCmp (s : State) : State :=
  let p1   := s.regs.r1
  let p2   := s.regs.r2
  let n    := s.regs.r3
  let outA := s.regs.r4
  let cmp : Int := (List.range n).foldl (fun acc i =>
    if acc ≠ 0 then acc
    else
      let va := s.mem (p1 + i) % 256
      let vb := s.mem (p2 + i) % 256
      if va < vb then -1
      else if va > vb then 1
      else 0) 0
  let cmpU32 : Nat :=
    if cmp = 0 then 0
    else if cmp < 0 then 0xFFFFFFFF
    else 1
  let mem' := Memory.writeU32 s.mem outA cmpU32
  { s with regs := s.regs.set .r0 0, mem := mem' }

end MemOps
end Svm.SBPF
