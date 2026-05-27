/-
  ABI / calling-convention vocabulary for sBPF state.

  Layer 0 for the *machine* (not the domain). The Solana ABI pins
  fixed roles to fixed registers — `r1` is the program input pointer,
  `r0` is the return value, `r10` is the read-only frame pointer.
  These thin accessors let consumer-facing theorems name what they
  mean ("input pointer", "frame top") instead of spelling out the
  register file projection.

  Companion to `Abstract/Domain.lean` (Layer 0 for the abstract heap):
  same readability rationale, but on the concrete-side machine state.

  Extension protocol: add accessors here only when an in-flight pilot
  needs them. No simp attributes, no rewrite rules — this is just
  vocabulary; calling-convention lemmas live with the pilots that
  consume them.
-/

import SVM.SBPF.Machine

namespace SVM.SBPF.State

/-- The Solana ABI input pointer (`r1` by convention — points at the
    program input region serialized by the loader). -/
@[inline] def inputPtr (s : State) : Nat := s.regs.r1

/-- The Solana ABI return value (`r0` by convention — the program
    exit code lands here before `.exit`). -/
@[inline] def returnValue (s : State) : Nat := s.regs.r0

/-- The Solana ABI frame pointer (`r10` by convention — points at
    the top of the program's stack frame; read-only at the ISA level). -/
@[inline] def frameTop (s : State) : Nat := s.regs.r10

end SVM.SBPF.State
