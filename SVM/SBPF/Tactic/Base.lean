-- simp improvements for effectiveAddr and readByWidth.

import SVM.SBPF.Execute

namespace SVM.SBPF

open Memory

/-! ## Simplification improvements -/

/-- effectiveAddr with non-negative offset reduces to Nat addition (avoids the
    Int.toNat roundtrip). -/
@[simp] theorem effectiveAddr_nat (base off : Nat) :
    effectiveAddr base (↑off) = base + off := by
  unfold effectiveAddr; omega

attribute [simp] Memory.readByWidth

end SVM.SBPF
