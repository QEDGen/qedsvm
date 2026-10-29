/-
  Load/store addresses wrap mod 2^64, as agave's `wrapping_add` does (#135).

  V3 maps rodata at 0, so a clamp to 0 (the old `effectiveAddr`) read program
  bytes where agave faults. Each case runs one `step` against a region at 0.

  Reproduce with `lake build SVM.SBPF.AddrWrapTests`.
-/

import SVM.SBPF.Execute

namespace SVM.SBPF.AddrWrapTests

open SVM.SBPF SVM.SBPF.Memory

example : effectiveAddr 0 (-8) = 2 ^ 64 - 8 := by decide
example : effectiveAddr 16 (-8) = 8 := by decide
example (base k : Nat) : effectiveAddr base (↑k) = base + k := rfl

/-- A V3-like state: a 64-byte region at 0 (rodata), `r1 = base`, `r2 = 0x2a`. -/
private def at0 (base : Nat) (writable : Bool := false) : State :=
  { regs := { r1 := base, r2 := 0x2a }, mem := {},
    regions := [{ start := 0, size := 64, writable }], pc := 0 }

/-- `ldxdw r0, [r1 - 8]` with `r1 = 0`: the address wraps to 2^64 - 8, unmapped. -/
example : (step (.ldx .dword .r0 .r1 (-8)) (at0 0)).vmError = some .accessViolation := by
  native_decide

/-- In range, the same load reads the region. -/
example : (step (.ldx .dword .r0 .r1 (-8)) (at0 8)).vmError = none := by native_decide

/-- `stxb [r1 + 8], r2` with `r1 = 2^64 - 1`: the sum 2^64 + 7 wraps to 7. -/
example : (step (.stx .byte .r1 8 .r2) (at0 (2 ^ 64 - 1) true)).mem.read 7 = 0x2a := by
  native_decide

/-- `ldxb r0, [r1 + 8]` with `r1 = 2^64 - 1` reads address 7. -/
example :
    let s := step (.stx .byte .r1 8 .r2) (at0 (2 ^ 64 - 1) true)
    (step (.ldx .byte .r0 .r1 8) s).regs.r0 = 0x2a := by
  native_decide

/-- A wrapped address still has to land in a region. -/
example : (step (.ldx .byte .r0 .r1 0x100) (at0 (2 ^ 64 - 1))).vmError =
    some .accessViolation := by native_decide

end SVM.SBPF.AddrWrapTests
