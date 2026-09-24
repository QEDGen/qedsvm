import SVM.SBPF.Elf

namespace SVM.SBPF.ElfTests

private def headerWithFlags (flags : UInt8) : ByteArray :=
  ⟨((Array.replicate 48 (0 : UInt8)).push flags) ++ Array.replicate 15 0⟩

example : Elf.readVersion (headerWithFlags 0) = some .v0 := by native_decide
example : Elf.readVersion (headerWithFlags 3) = some .v3 := by native_decide
example : Elf.readVersion (headerWithFlags 1) = none := by native_decide
example : Elf.readVersion (headerWithFlags 4) = none := by native_decide

end SVM.SBPF.ElfTests
