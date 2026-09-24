import SVM.SBPF.Elf

namespace SVM.SBPF.ElfTests

private def headerWithFlags (flags : UInt8) : ByteArray :=
  ⟨((Array.replicate 48 (0 : UInt8)).push flags) ++ Array.replicate 15 0⟩

example : Elf.readVersion (headerWithFlags 0) = some .v0 := by native_decide
example : Elf.readVersion (headerWithFlags 3) = some .v3 := by native_decide
example : Elf.readVersion (headerWithFlags 1) = none := by native_decide
example : Elf.readVersion (headerWithFlags 4) = none := by native_decide

private def v3Minimal : ByteArray := Decode.bytesOfHex
  "7f454c460201010000000000000000000300f70001000000000000000100000040000000000000000000000000000000030000004000380001000000000000000100000001000000780000000000000000000000010000000000000001000000100000000000000010000000000000000800000000000000b70000002a0000009500000000000000"

example : (Elf.loadV3 v3Minimal).map (·.entrySlot) = some 0 := by native_decide
example : (Elf.loadV3 v3Minimal).map (·.textBytes.size) = some 16 := by native_decide
example : (Elf.loadV3 (v3Minimal.set! 56 0)).isNone = true := by native_decide
example : (Elf.loadV3 (v3Minimal.set! 24 16)).isNone = true := by native_decide
example : (Elf.loadV3 (v3Minimal.set! 96 32)).isNone = true := by native_decide
example : (Elf.loadV3 (v3Minimal.set! 68 4)).isNone = true := by native_decide
example : (Elf.loadV3 (v3Minimal.set! 40 255)).map (·.entrySlot) = some 0 := by native_decide

private def v3WithRodata : ByteArray := Decode.bytesOfHex
  "7f454c460201010000000000000000000300f70001000000000000000100000040000000000000000000000000000000030000004000380002000000000000000100000004000000b000000000000000000000000000000000000000000000000800000000000000080000000000000008000000000000000100000001000000b8000000000000000000000001000000000000000100000008000000000000000800000000000000080000000000000001020304050607089500000000000000"

example : (Elf.loadV3 v3WithRodata).map (·.rodata.size) = some 8 := by native_decide
example : (Elf.loadV3 v3WithRodata).map (·.textBytes.size) = some 8 := by native_decide

end SVM.SBPF.ElfTests
