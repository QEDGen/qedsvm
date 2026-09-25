import SVM.SBPF.Decode

namespace SVM.SBPF.V3DecodeTests

-- CALL_REG in V3 takes the destination nibble as its target register.
example : Decode.decodeInsn (Decode.bytesOfHex "8d01000000000000") #[0] 0 [] .v3 =
    some (.callx .r1, 8) := by
  native_decide

end SVM.SBPF.V3DecodeTests
