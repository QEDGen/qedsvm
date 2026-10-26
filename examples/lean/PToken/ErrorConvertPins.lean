/-
  Decode pins for `PToken.ErrorConvert` (soundness-audit H8 pattern): every instruction its
  `CodeReq`s claim at PCs 116-196 is the decode of p_token's `.text` at that PC's byte offset,
  checked in-kernel by `native_decide`. GENERATED alongside `ErrorConvert.lean`. Kept separate
  so the standard-axiom module does not pull in `native_decide` or the 100 KB text literal.
-/
import SVM.SBPF.Decode
import Generated.PTokenText

namespace Examples.PTokenErrorConvert

open SVM.SBPF Examples.Lifted

theorem error_convert_decode_pins :
    ([936, 944, 952, 960, 968, 976, 984, 992, 1000, 1016, 1024, 1032, 1040, 1048, 1056, 1072, 1080, 1088, 1096, 1112, 1120, 1136, 1144, 1152, 1160, 1168, 1184, 1192, 1200, 1208, 1224, 1232, 1240, 1248, 1264, 1272, 1280, 1288, 1304, 1312, 1320, 1328, 1344, 1352, 1360, 1376, 1384, 1392, 1408, 1416, 1432, 1440, 1456, 1464, 1472, 1480, 1488, 1504, 1512, 1528, 1536, 1552, 1560, 1576, 1584, 1600, 1608, 1624, 1632, 1648, 1656, 1672, 1680, 1696, 1704, 1720, 1728, 1744, 1752, 1768, 1776].map fun off =>
      Decode.decodeInsn PTokenText PTokenSlotMap off PTokenFnRegistry) = [
      some (.mov64 .r0 (.reg .r2), 8),
      some (.lsh64 .r1 (.imm 32), 8),
      some (.rsh64 .r1 (.imm 32), 8),
      some (.jsgt .r1 (.imm 12) 126, 8),
      some (.jsle .r1 (.imm 5) 132, 8),
      some (.jsle .r1 (.imm 8) 143, 8),
      some (.jsgt .r1 (.imm 10) 159, 8),
      some (.jne .r1 (.imm 9) 184, 8),
      some (.lddw .r0 42949672960, 16),
      some (.ja 197, 8),
      some (.jsle .r1 (.imm 18) 138, 8),
      some (.jsle .r1 (.imm 21) 147, 8),
      some (.jsgt .r1 (.imm 23) 162, 8),
      some (.jne .r1 (.imm 22) 186, 8),
      some (.lddw .r0 98784247808, 16),
      some (.ja 197, 8),
      some (.jsgt .r1 (.imm 2) 151, 8),
      some (.jeq .r1 (.imm 0) 169, 8),
      some (.lddw .r0 8589934592, 16),
      some (.jeq .r1 (.imm 1) 197, 8),
      some (.lddw .r0 12884901888, 16),
      some (.ja 197, 8),
      some (.jsgt .r1 (.imm 15) 155, 8),
      some (.jeq .r1 (.imm 13) 174, 8),
      some (.jne .r1 (.imm 14) 192, 8),
      some (.lddw .r0 64424509440, 16),
      some (.ja 197, 8),
      some (.jeq .r1 (.imm 6) 165, 8),
      some (.jne .r1 (.imm 7) 180, 8),
      some (.lddw .r0 34359738368, 16),
      some (.ja 197, 8),
      some (.jeq .r1 (.imm 19) 167, 8),
      some (.jne .r1 (.imm 20) 182, 8),
      some (.lddw .r0 90194313216, 16),
      some (.ja 197, 8),
      some (.jeq .r1 (.imm 3) 176, 8),
      some (.jne .r1 (.imm 4) 194, 8),
      some (.lddw .r0 21474836480, 16),
      some (.ja 197, 8),
      some (.jeq .r1 (.imm 16) 178, 8),
      some (.jne .r1 (.imm 17) 196, 8),
      some (.lddw .r0 77309411328, 16),
      some (.ja 197, 8),
      some (.jne .r1 (.imm 11) 188, 8),
      some (.lddw .r0 51539607552, 16),
      some (.ja 197, 8),
      some (.jne .r1 (.imm 24) 190, 8),
      some (.lddw .r0 107374182400, 16),
      some (.ja 197, 8),
      some (.lddw .r0 30064771072, 16),
      some (.ja 197, 8),
      some (.lddw .r0 85899345920, 16),
      some (.ja 197, 8),
      some (.lsh64 .r0 (.imm 32), 8),
      some (.rsh64 .r0 (.imm 32), 8),
      some (.jne .r0 (.imm 0) 197, 8),
      some (.lddw .r0 4294967296, 16),
      some (.ja 197, 8),
      some (.lddw .r0 60129542144, 16),
      some (.ja 197, 8),
      some (.lddw .r0 17179869184, 16),
      some (.ja 197, 8),
      some (.lddw .r0 73014444032, 16),
      some (.ja 197, 8),
      some (.lddw .r0 38654705664, 16),
      some (.ja 197, 8),
      some (.lddw .r0 94489280512, 16),
      some (.ja 197, 8),
      some (.lddw .r0 47244640256, 16),
      some (.ja 197, 8),
      some (.lddw .r0 103079215104, 16),
      some (.ja 197, 8),
      some (.lddw .r0 55834574848, 16),
      some (.ja 197, 8),
      some (.lddw .r0 111669149696, 16),
      some (.ja 197, 8),
      some (.lddw .r0 68719476736, 16),
      some (.ja 197, 8),
      some (.lddw .r0 25769803776, 16),
      some (.ja 197, 8),
      some (.lddw .r0 81604378624, 16)
    ] := by
  native_decide

end Examples.PTokenErrorConvert
