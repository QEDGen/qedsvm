/-
  Murmur3 syscall-hash regression pins. A silent seed/finalizer shift would leave
  `fromHash` internally consistent but break real syscall identification; these pins
  catch that by tying known agave literals to computed hashes (cross-checked vs
  `solana_sbpf::ebpf::hash_symbol_name`).
-/
import SVM.SBPF.SyscallHash

namespace Examples.SyscallHashPin
open SVM.SBPF

theorem pin_sol_log_            : SyscallHash.sol_log_hash            = 544561597  := by native_decide
theorem pin_sol_memcpy_         : SyscallHash.sol_memcpy_hash         = 1904002211 := by native_decide
theorem pin_sol_invoke_signed_c : SyscallHash.sol_invoke_signed_c_hash = 2720767109 := by native_decide
theorem pin_sol_set_return_data : SyscallHash.sol_set_return_data_hash = 2720453611 := by native_decide
theorem pin_sol_sha256          : SyscallHash.sol_sha256_hash         = 301243782  := by native_decide

end Examples.SyscallHashPin
