/-
Regression pin for the Murmur3 syscall-hash constants.

`SyscallHash.fromHash` identifies syscalls by the Murmur3-32 hash of their
name. If a refactor of `Murmur3` ever shifted the hashing (seed, tail
handling, finalizer), EVERY hash would move consistently and `fromHash`
would still be internally self-consistent, so no proof or diff test would
fail, yet real-world syscall identification would silently break.

These pins tie a representative hash from each functional group to its known
agave literal (e.g. `sol_log_` = 0x207559bd = 544561597), so any drift fails
the `Examples` build immediately. Values cross-checked against
`solana_sbpf::ebpf::hash_symbol_name`.
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
