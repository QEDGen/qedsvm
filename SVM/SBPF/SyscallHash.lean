/-
  Syscall name → Murmur3-32 hash → typed `Syscall` lookup.

  Each Solana syscall has a stable 32-bit identifier: the Murmur3-32 hash
  (seed 0) of its name. The `call` instruction in sBPF bytecode carries
  this hash in its 32-bit immediate field. To recover the typed `Syscall`
  variant, we precompute the hash for each name we know and check
  membership at decode time.

  The hashes are constants (Murmur3 is pure and kernel-reducible), so
  `fromHash` is a simple if-chain of `Nat` equalities — efficient under
  both `native_decide` and the regular Lean elaborator.

  Coverage matches the `Syscall` enum in `SVM.SBPF.ISA`. Any `call`
  whose hash isn't in this table decodes to `Syscall.unknown <hash>` and
  executes with default semantics.
-/

import SVM.SBPF.Murmur3
import SVM.SBPF.ISA

namespace SVM.SBPF
namespace SyscallHash

open Murmur3

/-! ## Precomputed hashes for each known syscall name. -/

def sol_log_hash                       : Nat := hashString "sol_log_"
def sol_log_64_hash                    : Nat := hashString "sol_log_64_"
def sol_log_compute_units_hash         : Nat := hashString "sol_log_compute_units_"
def sol_log_pubkey_hash                : Nat := hashString "sol_log_pubkey"
def sol_log_data_hash                  : Nat := hashString "sol_log_data"

def sol_create_program_address_hash    : Nat := hashString "sol_create_program_address"
def sol_try_find_program_address_hash  : Nat := hashString "sol_try_find_program_address"

def sol_invoke_signed_c_hash           : Nat := hashString "sol_invoke_signed_c"
def sol_invoke_signed_rust_hash        : Nat := hashString "sol_invoke_signed_rust"

def sol_get_clock_sysvar_hash          : Nat := hashString "sol_get_clock_sysvar"
def sol_get_rent_sysvar_hash           : Nat := hashString "sol_get_rent_sysvar"
def sol_get_epoch_schedule_sysvar_hash : Nat := hashString "sol_get_epoch_schedule_sysvar"
def sol_get_last_restart_slot_hash     : Nat := hashString "sol_get_last_restart_slot"

def sol_remaining_compute_units_hash   : Nat := hashString "sol_remaining_compute_units"
def sol_get_stack_height_hash          : Nat := hashString "sol_get_stack_height"

def sol_sha256_hash                    : Nat := hashString "sol_sha256"
def sol_keccak256_hash                 : Nat := hashString "sol_keccak256"
def sol_blake3_hash                    : Nat := hashString "sol_blake3"

def sol_memcpy_hash                    : Nat := hashString "sol_memcpy_"
def sol_memmove_hash                   : Nat := hashString "sol_memmove_"
def sol_memcmp_hash                    : Nat := hashString "sol_memcmp_"
def sol_memset_hash                    : Nat := hashString "sol_memset_"

def sol_secp256k1_recover_hash         : Nat := hashString "sol_secp256k1_recover"

def sol_get_return_data_hash           : Nat := hashString "sol_get_return_data"
def sol_set_return_data_hash           : Nat := hashString "sol_set_return_data"

-- Panic / abort
def abort_hash                         : Nat := hashString "abort"
def sol_panic_hash                     : Nat := hashString "sol_panic_"

-- Allocator
def sol_alloc_free_hash                : Nat := hashString "sol_alloc_free_"

-- Hashing (additions)
def sol_sha512_hash                    : Nat := hashString "sol_sha512"
def sol_poseidon_hash                  : Nat := hashString "sol_poseidon"

-- Sysvar additions
def sol_get_fees_sysvar_hash           : Nat := hashString "sol_get_fees_sysvar"
def sol_get_epoch_rewards_sysvar_hash  : Nat := hashString "sol_get_epoch_rewards_sysvar"
def sol_get_sysvar_hash                : Nat := hashString "sol_get_sysvar"
def sol_get_epoch_stake_hash           : Nat := hashString "sol_get_epoch_stake"

-- Introspection additions
def sol_get_processed_sibling_instruction_hash : Nat :=
  hashString "sol_get_processed_sibling_instruction"

-- curve25519 / ristretto
def sol_curve_validate_point_hash      : Nat := hashString "sol_curve_validate_point"
def sol_curve_group_op_hash            : Nat := hashString "sol_curve_group_op"
def sol_curve_multiscalar_mul_hash     : Nat := hashString "sol_curve_multiscalar_mul"
def sol_curve_decompress_hash          : Nat := hashString "sol_curve_decompress"
def sol_curve_pairing_map_hash         : Nat := hashString "sol_curve_pairing_map"

-- alt-bn128
def sol_alt_bn128_group_op_hash        : Nat := hashString "sol_alt_bn128_group_op"
def sol_alt_bn128_compression_hash     : Nat := hashString "sol_alt_bn128_compression"

-- Big integer
def sol_big_mod_exp_hash               : Nat := hashString "sol_big_mod_exp"

/-! ## Hash → Syscall lookup -/

/-- Resolve a Murmur3 syscall hash to its typed `Syscall` variant.
    Unknown hashes are returned as `Syscall.unknown`. -/
def fromHash (h : Nat) : Syscall :=
  if h = sol_log_hash                       then .sol_log_
  else if h = sol_log_64_hash               then .sol_log_64_
  else if h = sol_log_compute_units_hash    then .sol_log_compute_units_
  else if h = sol_log_pubkey_hash           then .sol_log_pubkey
  else if h = sol_log_data_hash             then .sol_log_data
  else if h = sol_create_program_address_hash    then .sol_create_program_address
  else if h = sol_try_find_program_address_hash  then .sol_try_find_program_address
  else if h = sol_invoke_signed_c_hash      then .sol_invoke_signed_c
  else if h = sol_invoke_signed_rust_hash   then .sol_invoke_signed
  else if h = sol_get_clock_sysvar_hash     then .sol_get_clock_sysvar
  else if h = sol_get_rent_sysvar_hash      then .sol_get_rent_sysvar
  else if h = sol_get_epoch_schedule_sysvar_hash then .sol_get_epoch_schedule_sysvar
  else if h = sol_get_last_restart_slot_hash     then .sol_get_last_restart_slot
  else if h = sol_remaining_compute_units_hash   then .sol_remaining_compute_units
  else if h = sol_get_stack_height_hash     then .sol_get_stack_height
  else if h = sol_sha256_hash               then .sol_sha256
  else if h = sol_keccak256_hash            then .sol_keccak256
  else if h = sol_blake3_hash               then .sol_blake3
  else if h = sol_memcpy_hash               then .sol_memcpy
  else if h = sol_memmove_hash              then .sol_memmove
  else if h = sol_memcmp_hash               then .sol_memcmp
  else if h = sol_memset_hash               then .sol_memset
  else if h = sol_secp256k1_recover_hash    then .sol_secp256k1_recover
  else if h = sol_get_return_data_hash      then .sol_get_return_data
  else if h = sol_set_return_data_hash      then .sol_set_return_data
  else if h = abort_hash                    then .abort
  else if h = sol_panic_hash                then .sol_panic_
  else if h = sol_alloc_free_hash           then .sol_alloc_free_
  else if h = sol_sha512_hash               then .sol_sha512
  else if h = sol_poseidon_hash             then .sol_poseidon
  else if h = sol_get_fees_sysvar_hash      then .sol_get_fees_sysvar
  else if h = sol_get_epoch_rewards_sysvar_hash  then .sol_get_epoch_rewards_sysvar
  else if h = sol_get_sysvar_hash           then .sol_get_sysvar
  else if h = sol_get_epoch_stake_hash      then .sol_get_epoch_stake
  else if h = sol_get_processed_sibling_instruction_hash then
    .sol_get_processed_sibling_instruction
  else if h = sol_curve_validate_point_hash then .sol_curve_validate_point
  else if h = sol_curve_group_op_hash       then .sol_curve_group_op
  else if h = sol_curve_multiscalar_mul_hash then .sol_curve_multiscalar_mul
  else if h = sol_curve_decompress_hash     then .sol_curve_decompress
  else if h = sol_curve_pairing_map_hash    then .sol_curve_pairing_map
  else if h = sol_alt_bn128_group_op_hash   then .sol_alt_bn128_group_op
  else if h = sol_alt_bn128_compression_hash then .sol_alt_bn128_compression
  else if h = sol_big_mod_exp_hash          then .sol_big_mod_exp
  else .unknown h

end SyscallHash
end SVM.SBPF
