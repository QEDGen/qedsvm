-- sBPF Instruction Set Architecture — minimal subset sufficient to verify
-- hand-written Solana programs. Reference: https://github.com/anza-xyz/sbpf

namespace SVM.SBPF

/-- 64-bit word modulus for wrapping arithmetic -/
def U64_MODULUS : Nat := 2 ^ 64

/-- sBPF registers: r0 = return/exit, r1-r5 caller-saved args (all call kinds),
    r6-r9 callee-saved, r10 read-only frame pointer. -/
inductive Reg
  | r0 | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8 | r9 | r10
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Source operand: register or signed immediate (made unsigned by resolveSrc). -/
inductive Src
  | reg (r : Reg)
  | imm (v : Int)
  deriving Repr, DecidableEq

/-- Memory access width -/
inductive Width
  | byte   -- 1 byte  (ldxb / stb / stxb)
  | half   -- 2 bytes (ldxh / sth / stxh)
  | word   -- 4 bytes (ldxw / stw / stxw)
  | dword  -- 8 bytes (ldxdw / stdw / stxdw)
  deriving Repr, DecidableEq

/-- Number of bytes for a given width -/
def Width.bytes : Width → Nat
  | .byte  => 1
  | .half  => 2
  | .word  => 4
  | .dword => 8

/-- Mask for truncating values to a given width -/
def Width.mask : Width → Nat
  | .byte  => 2 ^ 8 - 1
  | .half  => 2 ^ 16 - 1
  | .word  => 2 ^ 32 - 1
  | .dword => 2 ^ 64 - 1

/-- sBPF syscall identifiers — the registered set mirrored from agave's
    `syscalls/src/lib.rs`. We list all variants regardless of activation gate
    (modeling activation is separate from decoding); unimplemented ones fall
    through to `execSyscall`'s default arm (`r0 := 0`). -/
inductive Syscall
  -- Logging
  | sol_log_
  | sol_log_64_
  | sol_log_compute_units_
  | sol_log_pubkey
  | sol_log_data
  -- Panic / abort
  | abort
  | sol_panic_
  -- Allocator (deprecated; programs typically ship their own allocator)
  | sol_alloc_free_
  -- PDA derivation
  | sol_create_program_address
  | sol_try_find_program_address
  -- Cross-program invocation
  | sol_invoke_signed
  | sol_invoke_signed_c
  -- Sysvars (specific getters + generic accessor)
  | sol_get_clock_sysvar
  | sol_get_rent_sysvar
  | sol_get_epoch_schedule_sysvar
  | sol_get_last_restart_slot
  | sol_get_fees_sysvar
  | sol_get_epoch_rewards_sysvar
  | sol_get_sysvar
  | sol_get_epoch_stake
  -- Introspection
  | sol_remaining_compute_units
  | sol_get_stack_height
  | sol_get_processed_sibling_instruction
  -- Hashing
  | sol_sha256
  | sol_sha512
  | sol_keccak256
  | sol_blake3
  | sol_poseidon
  -- Memory operations
  | sol_memcpy
  | sol_memmove
  | sol_memcmp
  | sol_memset
  -- Crypto: secp256k1
  | sol_secp256k1_recover
  -- Crypto: curve25519 / ristretto family
  | sol_curve_validate_point
  | sol_curve_group_op
  | sol_curve_multiscalar_mul
  | sol_curve_decompress
  | sol_curve_pairing_map
  -- Crypto: alt-bn128 (Ethereum precompile parity)
  | sol_alt_bn128_group_op
  | sol_alt_bn128_compression
  -- Big integer arithmetic
  | sol_big_mod_exp
  -- Return data
  | sol_get_return_data
  | sol_set_return_data
  -- A `call <hash>` whose 32-bit hash isn't in our syscall hash table.
  | unknown (hash : Nat)
  deriving Repr, DecidableEq

/-- sBPF instructions. Jump targets are absolute instruction indices. Abstracts
    away lddw's 2 binary slots — each logical instruction is one array element. -/
inductive Insn
  -- Load 64-bit immediate into register
  | lddw  (dst : Reg) (imm : Int)
  -- Load from memory: dst = mem[src + off]
  | ldx   (w : Width) (dst src : Reg) (off : Int)
  -- Store immediate to memory: mem[dst + off] = imm
  | st    (w : Width) (dst : Reg) (off : Int) (imm : Int)
  -- Store register to memory: mem[dst + off] = src
  | stx   (w : Width) (dst : Reg) (off : Int) (src : Reg)
  -- ALU 64-bit
  | add64  (dst : Reg) (src : Src)
  | sub64  (dst : Reg) (src : Src)
  | mul64  (dst : Reg) (src : Src)
  | div64  (dst : Reg) (src : Src)
  | mod64  (dst : Reg) (src : Src)
  | or64   (dst : Reg) (src : Src)
  | and64  (dst : Reg) (src : Src)
  | xor64  (dst : Reg) (src : Src)
  | lsh64  (dst : Reg) (src : Src)
  | rsh64  (dst : Reg) (src : Src)
  | arsh64 (dst : Reg) (src : Src)
  | mov64  (dst : Reg) (src : Src)
  | neg64  (dst : Reg)
  -- ALU 32-bit (result zero-extended to 64 bits)
  | add32  (dst : Reg) (src : Src)
  | sub32  (dst : Reg) (src : Src)
  | mul32  (dst : Reg) (src : Src)
  | div32  (dst : Reg) (src : Src)
  | mod32  (dst : Reg) (src : Src)
  | or32   (dst : Reg) (src : Src)
  | and32  (dst : Reg) (src : Src)
  | xor32  (dst : Reg) (src : Src)
  | lsh32  (dst : Reg) (src : Src)
  | rsh32  (dst : Reg) (src : Src)
  | arsh32 (dst : Reg) (src : Src)
  | mov32  (dst : Reg) (src : Src)
  | neg32  (dst : Reg)
  -- Conditional jumps (target = absolute instruction index)
  | jeq   (dst : Reg) (src : Src) (target : Nat)
  | jne   (dst : Reg) (src : Src) (target : Nat)
  | jgt   (dst : Reg) (src : Src) (target : Nat)
  | jge   (dst : Reg) (src : Src) (target : Nat)
  | jlt   (dst : Reg) (src : Src) (target : Nat)
  | jle   (dst : Reg) (src : Src) (target : Nat)
  | jsgt  (dst : Reg) (src : Src) (target : Nat)
  | jsge  (dst : Reg) (src : Src) (target : Nat)
  | jslt  (dst : Reg) (src : Src) (target : Nat)
  | jsle  (dst : Reg) (src : Src) (target : Nat)
  | jset  (dst : Reg) (src : Src) (target : Nat)
  -- Unconditional jump
  | ja    (target : Nat)
  -- Syscall (`call <imm32>`, imm32 = Murmur3 hash of name, opcode 0x85 src=0)
  | call  (syscall : Syscall)
  -- Internal call (`call <imm32>` src=1). Pushes a call frame (return PC + saved
  -- r6–r9 + r10) onto `State.callStack`, bumps r10 by one V0 frame (0x1000), and
  -- jumps; `.exit` pops it (restoring r6–r9/r10) instead of terminating when the
  -- stack is non-empty. Callee-saved preservation IS modeled (`Execute.lean`).
  | call_local (target : Nat)
  -- Indirect call (`callx <reg>`, opcode 0x8d): jump to `regs[reg]` as a logical
  -- PC. Emitted for tail-call dispatch / Rust panic paths. Like `.call_local`,
  -- no return-stack push (mostly in unreachable error branches).
  | callx (reg : Reg)
  -- Program exit (exit code = value in r0)
  | exit
  deriving Repr, DecidableEq

/-- Interpret a 64-bit unsigned value as signed two's complement -/
def toSigned64 (v : Nat) : Int :=
  if v < U64_MODULUS / 2 then ↑v
  else ↑v - ↑U64_MODULUS

/-- Signed integer to unsigned 64-bit (sBPF immediates are sign-extended to 64
    bits); lets codegen emit readable negative literals while staying in Nat. -/
@[simp, reducible] def toU64 (v : Int) : Nat :=
  (v % (2^64 : Int)).toNat

end SVM.SBPF
