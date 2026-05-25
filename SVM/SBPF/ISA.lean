-- sBPF Instruction Set Architecture for hand-written Solana programs
--
-- Minimal subset of the sBPF ISA sufficient to verify hand-written Solana
-- programs.
--
-- Reference: https://github.com/anza-xyz/sbpf

namespace SVM.SBPF

/-- 64-bit word modulus for wrapping arithmetic -/
def U64_MODULUS : Nat := 2 ^ 64

/-- sBPF registers: r0-r9 general purpose, r10 read-only frame pointer.
    r0 holds return values / exit codes.
    r1-r5 are caller-saved argument registers (used for all calls: syscalls, BPF-to-BPF, CPI).
    r6-r9 are callee-saved.
    r10 is the read-only stack frame pointer. -/
inductive Reg
  | r0 | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8 | r9 | r10
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Source operand: register or signed immediate (converted to unsigned by resolveSrc) -/
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

/-- sBPF syscall identifiers (Solana runtime).
    These map to the sol_* functions available to on-chain programs.

    The full registered set is mirrored from
    `anza-xyz/agave/syscalls/src/lib.rs`. Several variants are
    activation-gated in agave; we list them all here regardless of
    feature flag, since modeling activation is a separate concern from
    decoding. Variants whose semantics are not yet implemented in
    `execSyscall` fall through to the default arm (`r0 := 0`). -/
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
  -- A syscall whose name → hash mapping we don't (yet) know. The decoder
  -- emits this for any `call <hash>` whose 32-bit hash isn't in our
  -- syscall hash table.
  | unknown (hash : Nat)
  deriving Repr, DecidableEq

/-- sBPF instructions.
    Jump targets are absolute instruction indices (resolved from labels by parser).
    This abstracts away lddw occupying 2 instruction slots in the binary encoding;
    our model treats each logical instruction as one array element. -/
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
  -- Syscall (`call <imm32>` where imm32 = Murmur3 hash of syscall name,
  -- opcode 0x85 with `src = 0`)
  | call  (syscall : Syscall)
  -- Internal call (`call <imm32>` with `src = 1`, opcode 0x85). The
  -- 32-bit immediate is a signed slot-offset from the next
  -- instruction; the decoder resolves it to an absolute logical PC.
  -- Semantics: push the return PC onto `State.callStack`, jump to
  -- target. `.exit` pops the stack instead of terminating when the
  -- stack is non-empty. Callee-saved register preservation (r6–r9 /
  -- r10) is *not* modeled — programs that rely on r6–r9 surviving
  -- across the call will misbehave (real sBPF writes those + r10 to
  -- the new frame; full frame modeling is Phase D).
  | call_local (target : Nat)
  -- Indirect call (`callx <reg>`, opcode 0x8d) — call target is the
  -- runtime value of `reg`, interpreted as a logical PC. Cargo-built
  -- Solana programs emit this for tail-call dispatch and for
  -- panic/error paths in Rust's codegen.
  --
  -- v1 semantics: jump to `regs[reg]`. Like `.call_local`, no
  -- call-frame return stack push (an exit would terminate, not
  -- return). Most occurrences are in unreachable error branches.
  | callx (reg : Reg)
  -- Program exit (exit code = value in r0)
  | exit
  deriving Repr, DecidableEq

/-- Interpret a 64-bit unsigned value as signed two's complement -/
def toSigned64 (v : Nat) : Int :=
  if v < U64_MODULUS / 2 then ↑v
  else ↑v - ↑U64_MODULUS

/-- Convert a signed integer to its unsigned 64-bit representation.
    sBPF immediates are sign-extended to 64 bits; this mirrors that
    so codegen can emit readable negative literals while staying in Nat. -/
@[simp, reducible] def toU64 (v : Int) : Nat :=
  (v % (2^64 : Int)).toNat

end SVM.SBPF
