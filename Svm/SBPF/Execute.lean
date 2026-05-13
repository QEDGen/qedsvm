-- sBPF execution semantics: single-step and multi-step evaluation
--
-- Defines the machine state, register file, and the step function that gives
-- operational semantics to each sBPF instruction.

import Svm.SBPF.ISA
import Svm.SBPF.Memory
import Svm.SBPF.Sha256
import Svm.SBPF.Keccak256
import Svm.SBPF.Blake3
import Svm.SBPF.Secp256k1

namespace Svm.SBPF

open Memory

/-! ## Register file as a concrete structure

Using named fields instead of a function `Reg → Nat` makes projections
trivially reducible by simp, avoiding the nested if-then-else chains that
cause timeouts in proofs. -/

structure RegFile where
  r0 : Nat := 0
  r1 : Nat := 0
  r2 : Nat := 0
  r3 : Nat := 0
  r4 : Nat := 0
  r5 : Nat := 0
  r6 : Nat := 0
  r7 : Nat := 0
  r8 : Nat := 0
  r9 : Nat := 0
  r10 : Nat := 0
  deriving Repr, Inhabited, DecidableEq, BEq

/-- Get a register value -/
@[simp] def RegFile.get (rf : RegFile) : Reg → Nat
  | .r0 => rf.r0 | .r1 => rf.r1 | .r2 => rf.r2 | .r3 => rf.r3
  | .r4 => rf.r4 | .r5 => rf.r5 | .r6 => rf.r6 | .r7 => rf.r7
  | .r8 => rf.r8 | .r9 => rf.r9 | .r10 => rf.r10

/-- Set a register value (r10 is read-only: writes are silently ignored) -/
@[simp] def RegFile.set (rf : RegFile) (r : Reg) (v : Nat) : RegFile :=
  match r with
  | .r0 => { rf with r0 := v } | .r1 => { rf with r1 := v }
  | .r2 => { rf with r2 := v } | .r3 => { rf with r3 := v }
  | .r4 => { rf with r4 := v } | .r5 => { rf with r5 := v }
  | .r6 => { rf with r6 := v } | .r7 => { rf with r7 := v }
  | .r8 => { rf with r8 := v } | .r9 => { rf with r9 := v }
  | .r10 => rf

/-- Writing to r10 is a no-op (frame pointer is read-only). -/
@[simp] theorem RegFile.set_r10 (rf : RegFile) (v : Nat) :
    rf.set .r10 v = rf := rfl

/-- Any register write preserves the r10 field (frame pointer is read-only). -/
@[simp] theorem RegFile.set_preserves_r10 (rf : RegFile) (r : Reg) (v : Nat) :
    (rf.set r v).r10 = rf.r10 := by
  cases r <;> rfl

/-- Reading the register just written returns the written value (r0-r9 only). -/
theorem RegFile.get_set_self (rf : RegFile) (r : Reg) (v : Nat) (h : r ≠ .r10) :
    (rf.set r v).get r = v := by
  cases r <;> simp_all [RegFile.get, RegFile.set]

/-- Reading a different register from the one written returns the original value. -/
theorem RegFile.get_set_diff (rf : RegFile) (r1 r2 : Reg) (v : Nat) (h : r1 ≠ r2) :
    (rf.set r2 v).get r1 = rf.get r1 := by
  cases r1 <;> cases r2 <;> simp_all [RegFile.get, RegFile.set]

/-! ## Machine state -/

/-- sBPF machine state -/
structure State where
  /-- Register file -/
  regs : RegFile
  /-- Byte-addressable memory -/
  mem : Mem
  /-- Program counter: index into the instruction array -/
  pc : Nat
  /-- Exit status: None if running, Some n if exited with code n -/
  exitCode : Option Nat := none
  /-- Side channel: messages written via `sol_log_*` syscalls.
      Each entry is one message. Observable from the runner; not owned
      by any separation-logic assertion. -/
  log : Array ByteArray := #[]
  /-- Side channel: return-data buffer set by `sol_set_return_data` and
      read by `sol_get_return_data`. -/
  returnData : ByteArray := ByteArray.empty
  deriving Inhabited

/-- Is the machine still running? -/
def State.running (s : State) : Prop := s.exitCode = none

/-! ## Helpers -/

/-- Resolve a source operand to its unsigned 64-bit value -/
@[simp] def resolveSrc (rf : RegFile) (src : Src) : Nat :=
  match src with
  | .reg r => rf.get r
  | .imm v => toU64 v

/-! ## Runtime error codes

These are used when the VM encounters an unrecoverable error (not a program
exit via `exit` instruction). They must be non-zero to distinguish from
success. -/

def ERR_DIVIDE_BY_ZERO : Nat := 0xFFFFFFFFFFFFFFFE
def ERR_INVALID_PC     : Nat := 0xFFFFFFFFFFFFFFFF

/-! ## Wrapping 64-bit arithmetic -/

@[simp] def wrapAdd (a b : Nat) : Nat := (a + b) % U64_MODULUS
@[simp] def wrapSub (a b : Nat) : Nat := (a + U64_MODULUS - b % U64_MODULUS) % U64_MODULUS
@[simp] def wrapMul (a b : Nat) : Nat := (a * b) % U64_MODULUS
@[simp] def wrapNeg (a : Nat) : Nat := (U64_MODULUS - a % U64_MODULUS) % U64_MODULUS

/-- 32-bit modulus for 32-bit ALU operations -/
def U32_MODULUS : Nat := 2 ^ 32

@[simp] def wrapAdd32 (a b : Nat) : Nat := (a + b) % U32_MODULUS
@[simp] def wrapSub32 (a b : Nat) : Nat := (a + U32_MODULUS - b % U32_MODULUS) % U32_MODULUS
@[simp] def wrapMul32 (a b : Nat) : Nat := (a * b) % U32_MODULUS
@[simp] def wrapNeg32 (a : Nat) : Nat := (U32_MODULUS - a % U32_MODULUS) % U32_MODULUS

/-! ## Syscall execution -/

/-- Read `len` bytes from `mem` starting at `addr` into a `ByteArray`. -/
def readBytes (mem : Memory.Mem) (addr len : Nat) : ByteArray :=
  ⟨(List.range len).foldl
    (fun acc i => acc.push (mem (addr + i) % 256).toUInt8) #[]⟩

/-- Execute a syscall.

    Logging syscalls (`sol_log_*`) write into `State.log` as observable
    side effects — `sol_log_` and `sol_log_pubkey` log their bytes
    verbatim; `sol_log_64_` / `sol_log_compute_units_` / `sol_log_data`
    push an empty marker (their formatted encoding is TODO).

    Memory syscalls (`sol_memcpy_*`, `sol_memmove_*`, `sol_memset_*`,
    `sol_memcmp_*`) are implemented with their actual byte-moving / byte-
    comparison semantics on `Mem`.

    `sol_set_return_data` / `sol_get_return_data` use `State.returnData`.

    Unmodeled syscalls fall through to the default arm (set `r0 := 0`). -/

@[simp] def execSyscall (sc : Syscall) (s : State) : State :=
  match sc with
  | .sol_log_ =>
    let ptr := s.regs.r1
    let len := s.regs.r2
    { s with regs := s.regs.set .r0 0
             log  := s.log.push (readBytes s.mem ptr len) }
  | .sol_log_pubkey =>
    let ptr := s.regs.r1
    { s with regs := s.regs.set .r0 0
             log  := s.log.push (readBytes s.mem ptr 32) }
  | .sol_log_64_ | .sol_log_compute_units_ | .sol_log_data =>
    -- Push an empty marker into the log; full encoding of these is TODO
    { s with regs := s.regs.set .r0 0
             log  := s.log.push ByteArray.empty }
  | .sol_set_return_data =>
    let ptr := s.regs.r1
    let len := s.regs.r2
    { s with regs := s.regs.set .r0 0
             returnData := readBytes s.mem ptr len }
  | .sol_get_return_data =>
    -- Copies up to `r2` bytes of `returnData` to `*r1`. Returns the
    -- actual length (NOT the truncated length). `r3` is `*Pubkey` of the
    -- program that set the data — we don't track this, write zeros.
    let outA    := s.regs.r1
    let maxLen  := s.regs.r2
    let pkA     := s.regs.r3
    let dataLen := s.returnData.size
    let copyLen := if dataLen ≤ maxLen then dataLen else maxLen
    let mem' : Memory.Mem := fun a =>
      if a ≥ outA ∧ a - outA < copyLen then
        (s.returnData.get! (a - outA)).toNat
      else if a ≥ pkA ∧ a - pkA < 32 then 0
      else s.mem a
    { s with regs := s.regs.set .r0 dataLen, mem := mem' }
  | .sol_get_stack_height =>
    { s with regs := s.regs.set .r0 1 }  -- top-level: depth 1
  | .sol_remaining_compute_units =>
    s  -- r0 gets an opaque runtime value (we don't track remaining CU here)
  -- Sysvar getters: zero-fill the output buffer at *r1. Real sysvar
  -- values vary by epoch/slot and aren't tracked in our model; zero
  -- is the safe default that lets dependent programs continue.
  | .sol_get_clock_sysvar =>
    -- Clock layout: 40 bytes (slot, epoch_start_ts, epoch, leader_epoch, unix_ts)
    let outA := s.regs.r1
    let mem' : Memory.Mem := fun a =>
      if a ≥ outA ∧ a - outA < 40 then 0 else s.mem a
    { s with regs := s.regs.set .r0 0, mem := mem' }
  | .sol_get_rent_sysvar =>
    -- Rent: 17 bytes (lamports_per_byte_year, exemption_threshold, burn_percent)
    let outA := s.regs.r1
    let mem' : Memory.Mem := fun a =>
      if a ≥ outA ∧ a - outA < 17 then 0 else s.mem a
    { s with regs := s.regs.set .r0 0, mem := mem' }
  | .sol_get_epoch_schedule_sysvar =>
    -- EpochSchedule: 33 bytes
    let outA := s.regs.r1
    let mem' : Memory.Mem := fun a =>
      if a ≥ outA ∧ a - outA < 33 then 0 else s.mem a
    { s with regs := s.regs.set .r0 0, mem := mem' }
  | .sol_get_last_restart_slot =>
    -- u64: 8 bytes
    let outA := s.regs.r1
    let mem' : Memory.Mem := fun a =>
      if a ≥ outA ∧ a - outA < 8 then 0 else s.mem a
    { s with regs := s.regs.set .r0 0, mem := mem' }
  | .sol_memcpy | .sol_memmove =>
    let dst := s.regs.r1
    let src := s.regs.r2
    let n   := s.regs.r3
    let mem' : Memory.Mem := fun a =>
      if a ≥ dst ∧ a - dst < n then s.mem (src + (a - dst)) % 256
      else s.mem a
    { s with regs := s.regs.set .r0 0, mem := mem' }
  | .sol_memset =>
    let dst := s.regs.r1
    let val := s.regs.r2 % 256
    let n   := s.regs.r3
    let mem' : Memory.Mem := fun a =>
      if a ≥ dst ∧ a - dst < n then val
      else s.mem a
    { s with regs := s.regs.set .r0 0, mem := mem' }
  | .sol_memcmp =>
    -- Compare n bytes from r1 and r2, write -1/0/+1 (as i32) to *r4.
    let p1   := s.regs.r1
    let p2   := s.regs.r2
    let n    := s.regs.r3
    let outA := s.regs.r4
    let cmp : Int := (List.range n).foldl (fun acc i =>
      if acc ≠ 0 then acc
      else
        let va := s.mem (p1 + i) % 256
        let vb := s.mem (p2 + i) % 256
        if va < vb then -1
        else if va > vb then 1
        else 0) 0
    let cmpU32 : Nat :=
      if cmp = 0 then 0
      else if cmp < 0 then 0xFFFFFFFF  -- -1 as u32 (two's complement)
      else 1
    let mem' := Memory.writeU32 s.mem outA cmpU32
    { s with regs := s.regs.set .r0 0, mem := mem' }
  | .sol_sha256 =>
    -- ABI: sol_sha256(vals: *const SliceDesc, nVals: u64, result: *mut [u8; 32])
    -- where SliceDesc = { ptr : u64, len : u64 } (16 bytes, little-endian).
    let valsA   := s.regs.r1
    let nVals   := s.regs.r2
    let resultA := s.regs.r3
    let allBytes : ByteArray :=
      (List.range nVals).foldl (fun acc i =>
        let descAddr := valsA + i * 16
        let ptr := Memory.readU64 s.mem descAddr
        let len := Memory.readU64 s.mem (descAddr + 8)
        acc ++ readBytes s.mem ptr len) ByteArray.empty
    let digest := Sha256.hash allBytes
    let mem' : Memory.Mem := fun a =>
      if a ≥ resultA ∧ a - resultA < 32 then (digest.get! (a - resultA)).toNat
      else s.mem a
    { s with regs := s.regs.set .r0 0, mem := mem' }
  | .sol_keccak256 =>
    -- Same ABI as `sol_sha256`. Hash is computed via FFI in `csrc/keccak256.c`.
    let valsA   := s.regs.r1
    let nVals   := s.regs.r2
    let resultA := s.regs.r3
    let allBytes : ByteArray :=
      (List.range nVals).foldl (fun acc i =>
        let descAddr := valsA + i * 16
        let ptr := Memory.readU64 s.mem descAddr
        let len := Memory.readU64 s.mem (descAddr + 8)
        acc ++ readBytes s.mem ptr len) ByteArray.empty
    let digest := Keccak256.hash allBytes
    let mem' : Memory.Mem := fun a =>
      if a ≥ resultA ∧ a - resultA < 32 then (digest.get! (a - resultA)).toNat
      else s.mem a
    { s with regs := s.regs.set .r0 0, mem := mem' }
  | .sol_blake3 =>
    -- Same ABI as `sol_sha256` / `sol_keccak256`. Hash is computed via
    -- FFI in `csrc/blake3.c` (default mode, 32-byte output).
    let valsA   := s.regs.r1
    let nVals   := s.regs.r2
    let resultA := s.regs.r3
    let allBytes : ByteArray :=
      (List.range nVals).foldl (fun acc i =>
        let descAddr := valsA + i * 16
        let ptr := Memory.readU64 s.mem descAddr
        let len := Memory.readU64 s.mem (descAddr + 8)
        acc ++ readBytes s.mem ptr len) ByteArray.empty
    let digest := Blake3.hash allBytes
    let mem' : Memory.Mem := fun a =>
      if a ≥ resultA ∧ a - resultA < 32 then (digest.get! (a - resultA)).toNat
      else s.mem a
    { s with regs := s.regs.set .r0 0, mem := mem' }
  | .sol_secp256k1_recover =>
    -- ABI:
    --   r1 = *const [u8; 32]   message hash
    --   r2 = u64               recovery_id (Solana rejects ≥ 4)
    --   r3 = *const [u8; 64]   compact signature (r || s)
    --   r4 = *mut [u8; 64]     output: x || y, no 0x04 prefix
    --   r0 = u64               0 success / 1 InvalidHash /
    --                          2 InvalidRecoveryId / 3 InvalidSignature
    --
    -- Implementation delegates to `Secp256k1.recover` (rust-bridge →
    -- paritytech `libsecp256k1` 0.7.2, same as agave). The recId > 3
    -- check matches agave's `u8::try_from + RecoveryId::parse` pair
    -- (both collapse to InvalidRecoveryId for any out-of-range value).
    -- The final state is structured as a single unconditional record
    -- update so `execSyscall_preserves_r10` goes through by simp alone.
    let hashA := s.regs.r1
    let recId := s.regs.r2
    let sigA  := s.regs.r3
    let outA  := s.regs.r4
    let result : Secp256k1.RecoverResult :=
      if recId > 3 then .invalidRecoveryId
      else Secp256k1.recover (readBytes s.mem hashA 32)
                              recId.toUInt8
                              (readBytes s.mem sigA 64)
    let errCode : Nat :=
      match result with
      | .success _         => 0
      | .invalidHash       => 1
      | .invalidRecoveryId => 2
      | .invalidSignature  => 3
    let mem' : Memory.Mem := fun a =>
      match result with
      | .success pubkey =>
        if a ≥ outA ∧ a - outA < 64 then (pubkey.get! (a - outA)).toNat
        else s.mem a
      | _ => s.mem a
    { s with regs := s.regs.set .r0 errCode, mem := mem' }
  | _ => { s with regs := s.regs.set .r0 0 }

/-! ## Single-step semantics -/

/-- Execute one instruction, returning the new state. -/
@[simp] def step (insn : Insn) (s : State) : State :=
  let rf := s.regs
  let mem := s.mem
  let pc' := s.pc + 1
  match insn with

  | .lddw dst imm =>
    { s with regs := rf.set dst (toU64 imm), pc := pc' }

  | .ldx w dst src off =>
    let addr := effectiveAddr (rf.get src) off
    let val := readByWidth mem addr w
    { s with regs := rf.set dst val, pc := pc' }

  | .st w dst off imm =>
    let addr := effectiveAddr (rf.get dst) off
    let val := (toU64 imm) % (2 ^ (w.bytes * 8))
    { s with mem := writeByWidth mem addr val w, pc := pc' }

  | .stx w dst off src =>
    let addr := effectiveAddr (rf.get dst) off
    let val := rf.get src % (2 ^ (w.bytes * 8))
    { s with mem := writeByWidth mem addr val w, pc := pc' }

  | .add64 dst src =>
    { s with regs := rf.set dst (wrapAdd (rf.get dst) (resolveSrc rf src)), pc := pc' }
  | .sub64 dst src =>
    { s with regs := rf.set dst (wrapSub (rf.get dst) (resolveSrc rf src)), pc := pc' }
  | .mul64 dst src =>
    { s with regs := rf.set dst (wrapMul (rf.get dst) (resolveSrc rf src)), pc := pc' }
  | .div64 dst src =>
    let b := resolveSrc rf src
    if b = 0 then { s with exitCode := some ERR_DIVIDE_BY_ZERO }
    else { s with regs := rf.set dst ((rf.get dst / b) % U64_MODULUS), pc := pc' }
  | .mod64 dst src =>
    let b := resolveSrc rf src
    if b = 0 then { s with exitCode := some ERR_DIVIDE_BY_ZERO }
    else { s with regs := rf.set dst (rf.get dst % b), pc := pc' }
  | .or64 dst src =>
    { s with regs := rf.set dst ((rf.get dst ||| resolveSrc rf src) % U64_MODULUS), pc := pc' }
  | .and64 dst src =>
    { s with regs := rf.set dst ((rf.get dst &&& resolveSrc rf src) % U64_MODULUS), pc := pc' }
  | .xor64 dst src =>
    { s with regs := rf.set dst ((rf.get dst ^^^ resolveSrc rf src) % U64_MODULUS), pc := pc' }
  | .lsh64 dst src =>
    let shift := resolveSrc rf src % 64
    { s with regs := rf.set dst ((rf.get dst <<< shift) % U64_MODULUS), pc := pc' }
  | .rsh64 dst src =>
    let shift := resolveSrc rf src % 64
    { s with regs := rf.set dst (rf.get dst >>> shift), pc := pc' }
  | .arsh64 dst src =>
    let shift := resolveSrc rf src % 64
    let a := rf.get dst
    let v := if a < U64_MODULUS / 2 then a >>> shift
      else let shifted := a >>> shift
           let highBits := (U64_MODULUS - 1) - (U64_MODULUS / (2 ^ shift) - 1)
           (shifted ||| highBits) % U64_MODULUS
    { s with regs := rf.set dst v, pc := pc' }
  | .mov64 dst src =>
    { s with regs := rf.set dst (resolveSrc rf src), pc := pc' }
  | .neg64 dst =>
    { s with regs := rf.set dst (wrapNeg (rf.get dst)), pc := pc' }

  -- 32-bit ALU: result zero-extended to 64 bits
  | .add32 dst src =>
    { s with regs := rf.set dst (wrapAdd32 (rf.get dst) (resolveSrc rf src)), pc := pc' }
  | .sub32 dst src =>
    { s with regs := rf.set dst (wrapSub32 (rf.get dst) (resolveSrc rf src)), pc := pc' }
  | .mul32 dst src =>
    { s with regs := rf.set dst (wrapMul32 (rf.get dst) (resolveSrc rf src)), pc := pc' }
  | .div32 dst src =>
    let b := resolveSrc rf src % U32_MODULUS
    if b = 0 then { s with exitCode := some ERR_DIVIDE_BY_ZERO }
    else { s with regs := rf.set dst ((rf.get dst % U32_MODULUS / b) % U32_MODULUS), pc := pc' }
  | .mod32 dst src =>
    let b := resolveSrc rf src % U32_MODULUS
    if b = 0 then { s with exitCode := some ERR_DIVIDE_BY_ZERO }
    else { s with regs := rf.set dst (rf.get dst % U32_MODULUS % b), pc := pc' }
  | .or32 dst src =>
    { s with regs := rf.set dst ((rf.get dst ||| resolveSrc rf src) % U32_MODULUS), pc := pc' }
  | .and32 dst src =>
    { s with regs := rf.set dst ((rf.get dst &&& resolveSrc rf src) % U32_MODULUS), pc := pc' }
  | .xor32 dst src =>
    { s with regs := rf.set dst ((rf.get dst ^^^ resolveSrc rf src) % U32_MODULUS), pc := pc' }
  | .lsh32 dst src =>
    let shift := resolveSrc rf src % 32
    { s with regs := rf.set dst ((rf.get dst <<< shift) % U32_MODULUS), pc := pc' }
  | .rsh32 dst src =>
    let shift := resolveSrc rf src % 32
    { s with regs := rf.set dst ((rf.get dst % U32_MODULUS) >>> shift), pc := pc' }
  | .arsh32 dst src =>
    let shift := resolveSrc rf src % 32
    let a := rf.get dst % U32_MODULUS
    let v := if a < U32_MODULUS / 2 then a >>> shift
      else let shifted := a >>> shift
           let highBits := (U32_MODULUS - 1) - (U32_MODULUS / (2 ^ shift) - 1)
           (shifted ||| highBits) % U32_MODULUS
    { s with regs := rf.set dst v, pc := pc' }
  | .mov32 dst src =>
    { s with regs := rf.set dst (resolveSrc rf src % U32_MODULUS), pc := pc' }
  | .neg32 dst =>
    { s with regs := rf.set dst (wrapNeg32 (rf.get dst)), pc := pc' }

  | .jeq dst src target =>
    { s with pc := if rf.get dst = resolveSrc rf src then target else pc' }
  | .jne dst src target =>
    { s with pc := if rf.get dst ≠ resolveSrc rf src then target else pc' }
  | .jgt dst src target =>
    { s with pc := if rf.get dst > resolveSrc rf src then target else pc' }
  | .jge dst src target =>
    { s with pc := if rf.get dst ≥ resolveSrc rf src then target else pc' }
  | .jlt dst src target =>
    { s with pc := if rf.get dst < resolveSrc rf src then target else pc' }
  | .jle dst src target =>
    { s with pc := if rf.get dst ≤ resolveSrc rf src then target else pc' }
  | .jsgt dst src target =>
    { s with pc := if toSigned64 (rf.get dst) > toSigned64 (resolveSrc rf src) then target else pc' }
  | .jsge dst src target =>
    { s with pc := if toSigned64 (rf.get dst) ≥ toSigned64 (resolveSrc rf src) then target else pc' }
  | .jslt dst src target =>
    { s with pc := if toSigned64 (rf.get dst) < toSigned64 (resolveSrc rf src) then target else pc' }
  | .jsle dst src target =>
    { s with pc := if toSigned64 (rf.get dst) ≤ toSigned64 (resolveSrc rf src) then target else pc' }
  | .jset dst src target =>
    { s with pc := if rf.get dst &&& resolveSrc rf src ≠ 0 then target else pc' }
  | .ja target =>
    { s with pc := target }

  | .call syscall =>
    let s' := execSyscall syscall s
    { s' with pc := pc' }

  | .exit =>
    { s with exitCode := some (rf.get .r0) }

/-! ## Multi-step execution -/

abbrev Program := Array Insn

/-- Execute using a function-based instruction fetch (O(1) per step). -/
def executeFn (fetch : Nat → Option Insn) (s : State) (fuel : Nat) : State :=
  match fuel with
  | 0 => s
  | fuel' + 1 =>
    match s.exitCode with
    | some _ => s
    | none =>
      match fetch s.pc with
      | none => { s with exitCode := some ERR_INVALID_PC }
      | some insn => executeFn fetch (step insn s) fuel'

/-- Create an initial machine state with r1 pointing to the input buffer -/
@[simp] def initState (inputAddr : Nat) (mem : Mem) : State where
  regs := { r1 := inputAddr, r10 := STACK_START + 0x1000 }
  mem := mem
  pc := 0

/-- Two-pointer initial state for SIMD-0321 programs.
    r1 = input buffer, r2 = instruction data pointer.
    `entryPc` allows starting at a non-zero entrypoint (e.g. when error
    handlers are laid out before the entrypoint). -/
@[simp] def initState2 (inputAddr insnAddr : Nat) (mem : Mem) (entryPc : Nat := 0) : State where
  regs := { r1 := inputAddr, r2 := insnAddr, r10 := STACK_START + 0x1000 }
  mem := mem
  pc := entryPc

/-! ## Execution unrolling lemmas -/

@[simp] theorem executeFn_halted (fetch : Nat → Option Insn) (s : State) (n : Nat) (code : Nat)
    (h : s.exitCode = some code) :
    executeFn fetch s n = s := by
  cases n with
  | zero => simp [executeFn]
  | succ n => simp [executeFn, h]

@[simp] theorem executeFn_zero (fetch : Nat → Option Insn) (s : State) :
    executeFn fetch s 0 = s := by
  simp [executeFn]

theorem executeFn_step (fetch : Nat → Option Insn) (s : State) (n : Nat) (insn : Insn)
    (h_running : s.exitCode = none)
    (h_fetch : fetch s.pc = some insn) :
    executeFn fetch s (n + 1) = executeFn fetch (step insn s) n := by
  simp [executeFn, h_running, h_fetch]

/-- Composability of deterministic execution: running n+m steps is the same as
    running n steps then running m steps from the resulting state. -/
theorem executeFn_compose (fetch : Nat → Option Insn) (s : State) (n m : Nat) :
    executeFn fetch s (n + m) = executeFn fetch (executeFn fetch s n) m := by
  induction n generalizing s with
  | zero => simp [executeFn]
  | succ n ih =>
    rw [Nat.succ_add]
    simp only [executeFn]
    split
    · -- halted: exitCode = some _
      rename_i h_halted
      simp [executeFn_halted, h_halted]
    · -- running: exitCode = none
      split
      · -- invalid PC: fetch returns none → sets exitCode, then halted for m steps
        simp [executeFn_halted]
      · -- valid instruction
        rename_i insn h_fetch
        exact ih (step insn s)

/-! ## Frame pointer (r10) invariance

r10 is the SVM frame pointer. It is set by the runtime at program entry
and never modified: `RegFile.set .r10 v = rf` (no-op). This means r10
is invariant through all execution — no need to thread `h_r10` hypotheses. -/

@[simp] theorem execSyscall_preserves_r10 (sc : Syscall) (s : State) :
    (execSyscall sc s).regs.r10 = s.regs.r10 := by
  cases sc <;> simp [execSyscall]

@[simp] theorem step_preserves_r10 (insn : Insn) (s : State) :
    (step insn s).regs.r10 = s.regs.r10 := by
  cases insn <;> (dsimp only [step]; try split) <;>
    simp only [RegFile.set_preserves_r10, execSyscall_preserves_r10]

@[simp] theorem executeFn_preserves_r10 (fetch : Nat → Option Insn) (s : State) (n : Nat) :
    (executeFn fetch s n).regs.r10 = s.regs.r10 := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [executeFn]
    split
    · rfl
    · split
      · rfl
      · rw [ih]; exact step_preserves_r10 _ _

/-- r10 = STACK_START + 0x1000 is invariant from initState. -/
theorem executeFn_r10_initState (fetch : Nat → Option Insn) (inputAddr : Nat) (mem : Mem) (n : Nat) :
    (executeFn fetch (initState inputAddr mem) n).regs.r10 = STACK_START + 0x1000 := by
  simp [initState]

/-- r10 = STACK_START + 0x1000 is invariant from initState2. -/
theorem executeFn_r10_initState2 (fetch : Nat → Option Insn) (inputAddr insnAddr : Nat)
    (mem : Mem) (entryPc : Nat) (n : Nat) :
    (executeFn fetch (initState2 inputAddr insnAddr mem entryPc) n).regs.r10
      = STACK_START + 0x1000 := by
  simp [initState2]

/-! ## Paired execution (for tactic automation)

`execInsn` and `execSegment` mirror `step` and `executeFn` exactly but
return `PUnit × State` instead of bare `State`. This paired form lets
`wp_exec` unfold one instruction at a time via `dsimp [execInsn, ...]`
at O(1) kernel depth per step — avoiding the recursive blowup that would
occur from unfolding `executeFn` directly. -/

/-- A paired state transition: takes a state, returns `((), newState)`.
    The `PUnit` tag is structurally required so `dsimp` can reduce
    one instruction at a time without unfolding the full recursion. -/
abbrev Step := State → PUnit × State

/-- Single-step paired transition: mirrors `step` exactly but returns
    `PUnit × State` for tactic-friendly unfolding. -/
@[simp] def execInsn (insn : Insn) : Step := fun s =>
  let rf := s.regs
  let mem := s.mem
  let pc' := s.pc + 1
  match insn with

  | .lddw dst imm =>
    ((), { s with regs := rf.set dst (toU64 imm), pc := pc' })

  | .ldx w dst src off =>
    let addr := effectiveAddr (rf.get src) off
    let val := readByWidth mem addr w
    ((), { s with regs := rf.set dst val, pc := pc' })

  | .st w dst off imm =>
    let addr := effectiveAddr (rf.get dst) off
    let val := (toU64 imm) % (2 ^ (w.bytes * 8))
    ((), { s with mem := writeByWidth mem addr val w, pc := pc' })

  | .stx w dst off src =>
    let addr := effectiveAddr (rf.get dst) off
    let val := rf.get src % (2 ^ (w.bytes * 8))
    ((), { s with mem := writeByWidth mem addr val w, pc := pc' })

  | .add64 dst src =>
    ((), { s with regs := rf.set dst (wrapAdd (rf.get dst) (resolveSrc rf src)), pc := pc' })
  | .sub64 dst src =>
    ((), { s with regs := rf.set dst (wrapSub (rf.get dst) (resolveSrc rf src)), pc := pc' })
  | .mul64 dst src =>
    ((), { s with regs := rf.set dst (wrapMul (rf.get dst) (resolveSrc rf src)), pc := pc' })
  | .div64 dst src =>
    let b := resolveSrc rf src
    if b = 0 then ((), { s with exitCode := some ERR_DIVIDE_BY_ZERO })
    else ((), { s with regs := rf.set dst ((rf.get dst / b) % U64_MODULUS), pc := pc' })
  | .mod64 dst src =>
    let b := resolveSrc rf src
    if b = 0 then ((), { s with exitCode := some ERR_DIVIDE_BY_ZERO })
    else ((), { s with regs := rf.set dst (rf.get dst % b), pc := pc' })
  | .or64 dst src =>
    ((), { s with regs := rf.set dst ((rf.get dst ||| resolveSrc rf src) % U64_MODULUS), pc := pc' })
  | .and64 dst src =>
    ((), { s with regs := rf.set dst ((rf.get dst &&& resolveSrc rf src) % U64_MODULUS), pc := pc' })
  | .xor64 dst src =>
    ((), { s with regs := rf.set dst ((rf.get dst ^^^ resolveSrc rf src) % U64_MODULUS), pc := pc' })
  | .lsh64 dst src =>
    let shift := resolveSrc rf src % 64
    ((), { s with regs := rf.set dst ((rf.get dst <<< shift) % U64_MODULUS), pc := pc' })
  | .rsh64 dst src =>
    let shift := resolveSrc rf src % 64
    ((), { s with regs := rf.set dst (rf.get dst >>> shift), pc := pc' })
  | .arsh64 dst src =>
    let shift := resolveSrc rf src % 64
    let a := rf.get dst
    let v := if a < U64_MODULUS / 2 then a >>> shift
      else let shifted := a >>> shift
           let highBits := (U64_MODULUS - 1) - (U64_MODULUS / (2 ^ shift) - 1)
           (shifted ||| highBits) % U64_MODULUS
    ((), { s with regs := rf.set dst v, pc := pc' })
  | .mov64 dst src =>
    ((), { s with regs := rf.set dst (resolveSrc rf src), pc := pc' })
  | .neg64 dst =>
    ((), { s with regs := rf.set dst (wrapNeg (rf.get dst)), pc := pc' })

  -- 32-bit ALU
  | .add32 dst src =>
    ((), { s with regs := rf.set dst (wrapAdd32 (rf.get dst) (resolveSrc rf src)), pc := pc' })
  | .sub32 dst src =>
    ((), { s with regs := rf.set dst (wrapSub32 (rf.get dst) (resolveSrc rf src)), pc := pc' })
  | .mul32 dst src =>
    ((), { s with regs := rf.set dst (wrapMul32 (rf.get dst) (resolveSrc rf src)), pc := pc' })
  | .div32 dst src =>
    let b := resolveSrc rf src % U32_MODULUS
    if b = 0 then ((), { s with exitCode := some ERR_DIVIDE_BY_ZERO })
    else ((), { s with regs := rf.set dst ((rf.get dst % U32_MODULUS / b) % U32_MODULUS), pc := pc' })
  | .mod32 dst src =>
    let b := resolveSrc rf src % U32_MODULUS
    if b = 0 then ((), { s with exitCode := some ERR_DIVIDE_BY_ZERO })
    else ((), { s with regs := rf.set dst (rf.get dst % U32_MODULUS % b), pc := pc' })
  | .or32 dst src =>
    ((), { s with regs := rf.set dst ((rf.get dst ||| resolveSrc rf src) % U32_MODULUS), pc := pc' })
  | .and32 dst src =>
    ((), { s with regs := rf.set dst ((rf.get dst &&& resolveSrc rf src) % U32_MODULUS), pc := pc' })
  | .xor32 dst src =>
    ((), { s with regs := rf.set dst ((rf.get dst ^^^ resolveSrc rf src) % U32_MODULUS), pc := pc' })
  | .lsh32 dst src =>
    let shift := resolveSrc rf src % 32
    ((), { s with regs := rf.set dst ((rf.get dst <<< shift) % U32_MODULUS), pc := pc' })
  | .rsh32 dst src =>
    let shift := resolveSrc rf src % 32
    ((), { s with regs := rf.set dst ((rf.get dst % U32_MODULUS) >>> shift), pc := pc' })
  | .arsh32 dst src =>
    let shift := resolveSrc rf src % 32
    let a := rf.get dst % U32_MODULUS
    let v := if a < U32_MODULUS / 2 then a >>> shift
      else let shifted := a >>> shift
           let highBits := (U32_MODULUS - 1) - (U32_MODULUS / (2 ^ shift) - 1)
           (shifted ||| highBits) % U32_MODULUS
    ((), { s with regs := rf.set dst v, pc := pc' })
  | .mov32 dst src =>
    ((), { s with regs := rf.set dst (resolveSrc rf src % U32_MODULUS), pc := pc' })
  | .neg32 dst =>
    ((), { s with regs := rf.set dst (wrapNeg32 (rf.get dst)), pc := pc' })

  -- Conditional jumps
  | .jeq dst src target =>
    ((), { s with pc := if rf.get dst = resolveSrc rf src then target else pc' })
  | .jne dst src target =>
    ((), { s with pc := if rf.get dst ≠ resolveSrc rf src then target else pc' })
  | .jgt dst src target =>
    ((), { s with pc := if rf.get dst > resolveSrc rf src then target else pc' })
  | .jge dst src target =>
    ((), { s with pc := if rf.get dst ≥ resolveSrc rf src then target else pc' })
  | .jlt dst src target =>
    ((), { s with pc := if rf.get dst < resolveSrc rf src then target else pc' })
  | .jle dst src target =>
    ((), { s with pc := if rf.get dst ≤ resolveSrc rf src then target else pc' })
  | .jsgt dst src target =>
    ((), { s with pc := if toSigned64 (rf.get dst) > toSigned64 (resolveSrc rf src) then target else pc' })
  | .jsge dst src target =>
    ((), { s with pc := if toSigned64 (rf.get dst) ≥ toSigned64 (resolveSrc rf src) then target else pc' })
  | .jslt dst src target =>
    ((), { s with pc := if toSigned64 (rf.get dst) < toSigned64 (resolveSrc rf src) then target else pc' })
  | .jsle dst src target =>
    ((), { s with pc := if toSigned64 (rf.get dst) ≤ toSigned64 (resolveSrc rf src) then target else pc' })
  | .jset dst src target =>
    ((), { s with pc := if rf.get dst &&& resolveSrc rf src ≠ 0 then target else pc' })
  | .ja target =>
    ((), { s with pc := target })

  -- Syscall
  | .call syscall =>
    let s' := execSyscall syscall s
    ((), { s' with pc := pc' })

  -- Exit
  | .exit =>
    ((), { s with exitCode := some (rf.get .r0) })

/-- execInsn produces the same state as step (just wrapped in a PUnit pair). -/
theorem step_eq_execInsn (insn : Insn) (s : State) :
    step insn s = (execInsn insn s).2 := by
  cases insn <;> simp only [step, execInsn] <;> split <;> rfl

/-- Multi-step paired execution using function-based fetch. -/
def execSegment (fetch : Nat → Option Insn) : Nat → Step
  | 0 => fun s => ((), s)
  | fuel + 1 => fun s =>
    match s.exitCode with
    | some _ => ((), s)
    | none =>
      match fetch s.pc with
      | none => ((), { s with exitCode := some ERR_INVALID_PC })
      | some insn =>
        let (_, s') := execInsn insn s
        execSegment fetch fuel s'

/-- executeFn and execSegment produce the same final state. -/
theorem executeFn_eq_execSegment (fetch : Nat → Option Insn) (s : State) (fuel : Nat) :
    executeFn fetch s fuel = (execSegment fetch fuel s).2 := by
  induction fuel generalizing s with
  | zero => rfl
  | succ n ih =>
    unfold executeFn execSegment
    cases h_exit : s.exitCode with
    | some _ => rfl
    | none =>
      cases h_fetch : fetch s.pc with
      | none => rfl
      | some insn =>
        simp (config := { failIfUnchanged := false }) only [h_exit]
        have heq : step insn s = (execInsn insn s).2 := step_eq_execInsn insn s
        rw [heq]
        exact ih (execInsn insn s).2

end Svm.SBPF
