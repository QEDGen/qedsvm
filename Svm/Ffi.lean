/-
  Rust-facing FFI entrypoint.

  Exposes a single C symbol — `formal_svm_run_elf_buffer` — that takes
  an ELF blob, an input buffer (the serialized accounts/instruction
  layout that real Solana programs deserialize via `entrypoint!`), and
  a CU budget. Drives `Runner.runElf` and serializes the observable
  result into a flat ByteArray for the Rust consumer to decode.

  We return a flat wire format rather than a multi-field Lean
  constructor because the Rust side only has to know one thing
  (ByteArray layout) instead of multiple (Lean's `Option`, `Array`,
  and ctor reprs). The format is documented inline below.

  This file is the *only* Lean entrypoint Rust callers should rely
  on. The rest of `Svm.*` is internal API that may change shape.
-/

import Svm.SBPF.Runner

namespace Svm.Ffi

open Svm.SBPF
open Svm.SBPF.Memory

/-! ## Wire format

The returned `ByteArray` is one of:

  status = 0  → ELF parse / decode failure. No further bytes.

  status = 1  → executed (cleanly or out-of-CU). Followed by:
                u8  exit_kind   0 = none (out of CU budget)
                                1 = some (program halted; r0 = exit_code)
                u64 exit_code   little-endian; present only if exit_kind == 1
                u64 cu_consumed little-endian; always present
                u32 input_len   little-endian; modified input region length
                [u8] input      `input_len` bytes
                u32 num_logs    little-endian
                  for each log:
                    u32 log_len
                    [u8] log    `log_len` bytes
                u32 rd_len      return-data length
                [u8] rd         `rd_len` bytes

All integers are little-endian (matches sBPF + Solana convention).
ByteArray construction is deliberately functional + straightforward;
the encoding path is not perf-critical (called once per `process_instruction`). -/

/-- Encode a `UInt32` as 4 LE bytes. -/
def encodeU32 (n : UInt32) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let n := n.toNat
  for i in [0:4] do
    out := out.push (((n / (256 ^ i)) % 256).toUInt8)
  return out

/-- Encode a `UInt64` as 8 LE bytes. -/
def encodeU64 (n : UInt64) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let n := n.toNat
  for i in [0:8] do
    out := out.push (((n / (256 ^ i)) % 256).toUInt8)
  return out

/-- Append a u32-length-prefixed byte slice. -/
def appendLP (acc bs : ByteArray) : ByteArray :=
  acc ++ encodeU32 (UInt32.ofNat bs.size) ++ bs

/-- The status-byte-only encoding of "couldn't decode this ELF". -/
def encodeElfError : ByteArray :=
  ByteArray.empty.push 0

/-- Encode the post-execution `State` along with the original input
    length (so the caller knows how many bytes of memory at
    `INPUT_START` represent the modified input region) and the
    compute units consumed during execution. -/
def encodeRun (s : State) (inputLen : Nat) (cuConsumed : UInt64) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  out := out.push 1  -- status: executed
  match s.exitCode with
  | none =>
    out := out.push 0
  | some n =>
    out := out.push 1
    out := out ++ encodeU64 (UInt64.ofNat n)
  out := out ++ encodeU64 cuConsumed
  -- Modified input region.
  let inputBytes := readBytes s.mem INPUT_START inputLen
  out := appendLP out inputBytes
  -- Logs.
  out := out ++ encodeU32 (UInt32.ofNat s.log.size)
  for log in s.log do
    out := appendLP out log
  -- Return data.
  out := appendLP out s.returnData
  return out

/-- The Rust-facing entrypoint.

    Decodes `elf`, places `input` at `INPUT_START`, runs for up to
    `cuBudget` compute units, and serializes the result (including
    `cuConsumed`). Total failure (couldn't decode the ELF) returns a
    single byte `0x00`. -/
@[export formal_svm_run_elf_buffer]
def runElfBuffer (elf input : ByteArray) (cuBudget : UInt64) : ByteArray :=
  let cfg : Runner.RunConfig := { input := input, cuBudget := cuBudget.toNat }
  match Runner.runElfWithFuel elf cfg with
  | none => encodeElfError
  | some (s, fuelRemaining) =>
    -- `fuelRemaining ≤ cuBudget.toNat` by construction of
    -- `executeFnCpiWithFuel`. Total reported CU = step count
    -- (cuBudget - fuelRemaining) + extra syscall overhead
    -- (s.cuConsumed); the latter is bumped by `step`'s `.call`
    -- arm via `Svm.SBPF.syscallCu`.
    let consumed := (cuBudget.toNat - fuelRemaining) + s.cuConsumed
    encodeRun s input.size (UInt64.ofNat consumed)

end Svm.Ffi
