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
import Svm.Native.Precompiles

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

/-! ## Multi-program registry (for CPI)

Real Solana programs CPI into other programs (System, Token, ATA, etc.).
The `Runner.RunConfig.programRegistry` field accepts a `Nat → Option
ByteArray` lookup from program-id (encoded as LE Nat over 32 bytes) to
that program's ELF bytes; the CPI stub at `Runner.executeFnCpiWithFuel`
consults it on `.sol_invoke_signed` / `.sol_invoke_signed_c`.

For Rust callers that hold multiple ELFs in a `HashMap<Pubkey, Vec<u8>>`,
we accept the whole map as a flat ByteArray blob, parse it once on
entry, and hand a closure to the runner.

Blob format (all LE):
  u32 num_entries
  for each entry:
    [32]u8 pubkey
    u32 elf_size
    [u8]; elf_size  elf bytes
-/

/-- Decode 32 raw pubkey bytes at `bytes[off..off+32]` as a little-endian
    Nat. Matches the same convention the CPI handler uses when reading
    32 bytes from caller memory (so both halves of the lookup agree). -/
def pubkeyToNat (bytes : ByteArray) (off : Nat) : Nat :=
  (List.range 32).foldl
    (fun acc i => acc + (bytes.get! (off + i)).toNat * 256^i) 0

/-- Parse a registry blob into a `(Nat → Option ByteArray)` lookup.
    Linear scan on each lookup — fine for the small program counts
    typical of one transaction (<= ~32 programs in practice).
    Malformed blob (truncated, count overflow) yields an empty
    registry. -/
def parseRegistry (blob : ByteArray) : Nat → Option ByteArray :=
  if blob.size < 4 then fun _ => none
  else
    let count := readU32LE blob 0
    let entries : List (Nat × ByteArray) :=
      (List.range count).foldl (fun acc _ =>
        let off : Nat :=
          acc.foldl (fun acc' (_, elf) => acc' + 32 + 4 + elf.size) 4
        if off + 36 > blob.size then acc
        else
          let pk := pubkeyToNat blob off
          let elfSize := readU32LE blob (off + 32)
          let elfEnd := off + 36 + elfSize
          if elfEnd > blob.size then acc
          else
            let elf := blob.extract (off + 36) elfEnd
            acc ++ [(pk, elf)]) []
    fun pid =>
      (entries.find? (·.1 = pid)).map (·.2)
where
  /-- Read u32 LE from a ByteArray (Ffi-local copy, distinct from
      Decode.readU32LE which works on a different input shape). -/
  readU32LE (bytes : ByteArray) (off : Nat) : Nat :=
    (bytes.get! off).toNat +
    (bytes.get! (off + 1)).toNat * 0x100 +
    (bytes.get! (off + 2)).toNat * 0x10000 +
    (bytes.get! (off + 3)).toNat * 0x1000000

/-- Like `runElfBuffer` but additionally accepts a `registry` blob (see
    "Multi-program registry" above). Used by Rust harnesses that need
    CPI support — `Svm::add_program` populates a map, we serialize it
    once, and the Lean runner consults it for each
    `.sol_invoke_signed{,_c}` call. -/
@[export formal_svm_run_with_registry]
def runWithRegistry (elf input registry : ByteArray) (cuBudget : UInt64)
    : ByteArray :=
  let cfg : Runner.RunConfig :=
    { input           := input
      cuBudget        := cuBudget.toNat
      programRegistry := parseRegistry registry }
  match Runner.runElfWithFuel elf cfg with
  | none => encodeElfError
  | some (s, fuelRemaining) =>
    let consumed := (cuBudget.toNat - fuelRemaining) + s.cuConsumed
    encodeRun s input.size (UInt64.ofNat consumed)

/-! ## Top-level precompile dispatch

Agave's three sig-verify precompiles (`Ed25519SigVerify1111…`,
`KeccakSecp256k11111…`, `Secp256r1SigVerify1111…`) never enter the
BPF VM. Rust callers detect their pubkeys early in
`process_instruction` and bypass the BPF path. This entrypoint runs
the Lean spec (`Svm.Native.Precompiles.dispatch`) end-to-end against
the instruction data and returns a compact `(r0, cu)` pair.

Wire format of the returned `ByteArray` (16 bytes total):
  bytes 0..8   u64 LE  r0 (0 = Success; 1 = failure)
  bytes 8..16  u64 LE  CU consumed

`pidBytes` is the 32-byte raw program pubkey; we LE-decode it into
the same `Nat` representation the dispatch table keys on. Non-
precompile pids return `(r0=1, cu=0)` — callers are expected to
gate this entrypoint behind their own precompile check, but the
fallback is safe. -/
@[export formal_svm_precompile_dispatch]
def precompileDispatch (pidBytes ixData : ByteArray) : ByteArray :=
  let pid := pubkeyToNat pidBytes 0
  let r := match Svm.Native.Precompiles.dispatch pid ixData [] (fun _ => 0) with
           | some res => (UInt64.ofNat res.r0, UInt64.ofNat res.cu)
           | none     => (1, 0)
  encodeU64 r.1 ++ encodeU64 r.2

end Svm.Ffi
