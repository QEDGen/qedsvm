/-
  sBPF runner — the production entrypoint for executing arbitrary sBPF
  bytecode under the Lean semantics.

  Decoupled from any demo or test fixture. The runner is the public
  interface a downstream consumer wires up:

      Svm.SBPF.Runner.run : ByteArray → RunConfig → Option State

  Given a bytecode blob and a configuration (input bytes, CU budget),
  returns the final machine state. The caller inspects `state.exitCode`
  to determine the outcome:

  - `none` → the CU budget was exhausted before the program halted
  - `some Memory.ERR_INVALID_PC` → execution fell off the program
  - `some n` → the program executed `exit` with `r0 = n`

  Real Solana programs receive their input via `r1` pointing to a
  serialized buffer in the input region. The runner populates this for
  you: bytes in `cfg.input` are written to memory at `INPUT_START`, and
  the initial `r1` is set to `INPUT_START`.
-/

import Svm.SBPF.Decode
import Svm.SBPF.Elf

namespace Svm.SBPF
namespace Runner

open Memory

/-! ## Memory + register initialization -/

/-- Empty memory: every byte is zero. -/
def emptyMem : Mem := fun _ => 0

/-- Overlay a ByteArray onto memory starting at `baseAddr`. Outside the
    overlaid range the underlying memory is preserved. -/
def loadBytesAt (mem : Mem) (bytes : ByteArray) (baseAddr : Nat) : Mem :=
  fun a =>
    if a < baseAddr then mem a
    else
      let offset := a - baseAddr
      if offset < bytes.size then (bytes.get! offset).toNat
      else mem a

/-- Overlay the input buffer at `INPUT_START`. -/
def loadInput (mem : Mem) (input : ByteArray) : Mem :=
  loadBytesAt mem input INPUT_START

/-- Build a `fetch` function from a decoded instruction array. -/
def fetchFromArray (insns : Array Insn) : Nat → Option Insn :=
  fun pc => if h : pc < insns.size then some (insns[pc]'h) else none

/-! ## Run configuration -/

/-- Per-run configuration for the sBPF runner. -/
structure RunConfig where
  /-- Bytes to load into memory at `INPUT_START`. Real Solana programs
      read their account inputs and instruction data from this region. -/
  input    : ByteArray := ByteArray.empty
  /-- Maximum number of compute units (instructions) to execute before
      giving up. Default matches Solana's per-program CU cap. -/
  cuBudget : Nat := 200_000
  /-- Registry of programs callable via `sol_invoke_signed[_c]`.
      Maps a program-id (modeled as a `Nat`; the demo uses `r1` directly
      as the id) to the callee's raw ELF-free bytecode. The CPI handler
      decodes on demand. Default: no callees — every CPI returns r0 := 1. -/
  programRegistry : Nat → Option ByteArray := fun _ => none

/-! ## CPI-aware execution

`executeFnCpi` is a CPI-handling wrapper around `step`. For every
instruction *except* `sol_invoke_signed` / `sol_invoke_signed_c` it
delegates to `step` (so the existing single-step semantics and all the
proofs about them still apply unchanged). For CPI it consults
`programRegistry`, decodes the callee, builds a fresh sub-state, runs
the callee recursively under the same registry, and writes the callee's
exit code into the caller's `r0`.

v1 simplifications (tracked in `docs/next-session-plan.md`):
- `r1` is read as the program-id directly (not a `*const SolInstruction`).
  A future revision will read a full `SolInstruction` C struct from
  memory at `r1` and use its `program_id` field.
- The callee starts with an empty input buffer (no serialized account
  metadata). Real callees expect a `solana-program/src/entrypoint.rs`
  layout at `INPUT_START`.
- No account write-back to the caller's memory.
- PDA signer seeds (`r4` / `r5`) are ignored.
- The full caller CU budget is passed to the callee (no proportional
  split). Re-entrant CPI is supported transparently by the recursion. -/
def executeFnCpi (registry : Nat → Option ByteArray)
    (fetch : Nat → Option Insn) (s : State) (fuel : Nat) : State :=
  match fuel with
  | 0 => s
  | fuel' + 1 =>
    match s.exitCode with
    | some _ => s
    | none =>
      match fetch s.pc with
      | none => { s with exitCode := some ERR_INVALID_PC }
      | some insn =>
        let s' : State :=
          match insn with
          | .call .sol_invoke_signed | .call .sol_invoke_signed_c =>
            let pid := s.regs.r1
            match registry pid with
            | none =>
              { s with regs := s.regs.set .r0 1, pc := s.pc + 1 }
            | some calleeBytes =>
              match Decode.decodeProgram calleeBytes with
              | none =>
                { s with regs := s.regs.set .r0 1, pc := s.pc + 1 }
              | some calleeInsns =>
                let subS : State :=
                  { regs       := { r1 := INPUT_START, r10 := STACK_START + 0x1000 }
                    mem        := s.mem
                    pc         := 0
                    exitCode   := none
                    log        := s.log
                    returnData := ByteArray.empty }
                let subFinal :=
                  executeFnCpi registry (fetchFromArray calleeInsns) subS fuel'
                { s with regs       := s.regs.set .r0 (subFinal.exitCode.getD 1)
                         pc         := s.pc + 1
                         log        := subFinal.log
                         returnData := subFinal.returnData }
          | _ => step insn s
        executeFnCpi registry fetch s' fuel'

/-! ## Entrypoints -/

/-- Decode `bytes` and run for up to `cfg.cuBudget` compute units. Returns
    the final machine state, or `none` if decoding fails.

    Inspect `state.exitCode`:
    - `none` → out of CU budget
    - `some Memory.ERR_INVALID_PC` → invalid PC (fell off program)
    - `some n` → clean exit with return code `n` -/
def run (bytes : ByteArray) (cfg : RunConfig := {}) : Option State := do
  let insns ← Decode.decodeProgram bytes
  let mem := loadInput emptyMem cfg.input
  let s : State :=
    { regs    := { r1 := INPUT_START, r10 := STACK_START + 0x1000 }
      mem     := mem
      pc      := 0
      exitCode := none }
  return executeFnCpi cfg.programRegistry (fetchFromArray insns) s cfg.cuBudget

/-- Convenience: return only the exit code if the program terminated. -/
def runForExit (bytes : ByteArray) (cfg : RunConfig := {}) : Option Nat :=
  (run bytes cfg).bind (·.exitCode)

/-! ## ELF entrypoints

Real Solana programs ship as ELF64 binaries. These entrypoints parse the
ELF wrapper, extract the `.text` bytecode, and feed it to `run`. -/

/-- Decode and run an sBPF ELF64 binary. Returns the final state, or
    `none` if the ELF is malformed or contains no `.text` section.

    `.rodata` (if present) is mapped into memory at its `sh_addr` so that
    `lddw`/`ldx` pointer dereferences against rodata addresses resolve
    correctly. This matches the universal pattern across Anchor,
    Pinocchio, native-Rust, and Quasar binaries. -/
def runElf (elfBytes : ByteArray) (cfg : RunConfig := {}) : Option State :=
  match Elf.parseHeader elfBytes with
  | none => none
  | some header =>
    match Elf.findSection elfBytes header Elf.textName with
    | none => none
    | some textSec =>
      let rawText   := Elf.extractSection elfBytes textSec
      -- Patch R_BPF_64_64 relocations (lddw → .rodata-relative pointers).
      -- A no-op when the ELF has no .dynsym/.rel.dyn sections.
      let textBytes := Elf.applyRelocations elfBytes header textSec.addr rawText
      match Decode.decodeProgram textBytes with
      | none => none
      | some insns =>
        let baseMem := loadInput emptyMem cfg.input
        let mem := match Elf.findSection elfBytes header Elf.rodataName with
          | some sec => loadBytesAt baseMem (Elf.extractSection elfBytes sec) sec.addr
          | none => baseMem
        let s : State :=
          { regs    := { r1 := INPUT_START, r10 := STACK_START + 0x1000 }
            mem     := mem
            pc      := 0
            exitCode := none }
        some (executeFnCpi cfg.programRegistry (fetchFromArray insns) s cfg.cuBudget)

/-- Convenience: ELF run returning only the exit code. -/
def runElfForExit (elfBytes : ByteArray) (cfg : RunConfig := {}) : Option Nat :=
  (runElf elfBytes cfg).bind (·.exitCode)

end Runner
end Svm.SBPF
