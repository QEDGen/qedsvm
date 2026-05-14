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

/-! ## CPI sub-input construction

When a program issues `sol_invoke_signed{,_c}`, the callee expects its
input buffer at `INPUT_START` to be a *fresh* `serialize_parameters`-
shaped layout for the CPI's target — not the caller's input. We build
this in Lean (mirroring `formal-svm-rs/src/serialize.rs`) so the
callee deserializes the callee-specific accounts + ix_data, not the
caller's.

Current support: zero-account CPIs only (Phase 3-minimal). Programs
that pass accounts will fall back to running against the caller's
memory (the previous semantics) — this is wrong for any callee that
actually reads its accounts, but matches what we shipped before.
-/

/-- Read `len` bytes from `mem` starting at `addr`. Mirrors
    `Machine.readBytes` but lives here so the Runner doesn't pull in
    `Machine` (which depends on `Memory` already; this keeps the
    dependency graph clean). -/
private def readMemBytes (mem : Mem) (addr len : Nat) : ByteArray :=
  ⟨(List.range len).foldl
    (fun acc i => acc.push ((mem (addr + i)) % 256).toUInt8) #[]⟩

/-- u64 LE → 8 ByteArray bytes. -/
private def u64ToLE (n : Nat) : ByteArray :=
  ⟨(List.range 8).foldl
    (fun acc i => acc.push ((n / 256^i) % 256).toUInt8) #[]⟩

/-- Build a zero-account sub-input buffer for a CPI:
    `[u64 0][u64 ix_data_len][u8;ix_data_len ix_data][u8;32 program_id]`.
    Total size = 8 + 8 + ix_data.size + 32 bytes. Matches the
    serialized layout `serialize_parameters` produces when
    `instruction.accounts` is empty. -/
def buildCpiSubInputNoAccounts (programId ixData : ByteArray) : ByteArray :=
  u64ToLE 0 ++ u64ToLE ixData.size ++ ixData ++ programId

/-! ### One-account CPI marshaling (Phase 3-full)

The AccountInfo struct passed via `r2` carries indirections through
`Rc<RefCell<…>>` to bytes that live in the *caller's* input region.
For CPI, we (a) read those bytes, (b) emit a fresh per-account block
in the sub-input, (c) run the callee, then (d) write the callee's
modifications back through the same pointers — so the caller's
input region (and thus the harness's post-state) reflects them.

`MAX_PERMITTED_DATA_INCREASE` matches agave's serializer (10240).
The per-account block layout is fixed:
```
0..1   dup_marker = 0xFF
1..2   is_signer
2..3   is_writable
3..4   executable
4..8   u32 padding 0
8..40  key (32B)
40..72 owner (32B)
72..80 lamports (u64)
80..88 data_len (u64)
88..88+L  data (L bytes)
…  align_pad + MAX_PERMITTED_DATA_INCREASE zero pad
…  rent_epoch (u64)
```
Then the trailer: `u64 ix_data_len`, `ix_data`, `u8;32 program_id`.
-/

/-- Parsed `solana_program::AccountInfo`. Captures the values needed
    for sub-input emission, plus the caller-memory addresses needed
    for write-back. Default Rust layout assumed (see comments in
    `parseAccountInfo`). -/
structure ParsedAcct where
  key             : ByteArray  -- 32 B
  owner           : ByteArray  -- 32 B
  lamports        : Nat
  dataLen         : Nat
  data            : ByteArray  -- `dataLen` bytes
  isSigner        : Bool
  isWritable      : Bool
  executable      : Bool
  rentEpoch       : Nat
  -- Write-back targets (caller-memory addresses):
  ownerPtr        : Nat  -- where `owner` bytes live in caller mem
  lamportsRefAddr : Nat  -- where the lamports u64 lives in caller mem
  dataPtr         : Nat  -- where `data` bytes live in caller mem

/-- Parse one `AccountInfo` struct at `addr` in `mem`, following the
    `Rc<RefCell<…>>` chains to the underlying bytes. Layout assumed
    (default Rust, 64-bit BPF target):
    ```
    +0   key: *const Pubkey   (u64 ptr)
    +8   lamports: Rc<RefCell<&mut u64>>  (u64 ptr to RcBox)
    +16  data: Rc<RefCell<&mut [u8]>>     (u64 ptr to RcBox)
    +24  owner: *const Pubkey
    +32  rent_epoch: u64
    +40  is_signer: u8
    +41  is_writable: u8
    +42  executable: u8
    +43..48  padding
    ```
    `RcBox<T>`: `{ strong: usize, weak: usize, value: T }` — value
    starts at offset 16. For `RefCell<T>`: `{ borrow: isize, value: T }`
    — value starts at offset 8. So `Rc<RefCell<inner>>`'s inner sits
    at `*Rc + 16 + 8 = *Rc + 24`. -/
def parseAccountInfo (mem : Mem) (addr : Nat) : ParsedAcct :=
  let keyPtr          := Memory.readU64 mem addr
  let lamportsRcPtr   := Memory.readU64 mem (addr + 8)
  let dataRcPtr       := Memory.readU64 mem (addr + 16)
  let ownerPtr        := Memory.readU64 mem (addr + 24)
  let rentEpoch       := Memory.readU64 mem (addr + 32)
  let isSigner        := (mem (addr + 40)) % 256 ≠ 0
  let isWritable      := (mem (addr + 41)) % 256 ≠ 0
  let executable      := (mem (addr + 42)) % 256 ≠ 0
  -- Chase the Rc pointers.
  let lamportsRefAddr := Memory.readU64 mem (lamportsRcPtr + 24)
  let lamports        := Memory.readU64 mem lamportsRefAddr
  let dataPtr         := Memory.readU64 mem (dataRcPtr + 24)
  let dataLen         := Memory.readU64 mem (dataRcPtr + 32)
  let key             := readMemBytes mem keyPtr 32
  let owner           := readMemBytes mem ownerPtr 32
  let data            := readMemBytes mem dataPtr dataLen
  { key, owner, lamports, dataLen, data,
    isSigner, isWritable, executable, rentEpoch,
    ownerPtr, lamportsRefAddr, dataPtr }

/-- `MAX_PERMITTED_DATA_INCREASE` from the Solana ABI. Number of zero
    bytes the serializer reserves after each account's data so the
    program may grow the buffer in place. -/
def MAX_PERMITTED_DATA_INCREASE : Nat := 10240

/-- Repeat a byte `n` times into a ByteArray. -/
private def zeroBytes (n : Nat) : ByteArray :=
  ⟨(List.range n).foldl (fun acc _ => acc.push 0) #[]⟩

/-- Build a one-account sub-input buffer for a CPI. Matches
    `serialize_parameters` byte-for-byte with `accounts = [acct]`. -/
def buildCpiSubInputOneAccount (acct : ParsedAcct)
    (programId ixData : ByteArray) : ByteArray :=
  let numAccounts := u64ToLE 1
  let dupMarker   := ByteArray.empty.push 0xFF
  let signer      : UInt8 := if acct.isSigner then 1 else 0
  let writable    : UInt8 := if acct.isWritable then 1 else 0
  let executable  : UInt8 := if acct.executable then 1 else 0
  let flags       := ⟨#[signer, writable, executable]⟩
  let padU32      := zeroBytes 4
  let lamports    := u64ToLE acct.lamports
  let dataLen     := u64ToLE acct.dataLen
  let alignPad    := zeroBytes ((8 - acct.dataLen % 8) % 8)
  let increasePad := zeroBytes MAX_PERMITTED_DATA_INCREASE
  let rentEpoch   := u64ToLE acct.rentEpoch
  let ixLen       := u64ToLE ixData.size
  numAccounts ++ dupMarker ++ flags ++ padU32
    ++ acct.key ++ acct.owner ++ lamports ++ dataLen
    ++ acct.data ++ alignPad ++ increasePad ++ rentEpoch
    ++ ixLen ++ ixData ++ programId

/-- Offsets (from `INPUT_START`) in a one-account sub-input. These
    match the layout `buildCpiSubInputOneAccount` emits: 8-byte
    `num_accounts` header, then per-account block laid out per
    `serialize_parameters`. -/
def CPI_OWNER_OFFSET    : Nat := 8 + 40                 -- = 48
def CPI_LAMPORTS_OFFSET : Nat := 8 + 72                 -- = 80
def CPI_DATA_OFFSET     : Nat := 8 + 88                 -- = 96

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
/-- CU-accounting variant of `executeFnCpi`. Returns the final state
    plus the remaining fuel — `cuConsumed = initial_fuel - returned_fuel`.

    Each step (including a CPI invocation) consumes one unit of the
    caller's fuel. The callee runs under its own copy of the caller's
    remaining budget and its consumption is *not* deducted from the
    caller — matching the v1 CPI semantics already documented at
    `executeFnCpi`. (Proper proportional CU split is a CPI v2
    concern, tracked alongside `programRegistry`-by-`Pubkey`.)

    The early-exit arms (`some _` already-exited, `ERR_INVALID_PC`
    on decode failure) preserve the remaining fuel at the moment of
    exit, so the consumed count correctly excludes the no-op tail. -/
def executeFnCpiWithFuel (registry : Nat → Option ByteArray)
    (fetch : Nat → Option Insn) (s : State) (fuel : Nat) : State × Nat :=
  match fuel with
  | 0 => (s, 0)
  | fuel' + 1 =>
    match s.exitCode with
    | some _ => (s, fuel)
    | none =>
      match fetch s.pc with
      | none => ({ s with exitCode := some ERR_INVALID_PC }, fuel')
      | some insn =>
        let s' : State :=
          match insn with
          | .call sc@.sol_invoke_signed | .call sc@.sol_invoke_signed_c =>
            -- CPI v2: r1 is a *pointer* into caller memory at which
            -- the Instruction descriptor lives. Two ABIs:
            --
            -- - `sol_invoke_signed` (Rust ABI from
            --   `solana_program::invoke`): r1 → `&Instruction`. With
            --   default Rust layout the high-alignment fields (Vec)
            --   come first, so `program_id` sits at offset 48 (after
            --   accounts:Vec=24B and data:Vec=24B). The 32-byte pubkey
            --   is inline.
            -- - `sol_invoke_signed_c` (C ABI): r1 → `SolInstruction`.
            --   First field is `SolPubkey *program_id` (a u64 pointer
            --   to the actual pubkey bytes); deref to get the 32B.
            --
            -- Both encode the resulting 32 bytes as a little-endian
            -- Nat (matches `Svm.Ffi.pubkeyToNat`) for registry lookup.
            --
            -- Phases 2/3 (account-info decoding + write-back) are
            -- still TODO — the sub-call currently runs against the
            -- *caller's* memory with `r1 := INPUT_START`. Programs
            -- that only need the callee's `r0` (exit code) work today;
            -- programs that inspect modified accounts after CPI don't.
            let pubkeyAddr : Nat := match sc with
              | .sol_invoke_signed   => s.regs.r1 + 48      -- inline @ +48
              | .sol_invoke_signed_c =>                     -- pointer @ +0
                Memory.readU64 s.mem s.regs.r1
              | _ => s.regs.r1
            let pid := (List.range 32).foldl
              (fun acc i => acc + (s.mem (pubkeyAddr + i) % 256) * 256^i) 0
            -- Read pubkey bytes for use in the sub-input trailer.
            let pidBytes := readMemBytes s.mem pubkeyAddr 32
            -- Phase 3-minimal: for zero-account CPIs, build a fresh
            -- sub-input + sub-mem so the callee deserializes its own
            -- (empty) accounts list rather than the caller's input
            -- region. We trigger on `Instruction.accounts.len()`
            -- (not r3): r3 is the *AccountInfo* count, which is
            -- typically larger or equal to the Instruction's account
            -- list (callers pass all their accounts to `invoke()`
            -- even when the CPI uses only some). The instruction's
            -- accounts.len lives at r1+16 in both Rust's `Instruction`
            -- layout (Vec @ +0 → (ptr,cap,len) → len @ +16) and C's
            -- `SolInstruction` (program_id*@0, accounts*@8, account_len@16).
            let accountCount := Memory.readU64 s.mem (s.regs.r1 + 16)
            -- The registry stores full ELF blobs (not raw text). We
            -- mirror `runElfWithFuel`'s loader pipeline (parse header,
            -- find `.text`, apply relocations, decode) before handing
            -- the decoded instruction array to the sub-VM.
            -- Returns `(subFinalState, callerMemAfterWriteBack)` so
            -- the outer code can propagate both observable effects
            -- (r0, log, return_data via subFinal) and account
            -- mutations (callerMem) in one go.
            let runCallee (calleeBytes : ByteArray) : Option (State × Mem) :=
              let tryElf : Option (ByteArray × Elf.Header × Elf.SectionHeader) := do
                let h ← Elf.parseHeader calleeBytes
                let textSec ← Elf.findSection calleeBytes h Elf.textName
                let rawText  := Elf.extractSection calleeBytes textSec
                let textBytes := Elf.applyRelocations calleeBytes h textSec.addr rawText
                some (textBytes, h, textSec)
              do
                let (textBytes, headerOpt, textSecOpt) :
                    ByteArray × Option Elf.Header × Option Elf.SectionHeader :=
                  match tryElf with
                  | some (tb, h, ts) => (tb, some h, some ts)
                  | none => (calleeBytes, none, none)
                let calleeInsns ← Decode.decodeProgram textBytes
                -- Phase 3-minimal (0 accounts) or Phase 3-full (1 account)?
                -- For >1 accounts, fall back to legacy (share caller's mem).
                let parsedAcct? : Option ParsedAcct :=
                  if accountCount = 1
                    then some (parseAccountInfo s.mem s.regs.r2)
                    else none
                let subInput : ByteArray :=
                  match parsedAcct? with
                  | some acct =>
                    buildCpiSubInputOneAccount acct pidBytes ByteArray.empty
                  | none =>
                    buildCpiSubInputNoAccounts pidBytes ByteArray.empty
                -- Build the sub-mem (only when accountCount ∈ {0, 1}).
                let useSubMem := accountCount ≤ 1
                let subMem :=
                  if useSubMem then
                    let baseMem := loadInput emptyMem subInput
                    match headerOpt with
                    | none => baseMem
                    | some h =>
                      let m1 := match Elf.findSection calleeBytes h Elf.rodataName with
                        | some sec =>
                          loadBytesAt baseMem (Elf.extractSection calleeBytes sec) sec.addr
                        | none => baseMem
                      match Elf.findSection calleeBytes h Elf.dataRelRoName with
                      | some sec =>
                        let raw       := Elf.extractSection calleeBytes sec
                        let relocated := Elf.applyDataRelocations calleeBytes h sec.addr raw
                        loadBytesAt m1 relocated sec.addr
                      | none => m1
                  else s.mem
                let entryPc :=
                  match headerOpt, textSecOpt with
                  | some h, some textSec =>
                    let slotMap := Decode.buildSlotMap textBytes
                    let byteOff := if h.entry ≥ textSec.addr
                                   then h.entry - textSec.addr else 0
                    let slot := byteOff / 8
                    if hbnd : slot < slotMap.size then slotMap[slot]'hbnd else 0
                  | _, _ => 0
                let subS : State :=
                  { regs       := { r1 := INPUT_START, r10 := STACK_START + 0x1000 }
                    mem        := subMem
                    pc         := entryPc
                    exitCode   := none
                    log        := s.log
                    returnData := ByteArray.empty }
                let subFinal := (executeFnCpiWithFuel registry
                  (fetchFromArray calleeInsns) subS fuel').1
                -- Phase 3 write-back. For each account in the
                -- sub-input that the callee may have modified, copy
                -- the bytes back to the corresponding caller-memory
                -- addresses (which is what the harness's
                -- `deserialize_account_writes` reads).
                let newCallerMem : Mem :=
                  match parsedAcct? with
                  | none => s.mem
                  | some acct =>
                    let newData := readMemBytes subFinal.mem
                      (INPUT_START + CPI_DATA_OFFSET) acct.dataLen
                    let m1 := loadBytesAt s.mem newData acct.dataPtr
                    let newLamports := Memory.readU64 subFinal.mem
                      (INPUT_START + CPI_LAMPORTS_OFFSET)
                    let m2 := Memory.writeU64 m1 acct.lamportsRefAddr newLamports
                    let newOwner := readMemBytes subFinal.mem
                      (INPUT_START + CPI_OWNER_OFFSET) 32
                    loadBytesAt m2 newOwner acct.ownerPtr
                some (subFinal, newCallerMem)
            match registry pid with
            | none =>
              { s with regs := s.regs.set .r0 1, pc := s.pc + 1 }
            | some calleeElf =>
              match runCallee calleeElf with
              | none =>
                { s with regs := s.regs.set .r0 1, pc := s.pc + 1 }
              | some (subFinal, newMem) =>
                { s with regs       := s.regs.set .r0 (subFinal.exitCode.getD 1)
                         mem        := newMem
                         pc         := s.pc + 1
                         log        := subFinal.log
                         returnData := subFinal.returnData }
          | _ => step insn s
        executeFnCpiWithFuel registry fetch s' fuel'

/-- Original signature, preserved for existing callers (demos +
    `Runner.run` / `Runner.runElf`). A thin wrapper around
    `executeFnCpiWithFuel` that discards the fuel-remaining
    component. -/
def executeFnCpi (registry : Nat → Option ByteArray)
    (fetch : Nat → Option Insn) (s : State) (fuel : Nat) : State :=
  (executeFnCpiWithFuel registry fetch s fuel).1

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
        let mem₁ := match Elf.findSection elfBytes header Elf.rodataName with
          | some sec => loadBytesAt baseMem (Elf.extractSection elfBytes sec) sec.addr
          | none => baseMem
        let mem := match Elf.findSection elfBytes header Elf.dataRelRoName with
          | some sec =>
            let raw       := Elf.extractSection elfBytes sec
            let relocated := Elf.applyDataRelocations elfBytes header sec.addr raw
            loadBytesAt mem₁ relocated sec.addr
          | none => mem₁
        let s : State :=
          { regs    := { r1 := INPUT_START, r10 := STACK_START + 0x1000 }
            mem     := mem
            pc      := 0
            exitCode := none }
        some (executeFnCpi cfg.programRegistry (fetchFromArray insns) s cfg.cuBudget)

/-- Convenience: ELF run returning only the exit code. -/
def runElfForExit (elfBytes : ByteArray) (cfg : RunConfig := {}) : Option Nat :=
  (runElf elfBytes cfg).bind (·.exitCode)

/-- ELF entrypoint that also surfaces remaining fuel, for CU accounting
    in downstream consumers (e.g. the Rust harness in `formal-svm-rs`).

    Returns `none` on ELF parse / decode failure, `some (state, remaining)`
    otherwise. The caller computes `cuConsumed = cfg.cuBudget - remaining`.
    Note: on out-of-budget, `state.exitCode = none` and `remaining = 0`.
    On clean exit, `remaining` is whatever fuel was unspent at the
    moment `exit` ran.

    Honors the ELF's `e_entry` field: execution starts at the
    instruction index `(e_entry - .text.sh_addr) / 8`. For hand-
    assembled fixtures with `e_entry = 0` we start at PC=0. For real
    `cargo-build-sbf` output we start wherever the linker placed the
    Rust `entrypoint` symbol — typically not at the front of `.text`. -/
def runElfWithFuel (elfBytes : ByteArray) (cfg : RunConfig := {}) :
    Option (State × Nat) :=
  match Elf.parseHeader elfBytes with
  | none => none
  | some header =>
    match Elf.findSection elfBytes header Elf.textName with
    | none => none
    | some textSec =>
      let rawText   := Elf.extractSection elfBytes textSec
      let textBytes := Elf.applyRelocations elfBytes header textSec.addr rawText
      match Decode.decodeProgram textBytes with
      | none => none
      | some insns =>
        let baseMem := loadInput emptyMem cfg.input
        let mem₁ := match Elf.findSection elfBytes header Elf.rodataName with
          | some sec => loadBytesAt baseMem (Elf.extractSection elfBytes sec) sec.addr
          | none => baseMem
        -- Map `.data.rel.ro` (read-only-after-relocation) if present.
        -- This is where the linker parks static structures whose fields
        -- include pointers — jump tables, `&'static` references, vtables.
        -- Each pointer field carries a RELATIVE reloc; applying them
        -- moves the address from the upper 32 bits of the u64 word to
        -- the lower 32. Programs with enum-dispatch (SPL Token, Anchor,
        -- Pinocchio-style match arms) crash without this.
        let mem := match Elf.findSection elfBytes header Elf.dataRelRoName with
          | some sec =>
            let raw       := Elf.extractSection elfBytes sec
            let relocated := Elf.applyDataRelocations elfBytes header sec.addr raw
            loadBytesAt mem₁ relocated sec.addr
          | none => mem₁
        -- Convert `e_entry` (virtual address) to logical PC. The
        -- byte offset within `.text` is `e_entry - textSec.addr`;
        -- divided by 8 gives the *byte-slot index*. Each `lddw`
        -- consumes two byte slots but is one logical instruction, so
        -- we must consult `buildSlotMap` to translate slot → logical
        -- PC. (Programs with no lddw before `e_entry` happen to have
        -- slotMap[i] = i, which is why earlier fixtures worked
        -- without this step.)
        let slotMap := Decode.buildSlotMap textBytes
        let entryByteOff := if header.entry ≥ textSec.addr
                           then header.entry - textSec.addr
                           else 0
        let entrySlot := entryByteOff / 8
        let entryPc := if h : entrySlot < slotMap.size
                       then slotMap[entrySlot]'h else 0
        let s : State :=
          { regs    := { r1 := INPUT_START, r10 := STACK_START + 0x1000 }
            mem     := mem
            pc      := entryPc
            exitCode := none }
        some (executeFnCpiWithFuel cfg.programRegistry (fetchFromArray insns) s cfg.cuBudget)

end Runner
end Svm.SBPF
