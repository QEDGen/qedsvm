/-
  sBPF runner — the production entrypoint for executing arbitrary sBPF
  bytecode under the Lean semantics.

  Decoupled from any demo or test fixture. The runner is the public
  interface a downstream consumer wires up:

      SVM.SBPF.Runner.run : ByteArray → RunConfig → Option State

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

import SVM.SBPF.Decode
import SVM.SBPF.Elf
import SVM.Native
import SVM.Syscalls.Pda

namespace SVM.SBPF
namespace Runner

open Memory

/-- One-off debug knob: when `true`, every step emits a one-line `STEP`
    trace to stderr via `dbg_trace`, including pc + r0..r10. Lean's
    if-then-else short-circuits, so when this is `false` (production)
    the dbg_trace and its s!"…" string interpolation never run.

    Flip to `true`, rebuild Lean, run a single fixture with
    `cargo test … -- --nocapture 2>trace.txt`, then flip back. Used to
    bisect cross-engine CU drift against mollusk's
    `SBF_TRACE_DIR` / `SBF_TRACE_DISASSEMBLE` output.

    For plain PC traces (the `.pcs` files qedlift/qedrecover consume)
    do NOT flip this — use the runtime hook below
    (`QEDSVM_TRACE_OUT=<path>`), which needs no rebuild. -/
def TRACE_STEPS : Bool := false

/-- Runtime PC-trace hook, the automated path for capturing `.pcs`
    files. Same shape as `dbgTrace` (identity on the thunk), so it is
    proof-transparent: `traceStep pc f = f ()` by definition. The
    extern implementation (`qedsvm-rs/lean-bridge/`) appends one
    decimal PC per line to the file named by `QEDSVM_TRACE_OUT` when
    that env var is set, and is a no-op otherwise. See
    `scripts/capture_trace.sh` for the one-command capture flow. -/
@[never_extract, extern "lean_qedsvm_trace_step"]
def traceStep (_pc : USize) (f : Unit → α) : α := f ()

/-- Pad a Nat as a `width`-digit lowercase hex string. -/
private def hex (n width : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 (n % (16^width)))
  String.ofList (List.replicate (width - s.length) '0') ++ s

/-! ## Memory + register initialization -/

/-- Empty memory: every byte is zero. -/
def emptyMem : Mem := {}

/-- Overlay a ByteArray onto memory starting at `baseAddr`. Outside the
    overlaid range the underlying memory is preserved.

    Bytes are written into the `Mem` overlay one at a time (was a
    function-form closure in the old `abbrev Mem` world; each byte
    used to walk the entire chain on read). -/
def loadBytesAt (mem : Mem) (bytes : ByteArray) (baseAddr : Nat) : Mem :=
  (List.range bytes.size).foldl
    (fun m i => Memory.writeU8 m (baseAddr + i) (bytes.get! i).toNat) mem

/-- Overlay the input buffer at `INPUT_START`. -/
def loadInput (mem : Mem) (input : ByteArray) : Mem :=
  loadBytesAt mem input INPUT_START

/-- Build a `fetch` function from a decoded instruction array. -/
def fetchFromArray (insns : Array Insn) : Nat → Option Insn :=
  fun pc => if h : pc < insns.size then some (insns[pc]'h) else none

/-! ## Region table construction

The `step` function consults `s.regions` on every `.ldx`/`.st`/`.stx`
and traps a miss to `ERR_ACCESS_VIOLATION`. The Runner is the one
place we have enough information (ELF sections + runtime memory
layout) to build a faithful region table.

Sizes mirror agave with `FeatureSet::all_enabled()` (mollusk's
default):
- Stack: `MAX_CALL_DEPTH (64) × stack_frame_size (0x1000) = 0x40000`
  (`enable_stack_frame_gaps = false` under
  `virtual_address_space_adjustments`).
- Heap: default 32 KiB. Programs may request up to 256 KiB via
  ComputeBudget; we don't model the request, so the default applies. -/

/-- Total stack region size (256 KiB). -/
def STACK_SIZE : Nat := 0x40000

/-- Default heap region size (32 KiB). Matches agave's
    `compute_budget::DEFAULT_HEAP_COST`-paired allocation. -/
def DEFAULT_HEAP_SIZE : Nat := 0x8000

/-- The fixed runtime regions (stack + heap + input) WITHOUT
    per-account writable subdivision. Used when the caller doesn't
    supply an account-formatted input (bare bytecode demos), or as a
    fallback when input parsing fails. Stack/heap stay writable,
    input is one big writable region.

    Prefer `runtimeRegionsForInput` for ELF-driven and CPI paths —
    it splits the input into per-account regions so writes past
    `MAX_PERMITTED_DATA_INCREASE` boundaries and writes to
    read-only accounts trap to `ERR_ACCESS_VIOLATION` (Tier-2 #9 +
    read-only enforcement). -/
def runtimeRegions (inputLen : Nat) : Memory.RegionTable :=
  [ { start := STACK_START, size := STACK_SIZE,        writable := true }
  , { start := HEAP_START,  size := DEFAULT_HEAP_SIZE, writable := true }
  , { start := INPUT_START, size := inputLen,          writable := true } ]

/-- The read-only program region for an ELF: spans `MM_REGION_SIZE` up
    to the end of the highest loaded section (text / rodata /
    data.rel.ro). Matches agave's single contiguous program region
    in `solana-sbpf`. -/
def programRegionElf (elfBytes : ByteArray) (header : Elf.Header)
    (textSec : Elf.SectionHeader) : Memory.Region :=
  let textEnd := Elf.relocateSecAddr textSec.addr + textSec.size
  let rodataEnd := match Elf.findSection elfBytes header Elf.rodataName with
    | some sec => Elf.relocateSecAddr sec.addr + sec.size
    | none => 0
  let dataRelRoEnd := match Elf.findSection elfBytes header Elf.dataRelRoName with
    | some sec => Elf.relocateSecAddr sec.addr + sec.size
    | none => 0
  let programEnd := max textEnd (max rodataEnd dataRelRoEnd)
  let programSize := programEnd - MM_REGION_SIZE
  { start := MM_REGION_SIZE, size := programSize, writable := false }

/-- Full region table for an ELF-loaded run. One big writable input
    region — per-account write boundaries (Tier-2 #9) and read-only
    write detection are enforced as *post-instruction* validation in
    the Rust harness, not via memory-region traps. Agave does the
    same: programs can write anywhere in the serialized input during
    execution; the runtime validates pre/post invariants at
    instruction exit (data_len ≤ pre + 10240, read-only accounts
    unchanged, etc.). -/
def elfRegions (elfBytes : ByteArray) (header : Elf.Header)
    (textSec : Elf.SectionHeader) (inputLen : Nat) : Memory.RegionTable :=
  programRegionElf elfBytes header textSec :: runtimeRegions inputLen

/-! ## CPI sub-input construction

When a program issues `sol_invoke_signed{,_c}`, the callee expects its
input buffer at `INPUT_START` to be a *fresh* `serialize_parameters`-
shaped layout for the CPI's target — not the caller's input. We build
this in Lean (mirroring `qedsvm-rs/src/serialize.rs`) so the
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
  dataLenRefAddr  : Nat  -- where the data slice's `len` u64 lives in caller mem

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
  let dataLenRefAddr  := dataRcPtr + 32
  let dataLen         := Memory.readU64 mem dataLenRefAddr
  let key             := readMemBytes mem keyPtr 32
  let owner           := readMemBytes mem ownerPtr 32
  let data            := readMemBytes mem dataPtr dataLen
  { key, owner, lamports, dataLen, data,
    isSigner, isWritable, executable, rentEpoch,
    ownerPtr, lamportsRefAddr, dataPtr, dataLenRefAddr }

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

/-! ### N-account CPI marshaling (Phase 3-N)

Generalizes `buildCpiSubInputOneAccount` to an arbitrary list of
parsed accounts. Two complications vs. N=1:

- **Duplicate accounts** (same pubkey at indices i < j in
  `ix.accounts`) compress: the j-th slot emits a 1-byte position
  index of `i` followed by 7 zero pad bytes, instead of a full
  block. The callee's deserializer collapses both AccountInfos
  onto the same underlying RefCell, so any mutation through the
  dup slot in the callee writes to the canonical slot's bytes —
  we only write back through the canonical slot's pointers. This
  mirrors `qedsvm-rs/src/serialize.rs`'s `seen[]` loop.
- **Per-slot cumulative offset** into the sub-input. Each
  non-dup block has stride `88 + dataLen + align_pad + 10240 + 8`
  (different per account if data sizes differ). Dups are stride 8.
  The block offset feeds into write-back so we know where each
  slot's modifiable region lives in the sub-input. -/

/-- One slot in the laid-out CPI sub-input. `parsed` carries the
    pre-call account data + write-back pointers; `dupOf?` is
    `some j` if this slot is a duplicate of an earlier slot (emit
    only the 8-byte dup marker, no own block); `blockOff` is the
    offset in the sub-input where this slot's bytes begin (used
    for write-back). -/
structure AcctSlot where
  parsed   : ParsedAcct
  dupOf?   : Option Nat
  blockOff : Nat

/-- Per-account stride in bytes (non-dup blocks only). Matches the
    full block layout: dup_marker(1) + flags(3) + pad(4) + key(32)
    + owner(32) + lamports(8) + data_len(8) + data(L) + align_pad
    + MAX_PERMITTED_DATA_INCREASE + rent_epoch(8). -/
private def nonDupBlockSize (dataLen : Nat) : Nat :=
  88 + dataLen + ((8 - dataLen % 8) % 8) + MAX_PERMITTED_DATA_INCREASE + 8

/-- Build the slot table from a list of pre-parsed accounts. Linear
    pass: for each slot, scan earlier slots for a key match. -/
def buildAcctSlots (parsed : List ParsedAcct) : List AcctSlot :=
  let n := parsed.length
  let parsedArr : Array ParsedAcct := parsed.toArray
  -- Fold over indices; carry the running block offset.
  -- Sentinel default for out-of-bounds reads (unreachable for `i < n`).
  let dflt : ParsedAcct :=
    { key := ByteArray.empty, owner := ByteArray.empty, lamports := 0,
      dataLen := 0, data := ByteArray.empty, isSigner := false,
      isWritable := false, executable := false, rentEpoch := 0,
      ownerPtr := 0, lamportsRefAddr := 0, dataPtr := 0,
      dataLenRefAddr := 0 }
  ((List.range n).foldl (fun (acc, off) i =>
    let p := parsedArr.getD i dflt
    -- Find first j < i with the same key (linear scan).
    let dup : Option Nat :=
      (List.range i).find? (fun j =>
        (parsedArr.getD j dflt).key = p.key)
    match dup with
    | some _ =>
      (acc ++ [({ parsed := p, dupOf? := dup, blockOff := off } : AcctSlot)],
       off + 8)
    | none =>
      (acc ++ [({ parsed := p, dupOf? := none, blockOff := off } : AcctSlot)],
       off + nonDupBlockSize p.dataLen))
   ([], 8)).1  -- initial offset = 8 (after num_accounts header)

/-- Parse `count` consecutive `AccountInfo` structs starting at
    `baseAddr`. Stride is 48 bytes (the size of Rust's
    `solana_program::AccountInfo` with default layout). -/
def parseAccountInfos (mem : Mem) (baseAddr count : Nat) : List ParsedAcct :=
  (List.range count).map (fun i => parseAccountInfo mem (baseAddr + i * 48))

/-- Parse one `CpiAccount` struct at `addr` in `mem`. This is the
    C-shaped variant `sol_invoke_signed_c` callers (Pinocchio,
    `solana-instruction-view`) pass instead of `AccountInfo`.

    Layout (`#[repr(C)]` from `solana-instruction-view/src/cpi.rs`):
    ```
    +0   address: *const Address    (u64 ptr)
    +8   lamports: *const u64       (u64 ptr — direct, not Rc-chained)
    +16  data_len: u64              (inline u64)
    +24  data: *const u8            (u64 ptr — direct)
    +32  owner: *const Address      (u64 ptr)
    +40  rent_epoch: u64            (inline u64)
    +48  is_signer: u8
    +49  is_writable: u8
    +50  executable: u8
    +51  _padding: u8
    +52..+56  trailing pad to satisfy struct alignment (largest field
              is u64, so size rounds up to 56)
    ```

    Notable differences from `parseAccountInfo`:
    - 56-byte stride vs. 48-byte stride
    - lamports / data pointers are direct (no Rc chain to chase
      through `+24` to reach the real address)
    - `data_len` is inline at `+16` rather than carried inside the
      `Rc<RefCell<&mut [u8]>>` length slot
    - flag bytes sit at `+48..+51` rather than `+40..+43`

    For write-back, the harness needs caller-memory addresses where
    each mutable field lives:
    - `lamportsRefAddr` = the value of the `lamports` pointer
      (CpiAccount stores a direct ptr; the u64 lives at that address
      in the caller's input buffer).
    - `dataLenRefAddr` = `addr + 16` (inline slot in the CpiAccount
      itself). Note: pinocchio's `AccountView` reads `data_len` out
      of the **input buffer** at `dataPtr - 8`, so the second
      `writeU64 _ (dataPtr - 8) _` in `execCreateAccount` /
      `execAllocate` is what the program actually sees post-CPI.
      The `dataLenRefAddr` write keeps the CpiAccount struct in sync
      for any code that re-reads it.
    - `dataPtr` = the value of the `data` pointer (points into the
      input buffer's data region for that account).
    - `ownerPtr` = the value of the `owner` pointer (32 bytes at
      that caller address — the same slot CreateAccount overwrites). -/
def parseCpiAccount (mem : Mem) (addr : Nat) : ParsedAcct :=
  let keyPtr          := Memory.readU64 mem addr
  let lamportsRefAddr := Memory.readU64 mem (addr + 8)
  let dataLen         := Memory.readU64 mem (addr + 16)
  let dataPtr         := Memory.readU64 mem (addr + 24)
  let ownerPtr        := Memory.readU64 mem (addr + 32)
  let rentEpoch       := Memory.readU64 mem (addr + 40)
  let isSigner        := (mem (addr + 48)) % 256 ≠ 0
  let isWritable      := (mem (addr + 49)) % 256 ≠ 0
  let executable      := (mem (addr + 50)) % 256 ≠ 0
  let dataLenRefAddr  := addr + 16
  let lamports        := Memory.readU64 mem lamportsRefAddr
  let key             := readMemBytes mem keyPtr 32
  let owner           := readMemBytes mem ownerPtr 32
  let data            := readMemBytes mem dataPtr dataLen
  { key, owner, lamports, dataLen, data,
    isSigner, isWritable, executable, rentEpoch,
    ownerPtr, lamportsRefAddr, dataPtr, dataLenRefAddr }

/-- Parse `count` consecutive `CpiAccount` structs starting at
    `baseAddr`. Stride is 56 bytes (vs. 48 for `AccountInfo`). -/
def parseCpiAccounts (mem : Mem) (baseAddr count : Nat) : List ParsedAcct :=
  (List.range count).map (fun i => parseCpiAccount mem (baseAddr + i * 56))

/-- Emit a single non-dup account block (88 + dataLen + align_pad +
    MAX_PERMITTED_DATA_INCREASE + 8 bytes). -/
private def emitNonDupBlock (p : ParsedAcct) : ByteArray :=
  let dupMarker   := ByteArray.empty.push 0xFF
  let signer      : UInt8 := if p.isSigner then 1 else 0
  let writable    : UInt8 := if p.isWritable then 1 else 0
  let executable  : UInt8 := if p.executable then 1 else 0
  let flags       := ⟨#[signer, writable, executable]⟩
  let padU32      := zeroBytes 4
  let lamports    := u64ToLE p.lamports
  let dataLen     := u64ToLE p.dataLen
  let alignPad    := zeroBytes ((8 - p.dataLen % 8) % 8)
  let increasePad := zeroBytes MAX_PERMITTED_DATA_INCREASE
  let rentEpoch   := u64ToLE p.rentEpoch
  dupMarker ++ flags ++ padU32 ++ p.key ++ p.owner
    ++ lamports ++ dataLen ++ p.data ++ alignPad
    ++ increasePad ++ rentEpoch

/-- Emit a dup-marker slot (1 byte position + 7 zero pad bytes). -/
private def emitDupBlock (j : Nat) : ByteArray :=
  (ByteArray.empty.push j.toUInt8) ++ zeroBytes 7

/-- Build an N-account CPI sub-input from a slot table. Byte-for-byte
    matches `serialize_parameters` for the same account list. -/
def buildCpiSubInputN (slots : List AcctSlot)
    (programId ixData : ByteArray) : ByteArray :=
  let numAccounts := u64ToLE slots.length
  let blocks : ByteArray := slots.foldl (fun acc slot =>
    match slot.dupOf? with
    | some j => acc ++ emitDupBlock j
    | none   => acc ++ emitNonDupBlock slot.parsed) ByteArray.empty
  let ixLen := u64ToLE ixData.size
  numAccounts ++ blocks ++ ixLen ++ ixData ++ programId

/-- Per-slot write-back offsets (from the slot's `blockOff`) for the
    three modifiable fields inside a non-dup block. -/
def CPI_BLOCK_OWNER_OFFSET    : Nat := 40   -- dup_marker(1)+flags(3)+pad(4)+key(32) = 40
def CPI_BLOCK_LAMPORTS_OFFSET : Nat := 72   -- ...+owner(32) = 72
def CPI_BLOCK_DATA_OFFSET     : Nat := 88   -- ...+lamports(8)+data_len(8) = 88

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
  /-- 32-byte program-id of the top-level program being executed.
      Threaded into `State.progIdBytes` so the CPI handler can derive
      PDAs from caller-supplied signer seeds. Default empty — programs
      that don't use `invoke_signed` with seeds are unaffected. -/
  progIdBytes : ByteArray := ByteArray.empty

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
/-! ## PDA signer-seed promotion

`invoke_signed` lets a caller act as a Program Derived Address: the
caller supplies (signer_seeds : &[&[&[u8]]]) at r4/r5, agave derives a
PDA from each inner seed-array using the caller's program-id, and any
AccountInfo whose pubkey matches a derived PDA is promoted to
is_signer=true on the callee side. Without this, callees can't
distinguish a PDA invocation from a non-signer.

Wire format at the syscall boundary (Rust slice fat pointers throughout):
  r4: ptr to array of signer entries  (each entry 16B: ptr@+0, len@+8)
  r5: number of signer entries
  signer_entries[i]:  16B (ptr to inner seed array, len of inner array)
  inner_seed_array[j]: 16B (ptr to seed bytes, len of seed bytes) -/

/-- Read one signer's seeds (the `&[&[u8]]` at `signerAddr`) as a
    list of byte slices. -/
def readSignerSeeds (mem : Mem) (signerAddr : Nat) : List ByteArray :=
  let innerPtr := Memory.readU64 mem signerAddr
  let innerLen := Memory.readU64 mem (signerAddr + 8)
  (List.range innerLen).map (fun j =>
    let seedPtr := Memory.readU64 mem (innerPtr + j * 16)
    let seedLen := Memory.readU64 mem (innerPtr + j * 16 + 8)
    readMemBytes mem seedPtr seedLen)

/-- For each signer in r4 (array of `&[&[u8]]` of length r5), derive
    the PDA via create_program_address(seeds, callerPid). Returns the
    32-byte derived pubkeys. -/
def deriveSignerPdas (mem : Mem) (seedsAddr seedsLen : Nat)
    (callerPid : ByteArray) : List ByteArray :=
  (List.range seedsLen).filterMap (fun i =>
    let seeds := readSignerSeeds mem (seedsAddr + i * 16)
    Pda.createProgramAddress seeds callerPid)

/-- Promote parsed account-infos: any account whose key matches a
    derived PDA gets is_signer = true. Agave's seed-derived signer
    promotion in `invoke_signed`. -/
def promoteSigners (parsedAccts : List ParsedAcct)
    (derivedPdas : List ByteArray) : List ParsedAcct :=
  parsedAccts.map (fun p =>
    if derivedPdas.any (fun pda => p.key == pda)
    then { p with isSigner := true }
    else p)

/-- Compute the next state for one of the two CPI-call syscalls
    (`sol_invoke_signed` / `sol_invoke_signed_c`). Non-recursive — the
    recursive sub-VM invocation is supplied as the `runCallee` closure
    by `executeFnCpiWithFuel`. Factored out so the per-instruction match
    inside `executeFnCpiWithFuel` has compact arms (helps proofs that
    case-split on the instruction without elaborating this whole body
    in every Syscall arm). -/
def cpiCallNextState (registry : Nat → Option ByteArray) (s : State)
    (sc : Syscall) (fuel' : Nat)
    (runCallee : ByteArray → Option (State × Mem × Nat)) : State :=
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
  let pubkeyAddr : Nat := match sc with
    | .sol_invoke_signed   => s.regs.r1 + 48      -- inline @ +48
    | .sol_invoke_signed_c =>                     -- pointer @ +0
      Memory.readU64 s.mem s.regs.r1
    | _ => s.regs.r1
  let pid := (List.range 32).foldl
    (fun acc i => acc + (s.mem (pubkeyAddr + i) % 256) * 256^i) 0
  let accountCount := Memory.readU64 s.mem (s.regs.r1 + 16)
  -- Account-info struct layout differs between the two CPI ABIs:
  --   - `sol_invoke_signed` (Rust ABI): 48-byte `AccountInfo` with
  --     `Rc<RefCell<&mut u64>>` for lamports and
  --     `Rc<RefCell<&mut [u8]>>` for data. `parseAccountInfo` chases
  --     the Rc/RefCell chain to reach the underlying bytes.
  --   - `sol_invoke_signed_c` (C ABI): 56-byte `CpiAccount` with
  --     direct `*const u64` / `*const u8` pointers and an inline
  --     `data_len: u64`. Pinocchio + `solana-instruction-view`
  --     callers use this. `parseCpiAccount` reads it directly.
  -- Parsing the wrong layout silently produces garbage `lamports`,
  -- `data`, and `is_signer` values — which is what caused #10
  -- (Pinocchio's PDA-target `CreateAccount` saw `is_signer=false`
  -- because the dispatcher read the CpiAccount's flag byte from
  -- the wrong offset and aborted before promotion).
  let parsedAcctsRaw : List ParsedAcct :=
    match sc with
    | .sol_invoke_signed_c => parseCpiAccounts   s.mem s.regs.r2 accountCount
    | _                    => parseAccountInfos  s.mem s.regs.r2 accountCount
  -- PDA signer-seed promotion: derive PDAs from r4/r5 using the
  -- currently-running program's id (`s.progIdBytes`) and flip
  -- is_signer=true on any parsed account whose key matches.
  let derivedPdas : List ByteArray :=
    deriveSignerPdas s.mem s.regs.r4 s.regs.r5 s.progIdBytes
  let parsedAccts : List ParsedAcct :=
    promoteSigners parsedAcctsRaw derivedPdas
  -- Tier-2 #8 — account aliasing detection.
  let parsedArr : Array ParsedAcct := parsedAccts.toArray
  let aliasedWritability : Bool :=
    (List.range parsedArr.size).any (fun i =>
      (List.range i).any (fun j =>
        let pi := parsedArr.getD i (parsedArr.getD 0
          { key := ByteArray.empty, owner := ByteArray.empty,
            lamports := 0, dataLen := 0, data := ByteArray.empty,
            isSigner := false, isWritable := false,
            executable := false, rentEpoch := 0,
            ownerPtr := 0, lamportsRefAddr := 0,
            dataPtr := 0, dataLenRefAddr := 0 })
        let pj := parsedArr.getD j (parsedArr.getD 0
          { key := ByteArray.empty, owner := ByteArray.empty,
            lamports := 0, dataLen := 0, data := ByteArray.empty,
            isSigner := false, isWritable := false,
            executable := false, rentEpoch := 0,
            ownerPtr := 0, lamportsRefAddr := 0,
            dataPtr := 0, dataLenRefAddr := 0 })
        pi.key == pj.key && pi.isWritable ≠ pj.isWritable))
  let ixDataPtr : Nat := Memory.readU64 s.mem (s.regs.r1 + 24)
  let ixDataLen : Nat := match sc with
    | .sol_invoke_signed   => Memory.readU64 s.mem (s.regs.r1 + 40)
    | .sol_invoke_signed_c => Memory.readU64 s.mem (s.regs.r1 + 32)
    | _ => 0
  let ixData : ByteArray := readMemBytes s.mem ixDataPtr ixDataLen
  let nativeAccts : List Native.AcctInput := parsedAccts.map (fun p =>
    { key := p.key, owner := p.owner, lamports := p.lamports,
      dataLen := p.dataLen, isSigner := p.isSigner,
      isWritable := p.isWritable,
      lamportsRefAddr := p.lamportsRefAddr,
      ownerPtr := p.ownerPtr, dataPtr := p.dataPtr,
      dataLenRefAddr := p.dataLenRefAddr })
  if aliasedWritability then
    { s with regs := s.regs.set .r0 1
             pc   := s.pc + 1
             cuConsumed := s.cuConsumed + Cpi.cu }
  else
  match Native.dispatch pid ixData nativeAccts s.mem with
  | some nr =>
    { s with regs       := s.regs.set .r0 nr.r0
             mem        := nr.mem
             pc         := s.pc + 1
             cuConsumed := s.cuConsumed + Cpi.cu + nr.cu }
  | none =>
  match registry pid with
  | none =>
    { s with regs := s.regs.set .r0 1
             pc := s.pc + 1
             cuConsumed := s.cuConsumed + Cpi.cu }
  | some calleeElf =>
    match runCallee calleeElf with
    | none =>
      { s with regs := s.regs.set .r0 1
               pc := s.pc + 1
               cuConsumed := s.cuConsumed + Cpi.cu }
    | some (subFinal, newMem, subFuelRemaining) =>
      -- Tier-2 #7 — proportional CU split. The caller's
      -- meter absorbs the callee's spend in two parts:
      --   * `subFinal.cuConsumed`: callee's syscall extras
      --     (already bumped into the callee's State during
      --     its own execution).
      --   * `fuel' - subFuelRemaining`: the callee's step
      --     count (each callee step decremented its local
      --     fuel by one; the diff equals the number of
      --     callee steps).
      { s with regs       := s.regs.set .r0 (subFinal.exitCode.getD 1)
               mem        := newMem
               pc         := s.pc + 1
               log        := subFinal.log
               returnData := subFinal.returnData
               cuConsumed := s.cuConsumed + Cpi.cu
                                          + subFinal.cuConsumed
                                          + (fuel' - subFuelRemaining) }

/-- CU-accounting variant of `executeFnCpi`. Returns the final state
    plus the remaining fuel — `cuConsumed = initial_fuel - returned_fuel`.

    Each step (including a CPI invocation) consumes one unit of the
    caller's fuel. CPI dispatch is delegated to `cpiCallNextState` for
    proof-friendliness; this function is responsible only for fuel
    management, fetch, and the per-instruction match.

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
        -- The runCallee closure captures `s`, `parsedAccts`/`pidBytes`
        -- (recomputed inside cpiCallNextState — see comment there), and
        -- the recursive `executeFnCpiWithFuel` invocation at `fuel'`
        -- (strictly smaller, so termination on `fuel` still holds).
        let runCallee (pidBytesIn : ByteArray) (parsedAcctsIn : List ParsedAcct)
            (ixDataIn : ByteArray) (calleeBytes : ByteArray)
            : Option (State × Mem × Nat) :=
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
            let slots : List AcctSlot := buildAcctSlots parsedAcctsIn
            let subInput : ByteArray :=
              buildCpiSubInputN slots pidBytesIn ixDataIn
            let subMem : Mem :=
              let baseMem := loadInput emptyMem subInput
              match headerOpt with
              | none => baseMem
              | some h =>
                -- Load the callee's .text into its program region too (M2).
                let mText := match textSecOpt with
                  | some textSec =>
                    loadBytesAt baseMem textBytes (Elf.relocateSecAddr textSec.addr)
                  | none => baseMem
                let m1 := match Elf.findSection calleeBytes h Elf.rodataName with
                  | some sec =>
                    loadBytesAt mText (Elf.extractSection calleeBytes sec)
                      (Elf.relocateSecAddr sec.addr)
                  | none => mText
                match Elf.findSection calleeBytes h Elf.dataRelRoName with
                | some sec =>
                  let raw       := Elf.extractSection calleeBytes sec
                  let relocated := Elf.applyDataRelocations calleeBytes h sec.addr raw
                  loadBytesAt m1 relocated (Elf.relocateSecAddr sec.addr)
                | none => m1
            let entryPc :=
              match headerOpt, textSecOpt with
              | some h, some textSec =>
                let slotMap := Decode.buildSlotMap textBytes
                let byteOff := if h.entry ≥ textSec.addr
                               then h.entry - textSec.addr else 0
                let slot := byteOff / 8
                if hbnd : slot < slotMap.size then slotMap[slot]'hbnd else 0
              | _, _ => 0
            let subRegions : Memory.RegionTable :=
              match headerOpt, textSecOpt with
              | some h, some textSec =>
                elfRegions calleeBytes h textSec subInput.size
              | _, _ => runtimeRegions subInput.size
            let subS : State :=
              { regs        := { r1 := INPUT_START, r10 := STACK_START + 0x1000 }
                mem         := subMem
                regions     := subRegions
                pc          := entryPc
                exitCode    := none
                log         := s.log
                returnData  := ByteArray.empty
                cuBudget    := fuel'
                progIdBytes := pidBytesIn }
            let (subFinal, subFuelRemaining) := executeFnCpiWithFuel registry
              (fetchFromArray calleeInsns) subS fuel'
            let newCallerMem : Mem := slots.foldl (fun mem slot =>
              match slot.dupOf? with
              | some _ => mem
              | none =>
                let p := slot.parsed
                let blockBase := INPUT_START + slot.blockOff
                let newData := readMemBytes subFinal.mem
                  (blockBase + CPI_BLOCK_DATA_OFFSET) p.dataLen
                let m1 := loadBytesAt mem newData p.dataPtr
                let newLamports := Memory.readU64 subFinal.mem
                  (blockBase + CPI_BLOCK_LAMPORTS_OFFSET)
                let m2 := Memory.writeU64 m1 p.lamportsRefAddr newLamports
                let newOwner := readMemBytes subFinal.mem
                  (blockBase + CPI_BLOCK_OWNER_OFFSET) 32
                loadBytesAt m2 newOwner p.ownerPtr) s.mem
            some (subFinal, newCallerMem, subFuelRemaining)
        let s' : State :=
          match insn with
          | .call .sol_invoke_signed =>
            let pubkeyAddr := s.regs.r1 + 48
            let pidBytes := readMemBytes s.mem pubkeyAddr 32
            let accountCount := Memory.readU64 s.mem (s.regs.r1 + 16)
            -- Promote seed-derived PDAs to is_signer=true so the
            -- callee's sub-input matches what cpiCallNextState
            -- internally computes for Native/aliasing checks.
            let parsedAcctsRaw := parseAccountInfos s.mem s.regs.r2 accountCount
            let derivedPdas := deriveSignerPdas s.mem s.regs.r4 s.regs.r5 s.progIdBytes
            let parsedAccts := promoteSigners parsedAcctsRaw derivedPdas
            -- Rust ABI Instruction: data:Vec at offset 24, layout
            -- { ptr@+24, cap@+32, len@+40 }.
            let ixDataPtr := Memory.readU64 s.mem (s.regs.r1 + 24)
            let ixDataLen := Memory.readU64 s.mem (s.regs.r1 + 40)
            let ixData    := readMemBytes s.mem ixDataPtr ixDataLen
            cpiCallNextState registry s .sol_invoke_signed fuel'
              (runCallee pidBytes parsedAccts ixData)
          | .call .sol_invoke_signed_c =>
            let pubkeyAddr := Memory.readU64 s.mem s.regs.r1
            let pidBytes := readMemBytes s.mem pubkeyAddr 32
            let accountCount := Memory.readU64 s.mem (s.regs.r1 + 16)
            -- C ABI passes `CpiAccount` structs (56-byte stride, direct
            -- pointers, inline data_len) instead of `AccountInfo`.
            -- Must use `parseCpiAccounts`, not `parseAccountInfos`,
            -- or `is_signer` lands at the wrong offset and the PDA
            -- promotion below picks up the wrong account (issue #10).
            let parsedAcctsRaw := parseCpiAccounts s.mem s.regs.r2 accountCount
            let derivedPdas := deriveSignerPdas s.mem s.regs.r4 s.regs.r5 s.progIdBytes
            let parsedAccts := promoteSigners parsedAcctsRaw derivedPdas
            -- C ABI SolInstruction: data_addr@+24, data_len@+32.
            let ixDataPtr := Memory.readU64 s.mem (s.regs.r1 + 24)
            let ixDataLen := Memory.readU64 s.mem (s.regs.r1 + 32)
            let ixData    := readMemBytes s.mem ixDataPtr ixDataLen
            cpiCallNextState registry s .sol_invoke_signed_c fuel'
              (runCallee pidBytes parsedAccts ixData)
          | _ => step insn s
        traceStep (USize.ofNat s.pc) fun _ =>
          if TRACE_STEPS then
            dbg_trace s!"STEP pc={hex s.pc 8} {hex s.regs.r0 16} {hex s.regs.r1 16} {hex s.regs.r2 16} {hex s.regs.r3 16} {hex s.regs.r4 16} {hex s.regs.r5 16} {hex s.regs.r6 16} {hex s.regs.r7 16} {hex s.regs.r8 16} {hex s.regs.r9 16} {hex s.regs.r10 16}"
            executeFnCpiWithFuel registry fetch s' fuel'
          else
            executeFnCpiWithFuel registry fetch s' fuel'

/-- Original signature, preserved for existing callers (demos +
    `Runner.run` / `Runner.runElf`). A thin wrapper around
    `executeFnCpiWithFuel` that discards the fuel-remaining
    component. -/
def executeFnCpi (registry : Nat → Option ByteArray)
    (fetch : Nat → Option Insn) (s : State) (fuel : Nat) : State :=
  (executeFnCpiWithFuel registry fetch s fuel).1

/-! ## Entrypoints -/

/-- Initial machine state for `Runner.run`. Extracted from the inline
    let-binding so end-to-end soundness theorems (`RunnerBridge.lean`)
    can refer to it by name and reason about its fields. -/
def initialState (cfg : RunConfig) : State :=
  { regs        := { r1 := INPUT_START, r10 := STACK_START + 0x1000 }
    mem         := loadInput emptyMem cfg.input
    regions     := runtimeRegions cfg.input.size
    pc          := 0
    exitCode    := none
    cuBudget    := cfg.cuBudget
    progIdBytes := cfg.progIdBytes }

@[simp] theorem initialState_pc (cfg : RunConfig) : (initialState cfg).pc = 0 := rfl

@[simp] theorem initialState_exitCode (cfg : RunConfig) :
    (initialState cfg).exitCode = none := rfl

@[simp] theorem initialState_callStack (cfg : RunConfig) :
    (initialState cfg).callStack = [] := rfl

/-- Decode `bytes` and run for up to `cfg.cuBudget` compute units. Returns
    the final machine state, or `none` if decoding fails.

    Inspect `state.exitCode`:
    - `none` → out of CU budget
    - `some Memory.ERR_INVALID_PC` → invalid PC (fell off program)
    - `some n` → clean exit with return code `n` -/
def run (bytes : ByteArray) (cfg : RunConfig := {}) : Option State := do
  let insns ← Decode.decodeProgram bytes
  return executeFnCpi cfg.programRegistry (fetchFromArray insns) (initialState cfg) cfg.cuBudget

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
        -- Load the (relocated) .text into the program region so an `ldx`
        -- into it reads the real bytecode, not a fabricated 0 (M2). Real
        -- programs read .text only for adjacent constants/jump tables;
        -- valid fixtures are unaffected (they don't read .text), and this
        -- now matches agave, which maps .text into the program region.
        let memText := loadBytesAt baseMem textBytes (Elf.relocateSecAddr textSec.addr)
        let mem₁ := match Elf.findSection elfBytes header Elf.rodataName with
          | some sec => loadBytesAt memText (Elf.extractSection elfBytes sec)
              (Elf.relocateSecAddr sec.addr)
          | none => memText
        let mem := match Elf.findSection elfBytes header Elf.dataRelRoName with
          | some sec =>
            let raw       := Elf.extractSection elfBytes sec
            let relocated := Elf.applyDataRelocations elfBytes header sec.addr raw
            loadBytesAt mem₁ relocated (Elf.relocateSecAddr sec.addr)
          | none => mem₁
        -- Start at the ELF entrypoint (L8): map `e_entry` to a logical PC
        -- via the slot map (mirrors `runElfWithFuel`). For fixtures whose
        -- entry is at slot 0 this is exactly the old `pc := 0`.
        let entryPc :=
          let slotMap := Decode.buildSlotMap textBytes
          let byteOff := if header.entry ≥ textSec.addr
                         then header.entry - textSec.addr else 0
          let slot := byteOff / 8
          if hbnd : slot < slotMap.size then slotMap[slot]'hbnd else 0
        let s : State :=
          { regs        := { r1 := INPUT_START, r10 := STACK_START + 0x1000 }
            mem         := mem
            regions     := elfRegions elfBytes header textSec cfg.input.size
            pc          := entryPc
            exitCode    := none
            cuBudget    := cfg.cuBudget
            progIdBytes := cfg.progIdBytes }
        some (executeFnCpi cfg.programRegistry (fetchFromArray insns) s cfg.cuBudget)

/-- Convenience: ELF run returning only the exit code. -/
def runElfForExit (elfBytes : ByteArray) (cfg : RunConfig := {}) : Option Nat :=
  (runElf elfBytes cfg).bind (·.exitCode)

/-- ELF entrypoint that also surfaces remaining fuel, for CU accounting
    in downstream consumers (e.g. the Rust harness in `qedsvm-rs`).

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
        -- Load the (relocated) .text into the program region so an `ldx`
        -- into it reads the real bytecode, not a fabricated 0 (M2). Real
        -- programs read .text only for adjacent constants/jump tables;
        -- valid fixtures are unaffected (they don't read .text), and this
        -- now matches agave, which maps .text into the program region.
        let memText := loadBytesAt baseMem textBytes (Elf.relocateSecAddr textSec.addr)
        let mem₁ := match Elf.findSection elfBytes header Elf.rodataName with
          | some sec => loadBytesAt memText (Elf.extractSection elfBytes sec)
              (Elf.relocateSecAddr sec.addr)
          | none => memText
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
            loadBytesAt mem₁ relocated (Elf.relocateSecAddr sec.addr)
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
          { regs        := { r1 := INPUT_START, r10 := STACK_START + 0x1000 }
            mem         := mem
            regions     := elfRegions elfBytes header textSec cfg.input.size
            pc          := entryPc
            exitCode    := none
            cuBudget    := cfg.cuBudget
            progIdBytes := cfg.progIdBytes }
        some (executeFnCpiWithFuel cfg.programRegistry (fetchFromArray insns) s cfg.cuBudget)

end Runner
end SVM.SBPF
