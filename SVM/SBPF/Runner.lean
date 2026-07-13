/-
  sBPF runner — the production entrypoint executing arbitrary sBPF
  bytecode under the Lean semantics.

      SVM.SBPF.Runner.run : ByteArray → RunConfig → Option State

  Returns the final machine state; `state.exitCode`:
  - `none` → CU budget exhausted before halt
  - `some Memory.ERR_INVALID_PC` → execution fell off the program
  - `some n` → program executed `exit` with `r0 = n`

  Input is delivered Solana-style: `cfg.input` bytes are written at
  `INPUT_START` and the initial `r1` points there.
-/

import SVM.SBPF.Decode
import SVM.SBPF.Elf
import SVM.Native
import SVM.Syscalls.Pda

namespace SVM.SBPF
namespace Runner

open Memory

/-- One-off debug knob: when `true`, every step `dbg_trace`s pc + r0..r10
    to stderr. `false` (production) short-circuits, so the interpolation
    never runs. Flip + rebuild to bisect cross-engine CU drift against
    mollusk's `SBF_TRACE_DIR`/`SBF_TRACE_DISASSEMBLE`. For plain PC traces
    (`.pcs` files) do NOT flip this — use the rebuild-free runtime hook
    `QEDSVM_TRACE_OUT` below. -/
def TRACE_STEPS : Bool := false

/-- Runtime PC-trace hook (the automated `.pcs` capture path). Identity on
    the thunk, so proof-transparent: `traceStep pc f = f ()` by definition.
    The extern impl appends one decimal PC/line to `QEDSVM_TRACE_OUT` when
    set, else no-op. See `scripts/capture_trace.sh`. -/
@[never_extract, extern "lean_qedsvm_trace_step"]
def traceStep (_pc : USize) (f : Unit → α) : α := f ()

/-- Pad a Nat as a `width`-digit lowercase hex string. -/
private def hex (n width : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 (n % (16^width)))
  String.ofList (List.replicate (width - s.length) '0') ++ s

/-! ## Memory + register initialization -/

/-- Empty memory: every byte is zero. -/
def emptyMem : Mem := {}

/-- Overlay a ByteArray onto memory at `baseAddr`; bytes outside the
    overlaid range are preserved. -/
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

`step` consults `s.regions` on every `.ldx`/`.st`/`.stx` and traps a
miss to `ERR_ACCESS_VIOLATION`. The Runner has the ELF sections +
runtime layout to build a faithful table. Sizes mirror agave with
`FeatureSet::all_enabled()` (mollusk's default): stack `64 × 0x1000`
(no frame gaps), heap default 32 KiB (ComputeBudget request unmodeled). -/

/-- Total stack region size (256 KiB). -/
def STACK_SIZE : Nat := 0x40000

/-- Default heap region size (32 KiB). Matches agave's
    `compute_budget::DEFAULT_HEAP_COST`-paired allocation. -/
def DEFAULT_HEAP_SIZE : Nat := 0x8000

/-- Fixed runtime regions (stack + heap + input, all writable) WITHOUT
    per-account writable subdivision. Used for bare-bytecode demos or as
    an input-parse-failure fallback. ELF/CPI paths enforce per-account
    write boundaries + read-only as post-instruction validation in the
    Rust harness instead. -/
def runtimeRegions (inputLen : Nat) : Memory.RegionTable :=
  [ { start := STACK_START, size := STACK_SIZE,        writable := true }
  , { start := HEAP_START,  size := DEFAULT_HEAP_SIZE, writable := true }
  , { start := INPUT_START, size := inputLen,          writable := true } ]

/-- Read-only program region for an ELF: `MM_REGION_SIZE` to the end of
    the highest loaded section (text/rodata/data.rel.ro). Matches agave's
    single contiguous program region in `solana-sbpf`. -/
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
    region; per-account write boundaries (Tier-2 #9) and read-only
    detection are *post-instruction* validation in the Rust harness, not
    region traps. Agave does the same: programs write anywhere in the
    serialized input, runtime checks pre/post invariants at instruction
    exit (data_len ≤ pre + 10240, read-only unchanged, etc.). -/
def elfRegions (elfBytes : ByteArray) (header : Elf.Header)
    (textSec : Elf.SectionHeader) (inputLen : Nat) : Memory.RegionTable :=
  programRegionElf elfBytes header textSec :: runtimeRegions inputLen

/-! ## CPI sub-input construction

On `sol_invoke_signed{,_c}` the callee expects a *fresh*
`serialize_parameters`-shaped buffer at `INPUT_START` for the CPI target,
not the caller's input. Built in Lean mirroring `qedsvm-rs/src/serialize.rs`.
-/

/-- Read `len` bytes from `mem` at `addr`. Local copy of `Machine.readBytes`
    so the Runner doesn't pull in `Machine` (keeps the dep graph clean). -/
private def readMemBytes (mem : Mem) (addr len : Nat) : ByteArray :=
  ⟨(List.range len).foldl
    (fun acc i => acc.push ((mem (addr + i)) % 256).toUInt8) #[]⟩

/-- u64 LE → 8 ByteArray bytes. -/
private def u64ToLE (n : Nat) : ByteArray :=
  ⟨(List.range 8).foldl
    (fun acc i => acc.push ((n / 256^i) % 256).toUInt8) #[]⟩

/-! ### One-account CPI marshaling (Phase 3-full)

The AccountInfo passed via `r2` indirects through `Rc<RefCell<…>>` to
bytes in the *caller's* input region. CPI flow: (a) read those bytes,
(b) emit a fresh per-account block in the sub-input, (c) run the callee,
(d) write modifications back through the same pointers so the caller's
input region (the harness's post-state) reflects them.

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

/-- Parsed `solana_program::AccountInfo`: values for sub-input emission
    plus caller-memory write-back addresses. Default Rust layout (see
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

/-- Parse one `AccountInfo` at `addr`, following the `Rc<RefCell<…>>`
    chains to the underlying bytes. Layout (default Rust, 64-bit BPF):
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

/-- Solana ABI: zero bytes the serializer reserves after each account's
    data so the program may grow the buffer in place. -/
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

Generalizes `buildCpiSubInputOneAccount` to an account list. Two
complications vs. N=1:

- **Duplicate accounts** (same pubkey at i < j) compress: slot j emits a
  1-byte position index `i` + 7 pad, not a full block. The callee
  collapses both AccountInfos onto the same RefCell, so we only write
  back through the canonical slot's pointers (mirrors `serialize.rs`'s
  `seen[]` loop).
- **Per-slot cumulative offset** into the sub-input. Non-dup stride is
  `88 + dataLen + align_pad + 10240 + 8` (per-account); dup stride 8.
  Feeds write-back so we know where each slot's modifiable region lives. -/

/-- One slot in the laid-out CPI sub-input. `dupOf? = some j` means a
    duplicate of slot j (emit only the 8-byte marker); `blockOff` is the
    sub-input offset where this slot's bytes begin (for write-back). -/
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

/-- Build the slot table from pre-parsed accounts. Linear pass: for each
    slot, scan earlier slots for a key match. -/
def buildAcctSlots (parsed : List ParsedAcct) : List AcctSlot :=
  let n := parsed.length
  let parsedArr : Array ParsedAcct := parsed.toArray
  -- Fold over indices carrying the running block offset.
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

/-- Parse one `CpiAccount` at `addr`: the C-shaped variant
    `sol_invoke_signed_c` callers (Pinocchio, `solana-instruction-view`)
    pass instead of `AccountInfo`.

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

    Write-back caller-memory addresses:
    - `lamportsRefAddr` = value of the `lamports` ptr (the u64 lives there).
    - `dataLenRefAddr` = `addr + 16` (inline slot). NOTE: pinocchio's
      `AccountView` reads `data_len` from the **input buffer** at
      `dataPtr - 8`, so the second `writeU64 _ (dataPtr - 8) _` in
      `execCreateAccount`/`execAllocate` is what the program sees post-CPI;
      the `dataLenRefAddr` write just keeps the struct in sync.
    - `dataPtr` = value of the `data` ptr (into the input data region).
    - `ownerPtr` = value of the `owner` ptr (the slot CreateAccount
      overwrites). -/
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
def CPI_BLOCK_DATALEN_OFFSET  : Nat := 80   -- ...+lamports(8) = 80 (the data_len u64)
def CPI_BLOCK_DATA_OFFSET     : Nat := 88   -- ...+data_len(8) = 88

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

`executeFnCpi` wraps `step`: every instruction *except*
`sol_invoke_signed{,_c}` delegates to `step` (so single-step semantics +
all proofs apply unchanged). CPI consults `programRegistry`, decodes the
callee, builds a fresh sub-state, runs it recursively under the same
registry, and writes the callee's exit code into the caller's `r0`. The
full caller CU budget is passed down (no proportional split); re-entrant
CPI works transparently via the recursion. -/
/-! ## PDA signer-seed promotion

`invoke_signed` lets a caller act as a PDA: it supplies
`signer_seeds : &[&[&[u8]]]` at r4/r5, agave derives a PDA per inner
seed-array using the caller's program-id, and any AccountInfo whose
pubkey matches is promoted to is_signer=true callee-side. Without this,
callees can't distinguish a PDA invocation from a non-signer.

Wire format (Rust slice fat pointers throughout):
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

/-- Agave's seed-derived signer promotion: any account whose key matches
    a derived PDA gets is_signer = true. -/
def promoteSigners (parsedAccts : List ParsedAcct)
    (derivedPdas : List ByteArray) : List ParsedAcct :=
  parsedAccts.map (fun p =>
    if derivedPdas.any (fun pda => p.key == pda)
    then { p with isSigner := true }
    else p)

/-- Parse the original `(key, is_signer, is_writable)` of each account
    from a serialized input (the `serialize_parameters` layout that
    `buildCpiSubInput*` emits). These are the runtime-set privileges the
    runner clamps CPI escalation against (C5). A dup account is a 1-byte
    index + 7 padding; its key was captured at the first occurrence, so we
    just skip it. -/
def parseInputPrivileges (input : ByteArray) : List (ByteArray × Bool × Bool) :=
  go 8 (Decode.readU64LE input 0) []
where
  go (off remaining : Nat) (acc : List (ByteArray × Bool × Bool)) :
      List (ByteArray × Bool × Bool) :=
    match remaining with
    | 0 => acc.reverse
    | r + 1 =>
      -- Stop if a (non-dup) block would run past the buffer — keeps the
      -- walk total on malformed/non-account input (e.g. bare bytecode).
      if off + 88 > input.size then acc.reverse
      else if Decode.readU8 input off = 0xFF then
        let signer   := Decode.readU8 input (off + 1) ≠ 0
        let writable := Decode.readU8 input (off + 2) ≠ 0
        let key      := input.extract (off + 8) (off + 40)
        let dataLen  := Decode.readU64LE input (off + 80)
        let alignPad := (8 - dataLen % 8) % 8
        let blockSize := 88 + dataLen + alignPad + MAX_PERMITTED_DATA_INCREASE + 8
        go (off + blockSize) r ((key, signer, writable) :: acc)
      else
        go (off + 8) r acc

/-- Clamp CPI account privileges (C5): a callee may receive `is_signer`
    only if the account is a derived PDA OR the program requested it AND
    the caller actually held it; `is_writable` only if requested AND held.
    Prevents a program from forging a signer/writable by overwriting the
    AccountInfo flag byte in its own memory. -/
def clampCpiPrivileges (parsed : List ParsedAcct) (derivedPdas : List ByteArray)
    (origPrivs : List (ByteArray × Bool × Bool)) : List ParsedAcct :=
  parsed.map (fun p =>
    let isPda := derivedPdas.any (· == p.key)
    let origS := origPrivs.any (fun t => t.1 == p.key && t.2.1)
    let origW := origPrivs.any (fun t => t.1 == p.key && t.2.2)
    { p with isSigner   := isPda || (p.isSigner && origS),
             isWritable := p.isWritable && origW })

/-- Next state for a CPI-call syscall (`sol_invoke_signed{,_c}`).
    Non-recursive — the sub-VM call is the `runCallee` closure supplied by
    `executeFnCpiWithFuel`. Factored out to keep the per-instruction match
    arms compact (helps proofs that case-split on the instruction). -/
def cpiCallNextState (registry : Nat → Option ByteArray) (s : State)
    (sc : Syscall) (_fuel' : Nat)
    (runCallee : ByteArray → Option (State × Mem × Nat)) : State :=
  -- r1 → Instruction descriptor in caller memory. Two ABIs:
  -- - `sol_invoke_signed` (Rust): r1 → `&Instruction`; Rust reorders the
  --   Vec fields first, so `program_id` (inline 32B) sits at +48.
  -- - `sol_invoke_signed_c` (C): r1 → `SolInstruction`; first field is a
  --   `SolPubkey *program_id` ptr — deref for the 32B.
  let pubkeyAddr : Nat := match sc with
    | .sol_invoke_signed   => s.regs.r1 + 48      -- inline @ +48
    | .sol_invoke_signed_c =>                     -- pointer @ +0
      Memory.readU64 s.mem s.regs.r1
    | _ => s.regs.r1
  -- Little-endian 32-byte program id, read as four u64 limbs. Same value as
  -- the byte-wise `(List.range 32).foldl … 256^i` fold (LE composition), but
  -- kernel-friendly: a deep `foldl` is exponentially slow to whnf in the
  -- kernel (no memoization), which blocked the `cpiEnvelope_pid_fold` bridge
  -- (#40 gap 4). Behavioral identity is pinned by the CPI diff fixtures.
  let pid := Memory.readU64 s.mem pubkeyAddr
    + Memory.readU64 s.mem (pubkeyAddr + 8) * 2 ^ 64
    + Memory.readU64 s.mem (pubkeyAddr + 16) * 2 ^ 128
    + Memory.readU64 s.mem (pubkeyAddr + 24) * 2 ^ 192
  let accountCount := Memory.readU64 s.mem (s.regs.r1 + 16)
  -- Account-info layout differs by ABI: Rust = 48B `AccountInfo` with
  -- Rc/RefCell-chained lamports/data (`parseAccountInfo` chases it); C =
  -- 56B `CpiAccount` with direct ptrs + inline data_len (`parseCpiAccount`).
  -- Parsing the wrong layout yields garbage flags — the #10 bug
  -- (CpiAccount flag byte read at the wrong offset → is_signer=false,
  -- abort before promotion).
  let parsedAcctsRaw : List ParsedAcct :=
    match sc with
    | .sol_invoke_signed_c => parseCpiAccounts   s.mem s.regs.r2 accountCount
    | _                    => parseAccountInfos  s.mem s.regs.r2 accountCount
  -- PDA signer-seed promotion (r4/r5 under `s.progIdBytes`).
  let derivedPdas : List ByteArray :=
    deriveSignerPdas s.mem s.regs.r4 s.regs.r5 s.progIdBytes
  let parsedAccts : List ParsedAcct :=
    clampCpiPrivileges parsedAcctsRaw derivedPdas s.origPrivs
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
  -- M6 invoke-depth limit: agave caps stack height at 5 (top = 1, so ≤4
  -- nested CPIs); the 5th-level invoke fails `CallDepth` before dispatch.
  if s.invokeDepth + 1 > 4 then
    { s with regs := s.regs.set .r0 1
             pc   := s.pc + 1
             cuConsumed := s.cuConsumed + Cpi.cu }
  else
  if aliasedWritability then
    { s with regs := s.regs.set .r0 1
             pc   := s.pc + 1
             cuConsumed := s.cuConsumed + Cpi.cu }
  else
  match Native.dispatch pid ixData nativeAccts s.mem with
  | some nr =>
    Cpi.applyResult s
      { code := nr.r0
        mem := nr.mem
        log := s.log
        returnData := s.returnData
        returnDataProgId := s.returnDataProgId
        cuConsumed := nr.cu }
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
    | some (subFinal, newMem, _subFuelRemaining) =>
      -- H5: `subFinal.cuConsumed` is the callee's TOTAL spend (its own
      -- per-step baselines + syscall surcharges), so the caller absorbs
      -- exactly `Cpi.cu + subFinal.cuConsumed`. The old step-count proxy
      -- `+ (fuel' - subFuelRemaining)` would double-count those baselines.
      -- `applyResult` is also the proof-facing transaction boundary: a
      -- nonzero callee result rolls `newMem` back to `s.mem`, including every
      -- successful nested CPI mutation performed inside this callee.
      Cpi.applyResult s
        { code := subFinal.exitCode.getD 1
          mem := newMem
          log := subFinal.log
          returnData := subFinal.returnData
          returnDataProgId := subFinal.returnDataProgId
          cuConsumed := subFinal.cuConsumed }

/-- Pre-invocation half of a CPI sub-VM launch (M1/H2/M2): parse the
    callee ELF (or fall back to raw text), fail closed on unresolvable
    relocations / registry collisions / decode failure, then build the
    callee's instruction stream, fresh sub-state `subS`, and account slots.
    Extracted from `runCallee` so the recursive sub-VM call stays the ONLY
    thing inline (termination structural on `fuel`) and this build is
    named for the Stage-B boundedness proof (BoundedCpi.lean). Pure
    factoring — `do` desugaring identical to the old inline body. -/
def buildCalleeVM (s : State) (fuel' : Nat) (pidBytesIn : ByteArray)
    (parsedAcctsIn : List ParsedAcct) (ixDataIn : ByteArray)
    (calleeBytes : ByteArray) : Option (Array Insn × State × List AcctSlot) :=
  let tryElf : Option (ByteArray × Elf.Header × Elf.SectionHeader
                       × List (Nat × Nat)) := do
    let h ← Elf.parseHeader calleeBytes
    let textSec ← Elf.findSection calleeBytes h Elf.textName
    let rawText  := Elf.extractSection calleeBytes textSec
    let textBytes := Elf.applyRelocations calleeBytes h textSec.addr rawText
    let fnReg := Elf.buildFnRegistry calleeBytes h textSec.addr rawText
    some (textBytes, h, textSec, fnReg)
  do
    -- M1 + H2: an ELF callee with unresolvable relocations (agave
    -- `UnknownSymbol`) or a registry key collision (`SymbolHashCollision`)
    -- fails the CPI load OUTRIGHT — must NOT fall through to the raw-text
    -- branch, which would reinterpret ELF bytes as code.
    if let some h := Elf.parseHeader calleeBytes then do
      guard (Elf.relocationsResolvable calleeBytes h)
      if let some textSec := Elf.findSection calleeBytes h Elf.textName then
        let rawText := Elf.extractSection calleeBytes textSec
        guard (Elf.registryCollisionFree
          (Elf.buildFnRegistry calleeBytes h textSec.addr rawText))
    let (textBytes, headerOpt, textSecOpt, fnReg) :
        ByteArray × Option Elf.Header × Option Elf.SectionHeader
        × List (Nat × Nat) :=
      match tryElf with
      | some (tb, h, ts, fr) => (tb, some h, some ts, fr)
      -- Raw text (no ELF wrapper): registry = entrypoint at slot 0, mirroring
      -- solana-sbpf's `new_from_text_bytes`.
      | none => (calleeBytes, none, none, [(Elf.entrypointHash, 0)])
    let calleeInsns ← Decode.decodeProgram textBytes fnReg
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
        returnData  := s.returnData
        returnDataProgId := s.returnDataProgId
        cuBudget    := fuel'
        progIdBytes := pidBytesIn
        origPrivs   := parseInputPrivileges subInput
        invokeDepth := s.invokeDepth + 1 }
    some (calleeInsns, subS, slots)

/-- Post-invocation half of a CPI sub-VM launch: M6 read-only re-verify (a
    non-writable account the callee modified fails the call), M6r
    realloc-bound check (a writable account grown past
    `original_data_len + MAX_PERMITTED_DATA_INCREASE` fails), and
    writable-account write-back (harvest POST-CPI `data_len` at block
    offset 80, dual-write both caller length slots). A violation rolls
    every account back (`callerMem`) + surfaces the typed fault in
    exitCode; the honest path commits `newCallerMem`. -/
def commitCallee (callerMem : Mem) (slots : List AcctSlot) (subFinal : State)
    (subFuelRemaining : Nat) : State × Mem × Nat :=
  let roViolated : Bool := slots.any (fun slot =>
    match slot.dupOf? with
    | some _ => false
    | none =>
      let p := slot.parsed
      if p.isWritable then false
      else
        let blockBase := INPUT_START + slot.blockOff
        let postLen := Memory.readU64 subFinal.mem
          (blockBase + CPI_BLOCK_DATALEN_OFFSET)
        let postData := readMemBytes subFinal.mem
          (blockBase + CPI_BLOCK_DATA_OFFSET) p.dataLen
        let postLam := Memory.readU64 subFinal.mem
          (blockBase + CPI_BLOCK_LAMPORTS_OFFSET)
        let postOwner := readMemBytes subFinal.mem
          (blockBase + CPI_BLOCK_OWNER_OFFSET) 32
        postLen != p.dataLen || postData != p.data
          || postLam != p.lamports || postOwner != p.owner)
  let reallocViolated : Bool := slots.any (fun slot =>
    match slot.dupOf? with
    | some _ => false
    | none =>
      let p := slot.parsed
      if !p.isWritable then false
      else
        let blockBase := INPUT_START + slot.blockOff
        let postLen := Memory.readU64 subFinal.mem
          (blockBase + CPI_BLOCK_DATALEN_OFFSET)
        decide (postLen > p.dataLen + MAX_PERMITTED_DATA_INCREASE))
  let newCallerMem : Mem := slots.foldl (fun mem slot =>
    match slot.dupOf? with
    | some _ => mem
    | none =>
      let p := slot.parsed
      if !p.isWritable then mem
      else
      let blockBase := INPUT_START + slot.blockOff
      let postLen := Memory.readU64 subFinal.mem
        (blockBase + CPI_BLOCK_DATALEN_OFFSET)
      let newData := readMemBytes subFinal.mem
        (blockBase + CPI_BLOCK_DATA_OFFSET) postLen
      let m1 := loadBytesAt mem newData p.dataPtr
      let m1' := Memory.writeU64 m1 p.dataLenRefAddr postLen
      let m1'' := Memory.writeU64 m1' (p.dataPtr - 8) postLen
      let newLamports := Memory.readU64 subFinal.mem
        (blockBase + CPI_BLOCK_LAMPORTS_OFFSET)
      let m2 := Memory.writeU64 m1'' p.lamportsRefAddr newLamports
      let newOwner := readMemBytes subFinal.mem
        (blockBase + CPI_BLOCK_OWNER_OFFSET) 32
      loadBytesAt m2 newOwner p.ownerPtr) callerMem
  if reallocViolated then
    ({ subFinal with exitCode := some ERR_INVALID_REALLOC, vmError := some .invalidRealloc },
      callerMem, subFuelRemaining)
  else if roViolated then
    ({ subFinal with exitCode := some ERR_READONLY_MODIFIED, vmError := some .readonlyModified },
      callerMem, subFuelRemaining)
  else
    (subFinal, newCallerMem, subFuelRemaining)

/-- CU-accounting variant of `executeFnCpi`, returning final state + fuel
    remaining (`cuConsumed = initial - returned`). Each step (incl. a CPI)
    burns one caller fuel unit; CPI dispatch is delegated to
    `cpiCallNextState`, so this handles only fuel/fetch/the instruction
    match. The early-exit arms preserve fuel at exit, so the consumed
    count excludes the no-op tail. -/
def executeFnCpiWithFuel (registry : Nat → Option ByteArray)
    (fetch : Nat → Option Insn) (s : State) (fuel : Nat) : State × Nat :=
  match fuel with
  | 0 => (s, 0)
  | fuel' + 1 =>
    match s.exitCode with
    | some _ => (s, fuel)
    | none =>
      -- H5 budget halt — mirrors `executeFn` exactly so the RunnerBridge
      -- equality stays a structural induction. Over-budget halts with
      -- `exitCode = none` (OutOfBudget on the wire).
      if s.cuConsumed > s.cuBudget then (s, fuel)
      else
      match fetch s.pc with
      | none => ({ s with exitCode := some ERR_INVALID_PC, vmError := some .invalidPc }, fuel')
      | some insn =>
        -- `runCallee` keeps ONLY the recursive sub-VM invocation inline (at
        -- `fuel'`, strictly smaller → termination structural on `fuel`);
        -- pre-build/post-commit are `buildCalleeVM`/`commitCallee`.
        let runCallee (pidBytesIn : ByteArray) (parsedAcctsIn : List ParsedAcct)
            (ixDataIn : ByteArray) (calleeBytes : ByteArray)
            : Option (State × Mem × Nat) := do
          let (calleeInsns, subS, slots) ←
            buildCalleeVM s fuel' pidBytesIn parsedAcctsIn ixDataIn calleeBytes
          let (subFinal, subFuelRemaining) := executeFnCpiWithFuel registry
            (fetchFromArray calleeInsns) subS fuel'
          some (commitCallee s.mem slots subFinal subFuelRemaining)
        let s' : State :=
          match insn with
          | .call .sol_invoke_signed =>
            let pubkeyAddr := s.regs.r1 + 48
            let pidBytes := readMemBytes s.mem pubkeyAddr 32
            let accountCount := Memory.readU64 s.mem (s.regs.r1 + 16)
            -- Promote seed-derived PDAs so the callee's sub-input matches
            -- what cpiCallNextState computes for Native/aliasing checks.
            let parsedAcctsRaw := parseAccountInfos s.mem s.regs.r2 accountCount
            let derivedPdas := deriveSignerPdas s.mem s.regs.r4 s.regs.r5 s.progIdBytes
            let parsedAccts := clampCpiPrivileges parsedAcctsRaw derivedPdas s.origPrivs
            -- Rust ABI Instruction: data:Vec { ptr@+24, cap@+32, len@+40 }.
            let ixDataPtr := Memory.readU64 s.mem (s.regs.r1 + 24)
            let ixDataLen := Memory.readU64 s.mem (s.regs.r1 + 40)
            let ixData    := readMemBytes s.mem ixDataPtr ixDataLen
            cpiCallNextState registry s .sol_invoke_signed fuel'
              (runCallee pidBytes parsedAccts ixData)
          | .call .sol_invoke_signed_c =>
            let pubkeyAddr := Memory.readU64 s.mem s.regs.r1
            let pidBytes := readMemBytes s.mem pubkeyAddr 32
            let accountCount := Memory.readU64 s.mem (s.regs.r1 + 16)
            -- C ABI: `CpiAccount` (56B stride, direct ptrs, inline data_len).
            -- Must use `parseCpiAccounts`, not `parseAccountInfos`, or
            -- is_signer lands at the wrong offset → wrong PDA promotion (#10).
            let parsedAcctsRaw := parseCpiAccounts s.mem s.regs.r2 accountCount
            let derivedPdas := deriveSignerPdas s.mem s.regs.r4 s.regs.r5 s.progIdBytes
            let parsedAccts := clampCpiPrivileges parsedAcctsRaw derivedPdas s.origPrivs
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
            executeFnCpiWithFuel registry fetch (chargeCu s') fuel'
          else
            executeFnCpiWithFuel registry fetch (chargeCu s') fuel'

/-- Thin wrapper around `executeFnCpiWithFuel` discarding the fuel
    remainder; preserved for existing callers (demos + `run`/`runElf`). -/
def executeFnCpi (registry : Nat → Option ByteArray)
    (fetch : Nat → Option Insn) (s : State) (fuel : Nat) : State :=
  (executeFnCpiWithFuel registry fetch s fuel).1

/-! ## Entrypoints -/

/-- Initial machine state for `Runner.run`. Named (not inline) so
    end-to-end soundness theorems (`RunnerBridge.lean`) can reason about
    its fields. -/
def initialState (cfg : RunConfig) : State :=
  { regs        := { r1 := INPUT_START, r10 := STACK_START + 0x1000 }
    mem         := loadInput emptyMem cfg.input
    regions     := runtimeRegions cfg.input.size
    pc          := 0
    exitCode    := none
    cuBudget    := cfg.cuBudget
    progIdBytes := cfg.progIdBytes
    origPrivs   := parseInputPrivileges cfg.input }

@[simp] theorem initialState_pc (cfg : RunConfig) : (initialState cfg).pc = 0 := rfl

@[simp] theorem initialState_exitCode (cfg : RunConfig) :
    (initialState cfg).exitCode = none := rfl

@[simp] theorem initialState_callStack (cfg : RunConfig) :
    (initialState cfg).callStack = [] := rfl

@[simp] theorem initialState_cuConsumed (cfg : RunConfig) :
    (initialState cfg).cuConsumed = 0 := rfl

@[simp] theorem initialState_cuBudget (cfg : RunConfig) :
    (initialState cfg).cuBudget = cfg.cuBudget := rfl

/-- Decode `bytes` and run for up to `cfg.cuBudget` CU. `none` on decode
    failure. `state.exitCode`: `none` = out of budget,
    `some ERR_INVALID_PC` = fell off program, `some n` = clean exit. -/
def run (bytes : ByteArray) (cfg : RunConfig := {}) : Option State := do
  -- Raw text (no ELF): registry = entrypoint at slot 0, mirroring
  -- solana-sbpf's `new_from_text_bytes`.
  let insns ← Decode.decodeProgram bytes [(Elf.entrypointHash, 0)]
  return executeFnCpi cfg.programRegistry (fetchFromArray insns) (initialState cfg) cfg.cuBudget

/-- Convenience: return only the exit code if the program terminated. -/
def runForExit (bytes : ByteArray) (cfg : RunConfig := {}) : Option Nat :=
  (run bytes cfg).bind (·.exitCode)

/-! ## ELF entrypoints

Real Solana programs ship as ELF64 binaries. These entrypoints parse the
ELF wrapper, extract the `.text` bytecode, and feed it to `run`. -/

/-- Decode and run an sBPF ELF64 binary. `none` if malformed or no `.text`.
    `.rodata` (if present) is mapped at its `sh_addr` so `lddw`/`ldx`
    derefs against rodata resolve — the universal Anchor/Pinocchio/
    native-Rust/Quasar pattern. -/
def runElf (elfBytes : ByteArray) (cfg : RunConfig := {}) : Option State :=
  match Elf.parseHeader elfBytes with
  | none => none
  | some header =>
    match Elf.findSection elfBytes header Elf.textName with
    | none => none
    | some textSec =>
      -- M1: fail closed on a relocation to a missing `.dynsym`/out-of-range
      -- symbol (agave `UnknownSymbol` at load); else `applyRelocations`
      -- 0-fills the bad read and patches a wrong address.
      if !Elf.relocationsResolvable elfBytes header then none else
      let rawText   := Elf.extractSection elfBytes textSec
      -- Patch R_BPF_64_64 (lddw → .rodata-relative); no-op without .rel.dyn.
      let textBytes := Elf.applyRelocations elfBytes header textSec.addr rawText
      let fnReg := Elf.buildFnRegistry elfBytes header textSec.addr rawText
      -- H2 residual: a registry key collision is agave's load-time
      -- `SymbolHashCollision` — fail closed, not first-match.
      if !Elf.registryCollisionFree fnReg then none else
      match Decode.decodeProgram textBytes fnReg with
      | none => none
      | some insns =>
        let baseMem := loadInput emptyMem cfg.input
        -- M2: load (relocated) .text into the program region so an `ldx`
        -- into it reads real bytecode, not a fabricated 0 (matches agave).
        -- Valid fixtures don't read .text, so are unaffected.
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
        -- L8: map `e_entry` to a logical PC via the slot map. Slot-0 entry
        -- fixtures reduce to the old `pc := 0`.
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
            progIdBytes := cfg.progIdBytes
            origPrivs   := parseInputPrivileges cfg.input }
        some (executeFnCpi cfg.programRegistry (fetchFromArray insns) s cfg.cuBudget)

/-- Convenience: ELF run returning only the exit code. -/
def runElfForExit (elfBytes : ByteArray) (cfg : RunConfig := {}) : Option Nat :=
  (runElf elfBytes cfg).bind (·.exitCode)

/-- ELF entrypoint also surfacing remaining fuel, for CU accounting in
    downstream consumers (the `qedsvm-rs` harness). `none` on parse/decode
    failure, else `some (state, remaining)` with
    `cuConsumed = cfg.cuBudget - remaining`. Out-of-budget: exitCode none,
    remaining 0. Honors `e_entry`: starts at `(e_entry - .text.sh_addr)/8`
    (0 for hand-assembled fixtures; the linker's `entrypoint` slot for real
    `cargo-build-sbf` output). -/
def runElfWithFuel (elfBytes : ByteArray) (cfg : RunConfig := {}) :
    Option (State × Nat) :=
  match Elf.parseHeader elfBytes with
  | none => none
  | some header =>
    match Elf.findSection elfBytes header Elf.textName with
    | none => none
    | some textSec =>
      -- M1: fail closed on an unresolvable relocation symbol (see `runElf`).
      if !Elf.relocationsResolvable elfBytes header then none else
      let rawText   := Elf.extractSection elfBytes textSec
      let textBytes := Elf.applyRelocations elfBytes header textSec.addr rawText
      let fnReg := Elf.buildFnRegistry elfBytes header textSec.addr rawText
      -- H2 residual: registry key collision = agave `SymbolHashCollision`,
      -- fail closed not first-match.
      if !Elf.registryCollisionFree fnReg then none else
      match Decode.decodeProgram textBytes fnReg with
      | none => none
      | some insns =>
        let baseMem := loadInput emptyMem cfg.input
        -- M2: load (relocated) .text into the program region so an `ldx`
        -- into it reads real bytecode, not a fabricated 0 (matches agave).
        let memText := loadBytesAt baseMem textBytes (Elf.relocateSecAddr textSec.addr)
        let mem₁ := match Elf.findSection elfBytes header Elf.rodataName with
          | some sec => loadBytesAt memText (Elf.extractSection elfBytes sec)
              (Elf.relocateSecAddr sec.addr)
          | none => memText
        -- Map `.data.rel.ro` if present: the linker parks pointer-bearing
        -- static structures here (jump tables, `&'static`, vtables). Each
        -- field carries a RELATIVE reloc moving the address from the upper
        -- to the lower 32 bits. Enum-dispatch programs (SPL Token, Anchor,
        -- Pinocchio match arms) crash without this.
        let mem := match Elf.findSection elfBytes header Elf.dataRelRoName with
          | some sec =>
            let raw       := Elf.extractSection elfBytes sec
            let relocated := Elf.applyDataRelocations elfBytes header sec.addr raw
            loadBytesAt mem₁ relocated (Elf.relocateSecAddr sec.addr)
          | none => mem₁
        -- `e_entry` (VA) → logical PC: byte offset `e_entry - textSec.addr`
        -- /8 is the byte-slot index, but a `lddw` is 2 slots / 1 logical
        -- insn, so `buildSlotMap` translates slot → PC. (No-lddw-before-
        -- entry programs have slotMap[i]=i, hence earlier fixtures worked.)
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
            progIdBytes := cfg.progIdBytes
            origPrivs   := parseInputPrivileges cfg.input }
        some (executeFnCpiWithFuel cfg.programRegistry (fetchFromArray insns) s cfg.cuBudget)

end Runner
end SVM.SBPF
