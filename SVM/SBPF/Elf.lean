/-
  Minimal ELF64 loader for Solana sBPF binaries.

  Solana programs ship as 64-bit little-endian ELF binaries with the
  bytecode in a `.text` section. This module parses:

  - the ELF64 file header (validating magic, class=64-bit, endian=LE),
  - the section header table,
  - the section name string table (`.shstrtab`),

  and exposes `extractText` to pull out the `.text` section's bytes
  ready to feed into `Decode.decodeProgram` / `Runner.run`.

  Coverage:
  - `.text` bytes are extracted via `extractText`. `.rodata` and
    `.data.rel.ro` are mapped into `Mem` at their VAs by the runner
    (`Runner.lean`), so table-driven code reads its constants.
  - Relocations applied by `applyRelocations`: `R_BPF_64_64` (patches an
    `lddw` immediate to a symbol's runtime address), `R_BPF_64_RELATIVE`
    (both the in-`.text` lddw form and the `.data.rel.ro` form), and
    `R_BPF_64_32` (inter-function `call` offsets → murmur3 hash).

  V0 internal-call resolution (audit H2, closed): `R_BPF_64_32` against
  a defined function patches the murmur3 hash of the target PC bytes
  (agave's `register_function_hashed_legacy` convention) and the pair
  is collected into the function registry (`buildFnRegistry`), which
  `Decode.decodeInsn` consults to resolve `.call_local` targets. An
  unresolved key decodes to `.call (.unknown _)`, which fails closed at
  runtime (agave: `UnsupportedInstruction`).

  Remaining divergences from agave are tracked in
  docs/SOUNDNESS_AUDIT_*.md (M1: structural fail-open on malformed
  section/relocation tables).
-/

import SVM.SBPF.Decode
import SVM.SBPF.Murmur3

namespace SVM.SBPF
namespace Elf

open Decode

/-! ## Parsed structures -/

/-- A parsed ELF64 file header (only the fields we use). -/
structure Header where
  /-- Entry point virtual address (e_entry). -/
  entry     : Nat
  /-- Section header table file offset (e_shoff). -/
  shoff     : Nat
  /-- Size of each section header entry (e_shentsize); should be 64. -/
  shentsize : Nat
  /-- Number of section header entries (e_shnum). -/
  shnum     : Nat
  /-- Index of the section header string table (e_shstrndx). -/
  shstrndx  : Nat

/-- A parsed section header (only the fields we use). -/
structure SectionHeader where
  /-- Offset of the section's name inside `.shstrtab`. -/
  nameOff : Nat
  /-- Section type (SHT_PROGBITS = 1, SHT_STRTAB = 3, ...). -/
  type    : Nat
  /-- Virtual address at which the section is loaded. For `.rodata` this
      is where `lddw`/`ldx` instructions in the program will read from. -/
  addr    : Nat
  /-- File offset of the section's contents. -/
  offset  : Nat
  /-- Section size in bytes. -/
  size    : Nat

/-! ## Header parsing -/

/-- Parse the ELF64 header. Returns `none` if the file is too short, the
    magic is wrong, the class is not 64-bit, the endianness is not LE, the
    machine is not BPF/SBPF, or the SBPF version (`e_flags`) is not V0.

    The `e_machine` and `e_flags` gates (C3) are load-time fail-closed
    checks: agave maps `e_flags` 0..4 to SBPF V0..V4 and rejects versions
    it doesn't enable, and requires `e_machine ∈ {EM_BPF, EM_SBPF}`. This
    model only faithfully implements V0 (decode + execute assume V0
    opcode/call/sign-extension semantics), so a non-V0 or non-BPF binary
    is rejected rather than silently mis-executed as V0. See
    docs/SOUNDNESS_AUDIT_* (C3). -/
def parseHeader (bytes : ByteArray) : Option Header :=
  if bytes.size < 64 then none
  else if readU8 bytes 0 ≠ 0x7f then none  -- magic
  else if readU8 bytes 1 ≠ 0x45 then none  -- 'E'
  else if readU8 bytes 2 ≠ 0x4c then none  -- 'L'
  else if readU8 bytes 3 ≠ 0x46 then none  -- 'F'
  else if readU8 bytes 4 ≠ 2 then none     -- ei_class = ELFCLASS64
  else if readU8 bytes 5 ≠ 1 then none     -- ei_data = ELFDATA2LSB
  -- ei_osabi (byte 7): agave rejects ≠ ELFOSABI_NONE (`WrongAbi`,
  -- solana-sbpf 0.14.4 elf.rs:721). M1.
  else if readU8 bytes 7 ≠ 0 then none
  -- e_type (offset 16): agave rejects ≠ ET_DYN = 3 (`WrongType`,
  -- elf.rs:727) — sBPF programs are shared objects. M1.
  else if readU16LE bytes 16 ≠ 3 then none
  -- e_machine (offset 18): EM_BPF = 247 or EM_SBPF = 263.
  else if readU16LE bytes 18 ≠ 247 ∧ readU16LE bytes 18 ≠ 263 then none
  -- e_flags (offset 48): SBPF version. Only V0 (0) is modeled.
  else if readU32LE bytes 48 ≠ 0 then none
  -- M1: section-table structural validation — fail closed on a malformed
  -- header rather than read past the file via zero-fill. `e_shstrndx`
  -- must index a real section, and the section header table must lie
  -- within the file. NOTE this check also rejects `SHN_XINDEX`
  -- (`e_shstrndx = 0xFFFF`, the extended-index sentinel): `shnum` is a
  -- u16, so `0xFFFF ≥ shnum` always — extended section numbering is
  -- deliberately not modeled. See docs/SOUNDNESS_AUDIT_* (M1).
  else if readU16LE bytes 62 ≥ readU16LE bytes 60 then none      -- shstrndx ≥ shnum
  else if readU64LE bytes 40 + readU16LE bytes 60 * readU16LE bytes 58 > bytes.size then none
  else some {
    entry     := readU64LE bytes 24
    shoff     := readU64LE bytes 40
    shentsize := readU16LE bytes 58
    shnum     := readU16LE bytes 60
    shstrndx  := readU16LE bytes 62
  }

/-! ## Section header parsing -/

/-- Parse the section header at index `idx`. -/
def parseSectionHeader (bytes : ByteArray) (h : Header) (idx : Nat) :
    SectionHeader :=
  let base := h.shoff + idx * h.shentsize
  { nameOff := readU32LE bytes base
    type    := readU32LE bytes (base + 4)
    addr    := readU64LE bytes (base + 16)
    offset  := readU64LE bytes (base + 24)
    size    := readU64LE bytes (base + 32) }

/-! ## Name lookup in `.shstrtab` -/

/-- Test whether a null-terminated C string at `bytes[off..]` matches
    `target` exactly (including the trailing null byte). -/
def matchesCString (bytes : ByteArray) (off : Nat) (target : ByteArray) :
    Bool :=
  go 0 (target.size + 1)
where
  go (i fuel : Nat) : Bool :=
    match fuel with
    | 0 => false
    | fuel' + 1 =>
      if i = target.size then
        readU8 bytes (off + i) == 0
      else
        readU8 bytes (off + i) == (target.get! i).toNat
          && go (i + 1) fuel'

/-! ## Finding a section by name -/

/-- Search the section header table for one whose name matches `name`.
    Returns the parsed `SectionHeader` if found. -/
def findSection (bytes : ByteArray) (h : Header) (name : ByteArray) :
    Option SectionHeader :=
  let shstrtab := parseSectionHeader bytes h h.shstrndx
  go 0 h.shnum shstrtab.offset
where
  go (i n shstrtabOff : Nat) : Option SectionHeader :=
    match n with
    | 0 => none
    | n' + 1 =>
      let sec := parseSectionHeader bytes h i
      if matchesCString bytes (shstrtabOff + sec.nameOff) name then some sec
      else go (i + 1) n' shstrtabOff

/-! ## Section extraction -/

/-- Copy the bytes of a section out of the ELF file. -/
def extractSection (bytes : ByteArray) (sec : SectionHeader) : ByteArray :=
  bytes.extract sec.offset (sec.offset + sec.size)

/-- `.text` section name as a byte array. -/
def textName : ByteArray := ⟨#[0x2e, 0x74, 0x65, 0x78, 0x74]⟩  -- ".text"

/-- `.rodata` section name as a byte array. Holds read-only program data
    (Anchor discriminator tables, string constants, IDL fragments, etc.). -/
def rodataName : ByteArray := ⟨#[0x2e, 0x72, 0x6f, 0x64, 0x61, 0x74, 0x61]⟩  -- ".rodata"

/-- `.data.rel.ro` — read-only-after-relocation data. The linker emits
    static structures containing pointer fields here (jump tables for
    enum match-arms, `&'static` references to rodata strings, vtables,
    etc.). Each pointer field carries an `R_BPF_64_RELATIVE` relocation
    whose payload-bytes layout is `00 00 00 00 <u32 target_addr>` —
    the address sits in the upper 32 bits of the u64 word, with the
    runtime loader expected to repack it as `<u32 target_addr> 00 00 00 00`
    (i.e., write target_addr into the low 32 bits). Programs with
    enum dispatch (SPL Token, Anchor, etc.) crash without this. -/
def dataRelRoName : ByteArray :=
  ⟨#[0x2e, 0x64, 0x61, 0x74, 0x61, 0x2e, 0x72, 0x65, 0x6c, 0x2e, 0x72, 0x6f]⟩  -- ".data.rel.ro"

/-- `.dynstr` section name — strings for dynamic-symbol entries
    (used to resolve syscall names referenced by `R_BPF_64_32`
    relocations). -/
def dynstrName : ByteArray :=
  ⟨#[0x2e, 0x64, 0x79, 0x6e, 0x73, 0x74, 0x72]⟩  -- ".dynstr"

/-! ## Symbols and relocations

We model the minimal subset needed to patch `R_BPF_64_64` relocations,
which is what `rustc` emits for any `lddw rN, <symbol>` against
`.rodata`. -/

/-- A parsed ELF64 symbol table entry (`Elf64_Sym`, 24 bytes). -/
structure SymbolEntry where
  /-- Offset into the associated string table (`.dynstr`). -/
  nameOff : Nat
  /-- Type + binding info (low nibble = type, high nibble = bind). -/
  info    : Nat
  /-- Reserved. -/
  other   : Nat
  /-- Section index this symbol belongs to. -/
  shndx   : Nat
  /-- Symbol's value (typically an offset within its section). -/
  value   : Nat
  /-- Symbol size in bytes. -/
  size    : Nat

/-- A parsed ELF64 relocation entry without addend (`Elf64_Rel`, 16 bytes). -/
structure RelocationEntry where
  /-- Address (or section-relative offset) where the patch is applied. -/
  offset : Nat
  /-- Encodes both the symbol index (high 32 bits) and the relocation
      type (low 32 bits). -/
  info   : Nat

/-- Relocation type field extracted from `r_info` (low 32 bits). -/
@[inline] def RelocationEntry.type (r : RelocationEntry) : Nat :=
  r.info % 0x100000000

/-- Symbol-table index extracted from `r_info` (high 32 bits). -/
@[inline] def RelocationEntry.sym (r : RelocationEntry) : Nat :=
  r.info / 0x100000000

/-- Known sBPF relocation type constants. -/
def R_BPF_64_64       : Nat := 1
def R_BPF_64_Abs64    : Nat := 2
def R_BPF_64_Abs32    : Nat := 3
def R_BPF_64_NoDyld32 : Nat := 6
def R_BPF_64_Relative : Nat := 8
def R_BPF_64_32       : Nat := 10

/-- Section type constants (from ELF spec). -/
def SHT_SYMTAB : Nat := 2
def SHT_REL    : Nat := 9
def SHT_DYNSYM : Nat := 11

/-- Parse a 24-byte symbol entry from `bytes` starting at `off`. -/
def parseSymbolEntry (bytes : ByteArray) (off : Nat) : SymbolEntry :=
  { nameOff := readU32LE bytes off
    info    := readU8    bytes (off + 4)
    other   := readU8    bytes (off + 5)
    shndx   := readU16LE bytes (off + 6)
    value   := readU64LE bytes (off + 8)
    size    := readU64LE bytes (off + 16) }

/-- Parse a 16-byte relocation entry from `bytes` starting at `off`. -/
def parseRelocationEntry (bytes : ByteArray) (off : Nat) : RelocationEntry :=
  { offset := readU64LE bytes off
    info   := readU64LE bytes (off + 8) }

/-! ## Locating the symbol + relocation sections -/

/-- Find the first section whose `type` field matches `targetType`. -/
def findSectionByType (bytes : ByteArray) (h : Header) (targetType : Nat) :
    Option SectionHeader :=
  go 0 h.shnum
where
  go (i n : Nat) : Option SectionHeader :=
    match n with
    | 0 => none
    | n' + 1 =>
      let sec := parseSectionHeader bytes h i
      if sec.type = targetType then some sec
      else go (i + 1) n'

/-! ## Patching helpers -/

/-- Bump a section-VA into the program region if it's below
    `MM_REGION_SIZE`. Mirrors agave's loader convention: sections with
    a sub-`MM_REGION_SIZE` `sh_addr` (the typical `cargo-build-sbf`
    case, e.g. `.rodata` at `0x1bf60`) get shifted to
    `MM_PROGRAM_START + sh_addr` (`0x1_0001_bf60`) at load time.
    Sections whose linker-assigned address is already at or above
    `MM_REGION_SIZE` (e.g. hand-assembled demo ELFs that put `.rodata`
    at `0x100000000`) are left alone. Use this everywhere a section
    is mapped into `Mem` or where a relocation target is computed,
    so that lddw imms (post-relocation) and the loaded bytes live at
    the same address. -/
def relocateSecAddr (addr : Nat) : Nat :=
  if addr < Memory.MM_REGION_SIZE then addr + Memory.MM_REGION_SIZE else addr

/-- Write a 32-bit little-endian value at offset `off` in `bytes`. -/
def writeU32LE (bytes : ByteArray) (off val : Nat) : ByteArray :=
  let b0 := bytes.set! off       (val % 0x100).toUInt8
  let b1 := b0.set!   (off + 1)  (val / 0x100 % 0x100).toUInt8
  let b2 := b1.set!   (off + 2)  (val / 0x10000 % 0x100).toUInt8
  b2.set!             (off + 3)  (val / 0x1000000 % 0x100).toUInt8

/-- Write a 64-bit little-endian value at offset `off` in `bytes`. -/
def writeU64LE (bytes : ByteArray) (off val : Nat) : ByteArray :=
  let lo := val % 0x100000000
  let hi := val / 0x100000000
  let b1 := writeU32LE bytes off lo
  writeU32LE b1 (off + 4) hi

/-! ## Applying relocations -/

/-- Apply a single `R_BPF_64_64` relocation to the loaded `.text` bytes.
    Splits a 64-bit symbol address into the two 32-bit immediate fields
    of an `lddw rN, IMM` (a 16-byte instruction). The resulting address
    is bumped into the program region (via `relocateSecAddr`) if it's
    below `MM_REGION_SIZE`, matching agave's loader convention. -/
def applyRel64 (textBytes : ByteArray) (textVA target : Nat) (relOff : Nat) :
    ByteArray :=
  let off := if relOff ≥ textVA then relOff - textVA else relOff
  let addend := readU32LE textBytes (off + 4)
  let raw    := (target + addend) % 0x10000000000000000  -- u64
  let final  := relocateSecAddr raw
  let lo := final % 0x100000000
  let hi := final / 0x100000000
  let b1 := writeU32LE textBytes (off + 4) lo
  writeU32LE b1 (off + 12) hi

/-- Apply a single `R_BPF_64_32` relocation. The patch site `relOff`
    points at the *start* of the 8-byte instruction (typically `0x85`);
    the imm to overwrite is at `relOff + 4`. The patched value is the
    function-registry key computed by `rel32KeyEntry` (a syscall's
    name hash, or a bpf-to-bpf target's PC-bytes hash). -/
def applyRel32 (textBytes : ByteArray) (textVA hash : Nat) (relOff : Nat) :
    ByteArray :=
  let off := if relOff ≥ textVA then relOff - textVA else relOff
  writeU32LE textBytes (off + 4) hash

/-- A u64 as 8 little-endian bytes — the input agave hashes to key a
    bpf-to-bpf call target in the function registry. -/
def le8 (n : Nat) : ByteArray :=
  ⟨#[UInt8.ofNat (n % 256),
     UInt8.ofNat (n / 0x100 % 256),
     UInt8.ofNat (n / 0x10000 % 256),
     UInt8.ofNat (n / 0x1000000 % 256),
     UInt8.ofNat (n / 0x100000000 % 256),
     UInt8.ofNat (n / 0x10000000000 % 256),
     UInt8.ofNat (n / 0x1000000000000 % 256),
     UInt8.ofNat (n / 0x100000000000000 % 256)]⟩

/-- agave's legacy function-registry key for a bpf-to-bpf call target:
    Murmur3-32 (seed 0) of the target slot index as 8 LE bytes
    (`register_function_hashed_legacy`, solana-sbpf 0.14.4
    program.rs:154-159 — the V0 path). The name "entrypoint" is the
    one exception: it keys by the hash of the NAME (`entrypointHash`). -/
def pcHash (targetSlot : Nat) : Nat :=
  Murmur3.hash (le8 targetSlot) 0

/-- The function-registry key of the program entrypoint: agave keys it
    by the hash of the literal name "entrypoint", not of its PC bytes
    (solana-sbpf program.rs:155-156, elf.rs:637-643). -/
def entrypointHash : Nat := Murmur3.hashString "entrypoint"

/-- The UTF-8 bytes of "entrypoint", for symbol-name comparison. -/
def entrypointName : ByteArray := "entrypoint".toUTF8

/-- Read a null-terminated string from `bytes` starting at `off`. Used
    for resolving `.dynstr` symbol names. Capped at 128 bytes to keep
    Lean's termination checker happy for runaway inputs. -/
def readCString (bytes : ByteArray) (off : Nat) : ByteArray :=
  go 0 128 #[]
where
  go (i fuel : Nat) (acc : Array UInt8) : ByteArray :=
    match fuel with
    | 0 => ⟨acc⟩
    | fuel' + 1 =>
      let b := readU8 bytes (off + i)
      if b = 0 then ⟨acc⟩ else go (i + 1) fuel' (acc.push b.toUInt8)

/-- PC-relative internal calls found by scanning the RAW text, mirroring
    the FIRST pass of solana-sbpf 0.14.4 `relocate` (elf.rs:922-948):
    every slot whose opcode is `CALL_IMM` (0x85) with `imm ≠ -1` is a
    PC-relative call to `slot + 1 + imm`; agave registers the target
    under its PC-bytes hash and rewrites the imm to that hash. (Calls
    that go through `R_BPF_64_32` relocations carry the placeholder
    imm = -1 on disk and are skipped here; the relocation pass handles
    them.) Returns `(slotIdx, targetSlot)` pairs.

    agave fails the LOAD on an out-of-bounds target
    (`RelativeJumpOutOfBounds`); this parser has no error channel, so
    such a call keeps its raw imm, decodes to `.call (.unknown _)`, and
    fails closed at runtime instead (audit H2). NOTE the scan is over
    SLOTS, exactly as agave's: it does not skip an `lddw`'s second slot
    (whose opcode byte is 0, never 0x85, so this cannot misfire). -/
def pcRelCallTargets (textBytes : ByteArray) : List (Nat × Nat) :=
  let nSlots := textBytes.size / 8
  (List.range nSlots).filterMap fun i =>
    let opc := readU8 textBytes (i * 8)
    let immU := readU32LE textBytes (i * 8 + 4)
    if opc = 0x85 ∧ immU ≠ 0xFFFFFFFF then
      let target : Int := (i : Int) + 1 + signExt32 immU
      if 0 ≤ target ∧ target < (nSlots : Int) then
        some (i, target.toNat)
      else
        none
    else
      none

/-- The patched imm key + optional function-registry entry for one
    `R_BPF_64_32` relocation, mirroring solana-sbpf 0.14.4 `relocate`
    (elf.rs:1096-1140):

    - a DEFINED function symbol (`STT_FUNC`, `st_value ≠ 0`) inside
      `.text` is a bpf-to-bpf call: its key is `pcHash` of the target
      slot (`(st_value − text.sh_addr) / 8`; the name "entrypoint"
      keys by `entrypointHash` instead), and the pair
      `(key, targetSlot)` is registered;
    - anything else is a syscall reference: key = Murmur3 hash of the
      symbol NAME, no registry entry.

    agave rejects a defined function OUTSIDE `.text` at load
    (`ValueOutOfBounds`); this parser has no error channel, so such a
    symbol gets its PC-bytes key WITHOUT a registry entry — the call
    then decodes to `.call (.unknown _)` and fails closed at runtime
    instead of at load (same observable class, see audit H2). -/
def rel32KeyEntry (elfBytes : ByteArray)
    (symBase dynstrBase textVA textSize : Nat) (rel : RelocationEntry) :
    Nat × Option (Nat × Nat) :=
  let sym  := parseSymbolEntry elfBytes (symBase + rel.sym * 24)
  let name := readCString elfBytes (dynstrBase + sym.nameOff)
  if sym.info % 16 = 2 ∧ sym.value ≠ 0 then
    let targetSlot := (sym.value - textVA) / 8
    let key := if name.data = entrypointName.data then entrypointHash
               else pcHash targetSlot
    if textVA ≤ sym.value ∧ sym.value < textVA + textSize then
      (key, some (key, targetSlot))
    else
      (key, none)
  else
    (Murmur3.hash name 0, none)

/-- Apply a single `R_BPF_64_Relative` relocation that falls inside
    `.text`. The patch site `relOff` points at an `lddw` (a 16-byte
    instruction); we combine the existing split-imm halves into a
    64-bit address, and if that address is below `MM_REGION_SIZE`
    (i.e. the linker left it as a low-32 file-VA), we add
    `MM_REGION_SIZE` to relocate it into the program region. The new
    address is split back into the two imm halves at `+4` and `+12`.

    Lifted from `solana-sbpf::Executable::relocate`'s branch for
    `R_BPF_64_RELATIVE` in `.text`. The "outside .text" branch (which
    `applyDataRelocations` handles for `.data.rel.ro`) is unaffected.

    Without this patch, programs that store the loaded address, do
    arithmetic on it, or compare it against another pointer diverge
    from agave — agave sees the upper 32 bits set (program-region
    address); we'd see them zero (raw VA). For pure rodata-byte
    dereferences our total `Mem` happens to map the byte at the
    file-VA, so simple loads still work; the bug surfaces on
    pointer-arithmetic patterns. -/
def applyRelRelativeText (textBytes : ByteArray) (textVA : Nat)
    (relOff : Nat) : ByteArray :=
  let off := if relOff ≥ textVA then relOff - textVA else relOff
  let lo := readU32LE textBytes (off + 4)
  let hi := readU32LE textBytes (off + 12)
  let addr := lo + hi * 0x100000000
  let relocated :=
    if addr < Memory.MM_REGION_SIZE then addr + Memory.MM_REGION_SIZE else addr
  let newLo := relocated % 0x100000000
  let newHi := relocated / 0x100000000
  let acc' := writeU32LE textBytes (off + 4) newLo
  writeU32LE acc' (off + 12) newHi

/-- Apply `R_BPF_64_64`, `R_BPF_64_32`, and in-`.text` `R_BPF_64_Relative`
    relocations from the ELF to the loaded `.text`. Returns the original
    bytes unchanged if no symbol/relocation tables are present (fast
    path for hand-assembled fixtures).

    - `R_BPF_64_64`: patches a 64-bit symbol address into an `lddw`'s
      split immediate fields. Used for pointers into `.rodata` etc.
    - `R_BPF_64_32`: patches the function-registry key into a `call`
      instruction's 32-bit imm at `relOff + 4` (see `rel32KeyEntry`:
      syscalls key by NAME hash, bpf-to-bpf targets by PC-bytes hash,
      exactly as agave relocates). After patching, the imm IS the
      function key — the decoder routes it to `.call syscall` via the
      syscall table or to `.call_local` via the function registry
      (`buildFnRegistry`), and fails closed on an unknown key.
    - `R_BPF_64_Relative` in `.text`: bumps a sub-`MM_REGION_SIZE`
      address loaded by an `lddw` into the program region (see
      `applyRelRelativeText`). Relocs of this type outside `.text`
      are left for `applyDataRelocations`. -/
def applyRelocations (elfBytes : ByteArray) (h : Header)
    (textVA : Nat) (textBytes : ByteArray) : ByteArray :=
  -- Pass 1 (elf.rs:922-948): rewrite every PC-relative internal call's
  -- imm to its PC-bytes registry hash. agave's `relocate` always runs
  -- this scan, even when the ELF carries no relocation tables. The
  -- target list is computed over the ORIGINAL text (the rewrites only
  -- touch the scanned slot's own imm, so order is immaterial).
  let textFixed := (pcRelCallTargets textBytes).foldl (fun acc p =>
      writeU32LE acc (p.1 * 8 + 4) (pcHash p.2)) textBytes
  match findSectionByType elfBytes h SHT_DYNSYM,
        findSectionByType elfBytes h SHT_REL,
        findSection elfBytes h dynstrName with
  | some symtab, some reltab, some dynstr =>
    let nRels := reltab.size / 16
    let symBase := symtab.offset
    let dynstrBase := dynstr.offset
    let textEnd := textVA + textBytes.size
    (List.range nRels).foldl (fun acc i =>
      let rel := parseRelocationEntry elfBytes (reltab.offset + i * 16)
      if rel.type = R_BPF_64_64 then
        let sym := parseSymbolEntry elfBytes (symBase + rel.sym * 24)
        let symSec := parseSectionHeader elfBytes h sym.shndx
        let target := symSec.addr + sym.value
        applyRel64 acc textVA target rel.offset
      else if rel.type = R_BPF_64_32 then
        let (key, _) := rel32KeyEntry elfBytes symBase dynstrBase
                          textVA textBytes.size rel
        applyRel32 acc textVA key rel.offset
      else if rel.type = R_BPF_64_Relative
              ∧ rel.offset ≥ textVA
              ∧ rel.offset + 16 ≤ textEnd then
        applyRelRelativeText acc textVA rel.offset
      else
        acc) textFixed
  | _, _, _ => textFixed

/-- The function registry (key → target SLOT index) for V0 internal
    calls, mirroring what agave's loader builds (audit H2):

    - one entry per PC-relative internal call found by the pass-1 text
      scan (`pcRelCallTargets` over the RAW text — the SAME scan whose
      rewrites `applyRelocations` applies, so every rewritten key
      resolves), keyed by `pcHash` of the target slot;
    - one entry per `R_BPF_64_32` relocation against a defined function
      inside `.text` (`rel32KeyEntry`; again the same walk that patched
      the call imms); and
    - the entrypoint, keyed by `entrypointHash` and mapping to
      `(e_entry − text.sh_addr) / 8` (agave unregisters any
      symbol-derived "entrypoint" entry and re-registers it from
      `e_entry` — elf.rs:637-643; putting the e_entry pair FIRST gives
      it the same precedence under first-match lookup).

    Values are SLOT indices (`lddw` counts as 2);
    `Decode.decodeInsn` resolves them to logical PCs through the slot
    map. Duplicate pairs (a function called from several sites) are
    harmless under first-match lookup. agave's hash-collision
    rejection (`SymbolHashCollision`) is not modeled — a collision
    would need murmur3(LE8(slotA)) = murmur3(LE8(slotB)) (or a clash
    with a syscall name hash), and the first-match lookup then picks
    the first registration, which is a completeness (not soundness)
    gap. -/
def buildFnRegistry (elfBytes : ByteArray) (h : Header)
    (textVA : Nat) (rawText : ByteArray) : List (Nat × Nat) :=
  let entrySlot := (if h.entry ≥ textVA then h.entry - textVA else 0) / 8
  let entryPair := (entrypointHash, entrySlot)
  let pass1 := (pcRelCallTargets rawText).map (fun p => (pcHash p.2, p.2))
  let relocPairs :=
    match findSectionByType elfBytes h SHT_DYNSYM,
          findSectionByType elfBytes h SHT_REL,
          findSection elfBytes h dynstrName with
    | some symtab, some reltab, some dynstr =>
      let nRels := reltab.size / 16
      (List.range nRels).foldr (fun i acc =>
        let rel := parseRelocationEntry elfBytes (reltab.offset + i * 16)
        if rel.type = R_BPF_64_32 then
          match (rel32KeyEntry elfBytes symtab.offset dynstr.offset
                   textVA rawText.size rel).2 with
          | some p => p :: acc
          | none => acc
        else acc) []
    | _, _, _ => []
  entryPair :: pass1 ++ relocPairs

/-- Whether every symbol-using relocation can resolve its symbol — the
    fail-closed gate for audit M1. solana-sbpf 0.14.4 `relocate`
    (elf.rs:969-973) reads each `R_Bpf_64_64` / `R_Bpf_64_32`
    relocation's symbol as
    `dynamic_symbol_table().and_then(|t| t.get(r_sym)).ok_or(UnknownSymbol)?`,
    so a relocation table that references a missing `.dynsym` or an
    out-of-range symbol index fails the LOAD. The total `applyRelocations`
    instead 0-fills such reads (OOB → 0) and silently patches a wrong
    address; the runners (`runElf`/`runElfWithFuel`/CPI) call this first and
    fail closed when it is `false`.

    A binary with NO relocation table is trivially resolvable (agave's
    `dynamic_relocations_table().unwrap_or_default()` yields an empty
    iterator — a valid static binary). `R_Bpf_64_Relative` relocations do
    not use the symbol table, so they never make this `false`. -/
def relocationsResolvable (elfBytes : ByteArray) (h : Header) : Bool :=
  match findSectionByType elfBytes h SHT_REL with
  | none => true
  | some reltab =>
    let nRels  := reltab.size / 16
    let symtab? := findSectionByType elfBytes h SHT_DYNSYM
    let nSyms  := match symtab? with | some s => s.size / 24 | none => 0
    (List.range nRels).all fun i =>
      let rel := parseRelocationEntry elfBytes (reltab.offset + i * 16)
      if rel.type = R_BPF_64_64 ∨ rel.type = R_BPF_64_32 then
        symtab?.isSome && rel.sym < nSyms
      else
        true

/-- Apply `R_BPF_64_RELATIVE` relocations that fall inside a non-text
    section (typically `.data.rel.ro`). Each reloc names a byte offset
    inside the section where the linker has placed an 8-byte word
    laid out as `[0u32 ; target_u32]` — the actual address sits in
    the *upper* 32 bits. Without patching, a u64-LE read of that word
    returns `target << 32` (a huge bogus address); after patching, it
    returns `target` directly (a valid section-space address that
    our `Mem` resolves through the section mapping).

    Implementation mirrors the backwards-compat branch of
    `solana-sbpf`'s `Executable::relocate` for `R_Bpf_64_Relative`
    outside `.text`: read u32 at `r_offset + 4`, write u64 at
    `r_offset`. Modern toolchain output (cargo-build-sbf 3.1.x) goes
    through this branch for all `.data.rel.ro` relocs.

    `secBytes`  — the section's raw bytes (typically `.data.rel.ro`).
    `secVA`     — `sh_addr` of the section, used to convert
                  `rel.offset` (an ELF VA) to a byte offset into
                  `secBytes`.

    Relocs not falling inside `[secVA, secVA + secBytes.size)` are
    skipped. -/
def applyDataRelocations (elfBytes : ByteArray) (h : Header)
    (secVA : Nat) (secBytes : ByteArray) : ByteArray :=
  match findSectionByType elfBytes h SHT_REL with
  | some reltab =>
    let nRels := reltab.size / 16
    let secEnd := secVA + secBytes.size
    (List.range nRels).foldl (fun acc i =>
      let rel := parseRelocationEntry elfBytes (reltab.offset + i * 16)
      if rel.type = R_BPF_64_Relative
         ∧ rel.offset ≥ secVA ∧ rel.offset < secEnd then
        let secOff := rel.offset - secVA
        let target := readU32LE secBytes (secOff + 4)
        writeU64LE acc secOff (relocateSecAddr target)
      else acc) secBytes
  | none => secBytes

/-- Extract the `.text` section (the bytecode) from a Solana sBPF ELF.
    Returns `none` if the header is malformed or there is no `.text`. -/
def extractText (bytes : ByteArray) : Option ByteArray :=
  match parseHeader bytes with
  | none => none
  | some h =>
    match findSection bytes h textName with
    | none => none
    | some sec => some (extractSection bytes sec)

/-- Get the entry point offset from an ELF binary. -/
def entryOffset (bytes : ByteArray) : Option Nat :=
  (parseHeader bytes).map (·.entry)

end Elf
end SVM.SBPF
