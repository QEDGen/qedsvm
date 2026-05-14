/-
  Minimal ELF64 loader for Solana sBPF binaries.

  Solana programs ship as 64-bit little-endian ELF binaries with the
  bytecode in a `.text` section. This module parses:

  - the ELF64 file header (validating magic, class=64-bit, endian=LE),
  - the section header table,
  - the section name string table (`.shstrtab`),

  and exposes `extractText` to pull out the `.text` section's bytes
  ready to feed into `Decode.decodeProgram` / `Runner.run`.

  Limitations:
  - We extract the raw `.text` section bytes only. Programs that rely on
    `.rodata` being mapped into memory (the usual case for table-driven
    Anchor code) will not yet behave correctly — that's a follow-up
    (need to map `.rodata` into `Mem` starting at the appropriate VA).
  - Relocations: we support the most common Solana sBPF relocation,
    `R_BPF_64_64`, which patches the immediate of an `lddw` instruction
    to point at a symbol's runtime address (typically a constant in
    `.rodata`). This is what `rustc` / Anchor / Pinocchio emit for any
    static reference. Other relocation types (`R_BPF_64_32` for inter-
    function `call` offsets, `R_BPF_64_Relative` for sBPF v3) are not
    yet processed; programs that rely on them will mis-execute.
-/

import Svm.SBPF.Decode
import Svm.SBPF.Murmur3

namespace Svm.SBPF
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
    magic is wrong, the class is not 64-bit, or the endianness is not LE. -/
def parseHeader (bytes : ByteArray) : Option Header :=
  if bytes.size < 64 then none
  else if readU8 bytes 0 ≠ 0x7f then none  -- magic
  else if readU8 bytes 1 ≠ 0x45 then none  -- 'E'
  else if readU8 bytes 2 ≠ 0x4c then none  -- 'L'
  else if readU8 bytes 3 ≠ 0x46 then none  -- 'F'
  else if readU8 bytes 4 ≠ 2 then none     -- ei_class = ELFCLASS64
  else if readU8 bytes 5 ≠ 1 then none     -- ei_data = ELFDATA2LSB
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
    of an `lddw rN, IMM` (a 16-byte instruction). -/
def applyRel64 (textBytes : ByteArray) (textVA target : Nat) (relOff : Nat) :
    ByteArray :=
  let off := if relOff ≥ textVA then relOff - textVA else relOff
  let addend := readU32LE textBytes (off + 4)
  let final  := (target + addend) % 0x10000000000000000  -- u64
  let lo := final % 0x100000000
  let hi := final / 0x100000000
  let b1 := writeU32LE textBytes (off + 4) lo
  writeU32LE b1 (off + 12) hi

/-- Apply a single `R_BPF_64_32` relocation. The patch site `relOff`
    points at the *start* of the 8-byte instruction (typically `0x85`);
    the imm to overwrite is at `relOff + 4`. The patched value is the
    Murmur3-32 hash of the symbol name (Solana's convention for
    resolving syscall and internal-function references). -/
def applyRel32 (textBytes : ByteArray) (textVA hash : Nat) (relOff : Nat) :
    ByteArray :=
  let off := if relOff ≥ textVA then relOff - textVA else relOff
  writeU32LE textBytes (off + 4) hash

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

/-- Apply `R_BPF_64_64` and `R_BPF_64_32` relocations from the ELF to
    the loaded `.text`. Returns the original bytes unchanged if no
    symbol/relocation tables are present (fast path for
    hand-assembled fixtures).

    - `R_BPF_64_64`: patches a 64-bit symbol address into an `lddw`'s
      split immediate fields. Used for pointers into `.rodata` etc.
    - `R_BPF_64_32`: patches the Murmur3-32 hash of the symbol name
      into a `call`/`call_local` instruction's 32-bit imm at
      `relOff + 4`. After patching, the imm IS the function key —
      either a syscall hash (decoder routes to `.call syscall`) or
      an internal-function hash (decoder falls back to
      `.call_local`). -/
def applyRelocations (elfBytes : ByteArray) (h : Header)
    (textVA : Nat) (textBytes : ByteArray) : ByteArray :=
  match findSectionByType elfBytes h SHT_DYNSYM,
        findSectionByType elfBytes h SHT_REL,
        findSection elfBytes h dynstrName with
  | some symtab, some reltab, some dynstr =>
    let nRels := reltab.size / 16
    let symBase := symtab.offset
    let dynstrBase := dynstr.offset
    (List.range nRels).foldl (fun acc i =>
      let rel := parseRelocationEntry elfBytes (reltab.offset + i * 16)
      if rel.type = R_BPF_64_64 then
        let sym := parseSymbolEntry elfBytes (symBase + rel.sym * 24)
        let symSec := parseSectionHeader elfBytes h sym.shndx
        let target := symSec.addr + sym.value
        applyRel64 acc textVA target rel.offset
      else if rel.type = R_BPF_64_32 then
        let sym := parseSymbolEntry elfBytes (symBase + rel.sym * 24)
        let name := readCString elfBytes (dynstrBase + sym.nameOff)
        let hash := Murmur3.hash name 0
        applyRel32 acc textVA hash rel.offset
      else
        acc) textBytes
  | _, _, _ => textBytes

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
        writeU64LE acc secOff target
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
end Svm.SBPF
