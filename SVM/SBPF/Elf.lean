/-
  Minimal ELF64 loader for Solana sBPF binaries.

  Parses the ELF64 header, section header table, and `.shstrtab`; exposes
  `extractText` to feed `.text` into `Decode.decodeProgram` / `Runner.run`.

  Coverage:
  - `.text` extracted via `extractText`. `.rodata` / `.data.rel.ro` are mapped
    into `Mem` at their VAs by the runner.
  - Relocations (`applyRelocations`): `R_BPF_64_64` (lddw imm → symbol address),
    `R_BPF_64_RELATIVE` (in-`.text` + `.data.rel.ro` forms), `R_BPF_64_32`
    (inter-function `call` → murmur3 hash).

  V0 internal-call resolution (audit H2, closed): `R_BPF_64_32` against a
  defined function patches the murmur3 hash of the target PC bytes
  (`register_function_hashed_legacy`) into the function registry
  (`buildFnRegistry`), which `Decode.decodeInsn` consults for `.call_local`.
  An unresolved key decodes to `.call (.unknown _)` and fails closed at runtime
  (agave: `UnsupportedInstruction`).

  Remaining agave divergences tracked in docs/SOUNDNESS_AUDIT_*.md (M1).
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
  /-- Virtual address the section loads at (for `.rodata`, where program
      `lddw`/`ldx` read from). -/
  addr    : Nat
  /-- File offset of the section's contents. -/
  offset  : Nat
  /-- Section size in bytes. -/
  size    : Nat

/-! ## Header parsing -/

/-- Parse the ELF64 header; `none` on too-short/bad-magic/non-64-bit/non-LE/
    non-BPF/non-V0.

    The `e_machine` and `e_flags` gates (C3) fail closed at load: this model
    only faithfully implements V0 semantics, so a non-V0 or non-BPF binary is
    rejected rather than silently mis-executed as V0. See SOUNDNESS_AUDIT (C3). -/
def parseHeader (bytes : ByteArray) : Option Header :=
  if bytes.size < 64 then none
  else if readU8 bytes 0 ≠ 0x7f then none  -- magic
  else if readU8 bytes 1 ≠ 0x45 then none  -- 'E'
  else if readU8 bytes 2 ≠ 0x4c then none  -- 'L'
  else if readU8 bytes 3 ≠ 0x46 then none  -- 'F'
  else if readU8 bytes 4 ≠ 2 then none     -- ei_class = ELFCLASS64
  else if readU8 bytes 5 ≠ 1 then none     -- ei_data = ELFDATA2LSB
  -- ei_osabi (7): agave rejects ≠ ELFOSABI_NONE (`WrongAbi`, elf.rs:721). M1.
  else if readU8 bytes 7 ≠ 0 then none
  -- e_type (16): agave rejects ≠ ET_DYN=3 (`WrongType`, elf.rs:727) — sBPF
  -- programs are shared objects. M1.
  else if readU16LE bytes 16 ≠ 3 then none
  -- e_machine (offset 18): EM_BPF = 247 or EM_SBPF = 263.
  else if readU16LE bytes 18 ≠ 247 ∧ readU16LE bytes 18 ≠ 263 then none
  -- e_flags (offset 48): SBPF version. Only V0 (0) is modeled.
  else if readU32LE bytes 48 ≠ 0 then none
  -- M1: section-table structural validation — fail closed rather than read
  -- past the file via zero-fill. `e_shstrndx` must index a real section and
  -- the section table lie within the file. NOTE also rejects `SHN_XINDEX`
  -- (`e_shstrndx = 0xFFFF`): `shnum` is u16 so `0xFFFF ≥ shnum` always —
  -- extended section numbering deliberately not modeled. SOUNDNESS_AUDIT (M1).
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

/-- `.data.rel.ro` — read-only-after-relocation data (enum jump tables,
    `&'static` rodata refs, vtables). Each pointer field carries an
    `R_BPF_64_RELATIVE` whose word is `00 00 00 00 <u32 target>` (address in
    the upper 32 bits); the loader repacks it into the low 32 bits. Enum-
    dispatch programs (SPL Token, Anchor) crash without this. -/
def dataRelRoName : ByteArray :=
  ⟨#[0x2e, 0x64, 0x61, 0x74, 0x61, 0x2e, 0x72, 0x65, 0x6c, 0x2e, 0x72, 0x6f]⟩  -- ".data.rel.ro"

/-- `.dynstr` section name — dynamic-symbol strings (resolves syscall names
    referenced by `R_BPF_64_32` relocations). -/
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

/-- Bump a section-VA into the program region if below `MM_REGION_SIZE`,
    mirroring agave's loader: a sub-`MM_REGION_SIZE` `sh_addr` (typical
    `cargo-build-sbf`, e.g. `.rodata` at `0x1bf60`) shifts to
    `MM_PROGRAM_START + sh_addr`; already-high addresses (hand-assembled
    fixtures) are left alone. Use everywhere a section is mapped or a
    relocation target computed, so lddw imms and loaded bytes coincide. -/
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

/-- Apply one `R_BPF_64_64` to loaded `.text`: split a 64-bit symbol address
    into the two imm fields of an `lddw` (16-byte insn), bumping into the
    program region via `relocateSecAddr`. -/
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

/-- Apply one `R_BPF_64_32`: `relOff` is the insn start (typically `0x85`),
    the imm to overwrite at `relOff + 4`. Patched value = the function-registry
    key from `rel32KeyEntry` (syscall name hash or bpf-to-bpf PC-bytes hash). -/
def applyRel32 (textBytes : ByteArray) (textVA hash : Nat) (relOff : Nat) :
    ByteArray :=
  let off := if relOff ≥ textVA then relOff - textVA else relOff
  writeU32LE textBytes (off + 4) hash

/-- A u64 as 8 LE bytes — what agave hashes to key a bpf-to-bpf call target. -/
def le8 (n : Nat) : ByteArray :=
  ⟨#[UInt8.ofNat (n % 256),
     UInt8.ofNat (n / 0x100 % 256),
     UInt8.ofNat (n / 0x10000 % 256),
     UInt8.ofNat (n / 0x1000000 % 256),
     UInt8.ofNat (n / 0x100000000 % 256),
     UInt8.ofNat (n / 0x10000000000 % 256),
     UInt8.ofNat (n / 0x1000000000000 % 256),
     UInt8.ofNat (n / 0x100000000000000 % 256)]⟩

/-- agave's legacy registry key for a bpf-to-bpf target: Murmur3-32 (seed 0)
    of the target slot as 8 LE bytes (`register_function_hashed_legacy`,
    program.rs:154-159, V0 path). "entrypoint" is the exception — keyed by the
    NAME hash (`entrypointHash`). -/
def pcHash (targetSlot : Nat) : Nat :=
  Murmur3.hash (le8 targetSlot) 0

/-- Entrypoint registry key: agave hashes the literal name "entrypoint", not
    its PC bytes (program.rs:155-156, elf.rs:637-643). -/
def entrypointHash : Nat := Murmur3.hashString "entrypoint"

/-- The UTF-8 bytes of "entrypoint", for symbol-name comparison. -/
def entrypointName : ByteArray := "entrypoint".toUTF8

/-- Read a null-terminated string at `off` (resolves `.dynstr` symbol names).
    Capped at 128 bytes for termination on runaway inputs. -/
def readCString (bytes : ByteArray) (off : Nat) : ByteArray :=
  go 0 128 #[]
where
  go (i fuel : Nat) (acc : Array UInt8) : ByteArray :=
    match fuel with
    | 0 => ⟨acc⟩
    | fuel' + 1 =>
      let b := readU8 bytes (off + i)
      if b = 0 then ⟨acc⟩ else go (i + 1) fuel' (acc.push b.toUInt8)

/-- PC-relative internal calls from scanning RAW text, mirroring pass 1 of
    solana-sbpf `relocate` (elf.rs:922-948): every slot with opcode `CALL_IMM`
    (0x85) and `imm ≠ -1` is a call to `slot + 1 + imm`; agave registers it
    under its PC-bytes hash and rewrites the imm. (Calls via `R_BPF_64_32` carry
    imm = -1 on disk and are skipped — the reloc pass handles them.) Returns
    `(slotIdx, targetSlot)`.

    agave fails the LOAD on an OOB target (`RelativeJumpOutOfBounds`); lacking
    an error channel, such a call keeps its raw imm, decodes to
    `.call (.unknown _)`, and fails closed at runtime (audit H2). NOTE scan is
    over SLOTS like agave's: an `lddw`'s second slot has opcode 0, never 0x85,
    so this cannot misfire. -/
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

/-- Patched imm key + optional registry entry for one `R_BPF_64_32`, mirroring
    solana-sbpf `relocate` (elf.rs:1096-1140):

    - DEFINED function (`STT_FUNC`, `st_value ≠ 0`) inside `.text` = bpf-to-bpf
      call: key = `pcHash` of the target slot (`(st_value − text.sh_addr) / 8`;
      "entrypoint" keys by `entrypointHash`), pair `(key, targetSlot)`
      registered;
    - else a syscall reference: key = Murmur3 of the symbol NAME, no entry.

    agave rejects a defined function OUTSIDE `.text` at load
    (`ValueOutOfBounds`); lacking an error channel, such a symbol gets its
    key WITHOUT a registry entry → `.call (.unknown _)`, fail-closed at runtime
    (same observable class, audit H2). -/
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

/-- Apply one in-`.text` `R_BPF_64_Relative`: `relOff` points at an `lddw`;
    combine its split-imm halves into a 64-bit address, bump sub-`MM_REGION_SIZE`
    ones into the program region, split back into `+4`/`+12`. Mirrors
    `solana-sbpf::Executable::relocate`'s in-`.text` branch (the outside-`.text`
    branch is `applyDataRelocations`).

    Without it, programs that store/arith/compare the loaded address diverge:
    agave sees the upper 32 bits set, we'd see them zero. Pure rodata-byte
    loads still work (our total `Mem` maps the file-VA byte); the bug surfaces
    on pointer-arithmetic patterns. -/
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

/-- Apply `R_BPF_64_64`, `R_BPF_64_32`, and in-`.text` `R_BPF_64_Relative` to
    loaded `.text`. Bytes unchanged if no symbol/relocation tables (fast path
    for hand-assembled fixtures).

    - `R_BPF_64_64`: 64-bit symbol address → `lddw` split imm (rodata pointers).
    - `R_BPF_64_32`: function-registry key → `call` imm at `relOff + 4` (see
      `rel32KeyEntry`); the decoder routes the key to `.call syscall` or
      `.call_local` (`buildFnRegistry`), failing closed on an unknown key.
    - in-`.text` `R_BPF_64_Relative`: bumps a sub-`MM_REGION_SIZE` lddw address
      into the program region; outside-`.text` ones go to
      `applyDataRelocations`. -/
def applyRelocations (elfBytes : ByteArray) (h : Header)
    (textVA : Nat) (textBytes : ByteArray) : ByteArray :=
  -- Pass 1 (elf.rs:922-948): rewrite every PC-relative call's imm to its
  -- PC-bytes registry hash; agave always runs this, even with no reloc tables.
  -- Targets are computed over the ORIGINAL text (rewrites touch only the
  -- scanned slot's own imm, so order is immaterial).
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

/-- Function registry (key → target SLOT) for V0 internal calls, mirroring
    agave's loader (audit H2):

    - one entry per pass-1 PC-relative call (`pcRelCallTargets` over RAW text,
      the SAME scan `applyRelocations` rewrites, so keys resolve), keyed by
      `pcHash`;
    - one per `R_BPF_64_32` against a defined in-`.text` function
      (`rel32KeyEntry`, same walk);
    - the entrypoint, keyed by `entrypointHash` → `(e_entry − text.sh_addr) / 8`
      (agave re-registers it from `e_entry`, elf.rs:637-643; placing it FIRST
      gives the same precedence under first-match lookup).

    Values are SLOT indices (`lddw` counts as 2); `Decode.decodeInsn` maps them
    to PCs. Duplicate pairs are harmless under first-match. agave's
    `SymbolHashCollision` rejection is not modeled — a collision needs a murmur3
    clash, and first-match then picks the first registration (a completeness,
    not soundness, gap). -/
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

/-- Function registry free of key collisions — agave's `SymbolHashCollision`
    load rejection (audit H2 residual). `register_function_hashed_legacy` errors
    when a key re-registers with a DIFFERENT slot; same-pair re-registration is
    normal (every call site registers the same pair). `entrypointHash` is exempt
    (agave re-registers it from `e_entry`, elf.rs:637-643; first-match precedence
    resolves the mismatch).

    A real collision needs a murmur3 clash — astronomically unlikely for honest
    binaries, so this is pure fail-closed hardening. Checked by the runners next
    to `relocationsResolvable`. -/
def registryCollisionFree (reg : List (Nat × Nat)) : Bool :=
  match reg with
  | [] => true
  | (k, v) :: rest =>
    (k == entrypointHash || rest.all fun p => p.1 != k || p.2 == v)
      && registryCollisionFree rest

/-- Every symbol-using relocation can resolve its symbol — fail-closed gate for
    audit M1. solana-sbpf `relocate` (elf.rs:969-973) reads each
    `R_Bpf_64_64`/`R_Bpf_64_32` symbol via `...ok_or(UnknownSymbol)?`, so a
    missing `.dynsym` or OOB symbol index fails the LOAD; our total
    `applyRelocations` instead 0-fills (OOB → 0) and patches a wrong address, so
    the runners call this first and fail closed on `false`.

    No relocation table → trivially resolvable (valid static binary).
    `R_Bpf_64_Relative` doesn't use the symbol table, so never makes this
    `false`. -/
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

/-- Apply outside-`.text` `R_BPF_64_RELATIVE` (typically `.data.rel.ro`). Each
    reloc names an 8-byte word laid out `[0u32 ; target_u32]` (address in the
    *upper* 32 bits); unpatched, a u64-LE read returns `target << 32`, patched it
    returns `target` (a valid section-space address). Mirrors the backwards-compat
    `Executable::relocate` branch (read u32 at `r_offset + 4`, write u64 at
    `r_offset`); modern cargo-build-sbf uses this for all `.data.rel.ro` relocs.

    `secVA` = `sh_addr`, converts `rel.offset` (ELF VA) to a byte offset; relocs
    outside `[secVA, secVA + secBytes.size)` are skipped. -/
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

/-- Extract the `.text` section (bytecode); `none` on malformed header or no
    `.text`. -/
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
