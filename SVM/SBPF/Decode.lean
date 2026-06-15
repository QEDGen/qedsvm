/-
  sBPF bytecode decoder (pure parser) → our `Insn`.

  Encoding (per https://github.com/anza-xyz/sbpf):

      byte 0     : opcode (8 bits)
      byte 1     : src:dst register nibbles (src high, dst low)
      bytes 2-3  : signed 16-bit offset (little-endian) — PC-relative for jumps
      bytes 4-7  : signed 32-bit immediate (little-endian)

  `lddw` spans 16 bytes; the second slot's `imm` is the high 32 bits.

  Jump targets are PC-relative in 8-byte slot units, but `lddw` compresses
  two slots to one logical `Insn`, so resolution needs a byte-slot →
  logical-PC map: pass 1 (`buildSlotMap`) builds it, pass 2 decodes with
  resolved targets.
-/

import SVM.SBPF.Execute
import SVM.SBPF.SyscallHash

namespace SVM.SBPF
namespace Decode

/-! ## Byte-array readers (little-endian) -/

/-- Read one byte, 0 if out of bounds. -/
def readU8 (bytes : ByteArray) (off : Nat) : Nat :=
  if h : off < bytes.size then (bytes[off]'h).toNat else 0

/-- Read 2 bytes little-endian as unsigned. -/
def readU16LE (bytes : ByteArray) (off : Nat) : Nat :=
  readU8 bytes off + readU8 bytes (off + 1) * 0x100

/-- Read 4 bytes little-endian as unsigned. -/
def readU32LE (bytes : ByteArray) (off : Nat) : Nat :=
  readU8 bytes off
  + readU8 bytes (off + 1) * 0x100
  + readU8 bytes (off + 2) * 0x10000
  + readU8 bytes (off + 3) * 0x1000000

/-- Read 8 bytes little-endian as unsigned. -/
def readU64LE (bytes : ByteArray) (off : Nat) : Nat :=
  readU32LE bytes off + readU32LE bytes (off + 4) * 0x100000000

/-- Sign-extend a 16-bit unsigned value to `Int`. -/
def signExt16 (n : Nat) : Int :=
  if n < 0x8000 then (n : Int) else (n : Int) - 0x10000

/-- Sign-extend a 32-bit unsigned value to `Int`. -/
def signExt32 (n : Nat) : Int :=
  if n < 0x80000000 then (n : Int) else (n : Int) - 0x100000000

/-- Read 2 bytes little-endian as signed `Int`. -/
def readI16LE (bytes : ByteArray) (off : Nat) : Int :=
  signExt16 (readU16LE bytes off)

/-- Read 4 bytes little-endian as signed `Int`. -/
def readI32LE (bytes : ByteArray) (off : Nat) : Int :=
  signExt32 (readU32LE bytes off)

/-! ## Hex-string byte embedding — qedlift embeds a large `.text` as a hex
STRING (not a `#[..]` `ByteArray`): an array literal elaborates through
nested `List.cons`, blowing `maxRecDepth` around a few KB, while a string is
one token of any size. Decode pins evaluate this under `native_decide`. -/

/-- Decode a hex string into a `ByteArray`. Non-hex chars (whitespace) are
    skipped so callers may wrap freely; a dangling nibble is dropped.
    Corruption is caught downstream: the decode pins compare `decodeInsn`
    over these bytes against the expected instructions. -/
def bytesOfHex (s : String) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let mut hi : Option Nat := none
  for c in s.data do
    let v? : Option Nat :=
      if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
      else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
      else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
      else none
    match v?, hi with
    | some v, none   => hi := some v
    | some v, some h => out := out.push (UInt8.ofNat (h * 16 + v)); hi := none
    | none,   _      => pure ()
  return out

/-! ## Register decoding -/

/-- Map a 4-bit nibble to the corresponding `Reg`, or `none` for invalid values. -/
def decodeReg (n : Nat) : Option Reg :=
  match n with
  | 0  => some .r0  | 1 => some .r1  | 2 => some .r2  | 3 => some .r3
  | 4  => some .r4  | 5 => some .r5  | 6 => some .r6  | 7 => some .r7
  | 8  => some .r8  | 9 => some .r9  | 10 => some .r10
  | _  => none

/-! ## Pass 1: byte-slot → logical-PC map

`slotMap[i]` = logical PC of the instruction whose first byte is at `8*i`.
For `lddw`, both its slots map to the same logical PC. (Jumping into the
middle of an `lddw` is malformed; the map still yields *some* PC, but
execution re-runs the `lddw`. M4 fails such jumps closed in `decodeInsn`.) -/

def buildSlotMap (bytes : ByteArray) : Array Nat :=
  go 0 0 #[] (bytes.size + 1)
where
  go (off logicalPc : Nat) (acc : Array Nat) (fuel : Nat) : Array Nat :=
    match fuel with
    | 0 => acc
    | fuel' + 1 =>
      if off + 8 > bytes.size then acc
      else
        let opcode := readU8 bytes off
        if opcode = 0x18 then
          -- lddw: this slot and the next both belong to one logical instruction.
          go (off + 16) (logicalPc + 1)
            ((acc.push logicalPc).push logicalPc) fuel'
        else
          go (off + 8) (logicalPc + 1) (acc.push logicalPc) fuel'

/-! ## Pass 2: single-instruction decoding with resolved jump targets -/

/-- First-match lookup in the V0 function registry (key → target slot,
    `Elf.buildFnRegistry`). First match mirrors agave entrypoint precedence
    (e_entry registered first). -/
def fnRegLookup (fnReg : List (Nat × Nat)) (key : Nat) : Option Nat :=
  (fnReg.find? (fun p => p.1 = key)).map (·.2)

/-- Decode one sBPF instruction at byte offset `off`. `slotMap` translates
    PC-relative byte-slot branch offsets to logical PCs; `fnReg` is the V0
    function registry resolving internal `call` immediates (audit H2).
    Returns `(Insn, byte size)` (8, or 16 for `lddw`), or `none` if the
    opcode is unrecognized or register fields are invalid. -/
def decodeInsn (bytes : ByteArray) (slotMap : Array Nat) (off : Nat)
    (fnReg : List (Nat × Nat) := []) : Option (Insn × Nat) :=
  let opcode := readU8 bytes off
  let regs   := readU8 bytes (off + 1)
  let dstN   := regs &&& 0xF
  let srcN   := regs >>> 4
  let off16  := readI16LE bytes (off + 2)
  let imm    := readI32LE bytes (off + 4)
  let dst?   := decodeReg dstN
  let src?   := decodeReg srcN
  -- Resolve a PC-relative slot offset to a logical PC, `none` if out of
  -- code. Agave's verifier rejects out-of-code jumps at load
  -- (`JumpOutOfCode`); failing the decode reproduces that instead of
  -- silently retargeting to PC 0 (H3).
  let currentSlot : Int := (off / 8 : Int)
  let resolveTarget : Int → Option Nat := fun slotInt =>
    if slotInt < 0 then none
    else
      let n := slotInt.toNat
      if h : n < slotMap.size then
        let pc := slotMap[n]'h
        -- M4: a target on an `lddw`'s 2nd slot is `JumpToMiddleOfLddw`
        -- (agave rejection). Both `lddw` slots share one logical PC and
        -- every other insn has a fresh one, so a continuation slot is
        -- exactly `slotMap[n] = slotMap[n-1]`. Fail closed.
        if n > 0 ∧ slotMap[n - 1]? = some pc then none else some pc
      else none
  let targetPc? : Option Nat := resolveTarget (currentSlot + 1 + off16)
  -- M4: agave rejects any instruction WRITING the read-only r10
  -- (`CannotWriteR10`). Register-writing classes: LDX (low3=1), ALU32
  -- (low3=4), ALU64 (low3=7), `lddw` (0x18). Stores (low3=2/3) use dst as a
  -- memory BASE, not a write, so `stx [r10+off], rN` stays valid. Fail closed.
  let writesDstReg : Bool :=
    (opcode &&& 0x07) == 0x01 || (opcode &&& 0x07) == 0x04
      || (opcode &&& 0x07) == 0x07 || opcode == 0x18
  if writesDstReg && dstN == 10 then none else
  match opcode with
  -- ALU 64-bit immediate (class = 7, source = 0)
  | 0x07 => dst?.map fun d => (.add64 d (.imm imm), 8)
  | 0x17 => dst?.map fun d => (.sub64 d (.imm imm), 8)
  | 0x27 => dst?.map fun d => (.mul64 d (.imm imm), 8)
  | 0x37 => dst?.map fun d => (.div64 d (.imm imm), 8)
  | 0x47 => dst?.map fun d => (.or64  d (.imm imm), 8)
  | 0x57 => dst?.map fun d => (.and64 d (.imm imm), 8)
  -- M4: agave rejects an immediate shift ≥ register width
  -- (`ShiftWithOverflow`). Fail closed at decode. (Register-sourced shifts
  -- are runtime-masked by both, so only imm forms are gated.)
  | 0x67 => if imm < 0 ∨ imm ≥ 64 then none else dst?.map fun d => (.lsh64 d (.imm imm), 8)
  | 0x77 => if imm < 0 ∨ imm ≥ 64 then none else dst?.map fun d => (.rsh64 d (.imm imm), 8)
  | 0x87 => dst?.map fun d => (.neg64 d, 8)
  | 0x97 => dst?.map fun d => (.mod64 d (.imm imm), 8)
  | 0xa7 => dst?.map fun d => (.xor64 d (.imm imm), 8)
  | 0xb7 => dst?.map fun d => (.mov64 d (.imm imm), 8)
  | 0xc7 => if imm < 0 ∨ imm ≥ 64 then none else dst?.map fun d => (.arsh64 d (.imm imm), 8)
  -- ALU 64-bit register (class = 7, source = 1)
  | 0x0f => match dst?, src? with | some d, some s => some (.add64  d (.reg s), 8) | _, _ => none
  | 0x1f => match dst?, src? with | some d, some s => some (.sub64  d (.reg s), 8) | _, _ => none
  | 0x2f => match dst?, src? with | some d, some s => some (.mul64  d (.reg s), 8) | _, _ => none
  | 0x3f => match dst?, src? with | some d, some s => some (.div64  d (.reg s), 8) | _, _ => none
  | 0x4f => match dst?, src? with | some d, some s => some (.or64   d (.reg s), 8) | _, _ => none
  | 0x5f => match dst?, src? with | some d, some s => some (.and64  d (.reg s), 8) | _, _ => none
  | 0x6f => match dst?, src? with | some d, some s => some (.lsh64  d (.reg s), 8) | _, _ => none
  | 0x7f => match dst?, src? with | some d, some s => some (.rsh64  d (.reg s), 8) | _, _ => none
  | 0x9f => match dst?, src? with | some d, some s => some (.mod64  d (.reg s), 8) | _, _ => none
  | 0xaf => match dst?, src? with | some d, some s => some (.xor64  d (.reg s), 8) | _, _ => none
  | 0xbf => match dst?, src? with | some d, some s => some (.mov64  d (.reg s), 8) | _, _ => none
  | 0xcf => match dst?, src? with | some d, some s => some (.arsh64 d (.reg s), 8) | _, _ => none
  -- ALU 32-bit immediate (class = 4)
  | 0x04 => dst?.map fun d => (.add32 d (.imm imm), 8)
  | 0x14 => dst?.map fun d => (.sub32 d (.imm imm), 8)
  | 0x24 => dst?.map fun d => (.mul32 d (.imm imm), 8)
  | 0x34 => dst?.map fun d => (.div32 d (.imm imm), 8)
  | 0x44 => dst?.map fun d => (.or32  d (.imm imm), 8)
  | 0x54 => dst?.map fun d => (.and32 d (.imm imm), 8)
  | 0x64 => if imm < 0 ∨ imm ≥ 32 then none else dst?.map fun d => (.lsh32 d (.imm imm), 8)
  | 0x74 => if imm < 0 ∨ imm ≥ 32 then none else dst?.map fun d => (.rsh32 d (.imm imm), 8)
  | 0x84 => dst?.map fun d => (.neg32 d, 8)
  | 0x94 => dst?.map fun d => (.mod32 d (.imm imm), 8)
  | 0xa4 => dst?.map fun d => (.xor32 d (.imm imm), 8)
  | 0xb4 => dst?.map fun d => (.mov32 d (.imm imm), 8)
  | 0xc4 => if imm < 0 ∨ imm ≥ 32 then none else dst?.map fun d => (.arsh32 d (.imm imm), 8)
  -- ALU 32-bit register
  | 0x0c => match dst?, src? with | some d, some s => some (.add32  d (.reg s), 8) | _, _ => none
  | 0x1c => match dst?, src? with | some d, some s => some (.sub32  d (.reg s), 8) | _, _ => none
  | 0x2c => match dst?, src? with | some d, some s => some (.mul32  d (.reg s), 8) | _, _ => none
  | 0x3c => match dst?, src? with | some d, some s => some (.div32  d (.reg s), 8) | _, _ => none
  | 0x4c => match dst?, src? with | some d, some s => some (.or32   d (.reg s), 8) | _, _ => none
  | 0x5c => match dst?, src? with | some d, some s => some (.and32  d (.reg s), 8) | _, _ => none
  | 0x6c => match dst?, src? with | some d, some s => some (.lsh32  d (.reg s), 8) | _, _ => none
  | 0x7c => match dst?, src? with | some d, some s => some (.rsh32  d (.reg s), 8) | _, _ => none
  | 0x9c => match dst?, src? with | some d, some s => some (.mod32  d (.reg s), 8) | _, _ => none
  | 0xac => match dst?, src? with | some d, some s => some (.xor32  d (.reg s), 8) | _, _ => none
  | 0xbc => match dst?, src? with | some d, some s => some (.mov32  d (.reg s), 8) | _, _ => none
  | 0xcc => match dst?, src? with | some d, some s => some (.arsh32 d (.reg s), 8) | _, _ => none
  -- Jumps (class = 5, immediate source). An out-of-code target makes the
  -- whole decode fail (`targetPc? = none`); see resolveTarget above.
  | 0x05 => targetPc?.map fun t => (.ja t, 8)
  | 0x15 => dst?.bind fun d => targetPc?.map fun t => (.jeq  d (.imm imm) t, 8)
  | 0x25 => dst?.bind fun d => targetPc?.map fun t => (.jgt  d (.imm imm) t, 8)
  | 0x35 => dst?.bind fun d => targetPc?.map fun t => (.jge  d (.imm imm) t, 8)
  | 0x45 => dst?.bind fun d => targetPc?.map fun t => (.jset d (.imm imm) t, 8)
  | 0x55 => dst?.bind fun d => targetPc?.map fun t => (.jne  d (.imm imm) t, 8)
  | 0x65 => dst?.bind fun d => targetPc?.map fun t => (.jsgt d (.imm imm) t, 8)
  | 0x75 => dst?.bind fun d => targetPc?.map fun t => (.jsge d (.imm imm) t, 8)
  | 0xa5 => dst?.bind fun d => targetPc?.map fun t => (.jlt  d (.imm imm) t, 8)
  | 0xb5 => dst?.bind fun d => targetPc?.map fun t => (.jle  d (.imm imm) t, 8)
  | 0xc5 => dst?.bind fun d => targetPc?.map fun t => (.jslt d (.imm imm) t, 8)
  | 0xd5 => dst?.bind fun d => targetPc?.map fun t => (.jsle d (.imm imm) t, 8)
  -- Jumps (register source)
  | 0x1d => dst?.bind fun d => src?.bind fun s => targetPc?.map fun t => (.jeq  d (.reg s) t, 8)
  | 0x2d => dst?.bind fun d => src?.bind fun s => targetPc?.map fun t => (.jgt  d (.reg s) t, 8)
  | 0x3d => dst?.bind fun d => src?.bind fun s => targetPc?.map fun t => (.jge  d (.reg s) t, 8)
  | 0x4d => dst?.bind fun d => src?.bind fun s => targetPc?.map fun t => (.jset d (.reg s) t, 8)
  | 0x5d => dst?.bind fun d => src?.bind fun s => targetPc?.map fun t => (.jne  d (.reg s) t, 8)
  | 0x6d => dst?.bind fun d => src?.bind fun s => targetPc?.map fun t => (.jsgt d (.reg s) t, 8)
  | 0x7d => dst?.bind fun d => src?.bind fun s => targetPc?.map fun t => (.jsge d (.reg s) t, 8)
  | 0xad => dst?.bind fun d => src?.bind fun s => targetPc?.map fun t => (.jlt  d (.reg s) t, 8)
  | 0xbd => dst?.bind fun d => src?.bind fun s => targetPc?.map fun t => (.jle  d (.reg s) t, 8)
  | 0xcd => dst?.bind fun d => src?.bind fun s => targetPc?.map fun t => (.jslt d (.reg s) t, 8)
  | 0xdd => dst?.bind fun d => src?.bind fun s => targetPc?.map fun t => (.jsle d (.reg s) t, 8)
  -- Call (0x85). After R_BPF_64_32 relocation (`Elf.applyRelocations`) the
  -- imm is either a syscall's Murmur3 name hash or an internal function's
  -- Murmur3 PC-bytes hash (registered by `Elf.buildFnRegistry`). Resolution
  -- mirrors agave V0 (interpreter.rs CALL_IMM): syscall table
  -- (`SyscallHash.fromHash`) first, then the function registry, else fail
  -- closed. `src` is NOT used to disambiguate in V0.
  | 0x85 =>
    let immU := readU32LE bytes (off + 4)
    match SyscallHash.fromHash immU with
    | .unknown _ =>
      -- V0 internal call (H2, closed): a registered key resolves slot →
      -- logical PC; a registered slot past the program is malformed input
      -- (the loader guarantees in-text targets) so the decode fails; an
      -- UNKNOWN key → `.call (.unknown immU)`, executing fail-closed
      -- (`Misc.execUnknown` = agave's `UnsupportedInstruction`). The pre-H2
      -- slot-offset interpretation with its PC-0 fallback is gone.
      match fnRegLookup fnReg immU with
      | some targetSlot =>
        if h : targetSlot < slotMap.size then
          some (.call_local (slotMap[targetSlot]'h), 8)
        else none
      | none => some (.call (.unknown immU), 8)
    | sc => some (.call sc, 8)
  -- Indirect call `callx <reg>`: target = runtime src-register value.
  | 0x8d => src?.map fun s => (.callx s, 8)
  -- Exit
  | 0x95 => some (.exit, 8)
  -- Load/store (memory operations)
  | 0x71 => match dst?, src? with | some d, some s => some (.ldx .byte  d s off16, 8) | _, _ => none
  | 0x69 => match dst?, src? with | some d, some s => some (.ldx .half  d s off16, 8) | _, _ => none
  | 0x61 => match dst?, src? with | some d, some s => some (.ldx .word  d s off16, 8) | _, _ => none
  | 0x79 => match dst?, src? with | some d, some s => some (.ldx .dword d s off16, 8) | _, _ => none
  | 0x72 => dst?.map fun d => (.st .byte  d off16 imm, 8)
  | 0x6a => dst?.map fun d => (.st .half  d off16 imm, 8)
  | 0x62 => dst?.map fun d => (.st .word  d off16 imm, 8)
  | 0x7a => dst?.map fun d => (.st .dword d off16 imm, 8)
  | 0x73 => match dst?, src? with | some d, some s => some (.stx .byte  d off16 s, 8) | _, _ => none
  | 0x6b => match dst?, src? with | some d, some s => some (.stx .half  d off16 s, 8) | _, _ => none
  | 0x63 => match dst?, src? with | some d, some s => some (.stx .word  d off16 s, 8) | _, _ => none
  | 0x7b => match dst?, src? with | some d, some s => some (.stx .dword d off16 s, 8) | _, _ => none
  -- lddw — 16-byte: low 32 bits in this slot's imm, high 32 in the next.
  | 0x18 =>
    -- lddw needs 16 bytes; a truncated one at end-of-text is malformed
    -- (agave rejects the incomplete instruction).
    if off + 16 > bytes.size then none
    else
      let immLoNat := readU32LE bytes (off + 4)
      let immHiNat := readU32LE bytes (off + 12)
      let combined : Int := (immHiNat * 0x100000000 + immLoNat : Nat)
      dst?.map fun d => (.lddw d combined, 16)
  | _ => none

/-! ## Program decoding (two-pass) -/

/-- Decode flat sBPF bytecode into a logical `Insn` sequence (`lddw` = one
    entry, jump targets resolved to logical PCs, internal `call` immediates
    resolved through the V0 registry `fnReg`; pass `[]` for raw text, where
    every internal call decodes to fail-closed `.call (.unknown _)`).
    `none` if any instruction fails to decode. -/
def decodeProgram (bytes : ByteArray) (fnReg : List (Nat × Nat) := []) :
    Option (Array Insn) :=
  let slotMap := buildSlotMap bytes
  go 0 #[] (bytes.size + 1) slotMap
where
  go (off : Nat) (acc : Array Insn) (fuel : Nat) (slotMap : Array Nat) :
      Option (Array Insn) :=
    match fuel with
    | 0 => some acc
    | fuel' + 1 =>
      if off ≥ bytes.size then some acc
      else if off + 8 > bytes.size then
        -- Trailing partial slot (text length not a multiple of 8): agave
        -- rejects at load (`ProgramLengthNotMultiple`) — M4.
        none
      else
        match decodeInsn bytes slotMap off fnReg with
        | none => none
        | some (insn, sz) => go (off + sz) (acc.push insn) fuel' slotMap

end Decode
end SVM.SBPF
