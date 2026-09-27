"""Build `sbpfv3_isa_matrix.so`: one straight-line V3 path over every
non-call sBPF V3 instruction form (solana-sbpf 0.14.4 verifier inventory).

Account 0's data (at input + 96) holds the operands; results are stored back
into the same data so the Mollusk differential compares every effect:

    +96  a  (u64) = 100      +104 b (u64) = 200     +112 c (u32) = 50
    +116 d  (u16) = 1        +118 e (u8)  = 7
    +128.. results (see the store comments below)

Every conditional jump uses offset 0, so both outcomes reach the next
instruction and the path is the fall-through trace 0..N. Operands are chosen
so that every "not taken" condition holds at once (a=100, b=200, c=50, d=1),
which keeps the lifted theorem's path hypotheses jointly satisfiable.
"""

from pathlib import Path
import struct


def insn(op, dst=0, src=0, off=0, imm=0):
    return struct.pack("<BBhi", op, (src << 4) | dst, off, imm)


def lddw(dst, value):
    lo, hi = value & 0xFFFFFFFF, (value >> 32) & 0xFFFFFFFF
    return struct.pack("<BBhI", 0x18, dst, 0, lo) + struct.pack("<BBhI", 0, 0, 0, hi)


R0, R1, R2, R3, R4, R5, R6, R7, R8, R9 = range(10)
code = []
emit = code.append

emit(insn(0xBF, R9, R1))                      # mov64 r9, r1 (input base)
emit(insn(0x79, R2, R9, 96))                  # ldxdw r2, a
emit(insn(0x79, R3, R9, 104))                 # ldxdw r3, b
emit(insn(0x61, R4, R9, 112))                 # ldxw  r4, c
emit(insn(0x69, R5, R9, 116))                 # ldxh  r5, d
emit(insn(0x71, R6, R9, 118))                 # ldxb  r6, e

# ALU64 immediate forms on r7, stored at +128.
emit(insn(0xB7, R7, imm=9))                   # mov64 r7, 9
emit(insn(0xBF, R7, R2))                      # mov64 r7, r2
for op, imm in [(0x07, 5), (0x17, 3), (0x27, 7), (0x37, 3), (0x97, 1000),
                (0x47, 0x10), (0x57, 0xFF), (0xA7, 0x55), (0x67, 3),
                (0x77, 1), (0xC7, 2)]:
    emit(insn(op, R7, imm=imm))
emit(insn(0x87, R7))                          # neg64 r7
emit(insn(0x7B, R9, R7, 128))                 # stxdw [r9+128], r7

# ALU64 register forms on r8 (operand b = r3), stored at +136.
emit(insn(0xBF, R8, R2))
for op in [0x0F, 0x1F, 0x2F, 0x3F, 0x9F, 0x4F, 0x5F, 0xAF, 0x6F, 0x7F, 0xCF]:
    emit(insn(op, R8, R3))
emit(insn(0x7B, R9, R8, 136))

# ALU32 immediate forms on r7, stored at +144.
emit(insn(0xB4, R7, imm=0x1234))              # mov32 r7, imm
emit(insn(0xBC, R7, R2))                      # mov32 r7, r2
for op, imm in [(0x04, 5), (0x14, 3), (0x24, 7), (0x34, 3), (0x94, 1000),
                (0x44, 0x10), (0x54, 0xFF), (0xA4, 0x55), (0x64, 3),
                (0x74, 1), (0xC4, 2)]:
    emit(insn(op, R7, imm=imm))
emit(insn(0x84, R7))                          # neg32 r7
emit(insn(0x7B, R9, R7, 144))

# ALU32 register forms on r8 (operand b = r3), stored at +152.
emit(insn(0xBF, R8, R2))
for op in [0x0C, 0x1C, 0x2C, 0x3C, 0x9C, 0x4C, 0x5C, 0xAC, 0x6C, 0x7C, 0xCC]:
    emit(insn(op, R8, R3))
emit(insn(0x7B, R9, R8, 152))

# Endian conversions on r7, stored at +160.
emit(insn(0xBF, R7, R2))
for op in (0xDC, 0xD4):
    for width in (64, 32, 16):
        emit(insn(op, R7, imm=width))
emit(insn(0x7B, R9, R7, 160))

# lddw, stored at +168.
emit(lddw(R7, 0x1122334455667788))
emit(insn(0x7B, R9, R7, 168))

# Immediate stores (+176..+191) and register stores (+192..+199).
emit(insn(0x72, R9, off=176, imm=0x11))
emit(insn(0x6A, R9, off=178, imm=0x2233))
emit(insn(0x62, R9, off=180, imm=0x44556677))
emit(insn(0x7A, R9, off=184, imm=-1))
emit(insn(0x73, R9, R2, 192))
emit(insn(0x6B, R9, R2, 194))
emit(insn(0x63, R9, R2, 196))

# Conditional jumps, offset 0, every condition not taken for a=100, b=200,
# c=50, d=1: imm forms compare a with an immediate, reg forms pick register
# pairs whose "not taken" relations are simultaneously true. `jne` compares a
# with its copy in r0 (a self-comparison would own r2 twice in the spec).
emit(insn(0xBF, R0, R2))                      # mov64 r0, r2
IMM = {0x15: 1, 0x25: 200, 0x35: 200, 0xA5: 50, 0xB5: 50, 0x45: 1,
       0x55: 100, 0x65: 200, 0x75: 200, 0xC5: 50, 0xD5: 50}
REG = {0x1D: R3, 0x2D: R3, 0x3D: R3, 0xAD: R4, 0xBD: R4, 0x4D: R5,
       0x5D: R0, 0x6D: R3, 0x7D: R3, 0xCD: R4, 0xDD: R4}
for jmp32 in (False, True):
    delta = 1 if jmp32 else 0                 # JMP (class 5) -> JMP32 (class 6)
    for op, imm in IMM.items():
        emit(insn(op + delta, R2, imm=imm))
    for op, src in REG.items():
        emit(insn(op + delta, R2, src))
emit(insn(0x05))                              # ja +0

emit(insn(0xB7, R0, imm=0))                   # mov64 r0, 0
emit(insn(0x95))                              # exit

TEXT = b"".join(code)


def write_elf(name: str, text: bytes) -> None:
    elf = bytearray(120 + len(text))
    elf[:16] = bytes.fromhex("7f454c46020101000000000000000000")
    struct.pack_into(
        "<HHIQQQIHHHHHH", elf, 16,
        3, 247, 1, 0x100000000, 64, 0, 3, 64, 56, 1, 0, 0, 0,
    )
    struct.pack_into(
        "<IIQQQQQQ", elf, 64,
        1, 1, 120, 0x100000000, 0x100000000, len(text), len(text), 8,
    )
    elf[120:] = text
    Path(__file__).with_name(name).write_bytes(elf)


if __name__ == "__main__":
    write_elf("sbpfv3_isa_matrix.so", TEXT)
    slots = len(TEXT) // 8
    print(f"sbpfv3_isa_matrix.so: {slots} slots, {slots - 1} logical instructions")
