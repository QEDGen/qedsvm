#!/usr/bin/env python3
"""
Corpus generator for the solanalib differential oracle (SPIKE).

Emits one test vector per line in the shared `sbpf-oracle` contract:

    <version> <fuel> <byte0> <byte1> ...

Two corpora:
  --mode core  : register-only SBPFv1 programs over r0..r9 using the opcode
                 set BOTH engines model (ALU 32/64 imm+reg, mov, neg, shifts,
                 div/mod, conditional/unconditional jumps, lddw), ending in
                 EXIT. Maximizes the value-comparison (`ok N` vs `ok N`) bucket.
  --edge       : deliberately probes the known divergence axes (writes to r10,
                 immediate shift >= width, byteswap le/be, PQR-class opcodes)
                 so the diff harness can confirm the qedsvm-stricter buckets.

SBPFv1 only: neg/mul/div/mod live in the base ALU, and we avoid memory ops,
calls, and syscalls so initial-register/memory-layout differences between the
two models never become observable.
"""
import argparse
import random
import struct

# (name, opcode, has_src_reg_variant, src_imm_opcode) — base ALU/jump opcodes.
# We encode the register/immediate choice via the opcode + regbyte.
ALU64_IMM = {  # class 7, src=0
    "add": 0x07, "sub": 0x17, "mul": 0x27, "div": 0x37, "or": 0x47,
    "and": 0x57, "lsh": 0x67, "rsh": 0x77, "mod": 0x97, "xor": 0xA7,
    "mov": 0xB7, "arsh": 0xC7,
}
ALU64_REG = {  # class 7, src=1 (opcode = imm | 0x08)
    k: (v | 0x08) for k, v in ALU64_IMM.items()
}
ALU32_IMM = {  # class 4
    "add": 0x04, "sub": 0x14, "mul": 0x24, "div": 0x34, "or": 0x44,
    "and": 0x54, "lsh": 0x64, "rsh": 0x74, "mod": 0x94, "xor": 0xA4,
    "mov": 0xB4, "arsh": 0xC4,
}
ALU32_REG = {k: (v | 0x08) for k, v in ALU32_IMM.items()}

NEG64 = 0x87
NEG32 = 0x84
EXIT = 0x95
JA = 0x05

JMP_IMM = {  # class 5, src=0
    "jeq": 0x15, "jgt": 0x25, "jge": 0x35, "jset": 0x45, "jne": 0x55,
    "jsgt": 0x65, "jsge": 0x75, "jlt": 0xA5, "jle": 0xB5, "jslt": 0xC5,
    "jsle": 0xD5,
}
JMP_REG = {k: (v | 0x08) for k, v in JMP_IMM.items()}  # 0x1d..0xdd


def enc(opc, dst=0, src=0, off=0, imm=0):
    """Encode one 8-byte sBPF slot as a list of decimal byte values."""
    regbyte = ((src & 0xF) << 4) | (dst & 0xF)
    off_b = struct.pack("<h", off)          # signed i16 LE
    imm_b = struct.pack("<i", imm)          # signed i32 LE
    return [opc, regbyte, off_b[0], off_b[1], imm_b[0], imm_b[1], imm_b[2], imm_b[3]]


def enc_lddw(dst, imm64):
    """Encode the 16-byte lddw form (low imm in slot 0, high imm in slot 1)."""
    lo = imm64 & 0xFFFFFFFF
    hi = (imm64 >> 32) & 0xFFFFFFFF
    s0 = enc(0x18, dst=dst, imm=struct.unpack("<i", struct.pack("<I", lo))[0])
    s1 = enc(0x00, imm=struct.unpack("<i", struct.pack("<I", hi))[0])
    return s0 + s1


SHIFT_OPS = {"lsh", "rsh", "arsh"}


def gen_core_program(rng):
    """A random register-only program over r0..r9, terminating in EXIT.

    Two-pass: pass 1 picks each logical instruction (jumps record a forward
    LOGICAL target); pass 2 lays out slot positions (lddw = 2 slots, the rest
    1) and resolves each jump's offset in true SLOT units, so jumps always
    land on a real instruction boundary rather than spuriously misresolving.
    """
    n = rng.randint(1, 14)
    # pass 1: ops as dicts. jump ops carry tgt = logical index to land on.
    ops = []
    for i in range(n):
        kind = rng.random()
        if kind < 0.12:
            ops.append({"t": "lddw", "dst": rng.randint(0, 9),
                        "imm64": rng.getrandbits(64)})
        elif kind < 0.64:
            table = rng.choice([ALU64_IMM, ALU64_REG, ALU32_IMM, ALU32_REG])
            op = rng.choice(list(table.keys()))
            dst = rng.randint(0, 9)
            if table in (ALU64_REG, ALU32_REG):
                ops.append({"t": "alu_reg", "opc": table[op], "dst": dst,
                            "src": rng.randint(0, 9)})
            else:
                width = 64 if table is ALU64_IMM else 32
                if op in SHIFT_OPS:
                    imm = rng.randint(0, width - 1)
                elif op in ("div", "mod"):
                    imm = rng.randint(1, 1000)
                else:
                    imm = rng.randint(-(2**31), 2**31 - 1)
                ops.append({"t": "alu_imm", "opc": table[op], "dst": dst, "imm": imm})
        elif kind < 0.76:
            ops.append({"t": "neg", "opc": rng.choice([NEG64, NEG32]),
                        "dst": rng.randint(0, 9)})
        else:
            # forward jump: land on a real logical instruction in (i, n]
            tgt = rng.randint(i + 1, n)
            if rng.random() < 0.2:
                ops.append({"t": "ja", "tgt": tgt})
            else:
                table = rng.choice([JMP_IMM, JMP_REG])
                op = rng.choice(list(table.keys()))
                d = {"t": "jmp", "opc": table[op], "dst": rng.randint(0, 9), "tgt": tgt}
                if table is JMP_REG:
                    d["src"] = rng.randint(0, 9)
                else:
                    d["imm"] = rng.randint(-50, 50)
                ops.append(d)
    ops.append({"t": "exit"})

    # pass 2a: slot index of each logical op (lddw spans 2 slots).
    slot_of = []
    pos = 0
    for o in ops:
        slot_of.append(pos)
        pos += 2 if o["t"] == "lddw" else 1

    # pass 2b: encode. jump slot offset = slot_of[tgt] - slot_of[i] - 1.
    flat = []
    for i, o in enumerate(ops):
        t = o["t"]
        if t == "lddw":
            flat += enc_lddw(o["dst"], o["imm64"])
        elif t == "alu_reg":
            flat += enc(o["opc"], dst=o["dst"], src=o["src"])
        elif t == "alu_imm":
            flat += enc(o["opc"], dst=o["dst"], imm=o["imm"])
        elif t == "neg":
            flat += enc(o["opc"], dst=o["dst"])
        elif t == "exit":
            flat += enc(EXIT)
        else:
            off = slot_of[o["tgt"]] - slot_of[i] - 1
            if t == "ja":
                flat += enc(JA, off=off)
            elif "src" in o:
                flat += enc(o["opc"], dst=o["dst"], src=o["src"], off=off)
            else:
                flat += enc(o["opc"], dst=o["dst"], imm=o["imm"], off=off)
    return flat


def gen_edge_programs():
    """Deliberate probes of the known divergence axes."""
    progs = []
    # write to r10 (CannotWriteR10) -> qedsvm reject, solanalib executes
    progs.append(("r10_write", enc(0xB7, dst=10, imm=5) + enc(EXIT)))
    # immediate shift >= width (ShiftWithOverflow) -> qedsvm reject
    progs.append(("shift64_oob", enc(0x67, dst=0, imm=64) + enc(EXIT)))
    progs.append(("shift32_oob", enc(0x64, dst=0, imm=40) + enc(EXIT)))
    # byteswap le/be (0xd4/0xdc) -> qedsvm has no such Insn (reject); solanalib runs
    progs.append(("le16", enc(0xD4, dst=0, imm=16) + enc(EXIT)))
    progs.append(("be64", enc(0xDC, dst=0, imm=64) + enc(EXIT)))
    # PQR-class opcode 0x86 (v2 uhmul/sdiv etc.) -> qedsvm reject under v1
    progs.append(("pqr_86", enc(0x86, dst=0, src=1) + enc(EXIT)))
    # div by zero immediate -> both fault (sanity that agree-fault fires)
    progs.append(("div0_imm", enc(0x37, dst=0, imm=0) + enc(EXIT)))
    return progs


def gen_sharp_programs():
    """Targeted probes of the highest-risk semantic boundary: how a 32-bit
    ALU result is widened to 64 bits (sign- vs zero-extend), plus 64-bit
    wrap and arithmetic-shift sign behavior. Each ends in EXIT; the comment
    notes qedsvm's expected r0 (zero-extension model)."""
    P = []
    # 0 - 1 in 32 bits = 0xFFFFFFFF. zero-ext: 4294967295 / sign-ext: 2^64-1
    P.append(("sub32_underflow", enc(0x14, dst=0, imm=1) + enc(EXIT)))
    # 0x7FFFFFFF + 1 = 0x80000000 (bit31 set)
    P.append(("add32_to_highbit",
              enc(0xB4, dst=0, imm=0x7FFFFFFF) + enc(0x04, dst=0, imm=1) + enc(EXIT)))
    # 0xFFFF * 0xFFFF = 0xFFFE0001 (bit31 set)
    P.append(("mul32_highbit",
              enc(0xB4, dst=0, imm=0xFFFF) + enc(0x24, dst=0, imm=0xFFFF) + enc(EXIT)))
    # mov32 -1 -> 0xFFFFFFFF (mov is zero-extend in both)
    P.append(("mov32_neg_imm", enc(0xB4, dst=0, imm=-1) + enc(EXIT)))
    # neg32 of 1 -> 0xFFFFFFFF in 32 bits
    P.append(("neg32_one",
              enc(0xB4, dst=0, imm=1) + enc(NEG32, dst=0) + enc(EXIT)))
    # arsh32 of 0x80000000 by 4 -> 0xF8000000 (32-bit arithmetic)
    P.append(("arsh32_highbit",
              enc(0xB4, dst=0, imm=-2147483648) + enc(0xC4, dst=0, imm=4) + enc(EXIT)))
    # rsh32 (logical) of 0x80000000 by 4 -> 0x08000000
    P.append(("rsh32_highbit",
              enc(0xB4, dst=0, imm=-2147483648) + enc(0x74, dst=0, imm=4) + enc(EXIT)))
    # lsh32 1 << 31 -> 0x80000000
    P.append(("lsh32_to_signbit",
              enc(0xB4, dst=0, imm=1) + enc(0x64, dst=0, imm=31) + enc(EXIT)))
    # 64-bit wrap: 0xFFFFFFFFFFFFFFFF + 1 -> 0
    P.append(("add64_wrap",
              enc_lddw(0, 0xFFFFFFFFFFFFFFFF) + enc(0x07, dst=0, imm=1) + enc(EXIT)))
    # arsh64 of 0x8000...0 by 4 -> 0xF800...0
    P.append(("arsh64_highbit",
              enc_lddw(0, 0x8000000000000000) + enc(0xC7, dst=0, imm=4) + enc(EXIT)))
    # div32 unsigned: 0xFFFFFFFF / 2 -> 0x7FFFFFFF
    P.append(("div32_unsigned",
              enc(0xB4, dst=0, imm=-1) + enc(0x34, dst=0, imm=2) + enc(EXIT)))
    # mov32 high imm then read whole 64-bit reg
    P.append(("mov32_highbit_imm", enc(0xB4, dst=0, imm=-2147483648) + enc(EXIT)))
    return P


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", choices=["core", "edge", "sharp"], default="core")
    ap.add_argument("--n", type=int, default=2000, help="core program count")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--fuel", type=int, default=100000)
    ap.add_argument("--version", type=int, default=1)
    args = ap.parse_args()

    if args.mode in ("edge", "sharp"):
        progs = gen_edge_programs() if args.mode == "edge" else gen_sharp_programs()
        for _name, prog in progs:
            print(f"{args.version} {args.fuel} " + " ".join(str(b) for b in prog))
        return

    rng = random.Random(args.seed)
    for _ in range(args.n):
        prog = gen_core_program(rng)
        print(f"{args.version} {args.fuel} " + " ".join(str(b) for b in prog))


if __name__ == "__main__":
    main()
