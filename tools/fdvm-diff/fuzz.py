#!/usr/bin/env python3
"""Random sBPF programs for the three-engine differential run.

Programs are built from blocks: a main block and a few functions, each a
random instruction run ending in `exit`. The mix covers ALU64/ALU32 (immediate
and register, every operator, out-of-range shifts and zero divisors), loads and
stores against the input region and the stack (in and just out of bounds),
forward and backward conditional jumps (backward ones loop until the CU budget
runs out), calls to later functions (and, rarely, recursion), `callx` through a
computed text address or a junk register (V3 only until #134, unless
`--v0-callx`), `sol_log_64_`, and, rarely, an
instruction the verifier should reject. Cases set
`virtual_address_space_adjustments` (no stack frame gaps), the configuration
qedsvm models (all features on, as mollusk runs). No expectation is recorded
(`status: null`): the engines are compared against each other.

  fuzz.py --seed N --count K -o fuzz.bin --expect fuzz.expect.jsonl

The same seed always gives the same batch, so a failure replays exactly."""
import argparse, json, os, random, struct, sys
sys.path.insert(0, os.path.dirname(__file__))
from caselib import insn, pack_case, pack_batch, FEAT_VAS_ADJ
from murmur import murmur3_32

SOL_LOG_64 = murmur3_32(b"sol_log_64_")
TEXT_VADDR = 0x1_0000_0000
INPUT_LEN = 64
EXIT = 0x95

ALU_OPS = [0x00, 0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x90, 0xa0, 0xb0, 0xc0]
JMP_OPS = [0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0xa0, 0xb0, 0xc0, 0xd0]
# (ldx, st, stx, bytes) per width
MEM = [(0x71, 0x72, 0x73, 1), (0x69, 0x6a, 0x6b, 2), (0x61, 0x62, 0x63, 4), (0x79, 0x7a, 0x7b, 8)]

def fn_key(slot):
    return murmur3_32(struct.pack("<Q", slot))

class Gen:
    """One program. Items are (kind, payload); jumps and calls are resolved to
    slot offsets once every block's layout is known."""

    def __init__(self, rng, version, v0_callx):
        self.r, self.v, self.v0_callx = rng, version, v0_callx
        self.nfun = rng.choice([0, 0, 1, 2, 3])

    def reg(self):  # a destination: never r10
        return self.r.choice([0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9])

    def src(self):
        return self.r.choice(range(11))

    def imm(self):
        r = self.r
        return r.choice([0, 1, -1, 2, 7, 31, 32, 63, 64, 0x7fffffff, -0x80000000,
                         r.randrange(-0x80000000, 0x80000000), r.randrange(0, 256)])

    def alu(self):
        r = self.r
        cls = r.choice([0x07, 0x04])                  # ALU64 / ALU32
        op = r.choice(ALU_OPS)
        width = 64 if cls == 0x07 else 32
        if r.random() < 0.5:                          # register source
            return insn(op | cls | 0x08, dst=self.reg(), src=self.src())
        imm = self.imm()
        if op in (0x60, 0x70, 0xc0) and r.random() < 0.9:
            imm = r.randrange(0, width)               # mostly in-range shifts
        if op in (0x30, 0x90) and imm == 0 and r.random() < 0.95:
            imm = r.choice([1, 3, -1])                # mostly non-zero divisors
        return insn(op | cls, dst=self.reg(), imm=imm)

    def mem(self):
        r = self.r
        ldx, st, stx, n = r.choice(MEM)
        if r.random() < 0.6:                          # input region via r1
            base, off = 1, r.choice([r.randrange(0, INPUT_LEN - n + 1)] * 6
                                    + [-n, INPUT_LEN - n + 1, INPUT_LEN])
        else:                                         # stack via r10
            base, off = 10, r.choice([-n * r.randrange(1, 64)] * 6 + [0, -0x1000 - n, 8])
        kind = r.choice(["ldx", "st", "stx"])
        if kind == "ldx":
            return insn(ldx, dst=self.reg(), src=base, off=off)
        if kind == "st":
            return insn(st, dst=base, off=off, imm=self.imm())
        return insn(stx, dst=base, src=self.src(), off=off)

    def block(self, idx, n):
        """Item list for block `idx` (0 = main, 1.. = functions)."""
        r, items = self.r, []
        for _ in range(n):
            p = r.random()
            if p < 0.40:
                items.append(("raw", self.alu()))
            elif p < 0.62:
                items.append(("raw", self.mem()))
            elif p < 0.74:
                items.append(("jmp", None))
            elif p < 0.80:
                items.append(("raw", insn(0xb7, dst=self.reg(), imm=self.imm())))
            elif p < 0.85 and self.v == 0:
                items.append(("lddw", (self.reg(), r.getrandbits(64))))
            elif p < 0.89:
                items.append(("log", None))
            elif p < 0.94 and self.nfun:
                hi = range(idx + 1, self.nfun + 1)
                tgt = r.choice(list(hi)) if hi and r.random() < 0.95 else idx or 1
                items.append(("call", tgt))
            elif p < 0.96 and (self.v >= 3 or self.v0_callx):
                items.append(("callx", r.choice([None] + list(range(self.nfun + 1)))))
            elif p < 0.98 and self.v == 0:
                items.append(("raw", insn(r.choice([0xd4, 0xdc]), dst=self.reg(),
                                          imm=r.choice([16, 32, 64]))))
            elif p < 0.998:
                items.append(("raw", insn(r.choice([0x87, 0x84]), dst=self.reg())))
            else:                                     # verifier fodder
                items.append(("raw", r.choice([
                    insn(0x07, dst=10, imm=1), insn(0x37, dst=0, imm=0),
                    insn(0x67, dst=0, imm=64), insn(0xff), insn(0x05, off=0x7fff)])))
        items.append(("raw", insn(EXIT)))
        return items

    def build(self):
        r = self.r
        blocks = [self.block(i, r.randrange(3, 25)) for i in range(self.nfun + 1)]
        size = {"raw": 1, "jmp": 1, "log": 1, "call": 1, "lddw": 2, "callx": 4}
        starts, slot = [], 0
        for b in blocks:
            starts.append(slot)
            slot += sum(size[k] for k, _ in b)
        out, slot = b"", 0
        for bi, b in enumerate(blocks):
            pos, s = [], starts[bi]
            for k, _ in b:
                pos.append(s); s += size[k]
            for ii, (k, payload) in enumerate(b):
                here = pos[ii]
                if k == "raw":
                    out += payload
                elif k == "lddw":
                    d, v = payload
                    out += insn(0x18, dst=d, imm=v & 0xffffffff) + insn(0, imm=v >> 32)
                elif k == "jmp":
                    tgt = pos[r.randrange(0, len(b))]   # anywhere in this block
                    if tgt > here or r.random() < 0.3:
                        out += self.jump(tgt - here - 1)
                    else:
                        out += self.jump(pos[-1] - here - 1)  # forward to the exit
                elif k == "log":
                    out += insn(0x85, imm=SOL_LOG_64)
                elif k == "call":
                    if self.v >= 3:
                        out += insn(0x85, src=1, imm=starts[payload] - here - 1)
                    else:
                        out += insn(0x85, imm=fn_key(starts[payload]))
                elif k == "callx":
                    rx = r.choice([2, 3, 4, 5, 6, 7, 8, 9])
                    addr = TEXT_VADDR + 8 * starts[payload] if payload is not None \
                        else r.getrandbits(32)
                    out += insn(0xb7, dst=rx, imm=addr >> 32 or 0)       # rx = hi
                    out += insn(0x67, dst=rx, imm=32)                     # rx <<= 32
                    out += insn(0x07, dst=rx, imm=addr & 0x7fffffff)     # rx += lo
                    out += insn(0x8d, dst=rx) if self.v >= 3 else insn(0x8d, imm=rx)
        return out, starts[1:]

    def jump(self, off):
        r = self.r
        if r.random() < 0.15:
            return insn(0x05, off=off)
        op = r.choice(JMP_OPS)
        cls = 0x06 if self.v >= 3 and r.random() < 0.3 else 0x05   # JMP32 is V3 only
        if r.random() < 0.5:
            return insn(op | cls | 0x08, dst=self.reg(), src=self.src(), off=off)
        return insn(op | cls, dst=self.reg(), off=off, imm=self.imm())

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, required=True)
    ap.add_argument("--count", type=int, default=500)
    ap.add_argument("--v0-callx", action="store_true",
                    help="emit V0 callx, which qedsvm fails closed on (#134)")
    ap.add_argument("-o", required=True); ap.add_argument("--expect", required=True)
    a = ap.parse_args()
    rng = random.Random(a.seed)
    cases, meta = [], []
    for i in range(a.count):
        version = rng.choice([0, 0, 3])
        text, fns = Gen(rng, version, a.v0_callx).build()
        regs = {i: rng.getrandbits(64) for i in range(2, 10) if rng.random() < 0.5}
        input_ = bytes(rng.getrandbits(8) for _ in range(INPUT_LEN))
        cases.append(pack_case(text, version=version, budget=rng.choice([300, 2_000]),
                               heap_max=0, input_=input_, regs=regs, features=FEAT_VAS_ADJ,
                               calldests=fns if version == 0 else ()))
        meta.append(dict(file="fuzz", line=f"{a.seed}:{i}", status=None, exp=None,
                         skip=None, text=text.hex()))
    open(a.o, "wb").write(pack_batch(cases))
    with open(a.expect, "w") as fh:
        for m in meta: fh.write(json.dumps(m) + "\n")
    print(f"{len(cases)} cases (seed {a.seed})", file=sys.stderr)

if __name__ == "__main__":
    main()
